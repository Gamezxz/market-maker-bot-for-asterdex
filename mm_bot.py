#!/usr/bin/env python3
"""Simple ASTER market making bot.

Configuration constants live at the top of this file per the user request.
The bot places opposing limit orders around the mid price, manages fills
with timeout logic, and flattens inventory after sustained profit.
"""

import hashlib
import hmac
import json
import logging
import os
import time
from dataclasses import dataclass
from decimal import Decimal, ROUND_CEILING, ROUND_DOWN, ROUND_FLOOR, ROUND_HALF_UP, getcontext
from typing import Any, Dict, Optional
from urllib.parse import urlencode

import requests
from pathlib import Path


def _load_env_file() -> None:
    env_path = Path(__file__).resolve().parent / ".env"
    if not env_path.exists():
        return
    try:
        content = env_path.read_text(encoding="utf-8")
    except OSError as exc:  # noqa: BLE001
        logging.getLogger(__name__).warning("Unable to read .env file: %s", exc)
        return
    for raw_line in content.splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("export "):
            line = line[len("export ") :]
        if "=" not in line:
            continue
        key, _, value = line.partition("=")
        key = key.strip()
        value = value.strip().strip("'\"")
        if key and key not in os.environ:
            os.environ[key] = value


_load_env_file()

# ---------------------------------------------------------------------------
# Configuration (all adjustable values are here)
# ---------------------------------------------------------------------------
API_KEY = os.getenv("ASTERDEX_API_KEY", "")
API_SECRET = os.getenv("ASTERDEX_API_SECRET", "")
SYMBOL = "ASTERUSDT"
ACCOUNT_CAPITAL_USD = Decimal("10000")  # Total trading capital allocated to the bot
RISK_PER_ORDER = Decimal("0.02")  # 2% of capital posted on each side per cycle
MAX_INVENTORY_FRACTION = Decimal("0.08")  # Allow up to 8% capital exposure before managing inventory
PROFIT_TARGET_FRACTION = Decimal("0.005")  # Accept 0.5% profit on inventory before flattening
SPREAD_USD = Decimal("0.004")  # Distance between sell and buy quotes in USDT
ORDER_SIZE_USD = (ACCOUNT_CAPITAL_USD * RISK_PER_ORDER).quantize(Decimal("0.01"), rounding=ROUND_DOWN)
MIN_ORDER_SIZE_FRACTION = Decimal("0.25")  # Do not reduce size below 25% of base order
INVENTORY_DECAY_STRENGTH = Decimal("1.0")  # Higher values shrink orders faster as inventory grows
ORDER_TIMEOUT_SECONDS = 60  # Cancel & refresh quotes if untouched for this long
COUNTER_FILL_WAIT_SECONDS = 30  # Wait for the opposite side after one fill
SLEEP_SECONDS = 1.0  # Main loop sleep between iterations
POSITION_CHECK_INTERVAL = 5.0  # Seconds between position refreshes
INVENTORY_THRESHOLD_USD = (ACCOUNT_CAPITAL_USD * MAX_INVENTORY_FRACTION).quantize(Decimal("0.01"), rounding=ROUND_DOWN)
MIN_PROFIT_TO_CLOSE = (ACCOUNT_CAPITAL_USD * PROFIT_TARGET_FRACTION).quantize(Decimal("0.01"), rounding=ROUND_DOWN)
PNL_HOLD_SECONDS = 60  # Hold profit for 1 minutes before flattening
USE_TESTNET = False  # Flip to True if you have testnet credentials

# ---------------------------------------------------------------------------
# Decimal context
# ---------------------------------------------------------------------------
getcontext().prec = 28


@dataclass
class OrderState:
    order_id: int
    side: str
    price: Decimal
    quantity: Decimal
    created_at: float
    status: str = "NEW"
    executed_qty: Decimal = Decimal("0")


class AsterMarketMaker:
    spot_base_url = "https://sapi.asterdex.com"
    futures_base_url = "https://fapi.asterdex.com"

    def __init__(self) -> None:
        if USE_TESTNET:
            self.spot_base_url = "https://testnet-sapi.asterdex.com"
            self.futures_base_url = "https://testnet-fapi.asterdex.com"

        if not API_KEY or not API_SECRET:
            raise RuntimeError("Missing ASTERDEX_API_KEY/ASTERDEX_API_SECRET configuration")

        self._api_secret = API_SECRET.encode("utf-8")
        self._session = requests.Session()
        self._session.headers.update({
            "X-MBX-APIKEY": API_KEY,
            "User-Agent": "AsterMarketMaker/0.1",
        })

        self._logger = logging.getLogger(self.__class__.__name__)
        self._logger.info("Starting market maker | symbol=%s", SYMBOL)
        self._log_configuration()

        self._symbol_info = self._fetch_symbol_info()
        (
            self.qty_step,
            self.min_qty,
            self.price_tick,
            self.min_notional,
        ) = self._extract_symbol_filters(self._symbol_info)

        self.buy_order: Optional[OrderState] = None
        self.sell_order: Optional[OrderState] = None
        self.cycle_started_at = 0.0
        self.first_fill_side: Optional[str] = None
        self.first_fill_time: Optional[float] = None
        self._last_position_check = 0.0
        self._profit_timer_started: Optional[float] = None
        self._last_position_qty = Decimal("0")
        self._last_position_notional = Decimal("0")

    def _log_configuration(self) -> None:
        self._logger.info(
            "Config | order_size_usd=%s | inventory_threshold_usd=%s | min_profit_to_close=%s",
            self._decimal_to_str(ORDER_SIZE_USD),
            self._decimal_to_str(INVENTORY_THRESHOLD_USD),
            self._decimal_to_str(MIN_PROFIT_TO_CLOSE),
        )

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------
    def run(self) -> None:
        self._cancel_all_orders()
        self._logger.info("Entering main loop")
        try:
            while True:
                now = time.time()

                if self.buy_order:
                    self._refresh_order_state(self.buy_order)
                if self.sell_order:
                    self._refresh_order_state(self.sell_order)

                if not self.buy_order or not self.sell_order:
                    self._place_new_quotes()
                    now = time.time()

                self._evaluate_cycle_timers(now)

                if now - self._last_position_check >= POSITION_CHECK_INTERVAL:
                    self._last_position_check = now
                    self._check_inventory(now)

                time.sleep(SLEEP_SECONDS)
        except KeyboardInterrupt:
            self._logger.info("Shutdown requested; cancelling open orders")
        finally:
            self._cancel_remaining_orders()
            self._cancel_all_orders()
            self.buy_order = None
            self.sell_order = None

    # ------------------------------------------------------------------
    # Quote management
    # ------------------------------------------------------------------
    def _place_new_quotes(self) -> None:
        price_context = self._fetch_mid_price()
        if price_context is None:
            self._logger.warning("Unable to obtain order book snapshot; retrying")
            time.sleep(1)
            return

        bid, ask = price_context
        mid_price = (bid + ask) / Decimal("2")
        half_spread = SPREAD_USD / Decimal("2")
        buy_price = self._round_price(mid_price - half_spread, prefer="down")
        sell_price = self._round_price(mid_price + half_spread, prefer="up")
        if sell_price <= buy_price:
            sell_price = self._round_price(buy_price + self.price_tick)

        base_qty = ORDER_SIZE_USD / mid_price

        buy_qty, buy_scale = self._target_quantity_for_side(base_qty, mid_price, "BUY")
        sell_qty, sell_scale = self._target_quantity_for_side(base_qty, mid_price, "SELL")

        buy_response = self._place_limit_order("BUY", buy_price, buy_qty)
        sell_response = self._place_limit_order("SELL", sell_price, sell_qty)

        self.buy_order = OrderState(
            order_id=int(buy_response["orderId"]),
            side="BUY",
            price=buy_price,
            quantity=buy_qty,
            created_at=time.time(),
            status=buy_response.get("status", "NEW"),
            executed_qty=Decimal(buy_response.get("executedQty", "0")),
        )
        self.sell_order = OrderState(
            order_id=int(sell_response["orderId"]),
            side="SELL",
            price=sell_price,
            quantity=sell_qty,
            created_at=time.time(),
            status=sell_response.get("status", "NEW"),
            executed_qty=Decimal(sell_response.get("executedQty", "0")),
        )
        self.cycle_started_at = time.time()
        self.first_fill_side = None
        self.first_fill_time = None
        self._logger.info(
            "Placed quotes | buy=%s @ %s | sell=%s @ %s | scales=(buy:%s, sell:%s)",
            self._decimal_to_str(self.buy_order.quantity),
            self._decimal_to_str(self.buy_order.price),
            self._decimal_to_str(self.sell_order.quantity),
            self._decimal_to_str(self.sell_order.price),
            self._decimal_to_str(buy_scale),
            self._decimal_to_str(sell_scale),
        )

    def _target_quantity_for_side(
        self,
        base_qty: Decimal,
        mid_price: Decimal,
        side: str,
    ) -> tuple[Decimal, Decimal]:
        scale = self._order_size_scale(side)
        adjusted_qty = base_qty * scale
        target_qty = self._floor_to_step(adjusted_qty, self.qty_step)
        if target_qty < self.min_qty:
            target_qty = self.min_qty

        effective_scale = scale
        if base_qty > 0:
            effective_scale = (target_qty / base_qty).quantize(Decimal("0.0001"), rounding=ROUND_DOWN)

        notional = target_qty * mid_price
        if self.min_notional > 0 and notional < self.min_notional:
            raise RuntimeError(
                "Configured order size below exchange minimum notional: "
                f"side={side}, notional={notional}, min={self.min_notional}"
            )

        return target_qty, effective_scale

    def _evaluate_cycle_timers(self, now: float) -> None:
        if not self.buy_order or not self.sell_order:
            return

        buy_filled = self._order_filled(self.buy_order)
        sell_filled = self._order_filled(self.sell_order)

        if buy_filled and sell_filled:
            self._logger.info("Both sides filled; resetting quote cycle")
            self._reset_cycle()
            return

        if not self.first_fill_side:
            if buy_filled:
                self.first_fill_side = "BUY"
                self.first_fill_time = now
                self._logger.debug("Buy side filled first; waiting for sell fill")
            elif sell_filled:
                self.first_fill_side = "SELL"
                self.first_fill_time = now
                self._logger.debug("Sell side filled first; waiting for buy fill")
        else:
            deadline = (self.first_fill_time or now) + COUNTER_FILL_WAIT_SECONDS
            if now >= deadline:
                self._logger.info(
                    "Counter order did not fill within %ss; refreshing quotes",
                    COUNTER_FILL_WAIT_SECONDS,
                )
                self._cancel_remaining_orders()
                self._reset_cycle()
                return

        if now - self.cycle_started_at >= ORDER_TIMEOUT_SECONDS:
            self._logger.info("Quote timeout reached; refreshing orders")
            self._cancel_remaining_orders()
            self._reset_cycle()

    def _reset_cycle(self) -> None:
        self.buy_order = None
        self.sell_order = None
        self.cycle_started_at = 0.0
        self.first_fill_side = None
        self.first_fill_time = None

    def _refresh_order_state(self, order_state: OrderState) -> None:
        try:
            info = self._get_order(order_state.order_id)
        except Exception as exc:  # noqa: BLE001
            self._logger.warning("Failed to refresh order %s: %s", order_state.order_id, exc)
            return

        order_state.status = info.get("status", order_state.status)
        order_state.executed_qty = Decimal(info.get("executedQty", self._decimal_to_str(order_state.executed_qty)))
        if order_state.status in {"CANCELED", "EXPIRED", "REJECTED"}:
            self._logger.info(
                "Order closed | id=%s | side=%s | status=%s | filled=%s",
                order_state.order_id,
                order_state.side,
                order_state.status,
                self._decimal_to_str(order_state.executed_qty),
            )
            if order_state.side == "BUY":
                self.buy_order = None
            else:
                self.sell_order = None

    def _order_filled(self, order_state: OrderState) -> bool:
        if order_state.status == "FILLED":
            return True
        if order_state.executed_qty > 0 and order_state.status == "PARTIALLY_FILLED":
            return True
        return False

    def _cancel_remaining_orders(self) -> None:
        for state in (self.buy_order, self.sell_order):
            if not state:
                continue
            if state.status in {"CANCELED", "FILLED", "REJECTED", "EXPIRED"}:
                continue
            try:
                self._cancel_order(state.order_id)
                state.status = "CANCELED"
            except Exception as exc:  # noqa: BLE001
                self._logger.warning("Failed to cancel order %s: %s", state.order_id, exc)

    # ------------------------------------------------------------------
    # Inventory & PnL
    # ------------------------------------------------------------------
    def _check_inventory(self, now: float) -> None:
        try:
            position_amt, unrealized_profit, mark_price = self._fetch_position()
        except RuntimeError as exc:
            message = str(exc)
            lowered = message.lower()
            if "-1000" in message and "unknown error" in lowered:
                self._logger.debug("Skipping inventory check due to transient -1000 response from positionRisk: %s", message)
                return
            self._logger.warning("Skipping inventory check; failed to fetch position: %s", message)
            return
        if position_amt == 0:
            if self._profit_timer_started:
                self._logger.debug("Flat position; clearing profit timer")
            self._profit_timer_started = None
            self._last_position_qty = Decimal("0")
            self._last_position_notional = Decimal("0")
            return

        abs_position = abs(position_amt)
        price_reference = mark_price
        if price_reference <= 0:
            mid_context = self._fetch_mid_price()
            if mid_context:
                price_reference = (mid_context[0] + mid_context[1]) / Decimal("2")
        if price_reference <= 0:
            self._logger.warning("Cannot determine price reference for inventory; skipping check")
            return

        position_notional = abs_position * price_reference
        self._logger.debug(
            "Position status | size=%s | notional=%s | unrealized=%s",
            self._decimal_to_str(position_amt),
            self._decimal_to_str(position_notional),
            self._decimal_to_str(unrealized_profit),
        )

        self._last_position_qty = position_amt
        self._last_position_notional = position_notional

        if position_notional >= INVENTORY_THRESHOLD_USD and unrealized_profit >= MIN_PROFIT_TO_CLOSE:
            if not self._profit_timer_started:
                self._profit_timer_started = now
                self._logger.info(
                    "Inventory threshold met; profit timer started (notional=%s, pnl=%s)",
                    self._decimal_to_str(position_notional),
                    self._decimal_to_str(unrealized_profit),
                )
            elif now - self._profit_timer_started >= PNL_HOLD_SECONDS:
                self._logger.info(
                    "Sustained profit detected; flattening position | notional=%s | pnl=%s",
                    self._decimal_to_str(position_notional),
                    self._decimal_to_str(unrealized_profit),
                )
                self._flatten_position(position_amt)
                self._profit_timer_started = None
        else:
            self._profit_timer_started = None

    def _flatten_position(self, position_amt: Decimal) -> None:
        side = "SELL" if position_amt > 0 else "BUY"
        qty = self._floor_to_step(abs(position_amt), self.qty_step)
        if qty <= 0:
            self._logger.warning("Remaining position too small to flatten cleanly")
            return
        payload = {
            "symbol": SYMBOL,
            "side": side,
            "type": "MARKET",
            "quantity": self._decimal_to_str(qty),
            "reduceOnly": "true",
        }
        try:
            response = self._request(self.futures_base_url, "/fapi/v1/order", method="POST", params=payload, signed=True)
        except Exception as exc:  # noqa: BLE001
            self._logger.error("Failed to flatten position: %s", exc)
            return
        self._logger.info("Flattened position via %s | response=%s", side, json.dumps(response))

    # ------------------------------------------------------------------
    # REST helpers
    # ------------------------------------------------------------------
    def _fetch_last_price(self) -> Optional[Decimal]:
        try:
            ticker = self._request(
                self.futures_base_url,
                "/fapi/v1/ticker/price",
                params={"symbol": SYMBOL},
            )
        except Exception as exc:  # noqa: BLE001
            self._logger.warning("Failed to fetch last price: %s", exc)
            return None

        price_str = ticker.get("price") if isinstance(ticker, dict) else None
        if not price_str:
            self._logger.warning("Ticker price response missing price field: %s", ticker)
            return None

        try:
            return Decimal(price_str)
        except Exception as exc:  # noqa: BLE001
            self._logger.warning("Invalid last price payload %s: %s", price_str, exc)
            return None

    def _fetch_mid_price(self) -> Optional[tuple[Decimal, Decimal]]:
        last_price = self._fetch_last_price()
        if last_price is not None and last_price > 0:
            return last_price, last_price

        try:
            depth = self._request(
                self.futures_base_url,
                "/fapi/v1/depth",
                params={"symbol": SYMBOL, "limit": 5},
            )
        except Exception as exc:  # noqa: BLE001
            self._logger.warning("Failed to fetch order book: %s", exc)
            return None

        bids = depth.get("bids") or []
        asks = depth.get("asks") or []
        if not bids or not asks:
            return None

        best_bid = Decimal(bids[0][0])
        best_ask = Decimal(asks[0][0])
        return best_bid, best_ask

    def _place_limit_order(self, side: str, price: Decimal, quantity: Decimal) -> Dict[str, Any]:
        payload = {
            "symbol": SYMBOL,
            "side": side,
            "type": "LIMIT",
            "timeInForce": "GTC",
            "quantity": self._decimal_to_str(quantity),
            "price": self._decimal_to_str(price),
        }
        return self._request(self.futures_base_url, "/fapi/v1/order", method="POST", params=payload, signed=True)

    def _cancel_all_orders(self) -> None:
        try:
            self._request(self.futures_base_url, "/fapi/v1/allOpenOrders", method="DELETE", params={"symbol": SYMBOL}, signed=True)
            self._logger.info("Cancelled all open orders on startup")
        except Exception as exc:  # noqa: BLE001
            self._logger.warning("Failed to cancel all orders on startup: %s", exc)

    def _cancel_order(self, order_id: int) -> None:
        payload = {"symbol": SYMBOL, "orderId": order_id}
        self._request(self.futures_base_url, "/fapi/v1/order", method="DELETE", params=payload, signed=True)
        self._logger.debug("Cancelled order id=%s", order_id)

    def _get_order(self, order_id: int) -> Dict[str, Any]:
        payload = {"symbol": SYMBOL, "orderId": order_id}
        return self._request(self.futures_base_url, "/fapi/v1/order", params=payload, signed=True)

    def _fetch_position(self) -> tuple[Decimal, Decimal, Decimal]:
        params = {"symbol": SYMBOL}
        try:
            data = self._request(self.futures_base_url, "/fapi/v2/positionRisk", params=params, signed=True)
        except RuntimeError as exc:
            message = str(exc)
            lowered = message.lower()
            if "-1000" in message and "unknown error" in lowered:
                self._logger.debug(
                    "positionRisk endpoint returned -1000 unknown error; assuming empty position | error=%s",
                    message,
                )
                return Decimal("0"), Decimal("0"), Decimal("0")
            raise RuntimeError(f"positionRisk request failed: {exc}") from exc
        position_info: Optional[Dict[str, Any]] = None
        if isinstance(data, list):
            for entry in data:
                if entry.get("symbol") == SYMBOL:
                    position_info = entry
                    break
        elif isinstance(data, dict) and data.get("symbol") == SYMBOL:
            position_info = data

        if not position_info:
            return Decimal("0"), Decimal("0"), Decimal("0")

        position_amt = Decimal(position_info.get("positionAmt", "0"))
        unrealized = Decimal(position_info.get("unRealizedProfit", "0"))
        mark_price = Decimal(position_info.get("markPrice", "0") or "0")
        return position_amt, unrealized, mark_price

    def _fetch_symbol_info(self) -> Dict[str, Any]:
        exchange_info = self._request(self.futures_base_url, "/fapi/v1/exchangeInfo")
        for symbol in exchange_info.get("symbols", []):
            if symbol.get("symbol") == SYMBOL:
                return symbol
        raise RuntimeError(f"Symbol {SYMBOL} not found in exchangeInfo")

    def _extract_symbol_filters(self, symbol_info: Dict[str, Any]) -> tuple[Decimal, Decimal, Decimal, Decimal]:
        lot_filter = self._get_filter(symbol_info, "LOT_SIZE")
        qty_step = Decimal(lot_filter["stepSize"])
        min_qty = Decimal(lot_filter["minQty"])

        price_filter = self._get_filter(symbol_info, "PRICE_FILTER")
        price_tick = Decimal(price_filter["tickSize"])

        try:
            notional_filter = self._get_filter(symbol_info, "MIN_NOTIONAL")
            min_notional = Decimal(notional_filter.get("notional") or notional_filter.get("minNotional") or "0")
        except RuntimeError:
            min_notional = Decimal("0")

        return qty_step, min_qty, price_tick, min_notional

    def _get_filter(self, symbol_info: Dict[str, Any], filter_type: str) -> Dict[str, Any]:
        for f in symbol_info.get("filters", []):
            if f.get("filterType") == filter_type:
                return f
        raise RuntimeError(f"Filter {filter_type} not found for symbol {SYMBOL}")

    # ------------------------------------------------------------------
    # Generic request helpers
    # ------------------------------------------------------------------
    def _request(
        self,
        base_url: str,
        path: str,
        params: Optional[Dict[str, Any]] = None,
        *,
        method: str = "GET",
        signed: bool = False,
    ) -> Any:
        url = f"{base_url}{path}"
        params = params or {}
        if signed:
            request_params = self._sign_params(params)
        else:
            request_params = dict(params)

        method_upper = method.upper()
        if method_upper == "GET":
            response = self._session.get(url, params=request_params, timeout=10)
        else:
            response = self._session.request(method_upper, url, data=request_params, timeout=10)

        if response.status_code != 200:
            raise RuntimeError(f"HTTP {response.status_code}: {response.text}")

        data = response.json()
        if isinstance(data, dict) and "code" in data:
            code_val = data.get("code")
            if code_val in (0, "0"):
                return data
            message = str(data.get("msg", "")).lower()
            if code_val == 200 and "cancel all open order" in message:
                return {}
            raise RuntimeError(f"API error: {data}")
        return data

    def _sign_params(self, params: Dict[str, Any]) -> Dict[str, Any]:
        payload = dict(params)
        payload.setdefault("recvWindow", 5000)
        payload["timestamp"] = int(time.time() * 1000)
        query = urlencode(payload, doseq=True)
        signature = hmac.new(self._api_secret, query.encode("utf-8"), hashlib.sha256).hexdigest()
        payload["signature"] = signature
        return payload

    @staticmethod
    def _decimal_to_str(value: Decimal) -> str:
        s = format(value, "f")
        if "." in s:
            s = s.rstrip("0").rstrip(".")
        return s or "0"

    @staticmethod
    def _floor_to_step(value: Decimal, step: Decimal) -> Decimal:
        if step <= 0:
            return value
        remainder = value % step
        return (value - remainder).quantize(step, rounding=ROUND_DOWN)

    def _round_price(self, price: Decimal, *, prefer: str = "nearest") -> Decimal:
        if self.price_tick <= 0:
            return price
        scaled = price / self.price_tick
        if prefer == "up":
            scaled = scaled.to_integral_value(rounding=ROUND_CEILING)
        elif prefer == "down":
            scaled = scaled.to_integral_value(rounding=ROUND_FLOOR)
        else:
            scaled = scaled.to_integral_value(rounding=ROUND_HALF_UP)
        quantized = (scaled * self.price_tick).quantize(self.price_tick, rounding=ROUND_HALF_UP)
        return quantized

    def _order_size_scale(self, side: str) -> Decimal:
        notional = abs(self._last_position_notional)
        if notional <= 0 or INVENTORY_THRESHOLD_USD <= 0:
            return Decimal("1")

        position_side: Optional[str]
        if self._last_position_qty > 0:
            position_side = "BUY"
        elif self._last_position_qty < 0:
            position_side = "SELL"
        else:
            position_side = None

        if position_side and position_side == side.upper():
            return Decimal("1")

        ratio = notional / INVENTORY_THRESHOLD_USD
        decay = Decimal("1") / (Decimal("1") + (ratio * INVENTORY_DECAY_STRENGTH))
        if decay > Decimal("1"):
            decay = Decimal("1")
        return max(decay, MIN_ORDER_SIZE_FRACTION)


# ---------------------------------------------------------------------------
# Entrypoint
# ---------------------------------------------------------------------------
def configure_logging() -> None:
    level_name = os.getenv("MM_LOG_LEVEL", "INFO")
    level = getattr(logging, level_name.upper(), logging.INFO)
    class _ColorFormatter(logging.Formatter):
        COLOR_MAP = {
            logging.DEBUG: "\033[36m",  # Cyan
            logging.INFO: "\033[32m",  # Green
            logging.WARNING: "\033[33m",  # Yellow
            logging.ERROR: "\033[31m",  # Red
            logging.CRITICAL: "\033[35m",  # Magenta
        }
        RESET = "\033[0m"

        def format(self, record: logging.LogRecord) -> str:
            message = super().format(record)
            color = self.COLOR_MAP.get(record.levelno)
            if not color:
                return message
            return f"{color}{message}{self.RESET}"

    formatter = _ColorFormatter("%(levelname)s | %(message)s")
    handler = logging.StreamHandler()
    handler.setFormatter(formatter)

    root_logger = logging.getLogger()
    for existing in list(root_logger.handlers):
        root_logger.removeHandler(existing)
    root_logger.addHandler(handler)
    root_logger.setLevel(level)


def main() -> None:
    configure_logging()
    bot = AsterMarketMaker()
    bot.run()


if __name__ == "__main__":
    main()

import os, time, ccxt.async_support as ccxt, requests, pandas as pd, pandas_ta as ta
import datetime, logging, numpy as np, json, sqlite3, asyncio, aiohttp
from flask import Flask
from threading import Thread, Lock
from collections import OrderedDict, defaultdict

try:
    import websocket as ws_lib
    WS_AVAILABLE = True
except ImportError:
    WS_AVAILABLE = False
    logging.getLogger(__name__).warning("websocket-client 未安裝，CVD 降級為 REST 模式")

logging.basicConfig(
    level=logging.INFO,
    format=\'%(asctime)s [%(levelname)s] %(message)s\'
    datefmt=\'%Y-%m-%d %H:%M:%S\'
)
log = logging.getLogger(__name__)

app = Flask(__name__)

# --- 共享狀態與鎖定 ---
threads_started   = False
threads_lock      = Lock()
sent_signals      = OrderedDict()
signals_lock      = Lock()
active_positions  = {}
positions_lock    = Lock()

ws_cvd_buffer  = defaultdict(lambda: {\'buy\': 0.0, \'sell\': 0.0, \'ts\': 0.0})
ws_cvd_lock    = Lock()
ws_connections = {}

DB_PATH = \'/app/data/radar_v2_pro.db\'

# --- 可調參數 ---
TOP_SYMBOLS        = 40
MAX_POSITIONS      = 10
MAX_LONG           = 6
MAX_SHORT          = 6
MAX_SIGNALS_MEMORY = 500
SIGNAL_EXPIRY_TIME = 86400

ATR_TP1_MULT   = 2.0
ATR_TP2_MULT   = 4.0
MAX_HOLD_HOURS = 48

# SL_STRUCT_BUFFER = 0.003 # 移除固定緩衝，改為動態
MIN_SL_PCT       = 0.03
MAX_SL_PCT       = 0.12

EMA_FAST  = 20
EMA_MID   = 50
EMA_SLOW  = 200

BREAKOUT_LOOKBACK  = 20
VOLUME_MULTIPLIER  = 2.0

RSI_BULL_MIN = 55
RSI_BULL_MAX = 72
RSI_BEAR_MIN = 28
RSI_BEAR_MAX = 45

WINRATE_THRESHOLD   = 0.40
WINRATE_REDUCED_MAX = 5

TIMEFRAME = \'4h\'

# --- 新增抗震盪參數 ---
BB_WIDTH_LOOKBACK   = 100 # 計算布林帶寬度百分位數的 K 線數量
BB_WIDTH_PERCENTILE = 20  # 低於此百分位數則過濾
RSI_DIVERGENCE_LOOKBACK = 30 # 尋找 RSI 背離的 K 線數量

_STOCK_SYMBOLS = {
    \'TSLA\',\'AAPL\',\'GOOGL\',\'AMZN\',\'MSFT\',\'NVDA\',\'META\',\'BABA\',
    \'NFLX\',\'COIN\',\'MSTR\',\'AMD\',\'INTC\',\'ORCL\',\'PYPL\',\'UBER\',
}
_METAL_SYMBOLS = {\'XAU\',\'XAG\',\'PAXG\',\'XAUT\'}

def is_crypto_symbol(symbol: str) -> bool:
    base = symbol.split(\'/\')[0]
    if base in _METAL_SYMBOLS: return False
    if base in _STOCK_SYMBOLS: return False
    return True

LARGE_CAP = {\'BTC/USDT\',\'ETH/USDT\',\'BNB/USDT\',\'SOL/USDT\'}
MID_CAP   = {
    \'XRP/USDT\',\'ADA/USDT\',\'AVAX/USDT\',\'DOT/USDT\',\'MATIC/USDT\',
    \'LINK/USDT\',\'UNI/USDT\',\'ATOM/USDT\',\'LTC/USDT\',\'ETC/USDT\'
}

# --- SQLite 持久化 ---
def init_db():
    import os as _os
    _os.makedirs(_os.path.dirname(DB_PATH), exist_ok=True)
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute(\'\'\'CREATE TABLE IF NOT EXISTS positions (
        symbol      TEXT PRIMARY KEY,
        side        TEXT,
        ep          REAL,
        sl          REAL,
        tp1         REAL,
        tp2         REAL,
        tp1_hit     INTEGER DEFAULT 0,
        atr         REAL,
        entry_time  REAL,
        category    TEXT
    )\'\'\')
    c.execute(\'\'\'CREATE TABLE IF NOT EXISTS trades (
        id          INTEGER PRIMARY KEY AUTOINCREMENT,
        symbol      TEXT,
        side        TEXT,
        pnl         REAL,
        won         INTEGER,
        trade_time  TEXT,
        week_id     TEXT,
        exit_type   TEXT
    )\'\'\')
    conn.commit()
    conn.close()
    log.info("[DB] V2-Pro 持久化資料庫已初始化")

def get_week_id() -> str:
    now = datetime.datetime.now(datetime.timezone.utc)
    return f"{now.year}-W{now.isocalendar()[1]:02d}"

def db_save_position(symbol: str, data: dict):
    try:
        conn = sqlite3.connect(DB_PATH)
        conn.execute(\'\'\'INSERT OR REPLACE INTO positions
            (symbol, side, ep, sl, tp1, tp2, tp1_hit, atr, entry_time, category)
            VALUES (?,?,?,?,?,?,?,?,?,?)\'\'\',
            (symbol, data[\'side\'], data[\'ep\'], data[\'sl\'],
            data[\'tp1\'], data[\'tp2\'], int(data.get(\'tp1_hit\', False)),
            data.get(\'atr\', 0), data.get(\'entry_time\', time.time()),
            data.get(\'category\', \'\')))
        conn.commit(); conn.close()
    except Exception as e:
        log.warning(f"[DB] 儲存持倉失敗: {e}")

def db_update_position(symbol: str, updates: dict):
    try:
        conn = sqlite3.connect(DB_PATH)
        for key, val in updates.items():
            conn.execute(f\'UPDATE positions SET {key}=? WHERE symbol=?\',
                          (val, symbol))
        conn.commit(); conn.close()
    except Exception as e:
        log.warning(f"[DB] 更新持倉失敗: {e}")

def db_remove_position(symbol: str):
    try:
        conn = sqlite3.connect(DB_PATH)
        conn.execute(\'DELETE FROM positions WHERE symbol=?\', (symbol,))
        conn.commit(); conn.close()
    except Exception as e:
        log.warning(f"[DB] 刪除持倉失敗: {e}")

def db_load_positions() -> dict:
    try:
        conn = sqlite3.connect(DB_PATH)
        rows = conn.execute(\'SELECT * FROM positions\').fetchall()
        conn.close()
        result = {}
        for r in rows:
            result[r[0]] = {
                \'side\': r[1], \'ep\': r[2], \'sl\': r[3],
                \'tp1\': r[4], \'tp2\': r[5], \'tp1_hit\': bool(r[6]),
                \'atr\': r[7], \'entry_time\': r[8], \'category\': r[9]
            }
        return result
    except Exception as e:
        log.warning(f"[DB] 載入持倉失敗: {e}")
        return {}

def db_save_trade(symbol: str, side: str, pnl: float,
                  won: bool, exit_type: str = \'\'):
    try:
        conn = sqlite3.connect(DB_PATH)
        conn.execute(\'\'\'INSERT INTO trades
            (symbol, side, pnl, won, trade_time, week_id, exit_type)
            VALUES (?,?,?,?,?,?,?)\'\'\',
            (symbol, side, pnl, int(won),
            datetime.datetime.now(datetime.timezone.utc).isoformat(),
            get_week_id(), exit_type))
        conn.commit(); conn.close()
    except Exception as e:
        log.warning(f"[DB] 儲存交易失敗: {e}")

def _calc_stats(rows: list) -> dict:
    trades = [{\'pnl\': r[0], \'won\': bool(r[1])} for r in rows]
    total  = len(trades)
    wins   = sum(1 for t in trades if t[\'won\'])
    pnls   = [t[\'pnl\'] for t in trades]
    wr     = (wins / total * 100) if total > 0 else 0
    avg    = (sum(pnls) / total)  if total > 0 else 0
    streak = cur = 0
    for t in trades:
        cur    = cur + 1 if not t[\'won\'] else 0
        streak = max(streak, cur)
    return {
        \'total\': total, \'wins\': wins, \'losses\': total - wins,
        \'win_rate\': wr, \'avg_pnl\': avg,
        \'max_loss_streak\': streak,
        \'best\':  max(pnls) if pnls else 0,
        \'worst\': min(pnls) if pnls else 0,
    }

def _empty_stats() -> dict:
    return {\'total\':0,\'wins\':0,\'losses\':0,\'win_rate\':0,
            \'avg_pnl\':0,\'max_loss_streak\':0,\'best\':0,\'worst\':0}

def db_load_weekly_stats(week_id: str = None) -> dict:
    try:
        wid  = week_id or get_week_id()
        conn = sqlite3.connect(DB_PATH)
        rows = conn.execute(
            \'SELECT pnl, won FROM trades WHERE week_id=?\', (wid,)
        ).fetchall()
        conn.close()
        return _calc_stats(rows)
    except Exception as e:
        log.warning(f"[DB] 讀取週報失敗: {e}")
        return _empty_stats()

def db_load_monthly_stats(year: int, month: int) -> dict:
    import calendar
    try:
        last_day = calendar.monthrange(year, month)[1]
        date_from = f"{year}-{month:02d}-01"
        date_to   = f"{year}-{month:02d}-{last_day:02d}T23:59:59"
        conn = sqlite3.connect(DB_PATH)
        rows = conn.execute(
            \'SELECT pnl, won FROM trades WHERE trade_time >= ? AND trade_time <= ?\',
            (date_from, date_to)
        ).fetchall()
        conn.close()
        return _calc_stats(rows)
    except Exception as e:
        log.warning(f"[DB] 讀取月報失敗: {e}")
        return _empty_stats()

def db_load_recent_stats(days: int = 7) -> dict:
    try:
        since = (datetime.datetime.now(datetime.timezone.utc)
                 - datetime.timedelta(days=days)).isoformat()
        conn  = sqlite3.connect(DB_PATH)
        rows  = conn.execute(
            \'SELECT pnl, won FROM trades WHERE trade_time >= ?\', (since,)
        ).fetchall()
        conn.close()
        return _calc_stats(rows)
    except Exception as e:
        log.warning(f"[DB] 讀取近期統計失敗: {e}")
        return _empty_stats()

def db_load_all_stats() -> dict:
    try:
        conn  = sqlite3.connect(DB_PATH)
        rows  = conn.execute(
            \'SELECT pnl, won FROM trades ORDER BY trade_time\'
        ).fetchall()
        conn.close()
        if not rows:
            return {**_empty_stats(), \'total_pnl\': 0}
        base = _calc_stats(rows)
        base[\'total_pnl\'] = sum(r[0] for r in rows)
        return base
    except Exception as e:
        log.warning(f"[DB] 讀取全部統計失敗: {e}")
        return {**_empty_stats(), \'total_pnl\': 0}

# --- 持倉管理 ---
def position_count() -> int:
    with positions_lock: return len(active_positions)

def long_count() -> int:
    with positions_lock:
        return sum(1 for p in active_positions.values() if p[\'side\'] == \'long\')

def short_count() -> int:
    with positions_lock:
        return sum(1 for p in active_positions.values() if p[\'side\'] == \'short\')

def category_count(cat: str) -> int:
    with positions_lock:
        return sum(1 for s in active_positions if get_symbol_category(s) == cat)

def has_position(symbol: str) -> bool:
    with positions_lock: return symbol in active_positions

def get_position(symbol: str):
    with positions_lock: return active_positions.get(symbol)

def add_position(symbol: str, data: dict):
    with positions_lock:
        active_positions[symbol] = data
    db_save_position(symbol, data)

def update_position(symbol: str, updates: dict):
    with positions_lock:
        if symbol in active_positions:
            active_positions[symbol].update(updates)
    db_update_position(symbol, updates)

def remove_position(symbol: str):
    with positions_lock:
        active_positions.pop(symbol, None)
    db_remove_position(symbol)

def get_all_positions() -> dict:
    with positions_lock: return dict(active_positions)

def can_open_position(symbol: str, side: str) -> tuple:
    s       = db_load_recent_stats(days=30)
    wr      = s[\'win_rate\'] / 100 if s[\'total\'] >= 10 else 1.0
    eff_max = WINRATE_REDUCED_MAX if wr < WINRATE_THRESHOLD and s[\'total\'] >= 10 \
              else MAX_POSITIONS

    if position_count() >= eff_max:
        note = f"（勝率 {wr*100:.1f}% 未達標，保守模式）" if eff_max == WINRATE_REDUCED_MAX else \'\'
        return False, f"總倉位已達上限 {eff_max}{note}"
    if side == \'long\'  and long_count()  >= MAX_LONG:  return False, f"多單上限 {MAX_LONG}"
    if side == \'short\' and short_count() >= MAX_SHORT: return False, f"空單上限 {MAX_SHORT}"

    cat = get_symbol_category(symbol)
    if cat == \'large\' and category_count(\'large\') >= MAX_POSITIONS: # 這裡使用 MAX_POSITIONS 作為大市值幣的上限，可以調整
        return False, f"大型幣上限 {MAX_POSITIONS}"
    if cat == \'mid\'   and category_count(\'mid\')   >= MAX_POSITIONS: # 同上
        return False, f"中型幣上限 {MAX_POSITIONS}"

    return True, \'\'

# --- 訊號管理 ---
def is_signal_sent(key: str) -> bool:
    with signals_lock: return key in sent_signals

def record_signal(key: str):
    with signals_lock: sent_signals[key] = time.time()

def clean_signals():
    now = time.time()
    with signals_lock:
        for k in [k for k, v in sent_signals.items() if now - v > SIGNAL_EXPIRY_TIME]:
            del sent_signals[k]
        while len(sent_signals) > MAX_SIGNALS_MEMORY:
            sent_signals.popitem(last=False)

# --- 交易結果記錄 ---
def record_trade_result(symbol: str, side: str, pnl: float, won: bool, exit_type: str = \'\'):
    db_save_trade(symbol, side, pnl, won, exit_type)

# --- 輔助函數 ---
def get_symbol_category(symbol: str) -> str:
    base  = symbol.split(\'/\')[0]
    clean = f"{base}/USDT"
    if clean in LARGE_CAP: return \'large\'
    if clean in MID_CAP:   return \'mid\'
    return \'small\'

def send_telegram(message: str) -> bool:
    token   = os.environ.get(\'TELEGRAM_TOKEN\')
    chat_id = os.environ.get(\'TELEGRAM_CHAT_ID\')
    if not token or not chat_id:
        log.warning("Telegram 環境變數未設定")
        return False
    url    = f"https://api.telegram.org/bot{token}/sendMessage"
    params = {\'chat_id\': chat_id, \'text\': message, \'parse_mode\': \'Markdown\'}
    try:
        resp = requests.get(url, params=params, timeout=10)
        resp.raise_for_status()
        return True
    except Exception as e:
        log.error(f"Telegram 發送失敗: {e}")
        return False

async def get_exchange_async():
    exchange = ccxt.binance({
        \'apiKey\': os.environ.get(\'BINANCE_API_KEY\'),
        \'secret\': os.environ.get(\'BINANCE_SECRET\'),
        \'options\': {
            \'defaultType\': \'future\',
        },
        \'enableRateLimit\': True,
    })
    return exchange

async def fetch_ohlcv_df_async(exchange, symbol: str, timeframe: str, limit: int) -> pd.DataFrame:
    try:
        ohlcv = await exchange.fetch_ohlcv(symbol, timeframe, limit=limit + 1)
        if len(ohlcv) < limit: return None
        df = pd.DataFrame(ohlcv[:-1], columns=[\'t\', \'o\', \'h\', \'l\', \'c\', \'v\'])
        df[\'t\'] = pd.to_datetime(df[\'t\'], unit=\'ms\')
        df = df.astype({\'o\':float,\'h\':float,\'l\':float,\'c\':float,\'v\':float})
        return df
    except Exception as e:
        log.warning(f"[OHLCV] {symbol} {timeframe} 獲取失敗: {e}")
        return None

def calc_effective_atr(raw_atr: float, current_price: float) -> float:
    min_sl_abs = current_price * MIN_SL_PCT
    # 確保 ATR 止損距離至少達到 MIN_SL_PCT
    return max(raw_atr, min_sl_abs / ATR_TP1_MULT) # 注意這裡用 TP1_MULT 確保止盈目標合理

def is_weekend() -> bool:
    now = datetime.datetime.now(datetime.timezone.utc)
    return now.weekday() >= 5

async def wait_until_next_4h_close_async() -> float:
    now        = datetime.datetime.now(datetime.timezone.utc)
    hour       = now.hour
    minute     = now.minute
    second     = now.second
    current_4h = hour // 4
    next_close_hour = (current_4h + 1) * 4
    if next_close_hour >= 24:
        next_close = now.replace(
            hour=0, minute=2, second=0, microsecond=0
        ) + datetime.timedelta(days=1)
    else:
        next_close = now.replace(
            hour=next_close_hour, minute=2, second=0, microsecond=0
        )
    wait = (next_close - now).total_seconds()
    return max(wait, 60)

# --- WebSocket 即時 CVD (優化版，增加 REST 備用) ---
def _ws_on_message(symbol_key: str, msg: str):
    try:
        data = json.loads(msg)
        qty  = float(data.get(\'q\', 0))
        is_buyer_maker = data.get(\'m\', False)
        with ws_cvd_lock:
            if is_buyer_maker:
                ws_cvd_buffer[symbol_key][\'sell\'] += qty
            else:
                ws_cvd_buffer[symbol_key][\'buy\']  += qty
            ws_cvd_buffer[symbol_key][\'ts\'] = time.time()
    except Exception:
        pass

def start_ws_cvd(symbol: str):
    if not WS_AVAILABLE:
        return
    symbol_key = symbol.split(\'/\')[0].lower() + \'usdt\'
    if symbol_key in ws_connections:
        return

    def run():
        url = f"wss://fstream.binance.com/ws/{symbol_key}@aggTrade"
        def on_msg(ws, msg):   _ws_on_message(symbol_key, msg)
        def on_err(ws, err):   log.warning(f"[WS] {symbol_key} 錯誤: {err}")
        def on_close(ws, *a):
            log.info(f"[WS] {symbol_key} 連線關閉，5s 後重連")
            ws_connections.pop(symbol_key, None)
            time.sleep(5)
            start_ws_cvd(symbol)
        def on_open(ws):
            log.info(f"[WS] {symbol_key} aggTrade 串流已連線")
            with ws_cvd_lock:
                ws_cvd_buffer[symbol_key] = {\'buy\': 0.0, \'sell\': 0.0, \'ts\': time.time()}

        w = ws_lib.WebSocketApp(url, on_message=on_msg, on_error=on_err,
                                on_close=on_close, on_open=on_open)
        ws_connections[symbol_key] = True
        w.run_forever(ping_interval=30, ping_timeout=10)

    Thread(target=run, daemon=True).start()

async def get_cvd_bias_async(exchange, symbol: str) -> str:
    symbol_key = symbol.split(\'/\')[0].lower() + \'usdt\'

    with ws_cvd_lock:
        buf = ws_cvd_buffer.get(symbol_key)
        # 判斷 WS 數據是否新鮮且有足夠的交易量
        ws_fresh = buf and (time.time() - buf[\'ts\']) < 10 and \
                   (buf[\'buy\'] + buf[\'sell\']) > 0

    if ws_fresh:
        with ws_cvd_lock:
            buy_vol  = ws_cvd_buffer[symbol_key][\'buy\']
            sell_vol = ws_cvd_buffer[symbol_key][\'sell\']
            ws_cvd_buffer[symbol_key] = {\'buy\': 0.0, \'sell\': 0.0, \'ts\': time.time()} # 重置緩衝區
        total     = buy_vol + sell_vol
        buy_ratio = buy_vol / total if total > 0 else 0.5
        # V2 的 CVD 判斷更簡單，只看 bias
        if buy_ratio >= 0.55: return \'bull\'
        if buy_ratio <= 0.45: return \'bear\'
        return \'neutral\'
    else:
        # WS 數據不新鮮或不可用，回退到 REST API 獲取
        try:
            trades = await exchange.fetch_trades(symbol, limit=500)
            if not trades: return \'neutral\'
            df_t      = pd.DataFrame([{\'amount\': t[\'amount\'], \'side\': t[\'side\']} for t in trades])
            buy_vol   = df_t[df_t[\'side\'] == \'buy\'][\'amount\'].sum()
            total     = df_t[\'amount\'].sum()
            buy_ratio = buy_vol / total if total > 0 else 0.5
            if buy_ratio >= 0.55: return \'bull\'
            if buy_ratio <= 0.45: return \'bear\'
            return \'neutral\'
        except Exception as e:
            log.warning(f"[CVD/REST] {symbol}: {e}")
            return \'neutral\'

# --- 核心分析：動量突破型 V2-Pro (抗震盪強化版) ---
async def analyze_symbol_v2_pro(exchange, symbol: str):
    df = await fetch_ohlcv_df_async(exchange, symbol, TIMEFRAME, 250 + BB_WIDTH_LOOKBACK + RSI_DIVERGENCE_LOOKBACK)
    if df is None or len(df) < (210 + BB_WIDTH_LOOKBACK + RSI_DIVERGENCE_LOOKBACK): return None

    c   = df[\'c\']
    h   = df[\'h\']
    l   = df[\'l\']
    v   = df[\'v\']

    raw_atr = ta.atr(h, l, c, length=14).iloc[-1]
    if pd.isna(raw_atr) or raw_atr <= 0: return None

    curr_c = float(c.iloc[-1])

    # FIX：套用最低止損距離保護
    atr = calc_effective_atr(raw_atr, curr_c)

    # --- A. 波動率過濾 (BB Width) ---
    bb = ta.bbands(c, length=20, std=2)
    bb_width = bb[f\'BBL_20_2.0\'] - bb[f\'BBU_20_2.0\'] # 這裡應該是 BBU - BBL
    bb_width = bb[f\'BBU_20_2.0\'] - bb[f\'BBL_20_2.0\']
    if pd.isna(bb_width.iloc[-1]): return None

    # 計算過去 BB_WIDTH_LOOKBACK 根 K 線的布林帶寬度百分位數
    historical_bb_width = bb_width.iloc[-(BB_WIDTH_LOOKBACK+1):-1]
    if len(historical_bb_width) < BB_WIDTH_LOOKBACK: return None
    bb_width_threshold = np.percentile(historical_bb_width, BB_WIDTH_PERCENTILE)

    if bb_width.iloc[-1] < bb_width_threshold:
        log.debug(f"[V2-Pro Skip] {symbol} 波動率過低 (BB Width {bb_width.iloc[-1]:.4f} < {bb_width_threshold:.4f})")
        return None

    # ── Layer 1：EMA 三線排列 ──
    ema_fast = ta.ema(c, length=EMA_FAST)
    ema_mid  = ta.ema(c, length=EMA_MID)
    ema_slow = ta.ema(c, length=EMA_SLOW)

    ef = ema_fast.iloc[-1]
em = ema_mid.iloc[-1]
es = ema_slow.iloc[-1]

    if pd.isna(ef) or pd.isna(em) or pd.isna(es):
        return None

bull_trend = ef > em > es and curr_c > ef
bear_trend = ef < em < es and curr_c < ef

    if not bull_trend and not bear_trend:
        return None

    # ── Layer 2：突破 + 成交量確認 ──
    recent_high = h.iloc[-(BREAKOUT_LOOKBACK+1):-1].max()
    recent_low  = l.iloc[-(BREAKOUT_LOOKBACK+1):-1].min()
    avg_vol     = v.iloc[-BREAKOUT_LOOKBACK-1:-1].mean()
    curr_vol    = float(v.iloc[-1])
    vol_confirm = curr_vol >= avg_vol * VOLUME_MULTIPLIER

    bull_break = float(c.iloc[-1]) > recent_high and vol_confirm
bear_break = float(c.iloc[-1]) < recent_low  and vol_confirm

    if bull_trend and not bull_break: return None
    if bear_trend and not bear_break: return None

    # ── Layer 3：RSI 動量 ──
    rsi = ta.rsi(c, length=14).iloc[-1]
    if pd.isna(rsi): return None
    if bull_trend and not (RSI_BULL_MIN <= rsi <= RSI_BULL_MAX): return None
    if bear_trend and not (RSI_BEAR_MIN <= rsi <= RSI_BEAR_MAX): return None

    # --- C. RSI 背離確認 (簡易版) ---
    # 尋找最近的價格波峰/波谷和RSI波峰/波谷
    # 這裡採用簡化邏輯，尋找最近的極值點
    rsi_series = ta.rsi(c, length=14)

    # 尋找價格和RSI的局部極值點
    # 這裡使用簡單的 rolling max/min 配合 shift 來判斷波峰波谷
    # 更嚴謹的背離判斷需要更複雜的波峰波谷檢測算法
    is_price_peak = (h == h.rolling(window=3, center=True).max()).iloc[-RSI_DIVERGENCE_LOOKBACK:-1]
    is_price_trough = (l == l.rolling(window=3, center=True).min()).iloc[-RSI_DIVERGENCE_LOOKBACK:-1]
    is_rsi_peak = (rsi_series == rsi_series.rolling(window=3, center=True).max()).iloc[-RSI_DIVERGENCE_LOOKBACK:-1]
    is_rsi_trough = (rsi_series == rsi_series.rolling(window=3, center=True).min()).iloc[-RSI_DIVERGENCE_LOOKBACK:-1]

    divergence_found = False
    if bull_trend and bull_break: # 潛在看漲背離
        # 尋找最近的兩個價格低點和RSI低點
        price_troughs = l.iloc[-RSI_DIVERGENCE_LOOKBACK:-1][is_price_trough.values]
        rsi_at_troughs = rsi_series.iloc[-RSI_DIVERGENCE_LOOKBACK:-1][is_price_trough.values]

        if len(price_troughs) >= 2:
            # 價格形成更高低點 (Higher Low) 但 RSI 形成更低低點 (Lower Low) -> 隱藏看漲背離 (通常是趨勢延續)
            # 價格形成更低低點 (Lower Low) 但 RSI 形成更高低點 (Higher Low) -> 常規看漲背離 (通常是趨勢反轉)
            # 這裡我們只檢查常規看漲背離，因為它更具反轉意義，且在突破策略中可以作為過濾假突破的依據
            if price_troughs.iloc[-1] < price_troughs.iloc[-2] and \
               rsi_at_troughs.iloc[-1] > rsi_at_troughs.iloc[-2]:
                divergence_found = True
                log.debug(f"[V2-Pro Skip] {symbol} 潛在看漲背離 (價格更低低點, RSI更高低點)")
                return None # 發現背離，過濾掉這個突破信號

    elif bear_trend and bear_break: # 潛在看跌背離
        # 尋找最近的兩個價格高點和RSI高點
        price_peaks = h.iloc[-RSI_DIVERGENCE_LOOKBACK:-1][is_price_peak.values]
        rsi_at_peaks = rsi_series.iloc[-RSI_DIVERGENCE_LOOKBACK:-1][is_price_peak.values]

        if len(price_peaks) >= 2:
            # 價格形成更高高點 (Higher High) 但 RSI 形成更低高點 (Lower High) -> 常規看跌背離 (通常是趨勢反轉)
            if price_peaks.iloc[-1] > price_peaks.iloc[-2] and \
               rsi_at_peaks.iloc[-1] < rsi_at_peaks.iloc[-2]:
                divergence_found = True
                log.debug(f"[V2-Pro Skip] {symbol} 潛在看跌背離 (價格更高高點, RSI更低高點)")
                return None # 發現背離，過濾掉這個突破信號

    # ── CVD 加分項 (Async) ──
    cvd = await get_cvd_bias_async(exchange, symbol)
    cvd_ok = (bull_trend and cvd in (\'bull\',\'neutral\')) or \
             (bear_trend and cvd in (\'bear\',\'neutral\'))
    if not cvd_ok: return None

    side = \'long\' if bull_trend else \'short\'

    # --- D. 動態結構止損緩衝 ---
    # 將 SL_STRUCT_BUFFER 改為基於 ATR 的動態緩衝
    dynamic_sl_buffer = 0.5 * atr / curr_c # 例如 0.5 倍 ATR 佔當前價格的百分比

    # 止損改為結構位（突破前低/前高 + buffer）
    if side == \'long\':
        struct_sl = recent_low * (1 - dynamic_sl_buffer)
        sl = min(struct_sl, curr_c * (1 - MIN_SL_PCT))   # 取較低者
        sl = max(sl, curr_c * (1 - MAX_SL_PCT))           # 不能太遠
    else:
        struct_sl = recent_high * (1 + dynamic_sl_buffer)
        sl = max(struct_sl, curr_c * (1 + MIN_SL_PCT))
        sl = min(sl, curr_c * (1 + MAX_SL_PCT))

    # ATR 仍用於計算止盈目標
    MAX_TP_PCT = 0.50
    atr_capped = min(atr, curr_c * MAX_TP_PCT / ATR_TP2_MULT)

    tp1 = curr_c + ATR_TP1_MULT * atr_capped if side == \'long\' \
          else curr_c - ATR_TP1_MULT * atr_capped
    tp2 = curr_c + ATR_TP2_MULT * atr_capped if side == \'long\' \
          else curr_c - ATR_TP2_MULT * atr_capped

    if tp1 <= 0 or tp2 <= 0:
        log.debug(f"[V2-Pro Skip] {symbol} 止盈為負數 tp1={tp1:.6f}，跳過")
        return None

    sl_pct  = abs(curr_c - sl)  / curr_c * 100
    tp1_pct = abs(curr_c - tp1) / curr_c * 100
    tp2_pct = abs(curr_c - tp2) / curr_c * 100

    if sl_pct >= tp1_pct:
        log.debug(f"[V2-Pro Skip] {symbol} 風報比過差 sl={sl_pct:.1f}% >= tp1={tp1_pct:.1f}%")
        return None

    labels = (
        f"{\'📈 多頭排列\' if bull_trend else \'📉 空頭排列\'} "
        f"EMA {EMA_FAST}/{EMA_MID}/{EMA_SLOW}\n"
        f"🚀 {\'向上突破\' if bull_break else \'向下跌破\'} "
        f"近{BREAKOUT_LOOKBACK}根高低點\n"
        f"📊 成交量 {curr_vol/avg_vol:.1f}x 均量\n"
        f"💹 RSI {rsi:.1f} | CVD {cvd}\n"
        f"🛡 止損距離 {sl_pct:.1f}% | "
        f"🎯1 {tp1_pct:.1f}% | 🎯2 {tp2_pct:.1f}%"
    )

    return {
        \'side\': side, \'ep\': curr_c, \'sl\': sl,
        \'tp1\': tp1, \'tp2\': tp2, \'tp1_hit\': False,
        \'atr\': atr, \'labels\': labels, \'rsi\': rsi,
    }

# --- 持倉更新邏輯 (Async) ---
async def handle_position_update_async(exchange, symbol: str, curr_c: float, curr_h: float, curr_l: float) -> str:
    pos = get_position(symbol)
    if not pos: return \'hold\'

    side       = pos[\'side\']
    ep         = pos[\'ep\']
    sl         = pos[\'sl\']
    tp1        = pos[\'tp1\']
    tp2        = pos[\'tp2\']
    tp1_hit    = pos.get(\'tp1_hit\', False)
    atr_val    = pos.get(\'atr\', abs(tp1 - ep) / ATR_TP1_MULT)
    entry_time = pos.get(\'entry_time\', time.time())

    sl_price_long  = curr_l if curr_l is not None else curr_c
    sl_price_short = curr_h if curr_h is not None else curr_c

    if (time.time() - entry_time) / 3600 >= MAX_HOLD_HOURS:
        if is_weekend():
            log.debug(f"[Weekend] {symbol} 超時但週末，暫不出場")
            return \'hold\'
        return \'timeout\'

    if side == \'long\':
        if not tp1_hit:
            if curr_c >= tp1:
                update_position(symbol, {\'tp1_hit\': True, \'sl\': ep})
                log.info(f"[TP1] {symbol} 多單第一批止盈，止損移至進場價 {ep:.4f}")
                return \'tp1\'
            if sl_price_long <= sl:
                return \'sl\'
        else:
            if curr_c >= tp2:
                return \'tp2\'
            if sl_price_long <= get_position(symbol)[\'sl\']:
                return \'sl\'
            # 移動止損
            new_sl = curr_c - atr_val
            if new_sl > get_position(symbol)[\'sl\']:
                update_position(symbol, {\'sl\': new_sl})
                log.info(f"[Trail] {symbol} 多單止損上移 → {new_sl:.4f}")
    else: # short
        if not tp1_hit:
            if curr_c <= tp1:
                update_position(symbol, {\'tp1_hit\': True, \'sl\': ep})
                log.info(f"[TP1] {symbol} 空單第一批止盈，止損移至進場價 {ep:.4f}")
                return \'tp1\'
            if sl_price_short >= sl:
                return \'sl\'
        else:
            if curr_c <= tp2:
                return \'tp2\'
            if sl_price_short >= get_position(symbol)[\'sl\']:
                return \'sl\'
            # 移動止損
            new_sl = curr_c + atr_val
            if new_sl < get_position(symbol)[\'sl\']:
                update_position(symbol, {\'sl\': new_sl})
                log.info(f"[Trail] {symbol} 空單止損下移 → {new_sl:.4f}")

    return \'hold\'

# --- 主監控迴圈 (V2-Pro Async 版) ---
async def monitor_async():
    log.info("=== 動量突破 V2-Pro 監控啟動 ===")

    exchange = None
    semaphore = asyncio.Semaphore(5) # 限制並發任務數量

    while True:
        try:
            if exchange is None:
                exchange = await get_exchange_async()

            markets = await exchange.load_markets()
            all_symbols = [s for s in markets if \'/USDT\' in s and markets[s][\'spot\'] == False and markets[s][\'linear\'] == True and is_crypto_symbol(s)]
            symbols = [s for s in all_symbols][:TOP_SYMBOLS]

            if not symbols:
                await asyncio.sleep(60); continue

            log.info(f"掃描 {len(symbols)} 幣種...")

            async def process_symbol(symbol: str):
                async with semaphore:
                    try:
                        df_fast = await fetch_ohlcv_df_async(exchange, symbol, TIMEFRAME, 5)
                        if df_fast is None: return
                        curr_c   = float(df_fast[\'c\'].iloc[-1])
                        curr_h   = float(df_fast[\'h\'].iloc[-1])
                        curr_l   = float(df_fast[\'l\'].iloc[-1])
                        last_k_t = df_fast[\'t\'].iloc[-1]

                        pos = get_position(symbol)
                        if pos:
                            result = await handle_position_update_async(exchange, symbol, curr_c, curr_h, curr_l)
                            side   = pos[\'side\']
                            side_t = \'多\' if side == \'long\' else \'空\'
                            exit_c = curr_c
                            if result == \'sl\':
                                exit_c = pos[\'sl\']
                            if result == \'tp1\':
                                pnl = abs(curr_c - pos[\'ep\']) / pos[\'ep\'] * 100
                                send_telegram(
                                    f"✅ *V2-Pro {side_t}單第一批止盈*: `{symbol}`\n"
                                    f"損益: `+{pnl:.2f}%`（50% 倉位）\n"
                                    f"進場: `{pos[\'ep\']:.4f}` → 止盈1: `{curr_c:.4f}`\n"
                                    f"⚡ 止損已移至進場價，剩餘 50% 追第二批"
                                )
                                record_trade_result(symbol, side, pnl, True, \'tp1\')
                            elif result in (\'tp2\', \'sl\', \'timeout\'):
                                tp1_hit = pos.get(\'tp1_hit\', False)
                                if result == \'tp2\':
                                    pnl  = abs(curr_c - pos[\'ep\']) / pos[\'ep\'] * 100
                                    won  = True
                                    icon = \'🏆\'
                                    desc = f"{side_t}單第二批止盈"
                                    note = "（全部出場）"
                                elif result == \'sl\':
                                    pnl  = (exit_c/pos[\'ep\']-1)*100 if side==\'long\' \
                                           else (pos[\'ep\']/exit_c-1)*100
                                    won  = pnl > 0
                                    icon = \'❌\' if not won else \'✅\'
                                    desc = f"{side_t}單止損"
                                    note = "（第一批已保本）" if tp1_hit else ""
                                else:
                                    pnl  = (curr_c/pos[\'ep\']-1)*100 if side==\'long\' \
                                           else (pos[\'ep\']/curr_c-1)*100
                                    won  = pnl > 0
                                    icon = \'⏰\'
                                    desc = f"持倉 {MAX_HOLD_HOURS}h 超時出場"
                                    note = ""
                                send_telegram(
                                    f"{icon} *V2-Pro {desc}*: `{symbol}`\n"
                                    f"損益: `{pnl:+.2f}%` {note}\n"
                                    f"進場: `{pos[\'ep\']:.4f}` → 出場: `{exit_c:.4f}`"
                                )
                                record_trade_result(symbol, side, pnl, won, result)
                                remove_position(symbol)
                            return

                        base_key = f"{symbol}_{last_k_t}"
                        if is_signal_sent(f"long_{base_key}") or \
                           is_signal_sent(f"short_{base_key}"):
                            return

                        result = await analyze_symbol_v2_pro(exchange, symbol)
                        if result is None: return

                        side = result[\'side\']
                        ok, reason = can_open_position(symbol, side)
                        if not ok:
                            log.info(f"[Skip] {symbol} {side}: {reason}"); return

                        sig_key = f"{side}_{base_key}"
                        if is_signal_sent(sig_key): return

                        cat    = get_symbol_category(symbol)
                        side_t = \'多單\' if side == \'long\' else \'空單\'

                        add_position(symbol, {
                            \'side\': side, \'ep\': curr_c,
                            \'sl\': result[\'sl\'],
                            \'tp1\': result[\'tp1\'], \'tp2\': result[\'tp2\'],
                            \'atr\': result[\'atr\'],
                            \'labels\': result[\'labels\'],
                            \'entry_time\': time.time(),
                            \'category\': cat,
                        })

                        send_telegram(
                            f"🚀 *V2-Pro {side_t} 進場*: `{symbol}` [{cat}]\n"
                            f"進場價: `{curr_c:.4f}`\n"
                            f"🛡 止損: `{result[\'sl\']:.4f}`\n"
                            f"🎯 止盈1（50%）: `{result[\'tp1\']:.4f}`\n"
                            f"🏆 止盈2（50%）: `{result[\'tp2\']:.4f}`\n"
                            f"{\'─\'*20}\n"
                            f"{result[\'labels\]}"
                        )
                        log.info(
                            f"[Entry] {side_t}: {symbol} [{cat}] "
                            f"@ {curr_c:.4f} (突破)"
                        )
                        record_signal(sig_key)

                    except Exception as e:
                        log.warning(f"[ProcessSymbol] {symbol}: {e}")

            await asyncio.gather(*[process_symbol(symbol) for symbol in symbols])

            clean_signals()
            s        = db_load_recent_stats(days=30)
            eff_max  = WINRATE_REDUCED_MAX \
                       if s[\'total\'] >= 10 and s[\'win_rate\']/100 < WINRATE_THRESHOLD \
                       else MAX_POSITIONS
            wait = await wait_until_next_4h_close_async()
            next_dt = datetime.datetime.now(datetime.timezone.utc) + datetime.timedelta(seconds=wait)
            log.info(f"掃描完成 持倉:{position_count()}/{eff_max} "
                     f"近30天勝率:{s[\'win_rate\']:.1f}% "
                     f"下次掃描 UTC {next_dt.strftime(\'%H:%M\')}（{wait/60:.0f}分後）")
            await asyncio.sleep(wait)

        except Exception as e:
            log.error(f"[Monitor] 嚴重錯誤: {e}")
            if exchange:
                await exchange.close()
            exchange = None
            await asyncio.sleep(60)

# --- 每日報告 (Async) ---
async def daily_report_task_async():
    last_sent_date = datetime.date.today() - datetime.timedelta(days=1)
    log.info("[DailyReport] 線程已啟動")
    while True:
        try:
            now = datetime.datetime.now(datetime.timezone.utc)
            if now.date() > last_sent_date:
                log.info(f"[DailyReport] 開始發送 {now.date()}")
                pos_all = get_all_positions()
                s       = db_load_recent_stats(days=7)
                all_s   = db_load_all_stats()
                if \'total_pnl\' not in all_s:
                    all_s[\'total_pnl\'] = 0
                eff_max = WINRATE_REDUCED_MAX   \
                          if s[\'total\']>=10 and s[\'win_rate\']/100<WINRATE_THRESHOLD   \
                          else MAX_POSITIONS
                pos_detail = \'\n\'.join([
                    f"  • `{sym}` {p[\'side\']} @ {p[\'ep\']:.4f} "
                    f"[{p.get(\'category\',\'?\')}] "
                    f"({(time.time()-p.get(\'entry_time\',time.time()))/3600:.1f}h)"
                    for sym, p in pos_all.items()
                ]) if pos_all else \'  無\'
                mode = \'⚠️ 保守模式\' if eff_max == WINRATE_REDUCED_MAX else \'✅ 正常模式\'
                send_telegram(
                    f"📅 *動量突破 V2-Pro 每日報告*\n"
                    f"⏰ UTC 00:00（台灣 08:00）\n{\'─\'*24}\n"
                    f"💼 持倉 ({len(pos_all)}/{eff_max}) {mode}:\n{pos_detail}\n"
                    f"{\'─\'*24}\n"
                    f"近7天: {s[\'total\']} 筆 | 勝率 {s[\'win_rate\']:.1f}% | "
                    f"平均 {s[\'avg_pnl\']:.2f}%\n"
                    f"📊 累計: {all_s[\'total\']} 筆 | 勝率 {all_s[\'win_rate\']:.1f}% | "
                    f"總損益 {all_s[\'total_pnl\']:.2f}% | 最大連敗 {all_s[\'max_loss_streak\]}\n"
                )
                last_sent_date = now.date()
        except Exception as e:
            log.error(f"[DailyReport]: {e}")
            send_telegram(f"⚠️ *V2-Pro 每日報告發送失敗*\n錯誤: {e}")
        await asyncio.sleep(60)

# --- 每週報告 (Async) ---
async def weekly_report_task_async():
    last_sent_week = -1
    while True:
        try:
            now  = datetime.datetime.now(datetime.timezone.utc)
            week = now.isocalendar()[1]
            if week != last_sent_week:
                last_week    = now - datetime.timedelta(days=7)
                last_week_id = f"{last_week.year}-W{last_week.isocalendar()[1]:02d}"
                s      = db_load_weekly_stats(week_id=last_week_id)
                eff    = WINRATE_REDUCED_MAX   \
                         if s[\'total\']>=10 and s[\'win_rate\']/100<WINRATE_THRESHOLD   \
                         else MAX_POSITIONS
                status = \'⚠️ 勝率未達標，已縮減倉位\' if eff==WINRATE_REDUCED_MAX   \
                         else \'✅ 勝率正常，維持標準倉位\'
                send_telegram(
                    f"📊 *動量突破 V2-Pro 每週績效報告*\n"
                    f"📅 {last_week_id}\n{\'─\'*24}\n"
                    f"📈 總交易: {s[\'total\']} 筆\n"
                    f"✅ 勝: {s[\'wins\']} | ❌ 敗: {s[\'losses\]}\n"
                    f"🎯 勝率: `{s[\'win_rate\']:.1f}%`\n"
                    f"💰 平均損益: `{s[\'avg_pnl\']:.2f}%`\n"
                    f"🏆 最佳: `+{s[\'best\']:.2f}%`\n"
                    f"💀 最差: `{s[\'worst\']:.2f}%`\n"
                    f"🔴 最大連敗: {s[\'max_loss_streak\]} 筆\n"
                    f"⚖️ 風報比: 1:{ATR_TP1_MULT/MIN_SL_PCT:.1f} " # 這裡用 MIN_SL_PCT 作為止損基準，因為 V2 止損是結構化的
                    f"/ 1:{ATR_TP2_MULT/MIN_SL_PCT:.1f}（分批）\n{\'─\'*24}\n"
                    f"{status}\n_上週數據封存完畢_"
                )
                last_sent_week = week
        except Exception as e:
            log.error(f"[WeeklyReport]: {e}")
            send_telegram(f"⚠️ *V2-Pro 週報發送失敗*\n錯誤: {e}")
        await asyncio.sleep(3600)

# --- 每月報告 (Async) ---
async def monthly_report_task_async():
    last_sent_month = -1
    while True:
        try:
            now = datetime.datetime.now(datetime.timezone.utc)
            if now.month != last_sent_month:
                last_month      = now.month - 1 if now.month > 1 else 12
                last_month_year = now.year if now.month > 1 else now.year - 1
                s   = db_load_monthly_stats(last_month_year, last_month)
                eff = WINRATE_REDUCED_MAX   \
                      if s[\'total\']>=10 and s[\'win_rate\']/100<WINRATE_THRESHOLD   \
                      else MAX_POSITIONS
                status = \'⚠️ 勝率未達標\' if eff==WINRATE_REDUCED_MAX   \
                         else \'✅ 勝率正常\'
                send_telegram(
                    f"🗓 *動量突破 V2-Pro 月報*\n"
                    f"📅 {last_month_year}-{last_month:02d}\n{\'─\'*24}\n"
                    f"📈 總交易: {s[\'total\']} 筆\n"
                    f"✅ 勝: {s[\'wins\']} | ❌ 敗: {s[\'losses\]}\n"
                    f"🎯 勝率: `{s[\'win_rate\']:.1f}%`\n"
                    f"💰 平均損益: `{s[\'avg_pnl\']:.2f}%`\n"
                    f"🏆 最佳: `+{s[\'best\']:.2f}%`\n"
                    f"💀 最差: `{s[\'worst\']:.2f}%`\n"
                    f"🔴 最大連敗: {s[\'max_loss_streak\]} 筆\n"
                    f"{\'─\'*24}\n"
                    f"{status}\n_上月數據封存完畢_"
                )
                last_sent_month = now.month
        except Exception as e:
            log.error(f"[MonthlyReport]: {e}")
            send_telegram(f"⚠️ *V2-Pro 月報發送失敗*\n錯誤: {e}")
        await asyncio.sleep(3600)

# --- Flask 路由 ---
@app.route(\'/\')
def hello_world():
    return \'Hello, World! V2-Pro Radar is running!\'

@app.route(\'/stats\')
def get_stats():
    s = db_load_recent_stats(days=7)
    all_s = db_load_all_stats()
    return json.dumps({\'recent_stats\': s, \'all_stats\': all_s})

@app.route(\'/positions\')
def get_current_positions():
    return json.dumps(get_all_positions())

# --- 啟動所有線程/協程 ---
def start_all_background_tasks():
    global threads_started
    with threads_lock:
        if threads_started: return
        threads_started = True

        asyncio.create_task(daily_report_task_async())
        asyncio.create_task(weekly_report_task_async())
        asyncio.create_task(monthly_report_task_async())
        log.info("所有報告協程已啟動")

        Thread(target=lambda: app.run(host=\'0.0.0.0\', port=5001, debug=False), daemon=True).start() # V2-Pro 使用不同端口
        log.info("Flask 服務已啟動在 0.0.0.0:5001")

# --- 主入口點 ---
async def main():
    init_db()
    start_all_background_tasks()

    temp_exchange = ccxt.binance({
        \'apiKey\': os.environ.get(\'BINANCE_API_KEY\'),
        \'secret\': os.environ.get(\'BINANCE_SECRET\'),
        \'options\': {
            \'defaultType\': \'future\',
        },
        \'enableRateLimit\': True,
    })
    try:
        markets = await temp_exchange.load_markets()
        all_futures_symbols = [s for s in markets if \'/USDT\' in s and markets[s][\'spot\'] == False and markets[s][\'linear\'] == True and is_crypto_symbol(s)]
        initial_symbols = [s for s in all_futures_symbols][:TOP_SYMBOLS]
        for symbol in initial_symbols:
            start_ws_cvd(symbol)
            await asyncio.sleep(0.1)
        log.info(f"已為 {len(initial_symbols)} 個幣種啟動 WebSocket CVD 監聽")
    except Exception as e:
        log.error(f"[Main] 啟動 WebSocket 失敗: {e}")
    finally:
        await temp_exchange.close()

    await monitor_async()

if __name__ == \'__main__\':
    asyncio.run(main())

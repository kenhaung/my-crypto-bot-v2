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
    format='%(asctime)s [%(levelname)s] %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
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

ws_cvd_buffer  = defaultdict(lambda: {'buy': 0.0, 'sell': 0.0, 'ts': 0.0})
ws_cvd_lock    = Lock()
ws_connections = {}

DB_PATH = '/app/data/radar_v2_pro.db'

# --- 可調參數 ---
TOP_SYMBOLS        = 40
MAX_POSITIONS      = 10
MAX_LONG           = 6
MAX_SHORT          = 6
MAX_SIGNALS_MEMORY = 500
SIGNAL_EXPIRY_TIME = 86400

# 風控
ATR_SL_MULT    = 1.5    # 止損：BB外緣 + 1.5 ATR
ATR_TP2_MULT   = 3.0    # 第二批止盈（剩餘50%）：超過中軌
MAX_HOLD_HOURS = 12     # 動量突破不該抱太久
MIN_SL_PCT     = 0.03   # 最低止損距離
MAX_SL_PCT     = 0.12   # 最高止損距離

# EMA 參數
EMA_FAST_LENGTH = 20
EMA_MID_LENGTH  = 50
EMA_SLOW_LENGTH = 200

# 突破參數
BREAKOUT_LOOKBACK = 20  # 突破前 N 根 K 線的高點/低點
VOLUME_MULTIPLIER = 2.0 # 突破時成交量需達到均量的 X 倍
VOL_LOOKBACK      = 20  # 計算均量時回溯的 K 線數量

# RSI 參數
RSI_LENGTH     = 14
RSI_BULL_MIN   = 55    # 多頭突破時 RSI 需 > 55
RSI_BULL_MAX = 72
RSI_BEAR_MIN = 28
RSI_BEAR_MAX = 45    # 空頭突破時 RSI 需 < 45

# 勝率門檻
WINRATE_THRESHOLD   = 0.40
WINRATE_REDUCED_MAX = 5

# 時間框架
TIMEFRAME = '1h'

# --- 新增抗震盪參數 ---
BB_WIDTH_LOOKBACK   = 100 # 計算布林帶寬度百分位數的 K 線數量
BB_WIDTH_PERCENTILE = 20  # 低於此百分位數則過濾
RSI_DIVERGENCE_LOOKBACK = 30 # 尋找 RSI 背離的 K 線數量

_STOCK_SYMBOLS = {
    'TSLA','AAPL','GOOGL','AMZN','MSFT','NVDA','META','BABA',
    'NFLX','COIN','MSTR','AMD','INTC','ORCL','PYPL','UBER',
}
_METAL_SYMBOLS = {'XAU','XAG','PAXG','XAUT'}

def is_crypto_symbol(symbol: str) -> bool:
    base = symbol.split('/')[0]
    if base in _METAL_SYMBOLS: return False
    if base in _STOCK_SYMBOLS: return False
    return True

LARGE_CAP = {'BTC/USDT','ETH/USDT','BNB/USDT','SOL/USDT'}
MID_CAP   = {
    'XRP/USDT','ADA/USDT','AVAX/USDT','DOT/USDT','MATIC/USDT',
    'LINK/USDT','UNI/USDT','ATOM/USDT','LTC/USDT','ETC/USDT'
}

# --- SQLite 持久化 ---
def init_db():
    import os as _os
    _os.makedirs(_os.path.dirname(DB_PATH), exist_ok=True)
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute(''''CREATE TABLE IF NOT EXISTS positions (
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
    )''''')
    c.execute(''''CREATE TABLE IF NOT EXISTS trades (
        id          INTEGER PRIMARY KEY AUTOINCREMENT,
        symbol      TEXT,
        side        TEXT,
        pnl         REAL,
        won         INTEGER,
        trade_time  TEXT,
        week_id     TEXT,
        exit_type   TEXT
    )''''')
    conn.commit()
    conn.close()
    log.info("[DB] V2-Pro 持久化資料庫已初始化")

def get_week_id() -> str:
    now = datetime.datetime.now(datetime.timezone.utc)
    return f"{now.year}-W{now.isocalendar()[1]:02d}"

def db_save_position(symbol: str, data: dict):
    try:
        conn = sqlite3.connect(DB_PATH)
        conn.execute(''''INSERT OR REPLACE INTO positions
            (symbol, side, ep, sl, tp1, tp2, tp1_hit, atr, entry_time, category)
            VALUES (?,?,?,?,?,?,?,?,?,?)''''',
            (symbol, data['side'], data['ep'], data['sl'],
            data['tp1'], data['tp2'], int(data.get('tp1_hit', False)),
            data.get('atr', 0),
            data.get('entry_time', time.time()),
            data.get('category', '')))
        conn.commit(); conn.close()
    except Exception as e:
        log.warning(f"[DB] 儲存持倉失敗: {e}")

def db_update_position(symbol: str, updates: dict):
    try:
        conn = sqlite3.connect(DB_PATH)
        for key, val in updates.items():
            conn.execute(f'UPDATE positions SET {key}=? WHERE symbol=?',
                          (val, symbol))
        conn.commit(); conn.close()
    except Exception as e:
        log.warning(f"[DB] 更新持倉失敗: {e}")

def db_remove_position(symbol: str):
    try:
        conn = sqlite3.connect(DB_PATH)
        conn.execute('DELETE FROM positions WHERE symbol=?', (symbol,))
        conn.commit(); conn.close()
    except Exception as e:
        log.warning(f"[DB] 刪除持倉失敗: {e}")

def db_load_positions() -> dict:
    try:
        conn = sqlite3.connect(DB_PATH)
        rows = conn.execute('SELECT * FROM positions').fetchall()
        conn.close()
        result = {}
        for r in rows:
            result[r[0]] = {
                'side': r[1], 'ep': r[2], 'sl': r[3],
                'tp1': r[4], 'tp2': r[5], 'tp1_hit': bool(r[6]),
                'atr': r[7], 'entry_time': r[8], 'category': r[9]
            }
        return result
    except Exception as e:
        log.warning(f"[DB] 載入持倉失敗: {e}")
        return {}

def db_save_trade(symbol: str, side: str, pnl: float,
                  won: bool, exit_type: str = ''):
    try:
        conn = sqlite3.connect(DB_PATH)
        conn.execute(''''INSERT INTO trades
            (symbol, side, pnl, won, trade_time, week_id, exit_type)
            VALUES (?,?,?,?,?,?,?)''''',
            (symbol, side, pnl, int(won),
            datetime.datetime.now(datetime.timezone.utc).isoformat(),
            get_week_id(), exit_type))
        conn.commit(); conn.close()
    except Exception as e:
        log.warning(f"[DB] 儲存交易失敗: {e}")

def _calc_stats(rows: list) -> dict:
    trades = [{'pnl': r[0], 'won': bool(r[1])} for r in rows]
    total  = len(trades)
    wins   = sum(1 for t in trades if t['won'])
    pnls   = [t['pnl'] for t in trades]
    wr     = (wins / total * 100) if total > 0 else 0
    avg    = (sum(pnls) / total)  if total > 0 else 0
    streak = cur = 0
    for t in trades:
        cur    = cur + 1 if not t['won'] else 0
        streak = max(streak, cur)
    return {
        'total': total, 'wins': wins, 'losses': total - wins,
        'win_rate': wr, 'avg_pnl': avg,
        'max_loss_streak': streak,
        'best':  max(pnls) if pnls else 0,
        'worst': min(pnls) if pnls else 0,
    }

def _empty_stats() -> dict:
    return {'total':0,'wins':0,'losses':0,'win_rate':0,
            'avg_pnl':0,'max_loss_streak':0,'best':0,'worst':0}

def db_load_weekly_stats(week_id: str = None) -> dict:
    try:
        wid  = week_id or get_week_id()
        conn = sqlite3.connect(DB_PATH)
        rows = conn.execute(
            'SELECT pnl, won FROM trades WHERE week_id=?', (wid,)
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
            'SELECT pnl, won FROM trades WHERE trade_time >= ? AND trade_time <= ?',
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
            'SELECT pnl, won FROM trades WHERE trade_time >= ?', (since,)
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
            'SELECT pnl, won FROM trades ORDER BY trade_time'
        ).fetchall()
        conn.close()
        if not rows:
            return {**_empty_stats(), 'total_pnl': 0}
        base = _calc_stats(rows)
        base['total_pnl'] = sum(r[0] for r in rows)
        return base
    except Exception as e:
        log.warning(f"[DB] 讀取全部統計失敗: {e}")
        return {**_empty_stats(), 'total_pnl': 0}

# --- 持倉管理 ---
def position_count() -> int:
    with positions_lock: return len(active_positions)

def long_count() -> int:
    with positions_lock:
        return sum(1 for p in active_positions.values() if p['side'] == 'long')

def short_count() -> int:
    with positions_lock:
        return sum(1 for p in active_positions.values() if p['side'] == 'short')

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
    wr      = s['win_rate'] / 100 if s['total'] >= 10 else 1.0
    eff_max = WINRATE_REDUCED_MAX if wr < WINRATE_THRESHOLD and s['total'] >= 10 else MAX_POSITIONS
    if position_count() >= eff_max: return False, f"總倉位已達上限 {eff_max}"
    if side == 'long'  and long_count()  >= MAX_LONG:  return False, f"多單上限 {MAX_LONG}"
    if side == 'short' and short_count() >= MAX_SHORT: return False, f"空單上限 {MAX_SHORT}"
    return True, ''

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

# --- WebSocket CVD ---
def _ws_on_message(symbol_key: str, msg: str):
    try:
        data = json.loads(msg)
        qty  = float(data.get('q', 0))
        is_buyer_maker = data.get('m', False)
        with ws_cvd_lock:
            if is_buyer_maker: ws_cvd_buffer[symbol_key]['sell'] += qty
            else: ws_cvd_buffer[symbol_key]['buy']  += qty
            ws_cvd_buffer[symbol_key]['ts'] = time.time()
    except Exception: pass

def start_ws_cvd(symbol: str):
    if not WS_AVAILABLE: return
    symbol_key = symbol.split('/')[0].lower() + 'usdt'
    if symbol_key in ws_connections: return
    def run():
        url = f"wss://fstream.binance.com/ws/{symbol_key}@aggTrade"
        def on_msg(ws, msg):   _ws_on_message(symbol_key, msg)
        def on_err(ws, err):   log.warning(f"[WS] {symbol_key} 錯誤: {err}")
        def on_close(ws, *a):
            log.info(f"[WS] {symbol_key} 連線關閉，5s 後重連")
            ws_connections.pop(symbol_key, None)
            time.sleep(5); start_ws_cvd(symbol)
        def on_open(ws):
            log.info(f"[WS] {symbol_key} 串流已連線")
            with ws_cvd_lock: ws_cvd_buffer[symbol_key] = {'buy': 0.0, 'sell': 0.0, 'ts': time.time()}
        w = ws_lib.WebSocketApp(url, on_message=on_msg, on_error=on_err, on_close=on_close, on_open=on_open)
        ws_connections[symbol_key] = True
        w.run_forever(ping_interval=30, ping_timeout=10)
    Thread(target=run, daemon=True).start()

async def get_cvd_bias_async(exchange, symbol: str) -> str:
    symbol_key = symbol.split('/')[0].lower() + 'usdt'
    with ws_cvd_lock:
        buf = ws_cvd_buffer.get(symbol_key)
        ws_fresh = buf and (time.time() - buf['ts']) < 60
    if ws_fresh:
        with ws_cvd_lock:
            buy_vol, sell_vol = buf['buy'], buf['sell']
            ws_cvd_buffer[symbol_key] = {'buy': 0.0, 'sell': 0.0, 'ts': time.time()}
        total = buy_vol + sell_vol
        ratio = buy_vol / total if total > 0 else 0.5
        if ratio >= 0.55: return 'bull'
        if ratio <= 0.45: return 'bear'
        return 'neutral'
    else:
        try:
            trades = await exchange.fetch_trades(symbol, limit=500)
            if not trades: return 'neutral'
            df_t = pd.DataFrame([{'amount': t['amount'], 'side': t['side']} for t in trades])
            buy_vol = df_t[df_t['side'] == 'buy']['amount'].sum()
            total = df_t['amount'].sum()
            ratio = buy_vol / total if total > 0 else 0.5
            if ratio >= 0.55: return 'bull'
            if ratio <= 0.45: return 'bear'
            return 'neutral'
        except Exception: return 'neutral'

# --- 反轉K線辨識 ---
def is_reversal_candle_long(o, h, l, c):
    body, total = abs(c - o), h - l
    if total == 0: return 'none'
    lower_shadow, upper_shadow = min(o, c) - l, h - max(o, c)
    body_ratio = body / total
    if lower_shadow > REVERSAL_SHADOW_RATIO * body and upper_shadow < body and body_ratio < 0.40: return 'hammer'
    if c > o and body_ratio > REVERSAL_BODY_RATIO: return 'bullish_engulfing'
    if body_ratio < REVERSAL_DOJI_RATIO: return 'doji'
    return 'none'

def is_reversal_candle_short(o, h, l, c):
    body, total = abs(c - o), h - l
    if total == 0: return 'none'
    lower_shadow, upper_shadow = min(o, c) - l, h - max(o, c)
    body_ratio = body / total
    if upper_shadow > REVERSAL_SHADOW_RATIO * body and lower_shadow < body and body_ratio < 0.40: return 'shooting_star'
    if c < o and body_ratio > REVERSAL_BODY_RATIO: return 'bearish_engulfing'
    if body_ratio < REVERSAL_DOJI_RATIO: return 'doji'
    return 'none'

# --- 核心分析：動量突破型 V2-Pro ---
async def analyze_symbol_v2_pro(exchange, symbol: str):
    df = await fetch_ohlcv_df_async(exchange, symbol, TIMEFRAME, 250)
    if df is None or len(df) < 200: return None

    c, h, l, o, v = df['c'], df['h'], df['l'], df['o'], df['v']
    curr_c, curr_h, curr_l, curr_o, curr_v = float(c.iloc[-1]), float(h.iloc[-1]), float(l.iloc[-1]), float(o.iloc[-1]), float(v.iloc[-1])
    prev_c = float(c.iloc[-2])

    # 指標計算
    ema_fast = ta.ema(c, length=EMA_FAST_LENGTH).iloc[-1]
    ema_mid  = ta.ema(c, length=EMA_MID_LENGTH).iloc[-1]
    ema_slow = ta.ema(c, length=EMA_SLOW_LENGTH).iloc[-1]
    rsi      = ta.rsi(c, length=RSI_LENGTH).iloc[-1]
    atr      = ta.atr(h, l, c, length=14).iloc[-1]
    
    # 波動率過濾 (A): BB Width
    bb = ta.bbands(c, length=20, std=2.0)
    bb_width = (bb[f'BBU_20_2.0'].iloc[-1] - bb[f'BBL_20_2.0'].iloc[-1]) / bb[f'BBM_20_2.0'].iloc[-1]
    bb_width_history = (bb[f'BBU_20_2.0'] - bb[f'BBL_20_2.0']) / bb[f'BBM_20_2.0']
    if bb_width < bb_width_history.quantile(0.20): # 如果當前BB寬度小於過去100根K線的20%分位數，則認為波動過低
        # log.info(f"[{symbol}] 波動率過低 ({bb_width:.2%})，跳過")
        return None

    # 成交量確認
    avg_vol = float(v.iloc[-VOL_LOOKBACK-1:-1].mean())
    
    # 突破條件
    recent_high = df['h'].iloc[-BREAKOUT_LOOKBACK-1:-1].max()
    recent_low  = df['l'].iloc[-BREAKOUT_LOOKBACK-1:-1].min()

    side = None
    reason = ""

    # 多頭突破
    if curr_c > recent_high and curr_v >= avg_vol * VOLUME_MULTIPLIER:
        if ema_fast > ema_mid > ema_slow: # EMA 多頭排列
            if rsi > RSI_BULL_MIN: # RSI 動量確認
                # RSI 背離確認 (C): 頂背離過濾多頭
                # 簡化版：檢查最近一次價格高點和RSI高點
                prev_high_idx = df[df['h'] == recent_high].index[-1]
                prev_rsi_at_high = ta.rsi(df['c'].loc[:prev_high_idx], length=RSI_LENGTH).iloc[-1]
                if curr_c > recent_high and rsi < prev_rsi_at_high: # 價格創新高，RSI卻沒有
                    # log.info(f"[{symbol}] 頂背離，過濾多頭突破")
                    return None
                side, reason = 'long', '多頭突破'

    # 空頭突破
    elif curr_c < recent_low and curr_v >= avg_vol * VOLUME_MULTIPLIER:
        if ema_fast < ema_mid < ema_slow: # EMA 空頭排列
            if rsi < RSI_BEAR_MAX: # RSI 動量確認
                # RSI 背離確認 (C): 底背離過濾空頭
                # 簡化版：檢查最近一次價格低點和RSI低點
                prev_low_idx = df[df['l'] == recent_low].index[-1]
                prev_rsi_at_low = ta.rsi(df['c'].loc[:prev_low_idx], length=RSI_LENGTH).iloc[-1]
                if curr_c < recent_low and rsi > prev_rsi_at_low: # 價格創新低，RSI卻沒有
                    # log.info(f"[{symbol}] 底背離，過濾空頭突破")
                    return None
                side, reason = 'short', '空頭突破'

    if not side: return None

    # CVD 驗證
    cvd_bias = await get_cvd_bias_async(exchange, symbol)
    if (side == 'long' and cvd_bias == 'bear') or (side == 'short' and cvd_bias == 'bull'):
        # log.info(f"[{symbol}] CVD 偏離，過濾 {side} 信號")
        return None

    # 結構化止損 (D): 動態止損緩衝
    sl_struct = recent_low if side == 'long' else recent_high
    dynamic_sl_buffer = 0.5 * atr # 使用ATR動態緩衝
    sl = sl_struct - dynamic_sl_buffer if side == 'long' else sl_struct + dynamic_sl_buffer

    # 確保止損在合理範圍
    sl_pct = abs(curr_c - sl) / curr_c
    if sl_pct < MIN_SL_PCT: # 如果止損太近，則調整
        sl = curr_c * (1 - MIN_SL_PCT) if side == 'long' else curr_c * (1 + MIN_SL_PCT)
    elif sl_pct > MAX_SL_PCT: # 如果止損太遠，則調整
        sl = curr_c * (1 - MAX_SL_PCT) if side == 'long' else curr_c * (1 + MAX_SL_PCT)

    tp1 = curr_c + (curr_c - sl) * ATR_SL_MULT # 1.5倍止損距離
    tp2 = curr_c + (curr_c - sl) * ATR_TP2_MULT # 3.0倍止損距離

    labels = f"🚀 動量突破 ({reason})\n📊 EMA: {ema_fast:.4f}/{ema_mid:.4f}/{ema_slow:.4f}\n📈 RSI: {rsi:.1f} | 量能: {curr_v/avg_vol:.1f}x\n💹 CVD: {cvd_bias}"

    return {'side': side, 'ep': curr_c, 'sl': sl, 'tp1': tp1, 'tp2': tp2, 'atr': atr, 'labels': labels}

# --- 輔助與監控邏輯 ---
async def fetch_ohlcv_df_async(exchange, symbol, timeframe, limit):
    try:
        ohlcv = await exchange.fetch_ohlcv(symbol, timeframe, limit=limit)
        df = pd.DataFrame(ohlcv, columns=['t', 'o', 'h', 'l', 'c', 'v'])
        df['t'] = pd.to_datetime(df['t'], unit='ms')
        return df.astype({'o':float,'h':float,'l':float,'c':float,'v':float})
    except Exception: return None

async def get_exchange_async():
    return ccxt.binance({'apiKey': os.environ.get('BINANCE_API_KEY'), 'secret': os.environ.get('BINANCE_SECRET'), 'options': {'defaultType': 'future'}, 'enableRateLimit': True})

def send_telegram(msg):
    token, chat_id = os.environ.get('TELEGRAM_TOKEN'), os.environ.get('TELEGRAM_CHAT_ID')
    if token and chat_id:
        try: requests.get(f"https://api.telegram.org/bot{token}/sendMessage", params={'chat_id': chat_id, 'text': msg, 'parse_mode': 'Markdown'}, timeout=10)
        except Exception: pass

async def monitor_async():
    log.info("=== 動量突破 V2-Pro 監控啟動 ===")
    exchange = await get_exchange_async()
    semaphore = asyncio.Semaphore(5)
    while True:
        try:
            markets = await exchange.load_markets()
            symbols = [s for s in markets if '/USDT' in s and markets[s]['linear'] and is_crypto_symbol(s)][:TOP_SYMBOLS]
            async def process(symbol):
                async with semaphore:
                    try:
                        pos = get_position(symbol)
                        df_now = await fetch_ohlcv_df_async(exchange, symbol, TIMEFRAME, 2)
                        if df_now is None: return
                        curr_c = df_now['c'].iloc[-1]
                        if pos:
                            # 簡單出場邏輯
                            side, ep, sl, tp1, tp2 = pos['side'], pos['ep'], pos['sl'], pos['tp1'], pos['tp2']
                            exit_reason = None
                            if (side == 'long' and curr_c <= sl) or (side == 'short' and curr_c >= sl): exit_reason = "止損"
                            elif (side == 'long' and curr_c >= tp2) or (side == 'short' and curr_c <= tp2): exit_reason = "止盈2"
                            elif not pos['tp1_hit'] and ((side == 'long' and curr_c >= tp1) or (side == 'short' and curr_c <= tp1)):
                                update_position(symbol, {'tp1_hit': True, 'sl': ep})
                                send_telegram(f"✅ *V2-Pro {symbol} 第一批止盈*\n進場: {ep:.4f} -> 現價: {curr_c:.4f}\n🛡 止損已移至保本價")
                            if exit_reason:
                                pnl = (curr_c/ep-1)*100 if side=='long' else (ep/curr_c-1)*100
                                send_telegram(f"🏁 *V2-Pro {symbol} 出場 ({exit_reason})*\n損益: {pnl:+.2f}%")
                                db_save_trade(symbol, side, pnl, pnl>0, exit_reason)
                                remove_position(symbol)
                            return
                        
                        res = await analyze_symbol_v2_pro(exchange, symbol)
                        if res:
                            ok, _ = can_open_position(symbol, res['side'])
                            if ok:
                                add_position(symbol, res)
                                send_telegram(f"🚀 *V2-Pro {res['side']} 進場*: `{symbol}`\n進場價: `{res['ep']:.4f}`\n🛡 止損: `{res['sl']:.4f}`\n🎯 止盈1: `{res['tp1']:.4f}`\n{res['labels']}")
                    except Exception: pass
            await asyncio.gather(*[process(s) for s in symbols])
            await asyncio.sleep(60)
        except Exception as e:
            log.error(f"Monitor Error: {e}"); await asyncio.sleep(60)
async def main():
    init_db()
    exchange = await get_exchange_async()
    markets = await exchange.load_markets()
    symbols = [s for s in markets if 
'/USDT' in s and markets[s]['linear'] and is_crypto_symbol(s)][:TOP_SYMBOLS]

    # 發送啟動成功訊息
    telegram_msg = f"🔔 *V2-Pro 動量突破啟動成功！*\n時間: {datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%d %H:%M:%S UTC')}\n監控幣種: {len(symbols)} 個\n端口: 5001"
    send_telegram(telegram_msg)
    log.info(telegram_msg)

    # 啟動 WebSocket
    for s in symbols: start_ws_cvd(s); await asyncio.sleep(0.1)
    await exchange.close()
    await monitor_async()

# ════════════════════════════════════════════
# Flask Route
# ════════════════════════════════════════════

@app.route('/')
def home():
    pos_all = get_all_positions()
    s       = db_load_recent_stats(days=30)
    lines   = [
        f"{sym}: {p['side']} @ {p['ep']:.4f} "
        f"[{p.get('category','?')}] "
        f"{'(已TP1)' if p.get('tp1_hit') else ''}"
        for sym, p in pos_all.items()
    ]
    return (
        f"動量突破 V2-Pro（Async版）\n"
        f"持倉 {len(pos_all)}/{MAX_POSITIONS}\n\n"
        + ('\n'.join(lines) if lines else '無持倉')
        + f"\n\n近30天: {s['total']}筆 | 勝率 {s['win_rate']:.1f}%"
    )

@app.route('/reset_trades')
def reset_trades():
    try:
        conn  = sqlite3.connect(DB_PATH)
        count = conn.execute('SELECT COUNT(*) FROM trades').fetchone()[0]
        conn.execute('DELETE FROM trades')
        conn.commit(); conn.close()
        send_telegram(f"🗑 *[V2-Pro] 交易記錄已清除*\n共刪除 {count} 筆")
        return f"已清除 {count} 筆交易記錄"
    except Exception as e:
        return f"清除失敗: {e}"


# ════════════════════════════════════════════
# 啟動（gunicorn 相容）
# ════════════════════════════════════════════

def _run_async_main():
    """在背景線程跑 asyncio event loop，與 gunicorn 相容"""
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    loop.run_until_complete(main())

# gunicorn 啟動 Flask 時自動觸發
_started = False
_start_lock = __import__('threading').Lock()

def _auto_start():
    global _started
    with _start_lock:
        if not _started:
            _started = True
            Thread(target=_run_async_main, daemon=True).start()

_auto_start()

if __name__ == '__main__':
    port = int(os.environ.get('PORT', 8080))
    app.run(host='0.0.0.0', port=port, debug=False)


import os, time, ccxt, requests, pandas as pd, pandas_ta as ta
import datetime, logging, numpy as np, json, sqlite3
from flask import Flask
from threading import Thread, Lock
from collections import OrderedDict, defaultdict
try:
    import websocket as ws_lib
    WS_AVAILABLE = True
except ImportError:
    WS_AVAILABLE = False

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)
log = logging.getLogger(__name__)

app = Flask(__name__)

threads_started  = False
threads_lock     = Lock()
sent_signals     = OrderedDict()
signals_lock     = Lock()
active_positions = {}
positions_lock   = Lock()

ws_cvd_buffer  = defaultdict(lambda: {'buy': 0.0, 'sell': 0.0, 'ts': 0.0})
ws_cvd_lock    = Lock()
ws_connections = {}

DB_PATH = '/app/data/radar_v2.db'

# ════════════════════════════════════════════
# 可調參數
# ════════════════════════════════════════════

TOP_SYMBOLS        = 40
MAX_POSITIONS      = 10
MAX_LONG           = 6
MAX_SHORT          = 6
MAX_SIGNALS_MEMORY = 500
SIGNAL_EXPIRY_TIME = 86400

# 風控
ATR_SL_MULT    = 1.0
ATR_TP1_MULT   = 2.0   # 第一批止盈（50%倉位）
ATR_TP2_MULT   = 4.0   # 第二批止盈（剩餘50%）
MAX_HOLD_HOURS = 24

# 最低止損距離（防止極低價幣止損過近）
MIN_SL_PCT = 0.03   # 最少 3%

# 趨勢 EMA
EMA_FAST  = 20
EMA_MID   = 50
EMA_SLOW  = 200

# 突破條件
BREAKOUT_LOOKBACK  = 20
VOLUME_MULTIPLIER  = 1.5

# RSI 動量
RSI_BULL_MIN = 50
RSI_BULL_MAX = 75
RSI_BEAR_MIN = 25
RSI_BEAR_MAX = 50

# 勝率門檻
WINRATE_THRESHOLD   = 0.40
WINRATE_REDUCED_MAX = 5

# 時間框架
TIMEFRAME = '1h'

# 非加密貨幣過濾
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


# ════════════════════════════════════════════
# SQLite 持久化
# 新增欄位：tp2（第二批止盈）、tp1_hit（第一批是否已出場）
# ════════════════════════════════════════════

def init_db():
    import os as _os
    _os.makedirs(_os.path.dirname(DB_PATH), exist_ok=True)
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute('''CREATE TABLE IF NOT EXISTS positions (
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
    )''')
    c.execute('''CREATE TABLE IF NOT EXISTS trades (
        id          INTEGER PRIMARY KEY AUTOINCREMENT,
        symbol      TEXT,
        side        TEXT,
        pnl         REAL,
        won         INTEGER,
        trade_time  TEXT,
        week_id     TEXT,
        exit_type   TEXT
    )''')
    conn.commit()
    conn.close()
    log.info("[DB] V2 持久化資料庫已初始化（分批止盈版）")

def get_week_id() -> str:
    now = datetime.datetime.now(datetime.timezone.utc)
    return f"{now.year}-W{now.isocalendar()[1]:02d}"

def db_save_position(symbol: str, data: dict):
    try:
        conn = sqlite3.connect(DB_PATH)
        conn.execute('''INSERT OR REPLACE INTO positions
            (symbol, side, ep, sl, tp1, tp2, tp1_hit, atr, entry_time, category)
            VALUES (?,?,?,?,?,?,?,?,?,?)''',
            (symbol, data['side'], data['ep'], data['sl'],
             data['tp1'], data['tp2'], int(data.get('tp1_hit', False)),
             data.get('atr', 0), data.get('entry_time', time.time()),
             data.get('category', '')))
        conn.commit(); conn.close()
    except Exception as e:
        log.warning(f"[DB] 儲存持倉失敗: {e}")

def db_update_position(symbol: str, updates: dict):
    """通用更新持倉欄位"""
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
        conn.execute('''INSERT INTO trades
            (symbol, side, pnl, won, trade_time, week_id, exit_type)
            VALUES (?,?,?,?,?,?,?)''',
            (symbol, side, pnl, int(won),
             datetime.datetime.now(datetime.timezone.utc).isoformat(),
             get_week_id(), exit_type))
        conn.commit(); conn.close()
    except Exception as e:
        log.warning(f"[DB] 儲存交易失敗: {e}")

def db_load_weekly_stats() -> dict:
    try:
        conn = sqlite3.connect(DB_PATH)
        rows = conn.execute(
            'SELECT pnl, won FROM trades WHERE week_id=?',
            (get_week_id(),)
        ).fetchall()
        conn.close()
        trades = [{'pnl': r[0], 'won': bool(r[1])} for r in rows]
        total  = len(trades)
        wins   = sum(1 for t in trades if t['won'])
        pnls   = [t['pnl'] for t in trades]
        wr     = (wins / total * 100) if total > 0 else 0
        avg    = (sum(pnls) / total) if total > 0 else 0
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
    except Exception as e:
        log.warning(f"[DB] 讀取週報失敗: {e}")
        return {'total':0,'wins':0,'losses':0,'win_rate':0,
                'avg_pnl':0,'max_loss_streak':0,'best':0,'worst':0}


# ════════════════════════════════════════════
# 工具函式
# ════════════════════════════════════════════

def send_telegram(message: str) -> bool:
    token   = os.environ.get('TELEGRAM_TOKEN')
    chat_id = os.environ.get('TELEGRAM_CHAT_ID')
    if not token or not chat_id:
        log.warning("Telegram 環境變數未設定")
        return False
    url    = f"https://api.telegram.org/bot{token}/sendMessage"
    params = {'chat_id': chat_id, 'text': message, 'parse_mode': 'Markdown'}
    try:
        resp = requests.get(url, params=params, timeout=10)
        resp.raise_for_status()
        return True
    except Exception as e:
        log.error(f"Telegram 發送失敗: {e}")
        return False

def get_exchange():
    return ccxt.binance({
        'urls': {'api': {
            'public':     'https://api3.binance.com/api/v3',
            'fapiPublic': 'https://fapi.binance.com/fapi/v1',
        }},
        'options':         {'defaultType': 'future'},
        'enableRateLimit': True,
    })

_spot_exchange      = None
_spot_exchange_lock = Lock()

def get_spot_exchange():
    global _spot_exchange
    with _spot_exchange_lock:
        if _spot_exchange is None:
            _spot_exchange = ccxt.binance({'enableRateLimit': True})
        return _spot_exchange

def get_top_symbols(exchange, n: int = TOP_SYMBOLS):
    try:
        tickers = exchange.fetch_tickers()
        return [
            s for s, t in sorted(
                tickers.items(),
                key=lambda x: x[1].get('quoteVolume', 0), reverse=True
            )
            if '/USDT' in s and is_crypto_symbol(s)
        ][:n]
    except Exception as e:
        log.error(f"取得幣種列表失敗: {e}")
        return []

def fetch_ohlcv_df(exchange, symbol: str, timeframe: str, limit: int):
    ohlcv = exchange.fetch_ohlcv(symbol, timeframe=timeframe, limit=limit + 1)
    if len(ohlcv) < limit:
        return None
    df = pd.DataFrame(ohlcv[:-1], columns=['t','o','h','l','c','v'])
    df = df.astype({'o':float,'h':float,'l':float,'c':float,'v':float})
    return df

def get_symbol_category(symbol: str) -> str:
    base  = symbol.split('/')[0]
    clean = f"{base}/USDT"
    if clean in LARGE_CAP: return 'large'
    if clean in MID_CAP:   return 'mid'
    return 'small'

def calc_effective_atr(atr: float, curr_c: float) -> float:
    """
    FIX：防止極低價幣（1000PEPE等）止損點過近。
    ATR 絕對值至少要達到當前價格的 MIN_SL_PCT。
    """
    min_atr = curr_c * MIN_SL_PCT
    return max(atr, min_atr)

def is_weekend() -> bool:
    """週六、週日不執行超時出場，避免低量期錯過行情"""
    now = datetime.datetime.now(datetime.timezone.utc)
    return now.weekday() >= 5


def wait_until_next_1h_close() -> float:
    """對齊 1H K線收盤，收盤後 2 分鐘掃描"""
    now        = datetime.datetime.now(datetime.timezone.utc)
    next_close = now.replace(minute=2, second=0, microsecond=0) + \
                 datetime.timedelta(hours=1)
    wait = (next_close - now).total_seconds()
    return max(wait, 60)


# ════════════════════════════════════════════
# 持倉管理
# ════════════════════════════════════════════

def position_count() -> int:
    with positions_lock: return len(active_positions)

def long_count() -> int:
    with positions_lock:
        return sum(1 for p in active_positions.values() if p['side'] == 'long')

def short_count() -> int:
    with positions_lock:
        return sum(1 for p in active_positions.values() if p['side'] == 'short')

def get_position(symbol: str):
    with positions_lock: return active_positions.get(symbol)

def add_position(symbol: str, data: dict):
    with positions_lock: active_positions[symbol] = data
    db_save_position(symbol, data)

def update_position(symbol: str, updates: dict):
    with positions_lock:
        if symbol in active_positions:
            active_positions[symbol].update(updates)
    db_update_position(symbol, updates)

def remove_position(symbol: str):
    with positions_lock: active_positions.pop(symbol, None)
    db_remove_position(symbol)

def get_all_positions() -> dict:
    with positions_lock: return dict(active_positions)

def can_open_position(symbol: str, side: str) -> tuple:
    s       = db_load_weekly_stats()
    wr      = s['win_rate'] / 100 if s['total'] >= 10 else 1.0
    eff_max = WINRATE_REDUCED_MAX \
              if wr < WINRATE_THRESHOLD and s['total'] >= 10 else MAX_POSITIONS
    if position_count() >= eff_max:
        return False, f"總倉位已達上限 {eff_max}"
    if side == 'long'  and long_count()  >= MAX_LONG:
        return False, f"多單上限 {MAX_LONG}"
    if side == 'short' and short_count() >= MAX_SHORT:
        return False, f"空單上限 {MAX_SHORT}"
    return True, ''


# ════════════════════════════════════════════
# 訊號管理
# ════════════════════════════════════════════

def is_signal_sent(key: str) -> bool:
    with signals_lock: return key in sent_signals

def record_signal(key: str):
    with signals_lock: sent_signals[key] = time.time()

def clean_signals():
    now = time.time()
    with signals_lock:
        for k in [k for k, v in sent_signals.items()
                  if now - v > SIGNAL_EXPIRY_TIME]:
            del sent_signals[k]
        while len(sent_signals) > MAX_SIGNALS_MEMORY:
            sent_signals.popitem(last=False)


# ════════════════════════════════════════════
# WebSocket CVD
# ════════════════════════════════════════════

def _ws_on_message(symbol_key: str, msg: str):
    try:
        data = json.loads(msg)
        qty  = float(data.get('q', 0))
        is_buyer_maker = data.get('m', False)
        with ws_cvd_lock:
            if is_buyer_maker:
                ws_cvd_buffer[symbol_key]['sell'] += qty
            else:
                ws_cvd_buffer[symbol_key]['buy']  += qty
            ws_cvd_buffer[symbol_key]['ts'] = time.time()
    except Exception:
        pass

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
            with ws_cvd_lock:
                ws_cvd_buffer[symbol_key] = {
                    'buy': 0.0, 'sell': 0.0, 'ts': time.time()
                }
        w = ws_lib.WebSocketApp(url, on_message=on_msg, on_error=on_err,
                                on_close=on_close, on_open=on_open)
        ws_connections[symbol_key] = True
        w.run_forever(ping_interval=30, ping_timeout=10)

    Thread(target=run, daemon=True).start()

def get_cvd_bias(symbol: str) -> str:
    symbol_key = symbol.split('/')[0].lower() + 'usdt'
    with ws_cvd_lock:
        buf = ws_cvd_buffer.get(symbol_key)
        if not buf or (time.time() - buf['ts']) > 300:
            return 'neutral'
        total = buf['buy'] + buf['sell']
        if total == 0: return 'neutral'
        ratio = buf['buy'] / total
    if ratio >= 0.55: return 'bull'
    if ratio <= 0.45: return 'bear'
    return 'neutral'


# ════════════════════════════════════════════
# 核心分析：動量突破型 V2
# Layer 1：EMA 趨勢方向（20/50/200）
# Layer 2：價格突破近20根高低點 + 成交量放大
# Layer 3：RSI 動量區間過濾
# 加分項：CVD 方向一致
# ════════════════════════════════════════════

def analyze_symbol_v2(exchange, symbol: str):

    df = fetch_ohlcv_df(exchange, symbol, TIMEFRAME, 250)
    if df is None or len(df) < 210: return None

    c   = df['c']
    h   = df['h']
    l   = df['l']
    v   = df['v']

    raw_atr = ta.atr(h, l, c, length=14).iloc[-1]
    if not raw_atr or raw_atr <= 0: return None

    curr_c = float(c.iloc[-1])

    # FIX：套用最低止損距離保護
    atr = calc_effective_atr(raw_atr, curr_c)

    # ── Layer 1：EMA 三線排列 ──
    ema_fast = ta.ema(c, length=EMA_FAST)
    ema_mid  = ta.ema(c, length=EMA_MID)
    ema_slow = ta.ema(c, length=EMA_SLOW)

    ef = ema_fast.iloc[-1]
    em = ema_mid.iloc[-1]
    es = ema_slow.iloc[-1]

    # EMA 任一為 NaN（歷史數據不足）直接跳過
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

    bull_break = float(h.iloc[-1]) > recent_high and vol_confirm
    bear_break = float(l.iloc[-1]) < recent_low  and vol_confirm

    if bull_trend and not bull_break: return None
    if bear_trend and not bear_break: return None

    # ── Layer 3：RSI 動量 ──
    rsi = ta.rsi(c, length=14).iloc[-1]
    if pd.isna(rsi): return None
    if bull_trend and not (RSI_BULL_MIN <= rsi <= RSI_BULL_MAX): return None
    if bear_trend and not (RSI_BEAR_MIN <= rsi <= RSI_BEAR_MAX): return None

    # ── CVD 加分項 ──
    cvd = get_cvd_bias(symbol)
    cvd_ok = (bull_trend and cvd in ('bull','neutral')) or \
             (bear_trend and cvd in ('bear','neutral'))
    if not cvd_ok: return None

    side = 'long' if bull_trend else 'short'

    # 止損
    sl  = curr_c - ATR_SL_MULT * atr if side == 'long' \
          else curr_c + ATR_SL_MULT * atr

    # 分批止盈
    tp1 = curr_c + ATR_TP1_MULT * atr if side == 'long' \
          else curr_c - ATR_TP1_MULT * atr
    tp2 = curr_c + ATR_TP2_MULT * atr if side == 'long' \
          else curr_c - ATR_TP2_MULT * atr

    sl_pct  = abs(curr_c - sl)  / curr_c * 100
    tp1_pct = abs(curr_c - tp1) / curr_c * 100
    tp2_pct = abs(curr_c - tp2) / curr_c * 100

    labels = (
        f"{'📈 多頭排列' if bull_trend else '📉 空頭排列'} "
        f"EMA {EMA_FAST}/{EMA_MID}/{EMA_SLOW}\n"
        f"🚀 {'向上突破' if bull_break else '向下跌破'} "
        f"近{BREAKOUT_LOOKBACK}根高低點\n"
        f"📊 成交量 {curr_vol/avg_vol:.1f}x 均量\n"
        f"💹 RSI {rsi:.1f} | CVD {cvd}\n"
        f"🛡 止損距離 {sl_pct:.1f}% | "
        f"🎯1 {tp1_pct:.1f}% | 🎯2 {tp2_pct:.1f}%"
    )

    return {
        'side': side, 'ep': curr_c, 'sl': sl,
        'tp1': tp1, 'tp2': tp2, 'tp1_hit': False,
        'atr': atr, 'labels': labels, 'rsi': rsi,
    }


# ════════════════════════════════════════════
# 分批止盈 + 移動止損 + 超時出場
#
# 回傳值：
#   'hold'      → 繼續持有
#   'tp1'       → 第一批止盈（50%出場，剩餘繼續）
#   'tp2'       → 第二批止盈（全部出場）
#   'sl'        → 止損出場
#   'timeout'   → 超時出場
# ════════════════════════════════════════════

def handle_position_update(symbol: str, curr_c: float) -> str:
    pos = get_position(symbol)
    if not pos: return 'hold'

    side       = pos['side']
    ep         = pos['ep']
    sl         = pos['sl']
    tp1        = pos['tp1']
    tp2        = pos['tp2']
    tp1_hit    = pos.get('tp1_hit', False)
    atr        = pos.get('atr', abs(tp1 - ep) / ATR_TP1_MULT)
    entry_time = pos.get('entry_time', time.time())

    # 超時出場
    if (time.time() - entry_time) / 3600 >= MAX_HOLD_HOURS:
        if is_weekend():
            log.debug(f"[Weekend] {symbol} 超時但週末，暫不出場")
            return 'hold'
        return 'timeout'

    if side == 'long':
        # 第一批止盈尚未達到
        if not tp1_hit:
            if curr_c >= tp1:
                # 第一批出場：止損移到進場價（保本）
                update_position(symbol, {'tp1_hit': True, 'sl': ep})
                log.info(f"[TP1] {symbol} 多單第一批止盈，止損移至進場價 {ep:.4f}")
                return 'tp1'
            if curr_c <= sl:
                return 'sl'
        else:
            # 第一批已出場，追第二批
            if curr_c >= tp2:
                return 'tp2'
            if curr_c <= get_position(symbol)['sl']:
                return 'sl'
            # 移動止損：每超過 1ATR 往上移
            new_sl = curr_c - atr
            if new_sl > get_position(symbol)['sl']:
                update_position(symbol, {'sl': new_sl})
                log.info(f"[Trail] {symbol} 多單止損上移 → {new_sl:.4f}")
    else:
        # 第一批止盈尚未達到
        if not tp1_hit:
            if curr_c <= tp1:
                update_position(symbol, {'tp1_hit': True, 'sl': ep})
                log.info(f"[TP1] {symbol} 空單第一批止盈，止損移至進場價 {ep:.4f}")
                return 'tp1'
            if curr_c >= sl:
                return 'sl'
        else:
            if curr_c <= tp2:
                return 'tp2'
            if curr_c >= get_position(symbol)['sl']:
                return 'sl'
            new_sl = curr_c + atr
            if new_sl < get_position(symbol)['sl']:
                update_position(symbol, {'sl': new_sl})
                log.info(f"[Trail] {symbol} 空單止損下移 → {new_sl:.4f}")

    return 'hold'


# ════════════════════════════════════════════
# 主監控迴圈（對齊 1H K線收盤）
# ════════════════════════════════════════════

def monitor():
    log.info("=== 動量突破 V2 監控啟動 ===")
    exchange = None

    while True:
        try:
            if exchange is None:
                exchange = get_exchange()

            symbols = get_top_symbols(exchange)
            if not symbols:
                time.sleep(60); continue

            log.info(f"[V2] 掃描 {len(symbols)} 幣種...")

            for symbol in symbols:
                try:
                    df_fast = fetch_ohlcv_df(exchange, symbol, TIMEFRAME, 5)
                    if df_fast is None: continue
                    curr_c   = float(df_fast['c'].iloc[-1])
                    last_k_t = df_fast['t'].iloc[-1]

                    pos = get_position(symbol)
                    if pos:
                        result = handle_position_update(symbol, curr_c)
                        side   = pos['side']
                        side_t = '多' if side == 'long' else '空'
                        tp1_hit = pos.get('tp1_hit', False)

                        if result == 'tp1':
                            pnl = abs(curr_c - pos['ep']) / pos['ep'] * 100
                            send_telegram(
                                f"✅ *[V2] {side_t}單第一批止盈*: `{symbol}`\n"
                                f"損益: `+{pnl:.2f}%`（50% 倉位）\n"
                                f"進場: `{pos['ep']:.4f}` → 止盈1: `{curr_c:.4f}`\n"
                                f"⚡ 止損已移至進場價，剩餘 50% 追第二批"
                            )
                            db_save_trade(symbol, side, pnl, True, 'tp1')
                            continue

                        elif result in ('tp2', 'sl', 'timeout'):
                            if result == 'tp2':
                                pnl  = abs(curr_c - pos['ep']) / pos['ep'] * 100
                                won  = True
                                icon = '🏆'
                                desc = f"{side_t}單第二批止盈"
                                note = f"（全部出場，共兩批獲利）"
                            elif result == 'sl':
                                pnl = (curr_c/pos['ep']-1)*100 if side=='long' \
                                      else (pos['ep']/curr_c-1)*100
                                won  = pnl > 0
                                icon = '❌' if not won else '✅'
                                desc = f"{side_t}單止損"
                                note = "（第一批已保本）" if tp1_hit else ""
                            else:
                                pnl = (curr_c/pos['ep']-1)*100 if side=='long' \
                                      else (pos['ep']/curr_c-1)*100
                                won  = pnl > 0
                                icon = '⏰'
                                desc = f"持倉 {MAX_HOLD_HOURS}h 超時出場"
                                note = ""

                            send_telegram(
                                f"{icon} *[V2] {desc}*: `{symbol}`\n"
                                f"損益: `{pnl:+.2f}%` {note}\n"
                                f"進場: `{pos['ep']:.4f}` → 出場: `{curr_c:.4f}`"
                            )
                            db_save_trade(symbol, side, pnl, won, result)
                            remove_position(symbol)
                        continue

                    # 訊號去重
                    base_key = f"{symbol}_{last_k_t}"
                    if is_signal_sent(f"long_{base_key}") or \
                       is_signal_sent(f"short_{base_key}"):
                        continue

                    result = analyze_symbol_v2(exchange, symbol)
                    if result is None: continue

                    side = result['side']
                    ok, reason = can_open_position(symbol, side)
                    if not ok:
                        log.info(f"[V2 Skip] {symbol} {side}: {reason}")
                        continue

                    sig_key = f"{side}_{base_key}"
                    if is_signal_sent(sig_key): continue

                    cat    = get_symbol_category(symbol)
                    emoji  = '🟢' if side == 'long' else '🔴'
                    side_t = '多單' if side == 'long' else '空單'

                    send_telegram(
                        f"{emoji} *[V2] {side_t} 發動*\n"
                        f"幣種: `{symbol}` [{cat}]\n"
                        f"價位: `{result['ep']:.4f}`\n"
                        f"🛡 止損: `{result['sl']:.4f}`\n"
                        f"🎯 止盈1（50%）: `{result['tp1']:.4f}`\n"
                        f"🏆 止盈2（50%）: `{result['tp2']:.4f}`\n"
                        f"{'─'*20}\n"
                        f"{result['labels']}"
                    )
                    record_signal(sig_key)
                    add_position(symbol, {
                        'side': side, 'ep': result['ep'],
                        'sl': result['sl'],
                        'tp1': result['tp1'], 'tp2': result['tp2'],
                        'tp1_hit': False,
                        'atr': result['atr'], 'entry_time': time.time(),
                        'category': cat,
                    })
                    log.info(
                        f"[V2] {side_t}開倉: {symbol} [{cat}] "
                        f"@ {result['ep']:.4f} "
                        f"SL={result['sl']:.4f} "
                        f"TP1={result['tp1']:.4f} "
                        f"TP2={result['tp2']:.4f}"
                    )

                except Exception as e:
                    log.warning(f"[V2 Monitor] {symbol}: {e}")
                    continue

            clean_signals()
            s       = db_load_weekly_stats()
            eff_max = WINRATE_REDUCED_MAX \
                      if s['total'] >= 10 and s['win_rate']/100 < WINRATE_THRESHOLD \
                      else MAX_POSITIONS
            wait    = wait_until_next_1h_close()
            next_dt = datetime.datetime.now(datetime.timezone.utc) + \
                      datetime.timedelta(seconds=wait)
            log.info(
                f"[V2] 掃描完成 持倉:{position_count()}/{eff_max} "
                f"週勝率:{s['win_rate']:.1f}% "
                f"下次掃描 UTC {next_dt.strftime('%H:%M')}（{wait/60:.0f}分後）"
            )
            time.sleep(wait)

        except Exception as e:
            log.error(f"[V2 Monitor] 嚴重錯誤: {e}")
            exchange = None
            time.sleep(60)


# ════════════════════════════════════════════
# 每日報告
# ════════════════════════════════════════════

def daily_report_task():
    last_sent_date = datetime.date.today() - datetime.timedelta(days=1)
    while True:
        try:
            now = datetime.datetime.now(datetime.timezone.utc)
            if now.date() > last_sent_date and now.hour == 0:
                pos_all = get_all_positions()
                s       = db_load_weekly_stats()
                eff_max = WINRATE_REDUCED_MAX \
                          if s['total']>=10 and s['win_rate']/100<WINRATE_THRESHOLD \
                          else MAX_POSITIONS
                pos_detail = '\n'.join([
                    f"  • `{sym}` {p['side']} @ {p['ep']:.4f} "
                    f"[{p.get('category','?')}] "
                    f"({'已第一批止盈' if p.get('tp1_hit') else '持倉中'}) "
                    f"({(time.time()-p.get('entry_time',time.time()))/3600:.1f}h)"
                    for sym, p in pos_all.items()
                ]) if pos_all else '  無'
                send_telegram(
                    f"📅 *[V2] 動量突破每日報告*\n"
                    f"⏰ UTC 00:00（台灣 08:00）\n{'─'*24}\n"
                    f"💼 持倉 ({len(pos_all)}/{eff_max}):\n{pos_detail}\n{'─'*24}\n"
                    f"本週: {s['total']} 筆 | 勝率 {s['win_rate']:.1f}% | "
                    f"平均 {s['avg_pnl']:+.2f}%"
                )
                last_sent_date = now.date()
        except Exception as e:
            log.error(f"[V2 DailyReport]: {e}")
        time.sleep(60)


# ════════════════════════════════════════════
# 每週報告
# ════════════════════════════════════════════

def weekly_report_task():
    last_sent_week = -1
    while True:
        try:
            now  = datetime.datetime.now(datetime.timezone.utc)
            week = now.isocalendar()[1]
            if now.weekday() == 0 and week != last_sent_week:
                s   = db_load_weekly_stats()
                eff = WINRATE_REDUCED_MAX \
                      if s['total']>=10 and s['win_rate']/100<WINRATE_THRESHOLD \
                      else MAX_POSITIONS
                status = '⚠️ 勝率未達標，已縮減倉位' if eff==WINRATE_REDUCED_MAX \
                         else '✅ 勝率正常，維持標準倉位'
                send_telegram(
                    f"📊 *[V2] 動量突破每週報告*\n{'─'*24}\n"
                    f"📈 總交易: {s['total']} 筆\n"
                    f"✅ 勝: {s['wins']} | ❌ 敗: {s['losses']}\n"
                    f"🎯 勝率: `{s['win_rate']:.1f}%`\n"
                    f"💰 平均損益: `{s['avg_pnl']:+.2f}%`\n"
                    f"🏆 最佳: `+{s['best']:.2f}%`\n"
                    f"💀 最差: `{s['worst']:.2f}%`\n"
                    f"🔴 最大連敗: {s['max_loss_streak']} 筆\n"
                    f"⚖️ 風報比: 1:{ATR_TP1_MULT/ATR_SL_MULT:.1f} "
                    f"/ 1:{ATR_TP2_MULT/ATR_SL_MULT:.1f}（分批）\n{'─'*24}\n"
                    f"{status}"
                )
                last_sent_week = week
        except Exception as e:
            log.error(f"[V2 WeeklyReport]: {e}")
        time.sleep(3600)


# ════════════════════════════════════════════
# Flask
# ════════════════════════════════════════════

@app.route('/')
def home():
    pos_all = get_all_positions()
    s       = db_load_weekly_stats()
    eff_max = WINRATE_REDUCED_MAX \
              if s['total']>=10 and s['win_rate']/100<WINRATE_THRESHOLD \
              else MAX_POSITIONS
    lines = [
        f"{sym}: {p['side']} @ {p['ep']:.4f} "
        f"[{p.get('category','?')}] "
        f"{'(已TP1)' if p.get('tp1_hit') else ''}"
        for sym, p in pos_all.items()
    ]
    return (
        f"動量突破 V2（分批止盈版）\n"
        f"持倉 {len(pos_all)}/{eff_max}\n"
        f"多:{long_count()} 空:{short_count()}\n\n"
        + ('\n'.join(lines) if lines else '無持倉')
        + f"\n\n本週: {s['total']}筆 | 勝率 {s['win_rate']:.1f}%"
    )


# ════════════════════════════════════════════
# 啟動
# ════════════════════════════════════════════

def start_radar():
    global threads_started
    with threads_lock:
        if not threads_started:
            init_db()

            recovered = db_load_positions()
            if recovered:
                with positions_lock:
                    active_positions.update(recovered)
                log.info(f"[DB] 恢復 {len(recovered)} 筆持倉")

            if WS_AVAILABLE:
                try:
                    ex   = get_exchange()
                    syms = get_top_symbols(ex)
                    for s in syms:
                        start_ws_cvd(s)
                        time.sleep(0.2)
                    log.info(f"[V2] 已啟動 {len(syms)} 幣種 WebSocket CVD")
                except Exception as e:
                    log.warning(f"WebSocket 預啟動失敗: {e}")

            week_s = db_load_weekly_stats()
            send_telegram(
                f"🚀 *動量突破 V2 上線（分批止盈＋週末保護版）*\n"
                f"策略: EMA趨勢 + 價量突破 + RSI動量\n{'─'*24}\n"
                f"✅ 時間框架: 1H K線\n"
                f"✅ 掃描節奏: 對齊 1H K線收盤\n"
                f"✅ CVD: {'WebSocket即時' if WS_AVAILABLE else 'REST模式'}\n"
                f"✅ 分批止盈: TP1={ATR_TP1_MULT}ATR(50%) / TP2={ATR_TP2_MULT}ATR(50%)\n"
                f"✅ 最低止損保護: {MIN_SL_PCT*100:.0f}%\n"
                f"✅ 持倉持久化: SQLite\n{'─'*24}\n"
                f"EMA: {EMA_FAST}/{EMA_MID}/{EMA_SLOW}\n"
                f"突破: 近{BREAKOUT_LOOKBACK}根 | 量能: {VOLUME_MULTIPLIER}x\n"
                f"RSI 多頭: {RSI_BULL_MIN}-{RSI_BULL_MAX} | "
                f"空頭: {RSI_BEAR_MIN}-{RSI_BEAR_MAX}\n"
                f"止損: {ATR_SL_MULT}ATR | 最長: {MAX_HOLD_HOURS}h\n{'─'*24}\n"
                f"恢復持倉: {len(active_positions)} 筆 | "
                f"本週已交易: {week_s['total']} 筆"
            )
            Thread(target=monitor,            daemon=True).start()
            Thread(target=daily_report_task,  daemon=True).start()
            Thread(target=weekly_report_task, daemon=True).start()
            threads_started = True
            log.info("[V2] 所有線程已啟動")


start_radar()

if __name__ == '__main__':
    port = int(os.environ.get('PORT', 8080))
    app.run(host='0.0.0.0', port=port, debug=False)

import os, time, ccxt.async_support as ccxt, requests, pandas as pd, pandas_ta as ta
import datetime, logging, numpy as np, json, sqlite3, asyncio, aiohttp
from flask import Flask, jsonify
from threading import Thread, Lock
from collections import OrderedDict, defaultdict
from dataclasses import dataclass, asdict
from typing import Optional, Dict, List, Tuple
import warnings
warnings.filterwarnings('ignore')

# WebSocket 導入
try:
    import websocket as ws_lib
    WS_AVAILABLE = True
except ImportError:
    WS_AVAILABLE = False
    print("websocket-client 未安裝，CVD 降級為 REST 模式")

# ==================== 配置日誌 ====================
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)
log = logging.getLogger(__name__)

app = Flask(__name__)

# ==================== 常數定義 ====================
# 技術指標參數
EMA_FAST_LENGTH = 20
EMA_MID_LENGTH = 50
EMA_SLOW_LENGTH = 200
RSI_LENGTH = 14
ATR_LENGTH = 14

# 突破參數
BREAKOUT_LOOKBACK = 20
VOLUME_MULTIPLIER = 2.0
VOL_LOOKBACK = 20

# RSI 門檻
RSI_BULL_MIN = 55
RSI_BULL_MAX = 72
RSI_BEAR_MIN = 28
RSI_BEAR_MAX = 45

# 風控參數
ATR_SL_MULT = 1.5
ATR_TP2_MULT = 3.0
MIN_SL_PCT = 0.03
MAX_SL_PCT = 0.12
MAX_HOLD_HOURS = 48

# 反轉K線參數
REVERSAL_SHADOW_RATIO = 2.0
REVERSAL_BODY_RATIO = 0.6
REVERSAL_DOJI_RATIO = 0.1

# 持倉限制
TOP_SYMBOLS = 40
MAX_POSITIONS = 10
MAX_LONG = 6
MAX_SHORT = 6
MAX_SIGNALS_MEMORY = 500
SIGNAL_EXPIRY_TIME = 86400

# 勝率門檻
WINRATE_THRESHOLD = 0.40
WINRATE_REDUCED_MAX = 5

# 時間框架
TIMEFRAME = '4h'

# 波動率過濾參數
BB_WIDTH_LOOKBACK = 100
BB_WIDTH_PERCENTILE = 20

# 風險管理參數
MAX_DAILY_LOSS_PERCENT = 5  # 每日最大虧損百分比
MAX_WEEKLY_LOSS_PERCENT = 10  # 每週最大虧損百分比
MAX_DRAWDOWN_PERCENT = 20  # 最大回撤百分比
RISK_PER_TRADE_PERCENT = 1.5  # 每筆交易風險百分比
MAX_POSITION_SIZE_PERCENT = 20  # 單幣種最大倉位百分比

# 相關性群組
CORRELATION_GROUPS = {
    'defi': ['UNI/USDT', 'AAVE/USDT', 'SUSHI/USDT', 'CRV/USDT'],
    'layer1': ['ETH/USDT', 'SOL/USDT', 'ADA/USDT', 'AVAX/USDT', 'DOT/USDT'],
    'meme': ['DOGE/USDT', 'SHIB/USDT', 'PEPE/USDT'],
    'exchange': ['BNB/USDT', 'OKB/USDT'],
    'oracle': ['LINK/USDT', 'BAND/USDT']
}

# 大市值幣種
LARGE_CAP = {'BTC/USDT', 'ETH/USDT', 'BNB/USDT', 'SOL/USDT'}
MID_CAP = {
    'XRP/USDT', 'ADA/USDT', 'AVAX/USDT', 'DOT/USDT', 'MATIC/USDT',
    'LINK/USDT', 'UNI/USDT', 'ATOM/USDT', 'LTC/USDT', 'ETC/USDT'
}

_STOCK_SYMBOLS = {
    'TSLA', 'AAPL', 'GOOGL', 'AMZN', 'MSFT', 'NVDA', 'META', 'BABA',
    'NFLX', 'COIN', 'MSTR', 'AMD', 'INTC', 'ORCL', 'PYPL', 'UBER',
}
_METAL_SYMBOLS = {'XAU', 'XAG', 'PAXG', 'XAUT'}

# ==================== 資料類別 ====================
@dataclass
class Position:
    """持倉資料結構"""
    symbol: str
    side: str
    ep: float
    sl: float
    tp1: float
    tp2: float
    size: float
    tp1_hit: bool = False
    atr: float = 0
    entry_time: float = 0
    category: str = ''
    
    def to_dict(self):
        return asdict(self)

@dataclass
class Signal:
    """信號資料結構"""
    symbol: str
    side: str
    ep: float
    sl: float
    tp1: float
    tp2: float
    size: float
    atr: float
    labels: str
    timestamp: float = 0

# ==================== 全局狀態 ====================
threads_started = False
threads_lock = Lock()
sent_signals = OrderedDict()
signals_lock = Lock()
active_positions: Dict[str, Position] = {}
positions_lock = Lock()
ws_cvd_buffer = defaultdict(lambda: {'buy': 0.0, 'sell': 0.0, 'ts': 0.0})
ws_cvd_lock = Lock()
ws_connections = {}
emergency_mode = False
DB_PATH = '/app/data/radar_v2_pro.db'

# ==================== 風險管理類別 ====================
class DrawdownProtector:
    """回撤保護器"""
    def __init__(self, max_drawdown_percent=MAX_DRAWDOWN_PERCENT):
        self.max_drawdown = max_drawdown_percent
        self.peak_equity = None
        self.current_drawdown = 0
        self.lock = Lock()
    
    def update_equity(self, current_equity):
        with self.lock:
            if self.peak_equity is None:
                self.peak_equity = current_equity
            elif current_equity > self.peak_equity:
                self.peak_equity = current_equity
            
            if self.peak_equity > 0:
                self.current_drawdown = (self.peak_equity - current_equity) / self.peak_equity * 100
    
    def should_stop(self):
        with self.lock:
            return self.current_drawdown >= self.max_drawdown
    
    def reset(self):
        with self.lock:
            self.peak_equity = None
            self.current_drawdown = 0

class ProfitManager:
    """損益管理器"""
    def __init__(self, max_daily_loss=MAX_DAILY_LOSS_PERCENT, max_weekly_loss=MAX_WEEKLY_LOSS_PERCENT):
        self.max_daily_loss = max_daily_loss
        self.max_weekly_loss = max_weekly_loss
        self.daily_pnl = 0.0
        self.weekly_pnl = 0.0
        self.last_day = None
        self.last_week = None
        self.initial_equity = None
        self.lock = Lock()
    
    def initialize(self, initial_equity):
        with self.lock:
            self.initial_equity = initial_equity
            self.daily_pnl = 0
            self.weekly_pnl = 0
            self.last_day = datetime.datetime.now().day
            self.last_week = datetime.datetime.now().isocalendar()[1]
    
    def update_pnl(self, pnl_percent):
        with self.lock:
            self.daily_pnl += pnl_percent
            self.weekly_pnl += pnl_percent
    
    def reset_daily(self):
        with self.lock:
            self.daily_pnl = 0
    
    def reset_weekly(self):
        with self.lock:
            self.weekly_pnl = 0
    
    def can_trade(self):
        with self.lock:
            now = datetime.datetime.now()
            
            # 重置每日損益
            if now.day != self.last_day:
                self.daily_pnl = 0
                self.last_day = now.day
            
            # 重置每週損益
            week = now.isocalendar()[1]
            if week != self.last_week:
                self.weekly_pnl = 0
                self.last_week = week
            
            return self.daily_pnl > -self.max_daily_loss and \
                   self.weekly_pnl > -self.max_weekly_loss
    
    def get_stats(self):
        with self.lock:
            return {
                'daily_pnl': self.daily_pnl,
                'weekly_pnl': self.weekly_pnl,
                'max_daily_loss': self.max_daily_loss,
                'max_weekly_loss': self.max_weekly_loss
            }

class RateLimiter:
    """API 限流器"""
    def __init__(self, max_calls=20, time_window=1):
        self.max_calls = max_calls
        self.time_window = time_window
        self.calls = []
        self.lock = Lock()
    
    async def acquire(self):
        with self.lock:
            now = time.time()
            self.calls = [t for t in self.calls if now - t < self.time_window]
            
            if len(self.calls) >= self.max_calls:
                wait_time = self.time_window - (now - self.calls[0])
                if wait_time > 0:
                    await asyncio.sleep(wait_time)
            
            self.calls.append(now)
            return True

class PerformanceMonitor:
    """效能監控器"""
    def __init__(self):
        self.metrics = defaultdict(list)
        self.lock = Lock()
    
    def record(self, metric, value):
        with self.lock:
            self.metrics[metric].append({
                'value': value,
                'time': time.time()
            })
            if len(self.metrics[metric]) > 1000:
                self.metrics[metric] = self.metrics[metric][-1000:]
    
    def get_stats(self, metric):
        with self.lock:
            values = [m['value'] for m in self.metrics[metric]]
            if not values:
                return {}
            return {
                'avg': np.mean(values),
                'max': np.max(values),
                'min': np.min(values),
                'p95': np.percentile(values, 95),
                'count': len(values)
            }
    
    def get_all_stats(self):
        with self.lock:
            return {metric: self.get_stats(metric) for metric in self.metrics}

# 全局實例
drawdown_protector = DrawdownProtector()
profit_manager = ProfitManager()
rate_limiter = RateLimiter(max_calls=20, time_window=1)
perf_monitor = PerformanceMonitor()

# ==================== 輔助函數 ====================
def is_crypto_symbol(symbol: str) -> bool:
    """判斷是否為加密貨幣（排除股票和金屬）"""
    base = symbol.split('/')[0]
    if base in _METAL_SYMBOLS: return False
    if base in _STOCK_SYMBOLS: return False
    return True

def get_symbol_category(symbol: str) -> str:
    """獲取幣種分類"""
    if symbol in LARGE_CAP:
        return 'large_cap'
    elif symbol in MID_CAP:
        return 'mid_cap'
    else:
        return 'small_cap'

def get_week_id() -> str:
    """獲取週標識"""
    now = datetime.datetime.now(datetime.timezone.utc)
    return f"{now.year}-W{now.isocalendar()[1]:02d}"

def calculate_total_equity(exchange=None) -> float:
    """計算總權益（帳戶餘額 + 未實現損益）"""
    try:
        # 這裡需要根據實際交易所 API 實現
        # 簡化版本，返回模擬值
        return 10000  # 預設初始資金
    except Exception as e:
        log.error(f"計算總權益失敗: {e}")
        return 0

# ==================== 資料庫操作 ====================
def init_db():
    """初始化資料庫"""
    os.makedirs(os.path.dirname(DB_PATH), exist_ok=True)
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute('''CREATE TABLE IF NOT EXISTS positions (
        symbol      TEXT PRIMARY KEY,
        side        TEXT,
        ep          REAL,
        sl          REAL,
        tp1         REAL,
        tp2         REAL,
        size        REAL,
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
        exit_type   TEXT,
        size        REAL
    )''')
    c.execute('''CREATE TABLE IF NOT EXISTS daily_stats (
        date        TEXT PRIMARY KEY,
        daily_pnl   REAL,
        trade_count INTEGER,
        win_count   INTEGER
    )''')
    conn.commit()
    conn.close()
    log.info("[DB] V2-Pro 持久化資料庫已初始化")

def db_save_position(symbol: str, pos: Position):
    """儲存持倉"""
    try:
        conn = sqlite3.connect(DB_PATH)
        conn.execute('''INSERT OR REPLACE INTO positions
            (symbol, side, ep, sl, tp1, tp2, size, tp1_hit, atr, entry_time, category)
            VALUES (?,?,?,?,?,?,?,?,?,?,?)''',
            (symbol, pos.side, pos.ep, pos.sl, pos.tp1, pos.tp2, pos.size,
             int(pos.tp1_hit), pos.atr, pos.entry_time, pos.category))
        conn.commit()
        conn.close()
    except Exception as e:
        log.warning(f"[DB] 儲存持倉失敗: {e}")

def db_update_position(symbol: str, updates: dict):
    """更新持倉"""
    try:
        conn = sqlite3.connect(DB_PATH)
        for key, val in updates.items():
            conn.execute(f'UPDATE positions SET {key}=? WHERE symbol=?', (val, symbol))
        conn.commit()
        conn.close()
    except Exception as e:
        log.warning(f"[DB] 更新持倉失敗: {e}")

def db_remove_position(symbol: str):
    """刪除持倉"""
    try:
        conn = sqlite3.connect(DB_PATH)
        conn.execute('DELETE FROM positions WHERE symbol=?', (symbol,))
        conn.commit()
        conn.close()
    except Exception as e:
        log.warning(f"[DB] 刪除持倉失敗: {e}")

def db_load_positions() -> Dict[str, Position]:
    """載入持倉"""
    try:
        conn = sqlite3.connect(DB_PATH)
        rows = conn.execute('SELECT * FROM positions').fetchall()
        conn.close()
        result = {}
        for r in rows:
            result[r[0]] = Position(
                symbol=r[0], side=r[1], ep=r[2], sl=r[3],
                tp1=r[4], tp2=r[5], size=r[6], tp1_hit=bool(r[7]),
                atr=r[8], entry_time=r[9], category=r[10]
            )
        return result
    except Exception as e:
        log.warning(f"[DB] 載入持倉失敗: {e}")
        return {}

def db_save_trade(symbol: str, side: str, pnl: float, won: bool, exit_type: str = '', size: float = 0):
    """儲存交易記錄"""
    try:
        conn = sqlite3.connect(DB_PATH)
        conn.execute('''INSERT INTO trades
            (symbol, side, pnl, won, trade_time, week_id, exit_type, size)
            VALUES (?,?,?,?,?,?,?,?)''',
            (symbol, side, pnl, int(won),
             datetime.datetime.now(datetime.timezone.utc).isoformat(),
             get_week_id(), exit_type, size))
        conn.commit()
        conn.close()
    except Exception as e:
        log.warning(f"[DB] 儲存交易失敗: {e}")

def _calc_stats(rows: list) -> dict:
    """計算統計數據"""
    trades = [{'pnl': r[0], 'won': bool(r[1])} for r in rows]
    total = len(trades)
    wins = sum(1 for t in trades if t['won'])
    pnls = [t['pnl'] for t in trades]
    wr = (wins / total * 100) if total > 0 else 0
    avg = (sum(pnls) / total) if total > 0 else 0
    streak = cur = 0
    for t in trades:
        cur = cur + 1 if not t['won'] else 0
        streak = max(streak, cur)
    return {
        'total': total, 'wins': wins, 'losses': total - wins,
        'win_rate': wr, 'avg_pnl': avg,
        'max_loss_streak': streak,
        'best': max(pnls) if pnls else 0,
        'worst': min(pnls) if pnls else 0,
    }

def db_load_weekly_stats(week_id: str = None) -> dict:
    """載入週統計"""
    try:
        wid = week_id or get_week_id()
        conn = sqlite3.connect(DB_PATH)
        rows = conn.execute('SELECT pnl, won FROM trades WHERE week_id=?', (wid,)).fetchall()
        conn.close()
        return _calc_stats(rows)
    except Exception as e:
        log.warning(f"[DB] 讀取週報失敗: {e}")
        return {'total': 0, 'wins': 0, 'losses': 0, 'win_rate': 0, 'avg_pnl': 0, 'max_loss_streak': 0, 'best': 0, 'worst': 0}

def db_load_recent_stats(days: int = 7) -> dict:
    """載入近期統計"""
    try:
        since = (datetime.datetime.now(datetime.timezone.utc) - datetime.timedelta(days=days)).isoformat()
        conn = sqlite3.connect(DB_PATH)
        rows = conn.execute('SELECT pnl, won FROM trades WHERE trade_time >= ?', (since,)).fetchall()
        conn.close()
        return _calc_stats(rows)
    except Exception as e:
        log.warning(f"[DB] 讀取近期統計失敗: {e}")
        return {'total': 0, 'wins': 0, 'losses': 0, 'win_rate': 0, 'avg_pnl': 0, 'max_loss_streak': 0, 'best': 0, 'worst': 0}

def db_load_all_stats() -> dict:
    """載入全部統計"""
    try:
        conn = sqlite3.connect(DB_PATH)
        rows = conn.execute('SELECT pnl, won FROM trades ORDER BY trade_time').fetchall()
        conn.close()
        if not rows:
            return {'total': 0, 'wins': 0, 'losses': 0, 'win_rate': 0, 'avg_pnl': 0, 'max_loss_streak': 0, 'best': 0, 'worst': 0, 'total_pnl': 0}
        base = _calc_stats(rows)
        base['total_pnl'] = sum(r[0] for r in rows)
        return base
    except Exception as e:
        log.warning(f"[DB] 讀取全部統計失敗: {e}")
        return {'total': 0, 'wins': 0, 'losses': 0, 'win_rate': 0, 'avg_pnl': 0, 'max_loss_streak': 0, 'best': 0, 'worst': 0, 'total_pnl': 0}

# ==================== 持倉管理 ====================
def position_count() -> int:
    """獲取持倉數量"""
    with positions_lock:
        return len(active_positions)

def long_count() -> int:
    """獲取多單數量"""
    with positions_lock:
        return sum(1 for p in active_positions.values() if p.side == 'long')

def short_count() -> int:
    """獲取空單數量"""
    with positions_lock:
        return sum(1 for p in active_positions.values() if p.side == 'short')

def category_count(cat: str) -> int:
    """獲取分類持倉數量"""
    with positions_lock:
        return sum(1 for p in active_positions.values() if p.category == cat)

def has_position(symbol: str) -> bool:
    """檢查是否持有"""
    with positions_lock:
        return symbol in active_positions

def get_position(symbol: str) -> Optional[Position]:
    """獲取持倉"""
    with positions_lock:
        return active_positions.get(symbol)

def add_position(symbol: str, pos: Position):
    """添加持倉"""
    with positions_lock:
        active_positions[symbol] = pos
        db_save_position(symbol, pos)

def update_position(symbol: str, updates: dict):
    """更新持倉"""
    with positions_lock:
        if symbol in active_positions:
            for key, val in updates.items():
                setattr(active_positions[symbol], key, val)
            db_update_position(symbol, updates)

def remove_position(symbol: str):
    """移除持倉"""
    with positions_lock:
        active_positions.pop(symbol, None)
        db_remove_position(symbol)

def get_all_positions() -> Dict[str, Position]:
    """獲取所有持倉"""
    with positions_lock:
        return dict(active_positions)

def can_open_position(symbol: str, side: str) -> Tuple[bool, str]:
    """檢查是否可以開倉"""
    # 緊急模式檢查
    if emergency_mode:
        return False, "緊急模式已啟動，暫停開倉"
    
    # 全局風險檢查
    if not profit_manager.can_trade():
        stats = profit_manager.get_stats()
        return False, f"每日/每週虧損限制已達標 (日:{stats['daily_pnl']:.1f}%, 週:{stats['weekly_pnl']:.1f}%)"
    
    if drawdown_protector.should_stop():
        return False, f"最大回撤已達標 ({drawdown_protector.current_drawdown:.1f}%)"
    
    # 持倉數量檢查
    s = db_load_recent_stats(days=30)
    wr = s['win_rate'] / 100 if s['total'] >= 10 else 1.0
    eff_max = WINRATE_REDUCED_MAX if wr < WINRATE_THRESHOLD and s['total'] >= 10 else MAX_POSITIONS
    
    if position_count() >= eff_max:
        return False, f"總倉位已達上限 {eff_max}"
    if side == 'long' and long_count() >= MAX_LONG:
        return False, f"多單上限 {MAX_LONG}"
    if side == 'short' and short_count() >= MAX_SHORT:
        return False, f"空單上限 {MAX_SHORT}"
    
    # 相關性檢查
    if not check_correlation_filter(symbol, get_all_positions()):
        return False, "同組相關性過高"
    
    return True, ''

def check_correlation_filter(symbol: str, positions: Dict[str, Position]) -> bool:
    """檢查相關性過濾"""
    for group, tokens in CORRELATION_GROUPS.items():
        if symbol in tokens:
            group_count = sum(1 for s in positions.keys() if s in tokens)
            if group_count >= 2:
                return False
    return True

# ==================== 訊號管理 ====================
def is_signal_sent(key: str) -> bool:
    """檢查信號是否已發送"""
    with signals_lock:
        return key in sent_signals

def record_signal(key: str):
    """記錄信號"""
    with signals_lock:
        sent_signals[key] = time.time()

def clean_signals():
    """清理過期信號"""
    now = time.time()
    with signals_lock:
        for k in [k for k, v in sent_signals.items() if now - v > SIGNAL_EXPIRY_TIME]:
            del sent_signals[k]
        while len(sent_signals) > MAX_SIGNALS_MEMORY:
            sent_signals.popitem(last=False)

# ==================== 市場狀態判斷 ====================
async def check_market_regime(exchange, symbol: str = 'BTC/USDT') -> str:
    """判斷市場狀態（趨勢/震盪）"""
    try:
        df = await fetch_ohlcv_df_async(exchange, symbol, '4h', 100)
        if df is None:
            return 'unknown'
        
        # ADX 判斷趨勢強度
        adx = ta.adx(df['h'], df['l'], df['c'], length=14)
        adx_value = adx.iloc[-1]
        
        # 多時間框架 EMA
        ema_20 = ta.ema(df['c'], length=20).iloc[-1]
        ema_50 = ta.ema(df['c'], length=50).iloc[-1]
        
        if adx_value > 25 and ema_20 > ema_50:
            return 'trend_up'
        elif adx_value > 25 and ema_20 < ema_50:
            return 'trend_down'
        else:
            return 'ranging'
    except Exception as e:
        log.error(f"市場狀態判斷失敗: {e}")
        return 'unknown'

async def multi_timeframe_confirmation(exchange, symbol: str) -> str:
    """多時間框架確認"""
    timeframes = ['1h', '4h', '1d']
    signals = []
    
    for tf in timeframes:
        df = await fetch_ohlcv_df_async(exchange, symbol, tf, 100)
        if df is None:
            continue
        
        ema_fast = ta.ema(df['c'], length=20).iloc[-1]
        ema_slow = ta.ema(df['c'], length=50).iloc[-1]
        trend = 'bull' if ema_fast > ema_slow else 'bear'
        signals.append(trend)
    
    if signals.count('bull') >= 2:
        return 'bull'
    elif signals.count('bear') >= 2:
        return 'bear'
    return 'neutral'

async def adaptive_parameters(exchange, symbol: str) -> dict:
    """根據當前波動率調整策略參數"""
    df = await fetch_ohlcv_df_async(exchange, symbol, TIMEFRAME, 50)
    if df is None:
        return {}
    
    atr = ta.atr(df['h'], df['l'], df['c'], length=14)
    atr_pct = atr / df['c'] * 100
    current_atr_pct = atr_pct.iloc[-1]
    atr_percentile = (atr_pct < current_atr_pct).sum() / len(atr_pct)
    
    params = {}
    if atr_percentile > 0.7:  # 高波動
        params.update({
            'MIN_SL_PCT': 0.05,
            'MAX_SL_PCT': 0.15,
            'ATR_SL_MULT': 2.0,
            'VOLUME_MULTIPLIER': 1.5,
            'RSI_BULL_MIN': 50,
            'RSI_BEAR_MAX': 40
        })
    elif atr_percentile < 0.3:  # 低波動
        params.update({
            'MIN_SL_PCT': 0.02,
            'MAX_SL_PCT': 0.08,
            'ATR_SL_MULT': 1.2,
            'VOLUME_MULTIPLIER': 2.5,
            'RSI_BULL_MIN': 60,
            'RSI_BEAR_MAX': 35
        })
    else:  # 正常波動
        params.update({
            'MIN_SL_PCT': MIN_SL_PCT,
            'MAX_SL_PCT': MAX_SL_PCT,
            'ATR_SL_MULT': ATR_SL_MULT,
            'VOLUME_MULTIPLIER': VOLUME_MULTIPLIER,
            'RSI_BULL_MIN': RSI_BULL_MIN,
            'RSI_BEAR_MAX': RSI_BEAR_MAX
        })
    
    return params

# ==================== 倉位計算 ====================
async def calculate_position_size(exchange, symbol: str, side: str, sl_pct: float) -> float:
    """根據ATR和帳戶風險計算倉位大小"""
    try:
        balance = await exchange.fetch_balance()
        usdt_balance = balance['USDT']['free']
        
        risk_percent = RISK_PER_TRADE_PERCENT / 100
        
        # 根據波動率調整風險
        df = await fetch_ohlcv_df_async(exchange, symbol, TIMEFRAME, 50)
        if df is not None:
            atr = ta.atr(df['h'], df['l'], df['c'], length=14).iloc[-1]
            price = df['c'].iloc[-1]
            atr_pct = atr / price
            
            if atr_pct > 0.05:
                risk_percent *= 0.5
            elif atr_pct < 0.02:
                risk_percent *= 1.2
        
        # 計算倉位
        risk_amount = usdt_balance * risk_percent
        position_size = risk_amount / (sl_pct * price) if sl_pct > 0 else 0
        
        # 限制最大倉位
        max_size = usdt_balance * (MAX_POSITION_SIZE_PERCENT / 100)
        position_size = min(position_size, max_size)
        
        # 最小倉位檢查
        min_size = 10  # 最小 10 USDT
        if position_size < min_size:
            return 0
        
        return position_size
    except Exception as e:
        log.error(f"計算倉位失敗: {e}")
        return 0

# ==================== WebSocket CVD ====================
def _ws_on_message(symbol_key: str, msg: str):
    """WebSocket 消息處理"""
    try:
        data = json.loads(msg)
        qty = float(data.get('q', 0))
        is_buyer_maker = data.get('m', False)
        
        with ws_cvd_lock:
            if is_buyer_maker:
                ws_cvd_buffer[symbol_key]['sell'] += qty
            else:
                ws_cvd_buffer[symbol_key]['buy'] += qty
            ws_cvd_buffer[symbol_key]['ts'] = time.time()
            
            # 限制緩衝區大小
            if ws_cvd_buffer[symbol_key]['buy'] > 1e10:
                ws_cvd_buffer[symbol_key]['buy'] /= 2
                ws_cvd_buffer[symbol_key]['sell'] /= 2
    except Exception as e:
        log.debug(f"WS 訊息處理錯誤: {e}")

def start_ws_cvd(symbol: str):
    """啟動 WebSocket CVD"""
    if not WS_AVAILABLE:
        return
    
    symbol_key = symbol.split('/')[0].lower() + 'usdt'
    if symbol_key in ws_connections:
        return
    
    def run():
        url = f"wss://fstream.binance.com/ws/{symbol_key}@aggTrade"
        
        def on_msg(ws, msg):
            _ws_on_message(symbol_key, msg)
        
        def on_err(ws, err):
            log.warning(f"[WS] {symbol_key} 錯誤: {err}")
        
        def on_close(ws, *a):
            log.info(f"[WS] {symbol_key} 連線關閉，5s 後重連")
            ws_connections.pop(symbol_key, None)
            time.sleep(5)
            start_ws_cvd(symbol)
        
        def on_open(ws):
            log.info(f"[WS] {symbol_key} 串流已連線")
            with ws_cvd_lock:
                ws_cvd_buffer[symbol_key] = {'buy': 0.0, 'sell': 0.0, 'ts': time.time()}
        
        w = ws_lib.WebSocketApp(url, on_message=on_msg, on_error=on_err, on_close=on_close, on_open=on_open)
        ws_connections[symbol_key] = True
        w.run_forever(ping_interval=30, ping_timeout=10)
    
    Thread(target=run, daemon=True).start()

async def get_cvd_bias_async(exchange, symbol: str) -> str:
    """獲取 CVD 偏離"""
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
        if ratio >= 0.55:
            return 'bull'
        if ratio <= 0.45:
            return 'bear'
        return 'neutral'
    else:
        try:
            trades = await exchange.fetch_trades(symbol, limit=500)
            if not trades:
                return 'neutral'
            df_t = pd.DataFrame([{'amount': t['amount'], 'side': t['side']} for t in trades])
            buy_vol = df_t[df_t['side'] == 'buy']['amount'].sum()
            total = df_t['amount'].sum()
            ratio = buy_vol / total if total > 0 else 0.5
            if ratio >= 0.55:
                return 'bull'
            if ratio <= 0.45:
                return 'bear'
            return 'neutral'
        except Exception:
            return 'neutral'

# ==================== 核心分析函數 ====================
async def fetch_ohlcv_df_async(exchange, symbol: str, timeframe: str, limit: int):
    """獲取 OHLCV 數據"""
    await rate_limiter.acquire()
    try:
        ohlcv = await exchange.fetch_ohlcv(symbol, timeframe, limit=limit)
        if not ohlcv:
            return None
        df = pd.DataFrame(ohlcv, columns=['t', 'o', 'h', 'l', 'c', 'v'])
        df['t'] = pd.to_datetime(df['t'], unit='ms')
        return df.astype({col: float for col in ['o', 'h', 'l', 'c', 'v']})
    except Exception as e:
        log.error(f"獲取 {symbol} OHLCV 失敗: {e}")
        return None

async def analyze_symbol_v2_pro(exchange, symbol: str) -> Optional[Signal]:
    """核心分析：動量突破型 V2-Pro"""
    start_time = time.time()
    
    try:
        df = await fetch_ohlcv_df_async(exchange, symbol, TIMEFRAME, 250)
        if df is None or len(df) < 200:
            return None
        
        c, h, l, o, v = df['c'], df['h'], df['l'], df['o'], df['v']
        curr_c = float(c.iloc[-1])
        curr_h = float(h.iloc[-1])
        curr_l = float(l.iloc[-1])
        curr_o = float(o.iloc[-1])
        curr_v = float(v.iloc[-1])
        
        # 市場狀態檢查
        market_regime = await check_market_regime(exchange, symbol)
        if market_regime == 'ranging':
            return None
        
        # 多時間框架確認
        mtf_signal = await multi_timeframe_confirmation(exchange, symbol)
        
        # 動態參數
        dynamic_params = await adaptive_parameters(exchange, symbol)
        min_sl_pct = dynamic_params.get('MIN_SL_PCT', MIN_SL_PCT)
        max_sl_pct = dynamic_params.get('MAX_SL_PCT', MAX_SL_PCT)
        atr_sl_mult = dynamic_params.get('ATR_SL_MULT', ATR_SL_MULT)
        vol_mult = dynamic_params.get('VOLUME_MULTIPLIER', VOLUME_MULTIPLIER)
        rsi_bull_min = dynamic_params.get('RSI_BULL_MIN', RSI_BULL_MIN)
        rsi_bear_max = dynamic_params.get('RSI_BEAR_MAX', RSI_BEAR_MAX)
        
        # 指標計算
        ema_fast = ta.ema(c, length=EMA_FAST_LENGTH).iloc[-1]
        ema_mid = ta.ema(c, length=EMA_MID_LENGTH).iloc[-1]
        ema_slow = ta.ema(c, length=EMA_SLOW_LENGTH).iloc[-1]
        rsi = ta.rsi(c, length=RSI_LENGTH).iloc[-1]
        atr = ta.atr(h, l, c, length=ATR_LENGTH).iloc[-1]
        
        # 波動率過濾 - BB Width
        bb = ta.bbands(c, length=20, std=2.0)
        bb_width = (bb[f'BBU_20_2.0'].iloc[-1] - bb[f'BBL_20_2.0'].iloc[-1]) / bb[f'BBM_20_2.0'].iloc[-1]
        bb_width_history = (bb[f'BBU_20_2.0'] - bb[f'BBL_20_2.0']) / bb[f'BBM_20_2.0']
        if bb_width < bb_width_history.quantile(BB_WIDTH_PERCENTILE / 100):
            return None
        
        # 成交量確認
        avg_vol = float(v.iloc[-VOL_LOOKBACK-1:-1].mean())
        
        # 突破條件
        recent_high = df['h'].iloc[-BREAKOUT_LOOKBACK-1:-1].max()
        recent_low = df['l'].iloc[-BREAKOUT_LOOKBACK-1:-1].min()
        
        side = None
        reason = ""
        
        # 多頭突破
        if curr_c > recent_high and curr_v >= avg_vol * vol_mult:
            if ema_fast > ema_mid > ema_slow and mtf_signal != 'bear':
                if rsi > rsi_bull_min:
                    # RSI 背離檢查
                    prev_high_idx = df[df['h'] == recent_high].index[-1] if len(df[df['h'] == recent_high]) > 0 else -1
                    if prev_high_idx > 0:
                        prev_rsi_at_high = ta.rsi(df['c'].loc[:prev_high_idx], length=RSI_LENGTH).iloc[-1]
                        if curr_c > recent_high and rsi < prev_rsi_at_high:
                            return None
                    side, reason = 'long', '多頭突破'
        
        # 空頭突破
        elif curr_c < recent_low and curr_v >= avg_vol * vol_mult:
            if ema_fast < ema_mid < ema_slow and mtf_signal != 'bull':
                if rsi < rsi_bear_max:
                    # RSI 背離檢查
                    prev_low_idx = df[df['l'] == recent_low].index[-1] if len(df[df['l'] == recent_low]) > 0 else -1
                    if prev_low_idx > 0:
                        prev_rsi_at_low = ta.rsi(df['c'].loc[:prev_low_idx], length=RSI_LENGTH).iloc[-1]
                        if curr_c < recent_low and rsi > prev_rsi_at_low:
                            return None
                    side, reason = 'short', '空頭突破'
        
        if not side:
            return None
        
        # CVD 驗證
        cvd_bias = await get_cvd_bias_async(exchange, symbol)
        if (side == 'long' and cvd_bias == 'bear') or (side == 'short' and cvd_bias == 'bull'):
            return None
        
        # 計算止損
        sl_struct = recent_low if side == 'long' else recent_high
        dynamic_sl_buffer = 0.5 * atr
        sl = sl_struct - dynamic_sl_buffer if side == 'long' else sl_struct + dynamic_sl_buffer
        
        # 確保止損在合理範圍
        sl_pct = abs(curr_c - sl) / curr_c
        if sl_pct < min_sl_pct:
            sl = curr_c * (1 - min_sl_pct) if side == 'long' else curr_c * (1 + min_sl_pct)
        elif sl_pct > max_sl_pct:
            sl = curr_c * (1 - max_sl_pct) if side == 'long' else curr_c * (1 + max_sl_pct)
        
        # 計算止盈
        sl_dist = abs(curr_c - sl)
        if side == 'long':
            tp1 = curr_c + sl_dist * atr_sl_mult
            tp2 = curr_c + sl_dist * ATR_TP2_MULT
        else:
            tp1 = curr_c - sl_dist * atr_sl_mult
            tp2 = curr_c - sl_dist * ATR_TP2_MULT
        
        if tp1 <= 0 or tp2 <= 0:
            return None
        
        # 計算倉位大小
        final_sl_pct = abs(curr_c - sl) / curr_c
        position_size = await calculate_position_size(exchange, symbol, side, final_sl_pct)
        if position_size <= 0:
            return None
        
        labels = f"🚀 動量突破 ({reason})\n📊 EMA: {ema_fast:.4f}/{ema_mid:.4f}/{ema_slow:.4f}\n📈 RSI: {rsi:.1f} | 量能: {curr_v/avg_vol:.1f}x\n💹 CVD: {cvd_bias}\n📊 市場: {market_regime}"
        
        perf_monitor.record('analyze_time', time.time() - start_time)
        
        return Signal(
            symbol=symbol, side=side, ep=curr_c, sl=sl, tp1=tp1, tp2=tp2,
            size=position_size, atr=atr, labels=labels, timestamp=time.time()
        )
    
    except Exception as e:
        log.debug(f"[V2-Pro] {symbol}: {e}")
        return None

# ==================== 監控邏輯 ====================
async def monitor_async():
    """主監控循環"""
    log.info("=== 動量突破 V2-Pro 監控啟動 ===")
    exchange = None
    max_retries = 3
    retry_count = 0
    
    while True:
        try:
            if exchange is None:
                exchange = await get_exchange_async()
            
            markets = await exchange.load_markets()
            symbols = [s for s in markets
                      if '/USDT' in s and markets[s]['linear']
                      and is_crypto_symbol(s)][:TOP_SYMBOLS]
            
            semaphore = asyncio.Semaphore(5)
            
            async def process(symbol):
                async with semaphore:
                    try:
                        pos = get_position(symbol)
                        df_now = await fetch_ohlcv_df_async(exchange, symbol, TIMEFRAME, 3)
                        if df_now is None:
                            return
                        
                        curr_c = float(df_now['c'].iloc[-1])
                        curr_h = float(df_now['h'].iloc[-1])
                        curr_l = float(df_now['l'].iloc[-1])
                        
                        if pos:
                            # 止損判斷（使用最高最低價）
                            sl_triggered = ((pos.side == 'long' and curr_l <= pos.sl) or
                                          (pos.side == 'short' and curr_h >= pos.sl))
                            exit_reason = None
                            exit_c = pos.sl if sl_triggered else curr_c
                            
                            if sl_triggered:
                                exit_reason = "止損"
                            elif (pos.side == 'long' and curr_c >= pos.tp2) or \
                                 (pos.side == 'short' and curr_c <= pos.tp2):
                                exit_reason = "止盈2"
                            elif not pos.tp1_hit and (
                                (pos.side == 'long' and curr_c >= pos.tp1) or
                                (pos.side == 'short' and curr_c <= pos.tp1)
                            ):
                                update_position(pos.symbol, {'tp1_hit': True, 'sl': pos.ep})
                                send_telegram(
                                    f"✅ *V2-Pro {pos.symbol} 第一批止盈*\n"
                                    f"進場: {pos.ep:.4f} → 現價: {curr_c:.4f}\n"
                                    f"🛡 止損已移至保本價"
                                )
                            
                            # 超時出場
                            if not exit_reason and (time.time() - pos.entry_time) / 3600 >= MAX_HOLD_HOURS:
                                exit_reason = "超時"
                                exit_c = curr_c
                            
                            if exit_reason:
                                pnl = (exit_c / pos.ep - 1) * 100 if pos.side == 'long' else (pos.ep / exit_c - 1) * 100
                                send_telegram(
                                    f"🏁 *V2-Pro {pos.symbol} 出場 ({exit_reason})*\n"
                                    f"損益: `{pnl:+.2f}%`\n"
                                    f"進場: `{pos.ep:.4f}` → 出場: `{exit_c:.4f}`"
                                )
                                db_save_trade(pos.symbol, pos.side, pnl, pnl > 0, exit_reason, pos.size)
                                profit_manager.update_pnl(pnl)
                                remove_position(pos.symbol)
                            return
                        
                        # 分析新信號
                        res = await analyze_symbol_v2_pro(exchange, symbol)
                        if res:
                            ok, msg = can_open_position(symbol, res.side)
                            if ok:
                                pos = Position(
                                    symbol=res.symbol, side=res.side, ep=res.ep,
                                    sl=res.sl, tp1=res.tp1, tp2=res.tp2,
                                    size=res.size, atr=res.atr, entry_time=time.time(),
                                    category=get_symbol_category(symbol)
                                )
                                add_position(symbol, pos)
                                side_t = '多' if res.side == 'long' else '空'
                                send_telegram(
                                    f"🟢 *[V2-Pro] {side_t}單 發動*\n"
                                    f"幣種: `{symbol}`\n"
                                    f"價位: {res.ep:.4f}\n"
                                    f"倉位: {res.size:.2f} USDT\n"
                                    f"🛡 止損: {res.sl:.4f}\n"
                                    f"🎯 止盈1（50%）: {res.tp1:.4f}\n"
                                    f"🏆 止盈2（50%）: {res.tp2:.4f}\n"
                                    f"{'─'*20}\n"
                                    f"{res.labels}"
                                )
                    
                    except Exception as e:
                        log.debug(f"[V2-Pro] {symbol}: {e}")
            
            await asyncio.gather(*[process(s) for s in symbols])
            
            # 更新權益
            total_equity = calculate_total_equity()
            drawdown_protector.update_equity(total_equity)
            
            # 對齊 4H 收盤
            now = datetime.datetime.now(datetime.timezone.utc)
            next_4h = ((now.hour // 4) + 1) * 4
            if next_4h >= 24:
                next_dt = (now + datetime.timedelta(days=1)).replace(hour=0, minute=2, second=0, microsecond=0)
            else:
                next_dt = now.replace(hour=next_4h, minute=2, second=0, microsecond=0)
            wait = max((next_dt - now).total_seconds(), 60)
            
            s_stat = db_load_recent_stats(days=30)
            log.info(
                f"[V2-Pro] 掃描完成 持倉:{position_count()}/{MAX_POSITIONS} "
                f"近30天勝率:{s_stat['win_rate']:.1f}% "
                f"下次掃描 UTC {next_dt.strftime('%H:%M')}（{wait/60:.0f}分後）"
            )
            
            retry_count = 0
            await asyncio.sleep(wait)
        
        except Exception as e:
            log.error(f"[V2-Pro Monitor] 嚴重錯誤: {e}")
            retry_count += 1
            wait_time = min(60 * retry_count, 300)
            log.info(f"等待 {wait_time} 秒後重試...")
            await asyncio.sleep(wait_time)
            
            if retry_count >= max_retries:
                send_telegram(f"⚠️ V2-Pro 監控重試 {max_retries} 次失敗，請檢查系統")
                retry_count = 0
            
            # 重新創建交易所實例
            try:
                if exchange:
                    await exchange.close()
            except:
                pass
            exchange = None

# ==================== 報告任務 ====================
async def daily_report_task_async():
    """每日報告任務"""
    last_sent_date = datetime.date.today() - datetime.timedelta(days=1)
    log.info("[V2-Pro DailyReport] 線程已啟動")
    
    while True:
        try:
            now = datetime.datetime.now(datetime.timezone.utc)
            if now.date() > last_sent_date:
                log.info(f"[V2-Pro DailyReport] 開始發送 {now.date()}")
                pos_all = get_all_positions()
                s = db_load_recent_stats(days=7)
                all_s = db_load_all_stats()
                profit_stats = profit_manager.get_stats()
                
                pos_detail = '\n'.join([
                    f"  • `{sym}` {p.side} @ {p.ep:.4f} "
                    f"({'已TP1' if p.tp1_hit else '持倉中'}) "
                    f"({(time.time()-p.entry_time)/3600:.1f}h)"
                    for sym, p in pos_all.items()
                ]) if pos_all else '  無'
                
                send_telegram(
                    f"📅 *[V2-Pro] 動量突破每日報告*\n"
                    f"⏰ UTC 00:00（台灣 08:00）\n{'─'*24}\n"
                    f"💼 持倉 ({len(pos_all)}/{MAX_POSITIONS}):\n{pos_detail}\n{'─'*24}\n"
                    f"近7天: {s['total']} 筆 | 勝率 {s['win_rate']:.1f}% | "
                    f"平均 {s['avg_pnl']:+.2f}%\n"
                    f"📊 累計: {all_s['total']} 筆 | 勝率 {all_s['win_rate']:.1f}% | "
                    f"總損益 {all_s['total_pnl']:+.2f}%\n"
                    f"📈 今日損益: {profit_stats['daily_pnl']:+.2f}% | "
                    f"本週損益: {profit_stats['weekly_pnl']:+.2f}%\n"
                    f"🔴 最大連敗: {all_s['max_loss_streak']}"
                )
                last_sent_date = now.date()
        
        except Exception as e:
            log.error(f"[V2-Pro DailyReport]: {e}")
            send_telegram(f"⚠️ *V2-Pro 每日報告發送失敗*\n錯誤: {e}")
        
        await asyncio.sleep(60)

async def weekly_report_task_async():
    """每週報告任務"""
    last_sent_week = -1
    while True:
        try:
            now = datetime.datetime.now(datetime.timezone.utc)
            week = now.isocalendar()[1]
            if week != last_sent_week:
                last_week = now - datetime.timedelta(days=7)
                last_week_id = f"{last_week.year}-W{last_week.isocalendar()[1]:02d}"
                s = db_load_weekly_stats(week_id=last_week_id)
                profit_stats = profit_manager.get_stats()
                
                send_telegram(
                    f"📊 *[V2-Pro] 動量突破週報*\n"
                    f"📅 {last_week_id}\n{'─'*24}\n"
                    f"📈 總交易: {s['total']} 筆\n"
                    f"✅ 勝: {s['wins']} | ❌ 敗: {s['losses']}\n"
                    f"🎯 勝率: `{s['win_rate']:.1f}%`\n"
                    f"💰 平均損益: `{s['avg_pnl']:+.2f}%`\n"
                    f"📊 本週損益: `{profit_stats['weekly_pnl']:+.2f}%`\n"
                    f"🏆 最佳: `+{s['best']:.2f}%`\n"
                    f"💀 最差: `{s['worst']:.2f}%`\n"
                    f"🔴 最大連敗: {s['max_loss_streak']} 筆"
                )
                last_sent_week = week
        
        except Exception as e:
            log.error(f"[V2-Pro WeeklyReport]: {e}")
            send_telegram(f"⚠️ *V2-Pro 週報發送失敗*\n錯誤: {e}")
        
        await asyncio.sleep(1800)

async def monthly_report_task_async():
    """每月報告任務"""
    last_sent_month = -1
    while True:
        try:
            now = datetime.datetime.now(datetime.timezone.utc)
            if now.month != last_sent_month:
                last_month = now.month - 1 if now.month > 1 else 12
                last_month_year = now.year if now.month > 1 else now.year - 1
                s = db_load_monthly_stats(last_month_year, last_month)
                
                send_telegram(
                    f"🗓 *[V2-Pro] 動量突破月報*\n"
                    f"📅 {last_month_year}-{last_month:02d}\n{'─'*24}\n"
                    f"📈 總交易: {s['total']} 筆\n"
                    f"🎯 勝率: `{s['win_rate']:.1f}%`\n"
                    f"💰 平均損益: `{s['avg_pnl']:+.2f}%`\n"
                    f"🏆 最佳: `+{s['best']:.2f}%`\n"
                    f"💀 最差: `{s['worst']:.2f}%`\n"
                    f"🔴 最大連敗: {s['max_loss_streak']} 筆"
                )
                last_sent_month = now.month
        
        except Exception as e:
            log.error(f"[V2-Pro MonthlyReport]: {e}")
            send_telegram(f"⚠️ *V2-Pro 月報發送失敗*\n錯誤: {e}")
        
        await asyncio.sleep(1800)

def db_load_monthly_stats(year: int, month: int) -> dict:
    """載入月統計"""
    import calendar
    try:
        last_day = calendar.monthrange(year, month)[1]
        date_from = f"{year}-{month:02d}-01"
        date_to = f"{year}-{month:02d}-{last_day:02d}T23:59:59"
        conn = sqlite3.connect(DB_PATH)
        rows = conn.execute(
            'SELECT pnl, won FROM trades WHERE trade_time >= ? AND trade_time <= ?',
            (date_from, date_to)
        ).fetchall()
        conn.close()
        return _calc_stats(rows)
    except Exception as e:
        log.warning(f"[DB] 讀取月報失敗: {e}")
        return {'total': 0, 'wins': 0, 'losses': 0, 'win_rate': 0, 'avg_pnl': 0, 'max_loss_streak': 0, 'best': 0, 'worst': 0}

# ==================== 交易所初始化 ====================
async def get_exchange_async():
    """獲取交易所實例"""
    return ccxt.binance({
        'apiKey': os.environ.get('BINANCE_API_KEY'),
        'secret': os.environ.get('BINANCE_SECRET'),
        'options': {'defaultType': 'future'},
        'enableRateLimit': True,
        'rateLimit': 50,
    })

# ==================== Telegram 通知 ====================
def send_telegram(msg: str):
    """發送 Telegram 通知"""
    token = os.environ.get('TELEGRAM_TOKEN')
    chat_id = os.environ.get('TELEGRAM_CHAT_ID')
    if token and chat_id:
        try:
            requests.get(
                f"https://api.telegram.org/bot{token}/sendMessage",
                params={'chat_id': chat_id, 'text': msg, 'parse_mode': 'Markdown'},
                timeout=10
            )
        except Exception as e:
            log.error(f"Telegram 發送失敗: {e}")

# ==================== Flask 路由 ====================
@app.route('/')
def home():
    """主頁"""
    pos_all = get_all_positions()
    s = db_load_recent_stats(days=30)
    profit_stats = profit_manager.get_stats()
    perf_stats = perf_monitor.get_all_stats()
    
    lines = [
        f"{sym}: {p.side} @ {p.ep:.4f} "
        f"[{p.category}] "
        f"{'(已TP1)' if p.tp1_hit else ''} "
        f"(盈虧: {((p.tp1/p.ep-1)*100 if p.side=='long' else (p.ep/p.tp1-1)*100):+.1f}%)"
        for sym, p in pos_all.items()
    ]
    
    return (
        f"🚀 動量突破 V2-Pro（完整優化版）\n"
        f"{'='*40}\n"
        f"持倉 {len(pos_all)}/{MAX_POSITIONS}\n"
        + ('\n'.join(lines) if lines else '無持倉') +
        f"\n{'='*40}\n"
        f"📊 近30天: {s['total']}筆 | 勝率 {s['win_rate']:.1f}%\n"
        f"💰 今日損益: {profit_stats['daily_pnl']:+.2f}%\n"
        f"📈 本週損益: {profit_stats['weekly_pnl']:+.2f}%\n"
        f"🔴 最大回撤: {drawdown_protector.current_drawdown:.1f}%\n"
        f"{'='*40}\n"
        f"⚡ 效能: {perf_stats.get('analyze_time', {}).get('avg', 0)*1000:.1f}ms/次"
    )

@app.route('/health')
def health():
    """健康檢查端點"""
    return jsonify({
        'status': 'running' if not emergency_mode else 'emergency',
        'positions': position_count(),
        'max_positions': MAX_POSITIONS,
        'long_count': long_count(),
        'short_count': short_count(),
        'ws_connections': len(ws_connections),
        'signals_memory': len(sent_signals),
        'drawdown': drawdown_protector.current_drawdown,
        'daily_pnl': profit_manager.get_stats()['daily_pnl'],
        'weekly_pnl': profit_manager.get_stats()['weekly_pnl'],
        'emergency_mode': emergency_mode
    })

@app.route('/reset_trades')
def reset_trades():
    """重置交易記錄"""
    try:
        conn = sqlite3.connect(DB_PATH)
        count = conn.execute('SELECT COUNT(*) FROM trades').fetchone()[0]
        conn.execute('DELETE FROM trades')
        conn.commit()
        conn.close()
        send_telegram(f"🗑 *[V2-Pro] 交易記錄已清除*\n共刪除 {count} 筆")
        return f"已清除 {count} 筆交易記錄"
    except Exception as e:
        return f"清除失敗: {e}"

@app.route('/emergency_stop')
def emergency_stop():
    """緊急停止所有交易"""
    global emergency_mode
    
    try:
        emergency_mode = True
        
        # 平掉所有持倉
        positions = get_all_positions()
        for symbol, pos in positions.items():
            send_telegram(
                f"🚨 *緊急平倉: {symbol}*\n"
                f"方向: {pos.side}\n"
                f"進場價: {pos.ep:.4f}\n"
                f"倉位: {pos.size:.2f} USDT"
            )
            db_save_trade(symbol, pos.side, 0, False, 'emergency_stop', pos.size)
            remove_position(symbol)
        
        send_telegram(f"🚨 *緊急停止模式已啟動*\n已平倉 {len(positions)} 個持倉")
        return jsonify({'status': 'emergency_stop_activated', 'closed_positions': len(positions)})
    
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/emergency_resume')
def emergency_resume():
    """恢復正常交易"""
    global emergency_mode
    emergency_mode = False
    send_telegram("✅ *緊急停止模式已解除*，恢復正常交易")
    return jsonify({'status': 'resumed'})

@app.route('/stats')
def stats():
    """統計數據"""
    all_stats = db_load_all_stats()
    weekly_stats = db_load_weekly_stats()
    recent_stats = db_load_recent_stats(7)
    profit_stats = profit_manager.get_stats()
    perf_stats = perf_monitor.get_all_stats()
    
    return jsonify({
        'all_time': all_stats,
        'weekly': weekly_stats,
        'recent_7d': recent_stats,
        'risk_management': {
            'drawdown': drawdown_protector.current_drawdown,
            'max_drawdown': drawdown_protector.max_drawdown,
            'daily_pnl': profit_stats['daily_pnl'],
            'weekly_pnl': profit_stats['weekly_pnl'],
            'emergency_mode': emergency_mode
        },
        'performance': perf_stats,
        'positions': {
            symbol: {
                'side': p.side,
                'entry_price': p.ep,
                'size': p.size,
                'pnl_percent': ((p.tp1/p.ep-1)*100 if p.side=='long' else (p.ep/p.tp1-1)*100) if p.tp1_hit else 0
            }
            for symbol, p in get_all_positions().items()
        }
    })

@app.route('/reset_daily_pnl')
def reset_daily_pnl():
    """重置每日損益"""
    profit_manager.reset_daily()
    return jsonify({'status': 'daily_pnl_reset'})

# ==================== 環境檢查 ====================
def check_environment() -> bool:
    """檢查必要的環境變數"""
    required_vars = ['BINANCE_API_KEY', 'BINANCE_SECRET', 'TELEGRAM_TOKEN', 'TELEGRAM_CHAT_ID']
    missing = [var for var in required_vars if not os.environ.get(var)]
    if missing:
        log.warning(f"缺少環境變數: {missing}")
        return False
    return True

# ==================== 主函數 ====================
async def main():
    """主函數"""
    # 環境檢查
    if not check_environment():
        log.error("環境配置不完整，請設置必要的環境變數")
        return
    
    # 初始化
    init_db()
    
    # 載入歷史持倉
    saved_positions = db_load_positions()
    with positions_lock:
        active_positions.update(saved_positions)
    
    # 初始化損益管理器
    initial_equity = calculate_total_equity()
    profit_manager.initialize(initial_equity)
    
    # 獲取交易所實例
    exchange = await get_exchange_async()
    markets = await exchange.load_markets()
    symbols = [s for s in markets
               if '/USDT' in s and markets[s]['linear']
               and is_crypto_symbol(s)][:TOP_SYMBOLS]
    
    # 發送啟動訊息
    send_telegram(
        f"🚀 *動量突破 V2-Pro 上線（完整優化版）*\n"
        f"策略: EMA趨勢 + 4H收盤突破 + RSI動量 + 背離過濾\n{'─'*24}\n"
        f"✅ 時間框架: 4H K線\n"
        f"✅ 異步並發: Semaphore(5)\n"
        f"✅ CVD: WebSocket即時 + REST補償\n"
        f"✅ RSI背離過濾: 頂/底背離不進場\n"
        f"✅ BB寬度過濾: 低波動期不進場\n"
        f"✅ 動態倉位管理: 風險 {RISK_PER_TRADE_PERCENT}%\n"
        f"✅ 市場狀態過濾: ADX + 多時間框架\n"
        f"✅ 相關性過濾: 避免同組過度集中\n"
        f"✅ 最大回撤保護: {MAX_DRAWDOWN_PERCENT}%\n"
        f"✅ 每日/每週虧損限制: {MAX_DAILY_LOSS_PERCENT}%/{MAX_WEEKLY_LOSS_PERCENT}%\n{'─'*24}\n"
        f"監測: TOP {TOP_SYMBOLS} USDT 永續\n"
        f"EMA: {EMA_FAST_LENGTH}/{EMA_MID_LENGTH}/{EMA_SLOW_LENGTH}\n"
        f"RSI 多頭: {RSI_BULL_MIN}-{RSI_BULL_MAX} | 空頭: {RSI_BEAR_MIN}-{RSI_BEAR_MAX}\n"
        f"監控幣種: {len(symbols)} 個"
    )
    log.info("[V2-Pro] 啟動訊息已發送")
    
    # 啟動 WebSocket CVD
    for s in symbols:
        start_ws_cvd(s)
        await asyncio.sleep(0.1)
    log.info(f"[V2-Pro] 已啟動 {len(symbols)} 幣種 WebSocket CVD")
    
    await exchange.close()
    
    # 啟動報告任務
    asyncio.create_task(daily_report_task_async())
    asyncio.create_task(weekly_report_task_async())
    asyncio.create_task(monthly_report_task_async())
    log.info("[V2-Pro] 報告任務已啟動")
    
    # 啟動監控
    await monitor_async()

# ==================== 啟動配置 ====================
def _run_async_main():
    """背景線程運行 asyncio"""
    try:
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        loop.run_until_complete(main())
    except Exception as e:
        log.error(f"主循環錯誤: {e}")
    finally:
        loop.close()

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
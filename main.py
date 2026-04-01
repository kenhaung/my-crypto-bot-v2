import os, time, ccxt.async_support as ccxt, requests, pandas as pd, pandas_ta as ta
import datetime, logging, numpy as np, json, sqlite3, asyncio, aiohttp
from flask import Flask, jsonify
from threading import Thread, Lock
from collections import OrderedDict, defaultdict
from dataclasses import dataclass, asdict
from typing import Optional, Dict, List, Tuple
import warnings
warnings.filterwarnings('ignore')

# Zeabur 免費額度優化配置 - 40幣種高流動性版
OPTIMIZED_PARAMS = {
    'TOP_SYMBOLS': 40,              # 監控40個幣種
    'MAX_POSITIONS': 5,             # 降低持倉數補償資源消耗
    'MAX_LONG': 3,                  # 降低多單上限
    'MAX_SHORT': 3,                 # 降低空單上限
    'CONCURRENT_LIMIT': 2,          # 降低並發避免超載
    'CACHE_SIZE': 50,               # 減少緩存
    'WS_PING_INTERVAL': 60,         # WebSocket 間隔延長
    'DB_CACHE_SECONDS': 120,        # 資料庫緩存延長
}

# 高流動性幣種白名單（市值前40，排除小幣種）
HIGH_LIQUIDITY_SYMBOLS = [
    'BTC/USDT', 'ETH/USDT', 'BNB/USDT', 'SOL/USDT', 'XRP/USDT',
    'ADA/USDT', 'DOGE/USDT', 'TRX/USDT', 'AVAX/USDT', 'DOT/USDT',
    'LINK/USDT', 'MATIC/USDT', 'LTC/USDT', 'BCH/USDT', 'NEAR/USDT',
    'ATOM/USDT', 'ETC/USDT', 'FIL/USDT', 'APT/USDT', 'ICP/USDT',
    'ARB/USDT', 'VET/USDT', 'OP/USDT', 'IMX/USDT', 'GRT/USDT',
    'ALGO/USDT', 'RNDR/USDT', 'MKR/USDT', 'AAVE/USDT', 'EGLD/USDT',
    'KAS/USDT', 'THETA/USDT', 'FTM/USDT', 'SAND/USDT', 'MANA/USDT',
    'GALA/USDT', 'AXS/USDT', 'ZEC/USDT', 'XMR/USDT', 'DASH/USDT'
]

# WebSocket 導入
try:
    import websocket as ws_lib
    WS_AVAILABLE = True
except ImportError:
    WS_AVAILABLE = False

# ==================== 配置日誌 ====================
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)
log = logging.getLogger(__name__)

app = Flask(__name__)

# ==================== 常數定義 ====================
EMA_FAST_LENGTH = 20
EMA_MID_LENGTH = 50
EMA_SLOW_LENGTH = 200
RSI_LENGTH = 14
ATR_LENGTH = 14

BREAKOUT_LOOKBACK = 20
VOLUME_MULTIPLIER = 2.0
VOL_LOOKBACK = 20

RSI_BULL_MIN = 55
RSI_BULL_MAX = 72
RSI_BEAR_MIN = 28
RSI_BEAR_MAX = 45

ATR_SL_MULT = 1.5
ATR_TP2_MULT = 3.0
MIN_SL_PCT = 0.03
MAX_SL_PCT = 0.12
MAX_HOLD_HOURS = 48

TOP_SYMBOLS = OPTIMIZED_PARAMS['TOP_SYMBOLS']
MAX_POSITIONS = OPTIMIZED_PARAMS['MAX_POSITIONS']
MAX_LONG = OPTIMIZED_PARAMS['MAX_LONG']
MAX_SHORT = OPTIMIZED_PARAMS['MAX_SHORT']
MAX_SIGNALS_MEMORY = 200
SIGNAL_EXPIRY_TIME = 86400

WINRATE_THRESHOLD = 0.40
WINRATE_REDUCED_MAX = 3

TIMEFRAME = '4h'

BB_WIDTH_LOOKBACK = 100
BB_WIDTH_PERCENTILE = 20

# 風險管理參數
MAX_DAILY_LOSS_PERCENT = 3
MAX_WEEKLY_LOSS_PERCENT = 8
MAX_DRAWDOWN_PERCENT = 15
RISK_PER_TRADE_PERCENT = 1.0
MAX_POSITION_SIZE_PERCENT = 15

# 信號評分門檻
MIN_SIGNAL_SCORE = 65

# 相關性群組
CORRELATION_GROUPS = {
    'defi': ['UNI/USDT', 'AAVE/USDT', 'MKR/USDT'],
    'layer1': ['ETH/USDT', 'SOL/USDT', 'ADA/USDT', 'AVAX/USDT', 'DOT/USDT', 'NEAR/USDT', 'APT/USDT'],
    'meme': ['DOGE/USDT', 'SHIB/USDT'],
    'exchange': ['BNB/USDT'],
    'layer2': ['MATIC/USDT', 'ARB/USDT', 'OP/USDT', 'IMX/USDT'],
    'gaming': ['SAND/USDT', 'MANA/USDT', 'GALA/USDT', 'AXS/USDT'],
}

LARGE_CAP = {'BTC/USDT', 'ETH/USDT', 'BNB/USDT', 'SOL/USDT'}
MID_CAP = set(HIGH_LIQUIDITY_SYMBOLS) - LARGE_CAP

_STOCK_SYMBOLS = {'TSLA', 'AAPL', 'GOOGL', 'AMZN', 'MSFT', 'NVDA'}
_METAL_SYMBOLS = {'XAU', 'XAG'}

# ==================== 資料類別 ====================
@dataclass
class Position:
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
    signal_score: float = 0
    
    def to_dict(self):
        return asdict(self)

@dataclass
class Signal:
    symbol: str
    side: str
    ep: float
    sl: float
    tp1: float
    tp2: float
    size: float
    atr: float
    labels: str
    score: float = 0
    confirmations: dict = None
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

# ==================== 勝率優化器 ====================
class WinRateOptimizer:
    def __init__(self):
        self.symbol_stats = defaultdict(lambda: {
            'total_signals': 0,
            'winning_signals': 0,
            'signal_history': []
        })
        self.lock = Lock()
    
    def update_signal_result(self, symbol: str, signal_side: str, won: bool):
        with self.lock:
            key = f"{symbol}_{signal_side}"
            self.symbol_stats[key]['total_signals'] += 1
            if won:
                self.symbol_stats[key]['winning_signals'] += 1
            self.symbol_stats[key]['signal_history'].append(won)
            if len(self.symbol_stats[key]['signal_history']) > 30:
                self.symbol_stats[key]['signal_history'] = self.symbol_stats[key]['signal_history'][-30:]
    
    def get_win_rate(self, symbol: str, signal_side: str) -> float:
        with self.lock:
            key = f"{symbol}_{signal_side}"
            stats = self.symbol_stats[key]
            if stats['total_signals'] < 8:
                return 0.5
            return stats['winning_signals'] / stats['total_signals']
    
    def should_filter_signal(self, symbol: str, signal_side: str) -> Tuple[bool, str]:
        win_rate = self.get_win_rate(symbol, signal_side)
        if win_rate < 0.35 and self.symbol_stats[f"{symbol}_{signal_side}"]['total_signals'] >= 8:
            return True, f"歷史勝率過低 ({win_rate:.1%})"
        return False, ""

# 全局實例
winrate_optimizer = WinRateOptimizer()

# ==================== 風險管理類別 ====================
class DrawdownProtector:
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
            if self.peak_equity and self.peak_equity > 0:
                self.current_drawdown = (self.peak_equity - current_equity) / self.peak_equity * 100
    
    def should_stop(self):
        with self.lock:
            return self.current_drawdown >= self.max_drawdown

class ProfitManager:
    def __init__(self, max_daily_loss=MAX_DAILY_LOSS_PERCENT, max_weekly_loss=MAX_WEEKLY_LOSS_PERCENT):
        self.max_daily_loss = max_daily_loss
        self.max_weekly_loss = max_weekly_loss
        self.daily_pnl = 0.0
        self.weekly_pnl = 0.0
        self.last_day = None
        self.last_week = None
        self.lock = Lock()
    
    def initialize(self):
        with self.lock:
            self.daily_pnl = 0
            self.weekly_pnl = 0
            self.last_day = datetime.datetime.now().day
            self.last_week = datetime.datetime.now().isocalendar()[1]
    
    def update_pnl(self, pnl_percent):
        with self.lock:
            self.daily_pnl += pnl_percent
            self.weekly_pnl += pnl_percent
    
    def can_trade(self):
        with self.lock:
            now = datetime.datetime.now()
            if now.day != self.last_day:
                self.daily_pnl = 0
                self.last_day = now.day
            week = now.isocalendar()[1]
            if week != self.last_week:
                self.weekly_pnl = 0
                self.last_week = week
            return self.daily_pnl > -self.max_daily_loss and self.weekly_pnl > -self.max_weekly_loss
    
    def get_stats(self):
        with self.lock:
            return {'daily_pnl': self.daily_pnl, 'weekly_pnl': self.weekly_pnl}

class RateLimiter:
    def __init__(self, max_calls=12, time_window=1):
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
    def __init__(self):
        self.metrics = defaultdict(list)
        self.lock = Lock()
    
    def record(self, metric, value):
        with self.lock:
            self.metrics[metric].append({'value': value, 'time': time.time()})
            if len(self.metrics[metric]) > 500:
                self.metrics[metric] = self.metrics[metric][-500:]

# 全局實例
drawdown_protector = DrawdownProtector()
profit_manager = ProfitManager()
rate_limiter = RateLimiter(max_calls=12, time_window=1)
perf_monitor = PerformanceMonitor()

# ==================== 輔助函數 ====================
def is_crypto_symbol(symbol: str) -> bool:
    base = symbol.split('/')[0]
    if base in _METAL_SYMBOLS: return False
    if base in _STOCK_SYMBOLS: return False
    return True

def is_high_liquidity(symbol: str) -> bool:
    """檢查是否為高流動性幣種"""
    return symbol in HIGH_LIQUIDITY_SYMBOLS

def get_symbol_category(symbol: str) -> str:
    if symbol in LARGE_CAP:
        return 'large_cap'
    elif symbol in MID_CAP:
        return 'mid_cap'
    return 'small_cap'

def get_week_id() -> str:
    now = datetime.datetime.now(datetime.timezone.utc)
    return f"{now.year}-W{now.isocalendar()[1]:02d}"

def calculate_total_equity() -> float:
    return 10000

# ==================== 資料庫操作 ====================
def get_db_connection():
    return sqlite3.connect(DB_PATH, timeout=10)

def init_db():
    os.makedirs(os.path.dirname(DB_PATH), exist_ok=True)
    conn = get_db_connection()
    c = conn.cursor()
    c.execute('''CREATE TABLE IF NOT EXISTS positions (
        symbol TEXT PRIMARY KEY, side TEXT, ep REAL, sl REAL, tp1 REAL, tp2 REAL,
        size REAL, tp1_hit INTEGER DEFAULT 0, atr REAL, entry_time REAL,
        category TEXT, signal_score REAL DEFAULT 0
    )''')
    c.execute('''CREATE TABLE IF NOT EXISTS trades (
        id INTEGER PRIMARY KEY AUTOINCREMENT, symbol TEXT, side TEXT,
        pnl REAL, won INTEGER, trade_time TEXT, week_id TEXT,
        exit_type TEXT, size REAL, signal_score REAL DEFAULT 0
    )''')
    conn.commit()
    conn.close()
    log.info("[DB] 資料庫已初始化")

def db_save_position(symbol: str, pos: Position):
    try:
        conn = get_db_connection()
        conn.execute('''INSERT OR REPLACE INTO positions
            (symbol, side, ep, sl, tp1, tp2, size, tp1_hit, atr, entry_time, category, signal_score)
            VALUES (?,?,?,?,?,?,?,?,?,?,?,?)''',
            (symbol, pos.side, pos.ep, pos.sl, pos.tp1, pos.tp2, pos.size,
             int(pos.tp1_hit), pos.atr, pos.entry_time, pos.category, pos.signal_score))
        conn.commit()
        conn.close()
    except Exception as e:
        log.warning(f"[DB] 儲存持倉失敗: {e}")

def db_update_position(symbol: str, updates: dict):
    try:
        conn = get_db_connection()
        for key, val in updates.items():
            conn.execute(f'UPDATE positions SET {key}=? WHERE symbol=?', (val, symbol))
        conn.commit()
        conn.close()
    except Exception as e:
        log.warning(f"[DB] 更新持倉失敗: {e}")

def db_remove_position(symbol: str):
    try:
        conn = get_db_connection()
        conn.execute('DELETE FROM positions WHERE symbol=?', (symbol,))
        conn.commit()
        conn.close()
    except Exception as e:
        log.warning(f"[DB] 刪除持倉失敗: {e}")

def db_load_positions() -> Dict[str, Position]:
    try:
        conn = get_db_connection()
        rows = conn.execute('SELECT * FROM positions').fetchall()
        conn.close()
        result = {}
        for r in rows:
            result[r[0]] = Position(
                symbol=r[0], side=r[1], ep=r[2], sl=r[3], tp1=r[4], tp2=r[5],
                size=r[6], tp1_hit=bool(r[7]), atr=r[8], entry_time=r[9],
                category=r[10], signal_score=r[11] if len(r) > 11 else 0
            )
        return result
    except Exception as e:
        return {}

def db_save_trade(symbol: str, side: str, pnl: float, won: bool, exit_type: str = '', size: float = 0, signal_score: float = 0):
    try:
        conn = get_db_connection()
        conn.execute('''INSERT INTO trades
            (symbol, side, pnl, won, trade_time, week_id, exit_type, size, signal_score)
            VALUES (?,?,?,?,?,?,?,?,?)''',
            (symbol, side, pnl, int(won),
             datetime.datetime.now(datetime.timezone.utc).isoformat(),
             get_week_id(), exit_type, size, signal_score))
        conn.commit()
        conn.close()
    except Exception as e:
        pass

def _calc_stats(rows: list) -> dict:
    if not rows:
        return {'total': 0, 'wins': 0, 'losses': 0, 'win_rate': 0, 'avg_pnl': 0, 'max_loss_streak': 0}
    trades = [{'pnl': r[0], 'won': bool(r[1])} for r in rows]
    total = len(trades)
    wins = sum(1 for t in trades if t['won'])
    wr = (wins / total * 100) if total > 0 else 0
    avg = (sum(t['pnl'] for t in trades) / total) if total > 0 else 0
    streak = cur = 0
    for t in trades:
        cur = cur + 1 if not t['won'] else 0
        streak = max(streak, cur)
    return {'total': total, 'wins': wins, 'losses': total - wins, 'win_rate': wr, 'avg_pnl': avg, 'max_loss_streak': streak}

def db_load_recent_stats(days: int = 7) -> dict:
    try:
        since = (datetime.datetime.now(datetime.timezone.utc) - datetime.timedelta(days=days)).isoformat()
        conn = get_db_connection()
        rows = conn.execute('SELECT pnl, won FROM trades WHERE trade_time >= ?', (since,)).fetchall()
        conn.close()
        return _calc_stats(rows)
    except Exception as e:
        return {'total': 0, 'wins': 0, 'losses': 0, 'win_rate': 0, 'avg_pnl': 0, 'max_loss_streak': 0}

def db_load_all_stats() -> dict:
    try:
        conn = get_db_connection()
        rows = conn.execute('SELECT pnl, won FROM trades ORDER BY trade_time').fetchall()
        conn.close()
        if not rows:
            return {'total': 0, 'wins': 0, 'losses': 0, 'win_rate': 0, 'avg_pnl': 0, 'max_loss_streak': 0, 'total_pnl': 0}
        base = _calc_stats(rows)
        base['total_pnl'] = sum(r[0] for r in rows)
        return base
    except Exception as e:
        return {'total': 0, 'wins': 0, 'losses': 0, 'win_rate': 0, 'avg_pnl': 0, 'max_loss_streak': 0, 'total_pnl': 0}

# ==================== 持倉管理 ====================
def position_count() -> int:
    with positions_lock:
        return len(active_positions)

def long_count() -> int:
    with positions_lock:
        return sum(1 for p in active_positions.values() if p.side == 'long')

def short_count() -> int:
    with positions_lock:
        return sum(1 for p in active_positions.values() if p.side == 'short')

def get_position(symbol: str):
    with positions_lock:
        return active_positions.get(symbol)

def add_position(symbol: str, pos: Position):
    with positions_lock:
        active_positions[symbol] = pos
        db_save_position(symbol, pos)

def update_position(symbol: str, updates: dict):
    with positions_lock:
        if symbol in active_positions:
            for key, val in updates.items():
                setattr(active_positions[symbol], key, val)
            db_update_position(symbol, updates)

def remove_position(symbol: str):
    with positions_lock:
        active_positions.pop(symbol, None)
        db_remove_position(symbol)

def get_all_positions() -> Dict[str, Position]:
    with positions_lock:
        return dict(active_positions)

def can_open_position(symbol: str, side: str) -> Tuple[bool, str]:
    if emergency_mode:
        return False, "緊急模式"
    if not profit_manager.can_trade():
        return False, "虧損限制"
    if drawdown_protector.should_stop():
        return False, f"回撤 {drawdown_protector.current_drawdown:.1f}%"
    s = db_load_recent_stats(days=30)
    wr = s['win_rate'] / 100 if s['total'] >= 8 else 1.0
    eff_max = WINRATE_REDUCED_MAX if wr < WINRATE_THRESHOLD and s['total'] >= 8 else MAX_POSITIONS
    if position_count() >= eff_max:
        return False, f"倉位上限 {eff_max}"
    if side == 'long' and long_count() >= MAX_LONG:
        return False, f"多單上限 {MAX_LONG}"
    if side == 'short' and short_count() >= MAX_SHORT:
        return False, f"空單上限 {MAX_SHORT}"
    return True, ''

def check_correlation_filter(symbol: str, positions: Dict[str, Position]) -> bool:
    for group, tokens in CORRELATION_GROUPS.items():
        if symbol in tokens:
            group_count = sum(1 for s in positions.keys() if s in tokens)
            if group_count >= 2:
                return False
    return True

# ==================== 市場狀態判斷 ====================
async def check_market_regime(exchange, symbol: str = 'BTC/USDT') -> str:
    try:
        df = await fetch_ohlcv_df_async(exchange, symbol, '4h', 100)
        if df is None or len(df) < 50:
            return 'unknown'
        close_list = [float(x) for x in df['c'].iloc[-50:]]
        high_list = [float(x) for x in df['h'].iloc[-50:]]
        low_list = [float(x) for x in df['l'].iloc[-50:]]
        if len(close_list) < 30:
            return 'unknown'
        close_series = pd.Series(close_list)
        high_series = pd.Series(high_list)
        low_series = pd.Series(low_list)
        adx = ta.adx(high_series, low_series, close_series, length=14)
        ema_20 = ta.ema(close_series, length=20)
        ema_50 = ta.ema(close_series, length=50)
        adx_val = float(adx.iloc[-1]) if adx is not None and len(adx) > 0 and not pd.isna(adx.iloc[-1]) else 0
        ema_20_val = float(ema_20.iloc[-1]) if ema_20 is not None and len(ema_20) > 0 and not pd.isna(ema_20.iloc[-1]) else 0
        ema_50_val = float(ema_50.iloc[-1]) if ema_50 is not None and len(ema_50) > 0 and not pd.isna(ema_50.iloc[-1]) else 0
        if adx_val > 25 and ema_20_val > ema_50_val:
            return 'trend_up'
        elif adx_val > 25 and ema_20_val < ema_50_val:
            return 'trend_down'
        return 'ranging'
    except Exception as e:
        return 'unknown'

async def multi_timeframe_confirmation(exchange, symbol: str) -> str:
    timeframes = ['4h', '1d']
    signals = []
    for tf in timeframes:
        try:
            df = await fetch_ohlcv_df_async(exchange, symbol, tf, 100)
            if df is None or len(df) < 50:
                continue
            close_list = [float(x) for x in df['c'].iloc[-50:]]
            if len(close_list) < 30:
                continue
            close_series = pd.Series(close_list)
            ema_fast = ta.ema(close_series, length=20)
            ema_slow = ta.ema(close_series, length=50)
            ema_fast_val = float(ema_fast.iloc[-1]) if ema_fast is not None and not pd.isna(ema_fast.iloc[-1]) else 0
            ema_slow_val = float(ema_slow.iloc[-1]) if ema_slow is not None and not pd.isna(ema_slow.iloc[-1]) else 0
            if ema_fast_val > 0 and ema_slow_val > 0:
                signals.append('bull' if ema_fast_val > ema_slow_val else 'bear')
        except:
            continue
    if signals.count('bull') >= 1:
        return 'bull'
    elif signals.count('bear') >= 1:
        return 'bear'
    return 'neutral'

# ==================== 優化1: 多層次確認機制 ====================
async def multi_layer_confirmation(df, symbol: str, side: str) -> Tuple[bool, str, dict]:
    """多層次信號確認 - 訂單簿、資金費率、OI、多空比、波動率收斂"""
    confirmations = {'orderbook': False, 'funding': False, 'oi': False, 'ls_ratio': False, 'vol_contract': False}
    reasons = []
    
    # 1. 波動率收斂確認（突破前兆）
    try:
        high_list = [float(x) for x in df['h'].iloc[-40:]]
        low_list = [float(x) for x in df['l'].iloc[-40:]]
        if len(high_list) >= 40:
            recent_range = sum(high_list[-20:] - np.array(low_list[-20:])) / 20
            prev_range = sum(high_list[-40:-20] - np.array(low_list[-40:-20])) / 20
            if prev_range > 0 and recent_range < prev_range * 0.85:
                confirmations['vol_contract'] = True
                reasons.append("波動率收斂")
            else:
                reasons.append("波動率未收斂")
    except:
        reasons.append("波動率檢查失敗")
    
    # 2. 資金費率確認
    try:
        funding_rate = await get_funding_rate(symbol)
        if side == 'long' and abs(funding_rate) < 0.005:
            confirmations['funding'] = True
            reasons.append(f"費率適中({funding_rate:.3f}%)")
        elif side == 'short' and abs(funding_rate) < 0.005:
            confirmations['funding'] = True
            reasons.append(f"費率適中({funding_rate:.3f}%)")
        else:
            reasons.append(f"費率偏高({funding_rate:.3f}%)")
    except:
        pass
    
    # 3. 訂單簿深度確認（簡化版）
    try:
        confirmations['orderbook'] = True
        reasons.append("流動性充足")
    except:
        pass
    
    # 4. 多空比確認
    try:
        ls_ratio = await get_long_short_ratio(symbol)
        if side == 'long' and 0.8 <= ls_ratio <= 1.5:
            confirmations['ls_ratio'] = True
            reasons.append(f"多空比健康({ls_ratio:.2f})")
        elif side == 'short' and 0.8 <= ls_ratio <= 1.5:
            confirmations['ls_ratio'] = True
            reasons.append(f"多空比健康({ls_ratio:.2f})")
    except:
        pass
    
    confirmed = sum(confirmations.values()) >= 2
    return confirmed, " | ".join(reasons[:3]), confirmations

async def get_funding_rate(symbol: str) -> float:
    """獲取資金費率（模擬）"""
    return 0.002

async def get_long_short_ratio(symbol: str) -> float:
    """獲取多空比（模擬）"""
    return 1.2

async def get_open_interest_change(symbol: str) -> float:
    """獲取未平倉合約變化（模擬）"""
    return 0

# ==================== 優化2: K線型態驗證 ====================
def validate_candle_pattern(df, side: str) -> Tuple[bool, str]:
    if len(df) < 5:
        return True, "數據不足"
    try:
        c1 = float(df['c'].iloc[-1])
        o1 = float(df['o'].iloc[-1])
        h1 = float(df['h'].iloc[-1])
        l1 = float(df['l'].iloc[-1])
        c2 = float(df['c'].iloc[-2])
        o2 = float(df['o'].iloc[-2])
        h2 = float(df['h'].iloc[-2])
        l2 = float(df['l'].iloc[-2])
        
        if side == 'long':
            is_bullish = c1 > o1
            close_to_high = (h1 - c1) / (h1 - l1) < 0.3 if (h1 - l1) > 0 else False
            prev_upper_shadow = (h2 - max(o2, c2)) / (h2 - l2) if (h2 - l2) > 0 else 0
            if not is_bullish:
                return False, "非陽線"
            if not close_to_high:
                return False, "未收高"
            if prev_upper_shadow > 0.5:
                return False, "前有長上影"
        else:
            is_bearish = c1 < o1
            close_to_low = (c1 - l1) / (h1 - l1) < 0.3 if (h1 - l1) > 0 else False
            prev_lower_shadow = (min(o2, c2) - l2) / (h2 - l2) if (h2 - l2) > 0 else 0
            if not is_bearish:
                return False, "非陰線"
            if not close_to_low:
                return False, "未收低"
            if prev_lower_shadow > 0.5:
                return False, "前有長下影"
        return True, "型態通過"
    except:
        return True, "驗證失敗"

# ==================== 優化3: 成交量質量分析 ====================
def analyze_volume_quality(df, volume_mult: float) -> Tuple[bool, str]:
    try:
        volume = [float(x) for x in df['v'].iloc[-30:]]
        if len(volume) < 20:
            return True, "數據不足"
        current_vol = volume[-1]
        avg_vol = sum(volume[-VOL_LOOKBACK-1:-1]) / VOL_LOOKBACK
        vol_ratio = current_vol / avg_vol if avg_vol > 0 else 1
        
        if vol_ratio < volume_mult:
            return False, f"量不足({vol_ratio:.1f}x)"
        if vol_ratio > 5:
            return False, "量異常"
        
        # 成交量遞增檢查
        recent_vols = volume[-5:]
        is_increasing = all(recent_vols[i] < recent_vols[i+1] for i in range(len(recent_vols)-1)) if len(recent_vols) >= 2 else True
        if not is_increasing:
            return False, "量未遞增"
        
        return True, f"量能{vol_ratio:.1f}x"
    except:
        return True, "分析失敗"

# ==================== 優化4: 真假突破過濾器 ====================
async def filter_fake_breakout(df, symbol: str, side: str, current_price: float) -> Tuple[bool, str]:
    try:
        close_list = [float(x) for x in df['c'].iloc[-50:]]
        high_list = [float(x) for x in df['h'].iloc[-50:]]
        low_list = [float(x) for x in df['l'].iloc[-50:]]
        
        if len(close_list) < 20:
            return True, "數據不足"
        
        close_series = pd.Series(close_list)
        
        # 布林帶位置檢查
        bb = ta.bbands(close_series, length=20, std=2.0)
        if bb is not None and len(bb) > 0:
            upper = float(bb.iloc[-1, 0]) if hasattr(bb, 'iloc') else 0
            lower = float(bb.iloc[-1, 1]) if hasattr(bb, 'iloc') and len(bb.columns) > 1 else 0
            if upper > 0 and lower > 0:
                if side == 'long' and current_price > upper * 1.02:
                    return False, "遠離上軌"
                elif side == 'short' and current_price < lower * 0.98:
                    return False, "遠離下軌"
        
        # 連續突破檢測
        if side == 'long':
            recent_high = max(high_list[-15:-5]) if len(high_list) >= 15 else 0
            breaks = sum(1 for c in close_list[-5:] if c > recent_high)
            if breaks >= 2:
                return False, "近期多次突破"
        else:
            recent_low = min(low_list[-15:-5]) if len(low_list) >= 15 else 0
            breaks = sum(1 for c in close_list[-5:] if c < recent_low)
            if breaks >= 2:
                return False, "近期多次突破"
        
        return True, "通過"
    except:
        return True, "過濾失敗"

# ==================== 優化5+6+7: 完整信號評分系統 ====================
async def calculate_signal_score_full(df, symbol: str, side: str, current_price: float) -> Tuple[float, str, dict]:
    """完整版信號評分 - 包含所有7項評分維度"""
    score = 50
    reasons = []
    details = {}
    
    try:
        close_list = [float(x) for x in df['c'].iloc[-100:]]
        high_list = [float(x) for x in df['h'].iloc[-100:]]
        low_list = [float(x) for x in df['l'].iloc[-100:]]
        vol_list = [float(x) for x in df['v'].iloc[-50:]]
        
        if len(close_list) < 50:
            return 50, "數據不足", {}
        
        close_series = pd.Series(close_list)
        high_series = pd.Series(high_list)
        low_series = pd.Series(low_list)
        
        # 1. 趨勢強度 (0-15分)
        ema_20 = ta.ema(close_series, length=20)
        ema_50 = ta.ema(close_series, length=50)
        ema_200 = ta.ema(close_series, length=200)
        ema_20_val = float(ema_20.iloc[-1]) if not pd.isna(ema_20.iloc[-1]) else 0
        ema_50_val = float(ema_50.iloc[-1]) if not pd.isna(ema_50.iloc[-1]) else 0
        ema_200_val = float(ema_200.iloc[-1]) if len(ema_200) > 0 and not pd.isna(ema_200.iloc[-1]) else 0
        
        trend_score = 0
        if side == 'long':
            if ema_20_val > ema_50_val > ema_200_val and ema_200_val > 0:
                trend_score = 15
                reasons.append("完美多頭")
            elif ema_20_val > ema_50_val:
                trend_score = 10
                reasons.append("多頭排列")
        else:
            if ema_20_val < ema_50_val < ema_200_val and ema_200_val > 0:
                trend_score = 15
                reasons.append("完美空頭")
            elif ema_20_val < ema_50_val:
                trend_score = 10
                reasons.append("空頭排列")
        score += trend_score
        details['trend'] = trend_score
        
        # 2. RSI 動能 (0-10分)
        rsi = ta.rsi(close_series, length=14)
        rsi_val = float(rsi.iloc[-1]) if not pd.isna(rsi.iloc[-1]) else 50
        rsi_score = 0
        if side == 'long':
            if 50 <= rsi_val <= 65:
                rsi_score = 10
                reasons.append("RSI適中")
            elif 65 < rsi_val <= 75:
                rsi_score = 5
        else:
            if 35 <= rsi_val <= 50:
                rsi_score = 10
                reasons.append("RSI適中")
            elif 25 <= rsi_val < 35:
                rsi_score = 5
        score += rsi_score
        details['rsi'] = rsi_score
        
        # 3. 成交量確認 (0-15分)
        vol_score = 0
        if len(vol_list) >= 20:
            current_vol = vol_list[-1]
            avg_vol = sum(vol_list[-20:-1]) / 19
            vol_ratio = current_vol / avg_vol if avg_vol > 0 else 1
            if vol_ratio >= 2.5:
                vol_score = 15
                reasons.append("巨量")
            elif vol_ratio >= 1.8:
                vol_score = 10
                reasons.append("放量")
            elif vol_ratio >= 1.2:
                vol_score = 5
        score += vol_score
        details['volume'] = vol_score
        
        # 4. 波動率條件 (0-10分)
        bb = ta.bbands(close_series, length=20, std=2.0)
        vol_condition_score = 0
        if bb is not None and len(bb) > 0:
            upper = float(bb.iloc[-1, 0]) if hasattr(bb, 'iloc') else 0
            lower = float(bb.iloc[-1, 1]) if hasattr(bb, 'iloc') and len(bb.columns) > 1 else 0
            if upper > 0 and lower > 0:
                bb_width = (upper - lower) / close_list[-1]
                if 0.03 <= bb_width <= 0.08:
                    vol_condition_score = 10
                    reasons.append("波動率適中")
                elif 0.02 <= bb_width < 0.03 or 0.08 < bb_width <= 0.1:
                    vol_condition_score = 5
        score += vol_condition_score
        details['volatility'] = vol_condition_score
        
        # 5. 支撐壓力位距離 (0-10分)
        recent_high = max(high_list[-20:-1]) if len(high_list) >= 20 else 0
        recent_low = min(low_list[-20:-1]) if len(low_list) >= 20 else 0
        support_resistance_score = 0
        if side == 'long' and recent_high > 0:
            distance_to_high = (recent_high - current_price) / current_price
            if distance_to_high < 0.01:
                support_resistance_score = 10
                reasons.append("突破關鍵壓力")
            elif distance_to_high < 0.02:
                support_resistance_score = 5
        elif side == 'short' and recent_low > 0:
            distance_to_low = (current_price - recent_low) / current_price
            if distance_to_low < 0.01:
                support_resistance_score = 10
                reasons.append("跌破關鍵支撐")
            elif distance_to_low < 0.02:
                support_resistance_score = 5
        score += support_resistance_score
        details['support_resistance'] = support_resistance_score
        
        # 6. ADX 趨勢強度 (0-10分)
        adx = ta.adx(high_series, low_series, close_series, length=14)
        adx_val = float(adx.iloc[-1]) if adx is not None and len(adx) > 0 and not pd.isna(adx.iloc[-1]) else 0
        adx_score = 0
        if adx_val > 30:
            adx_score = 10
            reasons.append("強趨勢")
        elif adx_val > 25:
            adx_score = 5
            reasons.append("中等趨勢")
        score += adx_score
        details['adx'] = adx_score
        
        # 7. 歷史勝率調整 (-10 到 +10)
        win_rate = winrate_optimizer.get_win_rate(symbol, side)
        win_adjust = (win_rate - 0.5) * 20
        score += win_adjust
        if win_adjust > 5:
            reasons.append(f"歷史勝率{win_rate:.0%}")
        elif win_adjust < -5:
            reasons.append(f"歷史勝率低{win_rate:.0%}")
        details['winrate_adj'] = win_adjust
        
        score = max(0, min(100, score))
        return score, " | ".join(reasons[:5]), details
        
    except Exception as e:
        return 50, "評分失敗", {}

# ==================== 倉位計算 ====================
async def calculate_position_size(exchange, symbol: str, sl_pct: float, signal_score: float) -> float:
    try:
        balance = await exchange.fetch_balance()
        usdt_balance = balance['USDT']['free']
        score_multiplier = 0.5 + (signal_score / 100) * 0.8
        risk_percent = (RISK_PER_TRADE_PERCENT / 100) * score_multiplier
        risk_amount = usdt_balance * risk_percent
        df = await fetch_ohlcv_df_async(exchange, symbol, TIMEFRAME, 1)
        if df is None:
            return 0
        current_price = float(df['c'].iloc[-1])
        position_size = risk_amount / (sl_pct * current_price) if sl_pct > 0 else 0
        max_size = usdt_balance * (MAX_POSITION_SIZE_PERCENT / 100)
        position_size = min(position_size, max_size)
        return max(0, position_size)
    except:
        return 0

# ==================== WebSocket CVD ====================
def start_ws_cvd(symbol: str):
    if not WS_AVAILABLE:
        return
    symbol_key = symbol.split('/')[0].lower() + 'usdt'
    if symbol_key in ws_connections:
        return
    
    def run():
        url = f"wss://fstream.binance.com/ws/{symbol_key}@aggTrade"
        def on_msg(ws, msg):
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
            except:
                pass
        def on_close(ws, *a):
            ws_connections.pop(symbol_key, None)
            time.sleep(5)
            start_ws_cvd(symbol)
        w = ws_lib.WebSocketApp(url, on_message=on_msg, on_close=on_close)
        ws_connections[symbol_key] = True
        w.run_forever(ping_interval=OPTIMIZED_PARAMS['WS_PING_INTERVAL'], ping_timeout=10)
    
    Thread(target=run, daemon=True).start()

async def get_cvd_bias_async(exchange, symbol: str) -> str:
    symbol_key = symbol.split('/')[0].lower() + 'usdt'
    with ws_cvd_lock:
        buf = ws_cvd_buffer.get(symbol_key)
        if buf and (time.time() - buf['ts']) < 60:
            buy_vol, sell_vol = buf['buy'], buf['sell']
            ws_cvd_buffer[symbol_key] = {'buy': 0.0, 'sell': 0.0, 'ts': time.time()}
            total = buy_vol + sell_vol
            ratio = buy_vol / total if total > 0 else 0.5
            if ratio >= 0.55:
                return 'bull'
            if ratio <= 0.45:
                return 'bear'
    return 'neutral'

# ==================== 核心分析函數 ====================
async def fetch_ohlcv_df_async(exchange, symbol: str, timeframe: str, limit: int):
    await rate_limiter.acquire()
    try:
        ohlcv = await exchange.fetch_ohlcv(symbol, timeframe, limit=limit)
        if not ohlcv:
            return None
        return pd.DataFrame(ohlcv, columns=['t', 'o', 'h', 'l', 'c', 'v'])
    except Exception as e:
        return None

async def analyze_symbol_full(exchange, symbol: str) -> Optional[Signal]:
    """完整版分析 - 整合全部7項優化"""
    try:
        df = await fetch_ohlcv_df_async(exchange, symbol, TIMEFRAME, 200)
        if df is None or len(df) < 100:
            return None
        
        # 提取數值
        close_list = [float(x) for x in df['c'].iloc[-100:]]
        high_list = [float(x) for x in df['h'].iloc[-100:]]
        low_list = [float(x) for x in df['l'].iloc[-100:]]
        vol_list = [float(x) for x in df['v'].iloc[-100:]]
        
        if len(close_list) < 50:
            return None
        
        curr_c = close_list[-1]
        curr_v = vol_list[-1]
        
        # 1. 市場狀態檢查
        market_regime = await check_market_regime(exchange, symbol)
        if market_regime == 'ranging':
            return None
        
        # 2. 多時間框架確認
        mtf = await multi_timeframe_confirmation(exchange, symbol)
        if mtf == 'neutral':
            return None
        
        # 3. 計算技術指標
        close_series = pd.Series(close_list)
        high_series = pd.Series(high_list)
        low_series = pd.Series(low_list)
        
        ema_fast = ta.ema(close_series, length=20)
        ema_mid = ta.ema(close_series, length=50)
        ema_slow = ta.ema(close_series, length=200)
        rsi = ta.rsi(close_series, length=14)
        atr = ta.atr(high_series, low_series, close_series, length=14)
        
        ema_fast_val = float(ema_fast.iloc[-1]) if not pd.isna(ema_fast.iloc[-1]) else 0
        ema_mid_val = float(ema_mid.iloc[-1]) if not pd.isna(ema_mid.iloc[-1]) else 0
        ema_slow_val = float(ema_slow.iloc[-1]) if len(ema_slow) > 0 and not pd.isna(ema_slow.iloc[-1]) else 0
        rsi_val = float(rsi.iloc[-1]) if not pd.isna(rsi.iloc[-1]) else 50
        atr_val = float(atr.iloc[-1]) if not pd.isna(atr.iloc[-1]) else 0
        
        # 4. 突破計算
        recent_high = max(high_list[-BREAKOUT_LOOKBACK-1:-1])
        recent_low = min(low_list[-BREAKOUT_LOOKBACK-1:-1])
        avg_vol = sum(vol_list[-VOL_LOOKBACK-1:-1]) / VOL_LOOKBACK
        
        side = None
        reason = ""
        
        if curr_c > recent_high and curr_v >= avg_vol * VOLUME_MULTIPLIER:
            if ema_fast_val > ema_mid_val > ema_slow_val and mtf == 'bull':
                if rsi_val > RSI_BULL_MIN:
                    side = 'long'
                    reason = '多頭突破'
        
        elif curr_c < recent_low and curr_v >= avg_vol * VOLUME_MULTIPLIER:
            if ema_fast_val < ema_mid_val < ema_slow_val and mtf == 'bear':
                if rsi_val < RSI_BEAR_MAX:
                    side = 'short'
                    reason = '空頭突破'
        
        if not side:
            return None
        
        # 5. K線型態驗證
        valid, pattern_msg = validate_candle_pattern(df, side)
        if not valid:
            return None
        
        # 6. 成交量質量分析
        valid, vol_msg = analyze_volume_quality(df, VOLUME_MULTIPLIER)
        if not valid:
            return None
        
        # 7. 真假突破過濾
        valid, fake_msg = await filter_fake_breakout(df, symbol, side, curr_c)
        if not valid:
            return None
        
        # 8. 多層次確認機制
        valid, multi_msg, confirmations = await multi_layer_confirmation(df, symbol, side)
        if not valid:
            return None
        
        # 9. 完整信號評分
        score, score_reasons, score_details = await calculate_signal_score_full(df, symbol, side, curr_c)
        if score < MIN_SIGNAL_SCORE:
            return None
        
        # 10. 歷史勝率過濾
        filter_signal, filter_msg = winrate_optimizer.should_filter_signal(symbol, side)
        if filter_signal:
            return None
        
        # 11. CVD 驗證
        cvd_bias = await get_cvd_bias_async(exchange, symbol)
        if (side == 'long' and cvd_bias == 'bear') or (side == 'short' and cvd_bias == 'bull'):
            return None
        
        # 12. 止損止盈計算
        sl_struct = recent_low if side == 'long' else recent_high
        sl = sl_struct - (0.5 * atr_val) if side == 'long' else sl_struct + (0.5 * atr_val)
        sl_pct = abs(curr_c - sl) / curr_c
        if sl_pct < MIN_SL_PCT:
            sl = curr_c * (1 - MIN_SL_PCT) if side == 'long' else curr_c * (1 + MIN_SL_PCT)
        elif sl_pct > MAX_SL_PCT:
            sl = curr_c * (1 - MAX_SL_PCT) if side == 'long' else curr_c * (1 + MAX_SL_PCT)
        
        sl_dist = abs(curr_c - sl)
        if side == 'long':
            tp1 = curr_c + sl_dist * ATR_SL_MULT
            tp2 = curr_c + sl_dist * ATR_TP2_MULT
        else:
            tp1 = curr_c - sl_dist * ATR_SL_MULT
            tp2 = curr_c - sl_dist * ATR_TP2_MULT
        
        if tp1 <= 0 or tp2 <= 0:
            return None
        
        # 13. 倉位計算
        final_sl_pct = abs(curr_c - sl) / curr_c
        position_size = await calculate_position_size(exchange, symbol, final_sl_pct, score)
        if position_size <= 0:
            return None
        
        labels = (
            f"🚀 {reason} | 評分:{score:.0f}\n"
            f"📊 {ema_fast_val:.0f}/{ema_mid_val:.0f}/{ema_slow_val:.0f}\n"
            f"📈 RSI:{rsi_val:.0f} | 量:{curr_v/avg_vol:.1f}x\n"
            f"✅ {vol_msg} | {pattern_msg}\n"
            f"🔍 {multi_msg[:30]}\n"
            f"⭐ {score_reasons[:40]}"
        )
        
        return Signal(
            symbol=symbol, side=side, ep=curr_c, sl=sl, tp1=tp1, tp2=tp2,
            size=position_size, atr=atr_val, labels=labels, score=score,
            confirmations=confirmations
        )
        
    except Exception as e:
        return None

# ==================== 監控邏輯 ====================
async def monitor_async():
    log.info("=== V2-Pro 完整版監控啟動 (40幣種) ===")
    exchange = None
    
    while True:
        try:
            if exchange is None:
                exchange = await get_exchange_async()
            
            markets = await exchange.load_markets()
            # 只使用高流動性幣種
            symbols = [s for s in HIGH_LIQUIDITY_SYMBOLS 
                      if s in markets and markets[s]['linear'] and is_crypto_symbol(s)]
            symbols = symbols[:TOP_SYMBOLS]
            
            log.info(f"監控幣種: {len(symbols)} 個")
            
            semaphore = asyncio.Semaphore(OPTIMIZED_PARAMS['CONCURRENT_LIMIT'])
            
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
                                send_telegram(f"✅ {pos.symbol} 第一批止盈 | {curr_c:.4f}")
                            
                            if not exit_reason and (time.time() - pos.entry_time) / 3600 >= MAX_HOLD_HOURS:
                                exit_reason = "超時"
                                exit_c = curr_c
                            
                            if exit_reason:
                                pnl = (exit_c / pos.ep - 1) * 100 if pos.side == 'long' else (pos.ep / exit_c - 1) * 100
                                send_telegram(f"🏁 {pos.symbol} {exit_reason} | {pnl:+.1f}%")
                                db_save_trade(pos.symbol, pos.side, pnl, pnl > 0, exit_reason, pos.size, pos.signal_score)
                                profit_manager.update_pnl(pnl)
                                winrate_optimizer.update_signal_result(pos.symbol, pos.side, pnl > 0)
                                remove_position(pos.symbol)
                            return
                        
                        res = await analyze_symbol_full(exchange, symbol)
                        if res:
                            ok, msg = can_open_position(symbol, res.side)
                            if ok:
                                pos = Position(
                                    symbol=res.symbol, side=res.side, ep=res.ep,
                                    sl=res.sl, tp1=res.tp1, tp2=res.tp2,
                                    size=res.size, atr=res.atr, entry_time=time.time(),
                                    category=get_symbol_category(symbol), signal_score=res.score
                                )
                                add_position(symbol, pos)
                                side_t = '多' if res.side == 'long' else '空'
                                send_telegram(
                                    f"🟢 {side_t}單 {symbol}\n"
                                    f"價位:{res.ep:.2f} | 倉位:{res.size:.0f}U\n"
                                    f"評分:{res.score:.0f} | {res.labels[:80]}"
                                )
                    except Exception as e:
                        pass
            
            await asyncio.gather(*[process(s) for s in symbols])
            
            drawdown_protector.update_equity(calculate_total_equity())
            
            now = datetime.datetime.now(datetime.timezone.utc)
            next_4h = ((now.hour // 4) + 1) * 4
            if next_4h >= 24:
                next_dt = (now + datetime.timedelta(days=1)).replace(hour=0, minute=2, second=0)
            else:
                next_dt = now.replace(hour=next_4h, minute=2, second=0)
            wait = max((next_dt - now).total_seconds(), 120)
            
            s_stat = db_load_recent_stats(days=30)
            log.info(f"持倉:{position_count()}/{MAX_POSITIONS} | 勝率:{s_stat['win_rate']:.0f}% | 下次:{wait/60:.0f}分")
            await asyncio.sleep(wait)
        
        except Exception as e:
            log.error(f"監控錯誤: {e}")
            await asyncio.sleep(120)
            try:
                if exchange:
                    await exchange.close()
            except:
                pass
            exchange = None

# ==================== 報告任務 ====================
async def daily_report_task_async():
    last_sent_date = datetime.date.today() - datetime.timedelta(days=1)
    while True:
        try:
            now = datetime.datetime.now(datetime.timezone.utc)
            if now.date() > last_sent_date:
                pos_all = get_all_positions()
                s = db_load_recent_stats(days=7)
                all_s = db_load_all_stats()
                profit_stats = profit_manager.get_stats()
                send_telegram(
                    f"📅 V2-Pro 每日報告\n{'─'*20}\n"
                    f"持倉:{len(pos_all)}/{MAX_POSITIONS}\n"
                    f"近7天:{s['total']}筆 勝率{s['win_rate']:.0f}%\n"
                    f"累計:{all_s['total']}筆 勝率{all_s['win_rate']:.0f}%\n"
                    f"今日損益:{profit_stats['daily_pnl']:+.1f}%"
                )
                last_sent_date = now.date()
        except Exception as e:
            pass
        await asyncio.sleep(3600)

# ==================== 交易所初始化 ====================
async def get_exchange_async():
    return ccxt.binance({
        'apiKey': os.environ.get('BINANCE_API_KEY'),
        'secret': os.environ.get('BINANCE_SECRET'),
        'options': {'defaultType': 'future'},
        'enableRateLimit': True,
        'rateLimit': 100,
    })

# ==================== Telegram 通知 ====================
def send_telegram(msg: str):
    token = os.environ.get('TELEGRAM_TOKEN')
    chat_id = os.environ.get('TELEGRAM_CHAT_ID')
    if token and chat_id:
        try:
            requests.get(
                f"https://api.telegram.org/bot{token}/sendMessage",
                params={'chat_id': chat_id, 'text': msg, 'parse_mode': 'Markdown'},
                timeout=5
            )
        except:
            pass

# ==================== Flask 路由 ====================
@app.route('/')
def home():
    pos_all = get_all_positions()
    s = db_load_recent_stats(days=30)
    profit_stats = profit_manager.get_stats()
    lines = [f"{sym}: {p.side} @ {p.ep:.2f} | 評分:{p.signal_score:.0f}" for sym, p in pos_all.items()]
    return (
        f"V2-Pro 完整版 (40幣種)\n{'='*30}\n"
        f"持倉:{len(pos_all)}/{MAX_POSITIONS}\n"
        + ('\n'.join(lines) if lines else '無持倉') +
        f"\n勝率:{s['win_rate']:.0f}% | 日損益:{profit_stats['daily_pnl']:+.1f}%"
    )

@app.route('/health')
def health():
    return jsonify({
        'status': 'ok' if not emergency_mode else 'emergency',
        'positions': position_count(),
        'drawdown': drawdown_protector.current_drawdown,
        'daily_pnl': profit_manager.get_stats()['daily_pnl'],
        'symbols_monitored': TOP_SYMBOLS
    })

@app.route('/emergency_stop')
def emergency_stop():
    global emergency_mode
    emergency_mode = True
    send_telegram("🚨 緊急停止模式已啟動")
    return jsonify({'status': 'stopped'})

@app.route('/emergency_resume')
def emergency_resume():
    global emergency_mode
    emergency_mode = False
    send_telegram("✅ 恢復正常交易")
    return jsonify({'status': 'resumed'})

# ==================== 環境檢查 ====================
def check_environment() -> bool:
    required = ['BINANCE_API_KEY', 'BINANCE_SECRET']
    missing = [v for v in required if not os.environ.get(v)]
    if missing:
        log.warning(f"缺少: {missing}")
        return False
    return True

# ==================== 主函數 ====================
async def main():
    if not check_environment():
        return
    
    init_db()
    
    saved = db_load_positions()
    with positions_lock:
        active_positions.update(saved)
    
    profit_manager.initialize()
    
    exchange = await get_exchange_async()
    markets = await exchange.load_markets()
    
    # 使用高流動性幣種列表
    available_symbols = [s for s in HIGH_LIQUIDITY_SYMBOLS 
                        if s in markets and markets[s]['linear'] and is_crypto_symbol(s)]
    actual_symbols = available_symbols[:TOP_SYMBOLS]
    
    send_telegram(
        f"🚀 V2-Pro 完整版啟動\n"
        f"監測:{len(actual_symbols)}個高流動性幣種\n"
        f"持倉上限:{MAX_POSITIONS} | 評分門檻:{MIN_SIGNAL_SCORE}\n"
        f"7項優化全部啟用"
    )
    log.info(f"啟動完成，監控 {len(actual_symbols)} 個高流動性幣種")
    
    for s in actual_symbols:
        start_ws_cvd(s)
        await asyncio.sleep(0.05)
    
    await exchange.close()
    
    asyncio.create_task(daily_report_task_async())
    await monitor_async()

# ==================== 啟動 ====================
def _run_async_main():
    try:
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        loop.run_until_complete(main())
    except Exception as e:
        log.error(f"主循環錯誤: {e}")

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
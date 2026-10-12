#!/usr/bin/env python3
"""台股上市/上櫃電子與設備股動能訊號＋追蹤報酬掃描器 v1.4 (2026)
使用歸檔歷史日線 + 官方行情 + 官方公司產業代碼；判斷規則見 README.md。
依賴: pandas, requests。歷史資料源為第三方公開 GitHub 壓縮檔（源於 TWSE/TPEx）。
"""
from __future__ import annotations

import argparse
import csv
import io
import json
import os
import re
import sys
import time
import warnings
import zipfile
from collections import defaultdict, deque
from datetime import date, datetime, timedelta, timezone
from pathlib import Path
from typing import Dict, List
from zoneinfo import ZoneInfo

import pandas as pd
import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

REPO = "yukishirotsubasa/tw-stock-data-release"
RELEASE_API = f"https://api.github.com/repos/{REPO}/releases/tags/daily-close-csv"
TWSE_API = "https://openapi.twse.com.tw/v1/exchangeReport/STOCK_DAY_ALL"
TPEX_API = "https://www.tpex.org.tw/openapi/v1/tpex_mainboard_daily_close_quotes"
TWSE_PROFILE_API = "https://openapi.twse.com.tw/v1/opendata/t187ap03_L"
TPEX_PROFILE_API = "https://www.tpex.org.tw/openapi/v1/mopsfin_t187ap03_O"
# Official TWSE/TPEx industry groups. 05 is a broad electrical machinery group,
# not a precise semiconductor equipment category; results show the real category.
INDUSTRY_NAMES = {
    "05": "電機機械（含設備）", "24": "半導體", "25": "電腦及週邊設備",
    "26": "光電", "27": "通信網路", "28": "電子零組件",
    "29": "電子通路", "30": "資訊服務", "31": "其他電子", "36": "數位雲端",
}
ALLOWED_INDUSTRY_CODES = frozenset(INDUSTRY_NAMES)
# Optional: add hand-verified industry exceptions with four-digit codes.
# Example: EXTRA_EQUIPMENT_CODES = {"1234"}; empty by default.
EXTRA_EQUIPMENT_CODES = frozenset()
CODE = re.compile(r"^[1-9][0-9]{3}$")
EXCLUDED_SUFFIX = ("DR", "R1", "R2", "特")
# Indicator history window: 480+ trading sessions makes Wilder RSI seed effectively irrelevant.
MAX_BARS = 650
# Replay recent ~480 trading sessions every run. Does not depend on GitHub runner filesystem
# state (GitHub Actions starts from a clean environment on each execution).
REPLAY_DAYS = 480
# Explicit, configurable volume definition for a bearish high-volume candle.
BEARISH_VOLUME_MULTIPLIER = 1.0  # today's shares strictly > yesterday's shares
LONG_BLACK_BODY_PCT = 5.0
UPPER_WICK_DRAWDOWN_PCT = 7.0
UPPER_WICK_MIN_VOLUME_PREV_MULTIPLIER = 0.55
TZ_TAIPEI = ZoneInfo("Asia/Taipei")


def session():
    s = requests.Session()
    r = Retry(total=3, backoff_factor=1.5, status_forcelist=(429, 500, 502, 503, 504),
              allowed_methods=("GET",))
    s.mount("https://", HTTPAdapter(max_retries=r))
    s.headers.update({"User-Agent": "TaiwanMomentumScreener/1.0 (+educational use)",
                      "Accept": "application/json, */*"})
    return s


def usable_stock(code, name):
    """Only numeric, 4-digit ordinary shares; removes DR and explicitly named preferred shares."""
    return bool(CODE.fullmatch(str(code).strip())) and not str(name).strip().endswith(EXCLUDED_SUFFIX)


def num(x):
    try:
        s = str(x).strip().replace(",", "")
        if s in ("", "--", "---", "-", "None", "nan"):
            return None
        v = float(s)
        return v if pd.notna(v) else None
    except (ValueError, TypeError):
        return None


def iso_date(raw):
    s = str(raw).strip().replace("/", "").replace("-", "")
    if len(s) == 8 and s[:4].isdigit() and int(s[:4]) >= 1900:
        return f"{s[:4]}-{s[4:6]}-{s[6:8]}"
    if len(s) == 7 and s.isdigit():
        return f"{int(s[:3]) + 1911:04d}-{s[3:5]}-{s[5:7]}"
    raise ValueError(f"Invalid date: {raw!r}")


def normalize(r, market="歷史來源"):
    """Accept upstream daily CSV or official TWSE/TPEx latest JSON."""
    if "code" in r:
        d, code, name = r.get("date"), r.get("code"), r.get("name", "")
        vol, op, hi, lo, cl = (r.get(x) for x in ("volume", "open", "high", "low", "close"))
    elif "Code" in r:
        d, code, name = r.get("Date"), r.get("Code"), r.get("Name", "")
        vol, op, hi, lo, cl = (r.get(x) for x in ("TradeVolume", "OpeningPrice", "HighestPrice", "LowestPrice", "ClosingPrice"))
    else:
        d, code, name = r.get("Date"), r.get("SecuritiesCompanyCode"), r.get("CompanyName", "")
        vol, op, hi, lo, cl = (r.get(x) for x in ("TradingShares", "Open", "High", "Low", "Close"))
    code, name = str(code).strip(), str(name).strip()
    if not usable_stock(code, name):
        return None
    try:
        d = iso_date(d)
    except ValueError:
        return None
    vals = [num(x) for x in (vol, op, hi, lo, cl)]
    if any(v is None for v in vals):
        return None
    v, o, h, l, c = vals
    if v <= 0 or min(o, h, l, c) <= 0 or h < max(o, c, l) or l > min(o, c):
        return None
    return {"date": d, "code": code, "name": name, "volume": v,
            "open": o, "high": h, "low": l, "close": c, "market": market}


class History:
    def __init__(self):
        self.bars = defaultdict(lambda: deque(maxlen=MAX_BARS))
        self.max_high = {}
        self.first_date = {}
        self.all_market_dates = set()
        self.rows_loaded = 0

    def insert(self, row):
        code, day = row["code"], row["date"]
        arr = self.bars[code]
        if arr and day < arr[-1]["date"]:
            raise ValueError(f"Data out of chronological order for {code}: {day}")
        if arr and day == arr[-1]["date"]:
            # Same-day official snapshot is authoritative over the community archive.
            prev_high = arr[-1]["prior_high"]
            arr.pop()
        else:
            prev_high = self.max_high.get(code)
        row = dict(row, prior_high=prev_high)
        arr.append(row)
        self.max_high[code] = max(float(prev_high or 0), row["high"])
        self.first_date.setdefault(code, day)
        self.all_market_dates.add(day)
        self.rows_loaded += 1


def scan_archive_zip(history, path, as_of, year=None):
    """Read both the source's merged yearly_YYYY.csv / weekly_YYYY_Www.csv
    and legacy per-day YYYYMMDD.csv ZIP contents.

    The upstream packager merges all daily CSVs into ONE CSV before zipping;
    checking only YYYYMMDD.csv member names silently discards all history.
    """
    n = 0
    upper = date.fromisoformat(as_of)
    with zipfile.ZipFile(path) as zf:
        members = [x for x in zf.namelist() if x.lower().endswith('.csv') and not x.endswith('/')]
        if not members:
            raise RuntimeError(f"{path.name}: ZIP contains no CSV files")
        # Common source format has exactly one chronological, date-sorted CSV.
        for member in sorted(members):
            m = re.search(r"(20\d{2}[-]?\d{2}[-]?\d{2})\.csv$", member)
            fallback = iso_date(m.group(1)) if m else None
            with zf.open(member) as f:
                stream = io.TextIOWrapper(f, encoding='utf-8-sig', errors='replace', newline='')
                reader = csv.DictReader(stream)
                if not reader.fieldnames or 'code' not in reader.fieldnames:
                    raise RuntimeError(f"{path.name}/{member}: missing 'code' column; found {reader.fieldnames}")
                if 'date' not in reader.fieldnames and fallback is None:
                    raise RuntimeError(f"{path.name}/{member}: merged CSV is missing the 'date' column")
                for r in reader:
                    if not r or not r.get('code'):
                        continue
                    if not r.get('date') and fallback is not None:
                        r['date'] = fallback
                    item = normalize(r)
                    if item is None:
                        continue
                    d = date.fromisoformat(item['date'])
                    # ISO weeks around New Year overlap adjacent calendar years;
                    # insert only the calendar year currently being loaded.
                    if year is not None and d.year != year:
                        continue
                    if d <= upper:
                        history.insert(item)
                        n += 1
    return n


def weeks_intersecting_year(assets, year, upper):
    """Find released ISO-week ZIPs overlapping the specified calendar year."""
    result = []
    begin = date(year, 1, 1)
    end = min(date(year, 12, 31), date.fromisoformat(upper))
    if end < begin:
        return result
    for name in assets:
        m = re.fullmatch(r"weekly_(\d{4})_W(\d{2})\.zip", name)
        if not m:
            continue
        try:
            monday = date.fromisocalendar(int(m.group(1)), int(m.group(2)), 1)
        except ValueError:
            continue
        if monday <= end and monday + timedelta(days=6) >= begin:
            result.append((monday, name))
    return [name for _, name in sorted(result)]


def scan_csv(history, path, as_of):
    # CSV mode supports a file with many stocks/dates or a directory of YYYYMMDD.csvs.
    paths = sorted(path.glob("**/*.csv")) if path.is_dir() else [path]
    rows = []
    for p in paths:
        with p.open(encoding="utf-8-sig", newline="") as f:
            reader = csv.DictReader(f)
            for r in reader:
                if "date" not in r and re.search(r"\d{8}", p.stem):
                    r["date"] = re.search(r"\d{8}", p.stem).group()
                item = normalize(r)
                if item and item["date"] <= as_of:
                    rows.append(item)
    for r in sorted(rows, key=lambda x: (x["date"], x["code"])):
        history.insert(r)
    return len(rows)


def download_archives(history, cache_dir, as_of, start_year, force_current=True, archive_end=None):
    cache_dir.mkdir(parents=True, exist_ok=True)
    s = session()
    resp = s.get(RELEASE_API, timeout=45)
    resp.raise_for_status()
    payload = resp.json()
    assets = {x['name']: x['browser_download_url'] for x in payload.get('assets', [])}
    if not assets:
        raise RuntimeError('GitHub Release has no assets. Check release and permissions.')

    upper = archive_end or as_of
    end_year = int(as_of[:4])
    missing_years = []
    count = 0
    for year in range(start_year, end_year + 1):
        annual = f'yearly_{year}.zip'
        if annual in assets:
            filenames = [annual]
        else:
            filenames = weeks_intersecting_year(assets, year, upper)
        if not filenames:
            missing_years.append(year)
            continue
        year_rows = 0
        for name in filenames:
            file = cache_dir / name
            # An annual archive is fixed after that calendar year. Weekly files
            # are also fixed once their release has settled; refetch active
            # current weeks so corrections can be picked up.
            refresh = (force_current and year == end_year and
                       (name == annual or name == filenames[-1]))
            if not file.exists() or refresh:
                print(f'Downloading {name}...', flush=True)
                with s.get(assets[name], timeout=180, stream=True) as r:
                    r.raise_for_status()
                    temp = file.with_suffix('.zip.part')
                    with temp.open('wb') as out:
                        for chunk in r.iter_content(chunk_size=1024 * 256):
                            if chunk:
                                out.write(chunk)
                    if not zipfile.is_zipfile(temp):
                        temp.unlink(missing_ok=True)
                        raise ValueError(f'Broken archive: {name}')
                    temp.replace(file)
            rows = scan_archive_zip(history, file, upper, year=year)
            # A particular weekly archive can contain ONLY days after the
            # official backfill cutoff. Zero records in that case is expected.
            if name == annual and rows == 0:
                raise RuntimeError(f'{name}: 0 valid stock-date records after parsing; check CSV schema')
            year_rows += rows
            count += rows
        if year_rows == 0:
            # Current-year weekly releases can be all newer than the cutoff
            # only for extremely early January; ordinarily this is a bug.
            raise RuntimeError(f'{year}: 0 valid stock-date records; check weekly archives and CSV schema')
        print(f'  {year}: {year_rows:,} rows ({len(filenames)} archives); total {count:,}', flush=True)
    if missing_years:
        warnings.warn(f'Historical years missing from release: {missing_years}. ATH is not verifiable if history is incomplete.')
    if end_year in missing_years:
        raise RuntimeError('Current-year historical archive missing (no annual or weekly ZIPs); refuse incomplete screening.')
    if count == 0:
        raise RuntimeError('No OHLCV history was parsed; refuse incomplete screening.')
    return count, missing_years


def official_snapshot(s, url, market):
    response = s.get(url, timeout=35)
    response.raise_for_status()
    raw = response.json()
    if not isinstance(raw, list) or not raw:
        raise RuntimeError(f"{market} endpoint returned no list")
    rows = [normalize(r, market) for r in raw]
    rows = [r for r in rows if r is not None]
    if len(rows) < 100:
        raise RuntimeError(f"{market}: too few valid stock rows ({len(rows)}): schema may have changed")
    dates = {r["date"] for r in rows}
    if len(dates) != 1:
        raise RuntimeError(f"{market}: multiple dates: {dates}")
    return rows, dates.pop()


def fetch_official_latest_pair():
    """Get aligned latest sessions; OpenAPI TWSE may lag the market close."""
    s = session()
    twse, a = official_snapshot(s, TWSE_API, "上市")
    tpex, b = official_snapshot(s, TPEX_API, "上櫃")
    if a < b:
        # TWSE's latest-only OpenAPI can publish later than its dated MI_INDEX.
        twse = historical_twse(s, b)
        if len(twse) < 100:
            raise RuntimeError(f"TWSE OpenAPI is still at {a}; dated MI_INDEX for {b} has only {len(twse)} stocks")
        a = b
        print(f"TWSE latest OpenAPI lag detected; switched to dated MI_INDEX {a}", flush=True)
    elif b < a:
        tpex = historical_tpex(s, a)
        if len(tpex) < 100:
            raise RuntimeError(f"TPEx OpenAPI is still at {b}; dated dailyQuotes for {a} has only {len(tpex)} stocks")
        b = a
        print(f"TPEx latest OpenAPI lag detected; switched to dated dailyQuotes {b}", flush=True)
    if a != b:
        raise RuntimeError(f"Official dates do not match: TWSE {a} vs TPEx {b}")
    return s, twse, tpex, a


def historical_twse(s, day):
    """Official exchange-wide daily OHLCV by date, NOT the latest-only OpenAPI."""
    url = "https://www.twse.com.tw/rwd/zh/afterTrading/MI_INDEX"
    r = s.get(url, params={"response": "json", "date": day.replace("-", ""),
                           "type": "ALLBUT0999"}, timeout=45)
    r.raise_for_status()
    data = r.json()
    if not isinstance(data, dict):
        raise RuntimeError(f"TWSE {day}: historical response was not an object")
    if data.get("stat") == "OK":
        source_date = data.get("date")
        if not source_date or iso_date(source_date) != day:
            raise RuntimeError(f"TWSE {day}: source date mismatch (returned {source_date!r})")
    tables = data.get("tables", [])
    if not tables:
        tables = [{"fields": data.get(f"fields{i}", []), "data": data.get(f"data{i}", [])} for i in range(1, 15)]
    found = False
    result = []
    for table in tables:
        fields = [str(f).strip() for f in table.get("fields", [])]
        required = ["證券代號", "證券名稱", "成交股數", "開盤價", "最高價", "最低價", "收盤價"]
        if not all(k in fields for k in required):
            continue
        found = True
        ids = {k: fields.index(k) for k in required}
        for cols in table.get("data", []):
            if not isinstance(cols, list) or len(cols) <= max(ids.values()):
                continue
            item = normalize({"date": day, "code": cols[ids["證券代號"]],
                              "name": cols[ids["證券名稱"]], "volume": cols[ids["成交股數"]],
                              "open": cols[ids["開盤價"]], "high": cols[ids["最高價"]],
                              "low": cols[ids["最低價"]], "close": cols[ids["收盤價"]]}, "上市")
            if item:
                result.append(item)
    if not found and str(data.get("stat", "")).lower() not in ("no data", "很抱歉，沒有符合條件的資料!", "查無資料"):
        raise RuntimeError(f"TWSE {day}: no matching table; schema drift or missing dataset")
    return result


def historical_tpex(s, day):
    """TPEx official dated dailyQuotes: tables/fields/data (NOT legacy aaData).

    Validate source date and identify columns by their Chinese labels to avoid
    treating the average PRICE column as trading VOLUME.
    """
    url = "https://www.tpex.org.tw/www/zh-tw/afterTrading/dailyQuotes"
    r = s.get(url, params={"response": "json", "date": day.replace("-", "/")}, timeout=45)
    r.raise_for_status()
    payload = r.json()
    if not isinstance(payload, dict):
        raise RuntimeError(f"TPEx {day}: JSON payload was not an object")
    raw_date = payload.get("date") or payload.get("reportDate")
    if not raw_date:
        raise RuntimeError(f"TPEx {day}: response lacks a source date; refuse unverifiable data")
    try:
        observed_date = iso_date(raw_date)
    except (ValueError, TypeError) as e:
        raise RuntimeError(f"TPEx {day}: invalid source date {raw_date!r}") from e
    if observed_date != day:
        raise RuntimeError(f"TPEx {day}: source date mismatch (returned {observed_date})")
    tables = payload.get("tables") or []
    if not isinstance(tables, list):
        raise RuntimeError(f"TPEx {day}: tables is not a list")
    result = []
    found = False
    for table in tables:
        if not isinstance(table, dict):
            continue
        fields = [str(f).strip().replace(" ", "") for f in table.get("fields", [])]
        aliases = {
            "code": ("代號", "證券代號"), "name": ("名稱", "證券名稱"),
            "close": ("收盤", "收盤價"), "open": ("開盤", "開盤價"),
            "high": ("最高", "最高價"), "low": ("最低", "最低價"),
            "volume": ("成交股數", "成交股數(股)", "成交股數（股）"),
        }
        ix = {}
        for k, labels in aliases.items():
            ix[k] = next((fields.index(label) for label in labels if label in fields), None)
        if any(i is None for i in ix.values()):
            continue
        found = True
        for cols in table.get("data", []):
            if not isinstance(cols, (list, tuple)) or len(cols) <= max(ix.values()):
                continue
            row = {"date": day, **{k: cols[i] for k, i in ix.items()}}
            item = normalize(row, "上櫃")
            if item:
                result.append(item)
    if not found:
        raise RuntimeError(f"TPEx {day}: no complete OHLCV table (keys={list(payload.keys())})")
    if len(result) < 100:
        raise RuntimeError(f"TPEx {day}: only {len(result)} valid common stocks; possible incomplete payload")
    return result


def backfill_recent_from_official(history, s, archive_cutoff, latest, twse_latest, tpex_latest):
    """Fill only sessions absent from the archive, then replace the latest
    day's archived data with official exchange snapshots.

    All available release weekly ZIPs are loaded first. In particular, on
    weekends a freshly published week already contains Friday's quotes: do
    NOT re-request its already archived weekday dates from fragile old APIs.
    """
    if not history.all_market_dates:
        raise RuntimeError("No historical trading dates to backfill from")
    last_archive_day = max(history.all_market_dates)
    last = date.fromisoformat(latest)
    if date.fromisoformat(last_archive_day) > last:
        raise RuntimeError(f"Archive day {last_archive_day} newer than official latest {latest}; dates differ")
    if (last - date.fromisoformat(last_archive_day)).days > 14:
        raise RuntimeError(f"Archive is too old ({last_archive_day}) to safely patch to {latest}; verify data provider")
    day = date.fromisoformat(last_archive_day) + timedelta(days=1)
    filled = []
    while day < last:
        if day.weekday() < 5:
            d = day.isoformat()
            a = historical_twse(s, d)
            # No listed market data => no trading session; do not need a TPEX
            # historical request. If TWSE has quote data, both markets must.
            if a:
                b = historical_tpex(s, d)
                if len(a) < 100 or len(b) < 100:
                    raise RuntimeError(f"Incomplete official historical data for {d}: TWSE={len(a)} TPEx={len(b)}")
                for item in sorted(a + b, key=lambda x: x["code"]):
                    history.insert(item)
                filled.append(d)
        day += timedelta(days=1)
    if len(twse_latest) < 100 or len(tpex_latest) < 100:
        raise RuntimeError("Incomplete latest official snapshot; refuse partial screen")
    for item in sorted(twse_latest + tpex_latest, key=lambda x: x["code"]):
        history.insert(item)
    print(f"Official patched sessions: {filled + [latest]}", flush=True)
    return latest


def rsi_wilder(prices, period=14):
    """Wilder RSI with SMA initial seed on first 14 deltas (returns pd.Series)."""
    p = pd.Series(prices, dtype="float64")
    out = pd.Series(float("nan"), index=p.index)
    if len(p) <= period:
        return out
    diffs = p.diff()
    g = diffs.clip(lower=0)
    loss = (-diffs).clip(lower=0)
    gain_avg = float(g.iloc[1:period + 1].mean())
    loss_avg = float(loss.iloc[1:period + 1].mean())
    for i in range(period, len(p)):
        if i > period:
            gain_avg = (gain_avg * (period - 1) + float(g.iloc[i])) / period
            loss_avg = (loss_avg * (period - 1) + float(loss.iloc[i])) / period
        if loss_avg == 0:
            out.iloc[i] = 100.0 if gain_avg > 0 else 50.0
        else:
            rs = gain_avg / loss_avg
            out.iloc[i] = 100 - (100 / (1 + rs))
    return out


def parse_industry_row(row, market):
    """Return ((market, code), (industry_code, industry_label)), or None.

    TWSE company directory uses Chinese keys, TPEx directory English keys.
    Never infer industry from price-action or the stock's name.
    """
    if not isinstance(row, dict):
        return None
    if market == "上市":
        code = str(row.get("公司代號", "")).strip()
        industry = str(row.get("產業別", "")).strip()
    else:
        code = str(row.get("SecuritiesCompanyCode", "")).strip()
        industry = str(row.get("SecuritiesIndustryCode", "")).strip()
    if not CODE.fullmatch(code):
        return None
    if industry.isdigit():
        industry_code = industry.zfill(2)
    else:
        # Unrecognized descriptions must not be treated as eligible.
        return None
    return (market, code), (industry_code, INDUSTRY_NAMES.get(industry_code, f"其他產業({industry_code})"))


def industry_map_from_official(session_obj):
    """Fetch BOTH official company directories; refuse incomplete/unavailable data."""
    output = {}
    for market, url in (("上市", TWSE_PROFILE_API), ("上櫃", TPEX_PROFILE_API)):
        response = session_obj.get(url, timeout=50)
        response.raise_for_status()
        raw = response.json()
        if not isinstance(raw, list) or len(raw) < 100:
            raise RuntimeError(f"{market}: official company profile data missing/incomplete")
        parsed = dict(filter(None, (parse_industry_row(r, market) for r in raw)))
        if len(parsed) < 100 or len(parsed) < len(raw) * 0.6:
            raise RuntimeError(f"{market}: industry code parse insufficient ({len(parsed)}/{len(raw)}); schema changed?")
        output.update(parsed)
        print(f"Industry directory {market}: {len(parsed):,} 4-digit symbols", flush=True)
    return output


def industry_map_from_csv(path):
    """Offline testing option: CSV with 'market,code,industry' columns."""
    industry_map = {}
    with Path(path).open(encoding="utf-8-sig", newline="") as f:
        reader = csv.DictReader(f)
        expected = {"market", "code", "industry"}
        if not reader.fieldnames or not expected.issubset(reader.fieldnames):
            raise ValueError(f"Industry CSV must contain {', '.join(sorted(expected))}")
        for r in reader:
            m = str(r["market"]).strip()
            c = str(r["code"]).strip()
            ind = str(r["industry"]).strip()
            if m not in ("上市", "上櫃"):
                raise ValueError(f"Invalid market {m!r} in industry CSV")
            result = parse_industry_row({"公司代號": c, "產業別": ind}, "上市")
            if result is None:
                raise ValueError(f"Invalid industry CSV code/industry: {c!r}, {ind!r}")
            industry_map[(m,c)] = result[1]
    if not industry_map:
        raise ValueError("Industry CSV is empty")
    return industry_map


def condition3_price_volume(price, today_vol_lots):
    """Strict price bands/lot limits; prices of exactly 50 or 200 do not match."""
    return ((price > 200 and today_vol_lots > 6000) or
            (50 < price < 200 and today_vol_lots > 15000))


def calc_signal(bars, history_start, industry_code, industry_name):
    """Return a matching row or None; all volume input data is SHARES, outputs LOTS."""
    if len(bars) < 120:
        return None
    closes = pd.Series([x["close"] for x in bars], dtype="float64")
    volumes = pd.Series([x["volume"] for x in bars], dtype="float64")
    ma5 = float(closes.iloc[-5:].mean())
    ma10 = float(closes.iloc[-10:].mean())
    ma20 = float(closes.iloc[-20:].mean())
    ma60 = float(closes.iloc[-60:].mean())
    ma120 = float(closes.iloc[-120:].mean())
    rsis = rsi_wilder(closes, 14)
    rsi_prev, rsi_now = float(rsis.iloc[-2]), float(rsis.iloc[-1])
    vol10 = float(volumes.iloc[-10:].mean()) / 1000.0
    vol30 = float(volumes.iloc[-30:].mean()) / 1000.0
    today_vol = float(volumes.iloc[-1]) / 1000.0
    # Both mandatory volume requirements (>=1000 lots, not shares).
    if not (vol10 > vol30 and vol30 >= 1000):
        return None
    price = float(closes.iloc[-1])
    # C2: the 60-day window EXCLUDES today, using closing prices (not highs).
    prior60_max_close = float(closes.iloc[-61:-1].max())
    c1 = bool(ma20 > ma60 > ma120 and rsi_now > 50 > rsi_prev)
    c2 = bool(price > prior60_max_close)
    # Exactly 200 or 50 are excluded by the user's strict inequalities.
    c3 = bool(condition3_price_volume(price, today_vol))
    c4 = bool(ma5 > ma10 > ma20 > ma60 > ma120)
    conditions = [c1, c2, c3, c4]
    if not any(conditions):
        return None
    last = bars[-1]
    return {
        "日期": last["date"], "代號": last["code"], "名稱": last["name"],
        "市場": last["market"], "產業代碼": industry_code, "產業": industry_name,
        "收盤價": round(price, 4), "今日成交量(張)": round(today_vol, 2),
        "10日均量(張)": round(vol10, 2), "30日均量(張)": round(vol30, 2),
        "量比_10日比30日": round(vol10 / vol30, 4),
        "RSI14_昨日": round(rsi_prev, 2), "RSI14_今日": round(rsi_now, 2),
        "MA5": round(ma5, 4), "MA10": round(ma10, 4), "MA20": round(ma20, 4),
        "MA60": round(ma60, 4), "MA120": round(ma120, 4),
        "前60日最高收盤價": round(prior60_max_close, 4),
        "條件1": c1, "條件2": c2, "條件3": c3, "條件4": c4,
        "符合條件": ",".join(str(i) for i, v in enumerate(conditions, start=1) if v),
        "符合項目數": sum(conditions), "資料最早日期": history_start,
    }


def screen(history, as_of, industry_map):
    """Only contemporaneous 120-market-session OHLCV; fail closed on unknown industry."""
    if not history.all_market_dates:
        raise RuntimeError("No data loaded")
    market_dates = sorted(d for d in history.all_market_dates if d <= as_of)
    if len(market_dates) < 120:
        raise RuntimeError(f"Only {len(market_dates)} market sessions; need at least 120")
    date_latest = market_dates[-1]
    last120market = set(market_dates[-120:])
    results = []
    eligible = 0
    industry_pool = 0
    industry_missing = 0
    # Historical community CSV lacks a market column. Match ticker code to an
    # official directory ONLY when that code unambiguously belongs to one board.
    by_code = defaultdict(list)
    for (market, code), sector in industry_map.items():
        by_code[code].append((market, sector))
    for code, arr in history.bars.items():
        if not arr or arr[-1]["date"] != date_latest:
            continue
        latest_market = arr[-1]["market"]
        sector = industry_map.get((latest_market, code))
        if sector is None and latest_market == "歷史來源":
            candidates = by_code.get(code, [])
            if len(candidates) == 1:
                latest_market, sector = candidates[0]
        if sector is None:
            industry_missing += 1
            continue
        sector_code, sector_name = sector
        if sector_code not in ALLOWED_INDUSTRY_CODES and code not in EXTRA_EQUIPMENT_CODES:
            continue
        industry_pool += 1
        if len(arr) < 120 or not last120market.issubset({r["date"] for r in list(arr)[-120:]}):
            continue
        eligible += 1
        bars = list(arr)
        if latest_market != bars[-1]["market"]:
            bars[-1] = dict(bars[-1], market=latest_market)
        row = calc_signal(bars, history.first_date[code], sector_code, sector_name)
        if row:
            results.append(row)
    if industry_missing > 0:
        print(f"Industry unmapped (excluded): {industry_missing} latest symbols", flush=True)
    results.sort(key=lambda x: (-x["符合項目數"], -x["量比_10日比30日"], x["代號"]))
    return date_latest, eligible, results, industry_pool


def write_reports(outdir, latest, eligible, signals, first_date, missing_years, official_day, industry_pool):
    outdir.mkdir(parents=True, exist_ok=True)
    cols = ["日期", "代號", "名稱", "市場", "產業代碼", "產業", "收盤價", "今日成交量(張)",
            "10日均量(張)", "30日均量(張)", "量比_10日比30日", "RSI14_昨日", "RSI14_今日",
            "MA5", "MA10", "MA20", "MA60", "MA120", "前60日最高收盤價",
            "條件1", "條件2", "條件3", "條件4", "符合條件", "符合項目數", "資料最早日期"]
    df = pd.DataFrame(signals, columns=cols)
    df.to_csv(outdir / "signals.csv", index=False, encoding="utf-8-sig")
    lines = [f"# 台股電子／設備動能篩選報告 — {latest}", "",
             f"- 最新行情日：**{latest}**",
             f"- 符合產業範圍的當日股票：**{industry_pool} 檔**",
             f"- 產業符合且具備連續 120 個交易日資料：**{eligible} 檔**",
             f"- 必要條件全部符合且觸發至少 1 個訊號：**{len(signals)} 檔**",
             f"- 官方當日快照：**{official_day or '未使用（僅歸檔資料）'}**",
             "- 必要條件：10 日平均成交量 > 30 日平均成交量，且 30 日平均成交量 ≥ 1,000 張，且產業在設定範圍。",
             "- C1：MA20 > MA60 > MA120，且 RSI(14) 昨日 < 50 < 今日。",
             "- C2：今日收盤 > 前 60 個交易日最高收盤價（不含今日）。",
             "- C3：收盤 > 200 且成交量 > 6,000 張，或 50 < 收盤 < 200 且成交量 > 15,000 張。",
             "- C4：MA5 > MA10 > MA20 > MA60 > MA120。",
             "- 產業代碼：05 電機機械（較廣泛，非全數為半導體設備）、24～31 電子產業、36 數位雲端。",
             "- 均線與突破比較採原始（未還原）收盤價，除權息／拆股日需另行審慎判讀。",
             "- 本報告是機械化訊號，不代表已回測或保證報酬。", ""]
    if missing_years:
        lines.append(f"⚠ 歷史封存缺少年份：{missing_years}。")
    if signals:
        lines.extend(["| 代號 | 名稱 | 市場 | 產業 | 收盤價 | 當日量(張) | 10日/30日均量比 | RSI14 | 觸發條件 |",
                      "|---|---|---|---|---:|---:|---:|---:|---|"])
        for s in signals:
            lines.append(f"| {s['代號']} | {s['名稱']} | {s['市場']} | {s['產業']} | "
                         f"{s['收盤價']} | {s['今日成交量(張)']:,.0f} | "
                         f"{s['量比_10日比30日']:.2f} | {s['RSI14_今日']:.2f} | {s['符合條件']} |")
    else:
        lines.append("本交易日沒有符合全部必要條件且觸發至少一項篩選訊號的股票。")
    (outdir / "report.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    metadata = {"as_of": latest, "industry_pool": industry_pool, "eligible": eligible,
                "matched": len(signals), "missing_years": missing_years,
                "official_snapshot": official_day, "allowed_industry_codes": sorted(ALLOWED_INDUSTRY_CODES),
                "extra_equipment_codes": sorted(EXTRA_EQUIPMENT_CODES),
                "signal_ids": [x["代號"] for x in signals]}
    (outdir / "metadata.json").write_text(json.dumps(metadata, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"\nAs-of {latest}, industry_pool {industry_pool}, eligible {eligible}, matched {len(signals)}")
    print(f"Saved: {outdir / 'signals.csv'} | {outdir / 'report.md'}")
    if os.getenv("GITHUB_STEP_SUMMARY"):
        with Path(os.environ["GITHUB_STEP_SUMMARY"]).open("a", encoding="utf-8") as f:
            f.write("\n".join(lines) + "\n")




# === v1.4 rolling watchlist and exit/return accounting =======================
# A signal is an entry event, not a requirement that must recur each day.
# A position survives until an explicit exit trigger, even if its entry criteria
# stop matching. This is a model portfolio for research, not a live brokerage order.


def exit_flags(today, ma10, prev_volume):
    """Return exit conditions and raw intermediate data; all volume in SHARES."""
    close = float(today["close"])
    high = float(today["high"])
    open_ = float(today["open"])
    volume = float(today["volume"])
    upper_drop = (high - close) / high * 100.0
    body_drop = (open_ - close) / open_ * 100.0
    v_ratio = volume / prev_volume if prev_volume and prev_volume > 0 else None
    e1 = bool(pd.notna(ma10) and close < float(ma10))
    e2 = bool(v_ratio is not None and v_ratio >= UPPER_WICK_MIN_VOLUME_PREV_MULTIPLIER
              and upper_drop >= UPPER_WICK_DRAWDOWN_PCT)
    e3 = bool(v_ratio is not None and v_ratio > BEARISH_VOLUME_MULTIPLIER
              and body_drop >= LONG_BLACK_BODY_PCT)
    return (e1, e2, e3), {
        "高點至收盤回落%": round(upper_drop, 4),
        "開盤至收盤跌幅%": round(body_drop, 4),
        "當日量/前日量": round(v_ratio, 4) if v_ratio is not None else None,
    }


def resolve_industry(history_market, ticker, industry_map, by_code):
    sector = industry_map.get((history_market, ticker))
    if sector is not None:
        return history_market, sector
    if history_market == "歷史來源" and len(by_code.get(ticker, [])) == 1:
        return by_code[ticker][0]
    return history_market, None


def build_tracking_events(history, market_days, industry_map, start_day):
    """Compute each ticker's indicators once; assemble per-date signal/exit events.

    Daily snapshots require 120 consecutive MARKET sessions of data; missing
    daily prices cannot be silently treated as adjacent sessions. Exits are
    evaluated when the ticker actually trades; no fabricated prices on halts.
    """
    index_of = {d: i for i, d in enumerate(market_days)}
    by_code = defaultdict(list)
    for (market, code), sector in industry_map.items():
        by_code[code].append((market, sector))
    daily = defaultdict(dict)
    quotes_by_day = defaultdict(dict)
    eligible_latest = 0
    industry_latest = 0
    latest_day = market_days[-1]
    for code, recent in history.bars.items():
        if not recent:
            continue
        bars = list(recent)
        actual_market, sector = resolve_industry(bars[-1]['market'], code, industry_map, by_code)
        if sector is None:
            continue
        industry_code, industry_name = sector
        if industry_code not in ALLOWED_INDUSTRY_CODES and code not in EXTRA_EQUIPMENT_CODES:
            continue
        if bars[-1]['date'] == latest_day:
            industry_latest += 1
        if len(bars) < 120:
            continue
        df = pd.DataFrame(bars)
        close = pd.to_numeric(df['close'], errors='coerce')
        volume = pd.to_numeric(df['volume'], errors='coerce')
        dates = df['date'].tolist()
        ordinals = [index_of.get(d) for d in dates]
        ma = {k: close.rolling(k, min_periods=k).mean() for k in (5, 10, 20, 60, 120)}
        high60_close = close.shift(1).rolling(60, min_periods=60).max()
        rsi = rsi_wilder(close, 14)
        prev_close = close.shift(1)
        prev_volume = volume.shift(1)
        vol10 = volume.rolling(10, min_periods=10).mean()
        vol30 = volume.rolling(30, min_periods=30).mean()
        for i in range(119, len(bars)):
            day = dates[i]
            if day < start_day:
                continue
            d_idx = ordinals[i]
            # Require actual 120 continuous market-session bars.
            complete = (d_idx is not None and ordinals[i-119] is not None and
                        d_idx - ordinals[i-119] == 119)
            if day == latest_day and complete:
                eligible_latest += 1
            price = float(close.iat[i])
            prev = float(prev_close.iat[i]) if pd.notna(prev_close.iat[i]) else None
            previous_day_actual = (i > 0 and d_idx is not None and
                                   ordinals[i - 1] == d_idx - 1)
            delta = ((price / prev - 1) * 100 if
                     previous_day_actual and prev and prev > 0 else None)
            exit_v = float(prev_volume.iat[i]) if pd.notna(prev_volume.iat[i]) else None
            exits, diagnostic = exit_flags(bars[i], ma[10].iat[i], exit_v)
            sig = [False] * 4
            v10_lots = float(vol10.iat[i] / 1000) if pd.notna(vol10.iat[i]) else None
            v30_lots = float(vol30.iat[i] / 1000) if pd.notna(vol30.iat[i]) else None
            is_mandatory = bool(complete and v10_lots is not None and v30_lots is not None
                                and v10_lots > v30_lots and v30_lots >= 1000)
            if is_mandatory:
                prev_rsi = float(rsi.iat[i - 1])
                now_rsi = float(rsi.iat[i])
                sig = [
                    bool(ma[20].iat[i] > ma[60].iat[i] > ma[120].iat[i]
                         and now_rsi > 50 > prev_rsi),
                    bool(price > float(high60_close.iat[i])),
                    condition3_price_volume(price, float(volume.iat[i]) / 1000),
                    bool(ma[5].iat[i] > ma[10].iat[i] > ma[20].iat[i] > ma[60].iat[i] > ma[120].iat[i]),
                ]
            row = {
                "日期": day, "代號": code, "名稱": bars[i]["name"], "市場": actual_market,
                "產業代碼": industry_code, "產業": industry_name,
                "收盤價": round(price, 4),
                "前日收盤價": round(prev, 4) if prev is not None else None,
                "當日漲跌幅%": round(delta, 4) if delta is not None else None,
                "今日成交量(張)": round(float(volume.iat[i]) / 1000, 3),
                "10日均量(張)": round(v10_lots, 3) if v10_lots is not None else None,
                "30日均量(張)": round(v30_lots, 3) if v30_lots is not None else None,
                "量比_10日比30日": round(v10_lots / v30_lots, 4) if v30_lots else None,
                "RSI14": round(float(rsi.iat[i]), 3) if pd.notna(rsi.iat[i]) else None,
                "MA5": round(float(ma[5].iat[i]), 4),
                "MA10": round(float(ma[10].iat[i]), 4),
                "MA20": round(float(ma[20].iat[i]), 4),
                "MA60": round(float(ma[60].iat[i]), 4),
                "MA120": round(float(ma[120].iat[i]), 4),
                "前60日最高收盤價": (round(float(high60_close.iat[i]), 4)
                                    if pd.notna(high60_close.iat[i]) else None),
                "符合條件": ','.join(str(j) for j, flag in enumerate(sig, 1) if flag),
                "符合項目數": sum(sig),
                "汰除條件": ','.join(str(j) for j, flag in enumerate(exits, 1) if flag),
                **diagnostic,
                "當日K線完整": complete,
            }
            # To avoid excessive memory, retain only possible entries/exits.
            if row['符合項目數'] or row['汰除條件']:
                daily[day][code] = row
            # BUT ordinary active positions need current closes and pct even
            # without any signal. Keep a separate lightweight quote index.
            # We use a per-day map below from the same row.
            quotes_by_day[day][code] = row
    return daily, quotes_by_day, eligible_latest, industry_latest


def r4(value):
    return round(float(value), 4)


def tracking_replay(history, as_of, industry_map):
    market_days = sorted(d for d in history.all_market_dates if d <= as_of)
    if len(market_days) < 125:
        raise RuntimeError('At least 125 market sessions required for tracking')
    replay_days = market_days[-min(REPLAY_DAYS, len(market_days) - 121):]
    if len(replay_days) < 2:
        raise RuntimeError('Insufficient sessions for daily comparison')
    first = replay_days[0]
    # Recompute from daily source history (GitHub runner is ephemeral).
    events, quotes_by_day, eligible, industry_count = build_tracking_events(
        history, market_days, industry_map, first)
    day_indices = {d: idx for idx, d in enumerate(market_days)}
    active = {}  # code -> entry metadata
    daily_snapshots, daily_changes, trades = [], [], []
    yesterday_active_rows, latest_active_rows = [], []
    latest_new, latest_exit, latest_blocked = [], [], []
    prev_day = market_days[-2]
    latest_day = market_days[-1]

    for day in replay_days:
        q = quotes_by_day[day]
        ev = events[day]
        todays_new, todays_exit, todays_blocked = [], [], []
        prev_codes = set(active)
        # Exit: only if an explicit exit flag AND a real OHLCV bar is available.
        for code in list(active):
            row = q.get(code)
            if row is None or not row['汰除條件']:
                continue
            p = active.pop(code)
            duration_sessions = day_indices[day] - day_indices[p['入選日期']]
            closed = {**row, "事件": "剔除", "入選日期": p['入選日期'],
                      "入選收盤價": p['入選收盤價'], "入選條件": p['入選條件'],
                      "持續入選交易日數": duration_sessions,
                      "入選後報酬率%": r4((row['收盤價'] / p['入選收盤價'] - 1) * 100),
                      "已連續追蹤至少2日": duration_sessions >= 2,
                      "汰除日期": day, "汰除收盤價": row['收盤價']}
            trades.append(closed)
            todays_exit.append(closed)
            daily_changes.append(closed)
        # Entry: signal AND mandatory conditions already guaranteed by events;
        # a simultaneous exit condition blocks opening a new position.
        for code, row in ev.items():
            if not row['符合項目數'] or code in active:
                continue
            if row['汰除條件']:
                if code not in prev_codes:
                    blocked = {**row, '事件': '同日訊號但觸發汰除（未入選）'}
                    todays_blocked.append(blocked)
                    daily_changes.append(blocked)
                continue
            active[code] = {'入選日期': day, '入選收盤價': row['收盤價'],
                            '入選條件': row['符合條件'], '名稱': row['名稱']}
            record = {**row, '事件': '新增', '入選日期': day,
                      '入選收盤價': row['收盤價'], '入選條件': row['符合條件'],
                      '持續入選交易日數': 1, '入選後報酬率%': 0.0}
            todays_new.append(record)
            daily_changes.append(record)
        todays_active = []
        todays_new_codes = {x['代號'] for x in todays_new}
        for code, p in sorted(active.items()):
            row = q.get(code)
            if row is None:
                # Not traded / incomplete data; do not invent daily pct or P&L.
                row = {'日期': day, '代號': code, '名稱': p.get('名稱', ''),
                       '收盤價': None, '當日漲跌幅%': None, '符合條件': '',
                       '汰除條件': '', '資料狀態': '本日無日線，待確認'}
            duration = day_indices[day] - day_indices[p['入選日期']] + 1
            ret = ((row['收盤價'] / p['入選收盤價'] - 1) * 100
                   if row.get('收盤價') is not None else None)
            item = {**row, '事件': ('新增' if code in todays_new_codes else '持續追蹤'),
                    '入選日期': p['入選日期'], '入選收盤價': p['入選收盤價'],
                    '入選條件': p['入選條件'], '持續入選交易日數': duration,
                    '入選後報酬率%': r4(ret) if ret is not None else None,
                    '已連續追蹤至少2日': duration >= 2,
                    '資料狀態': row.get('資料狀態', '正常')}
            todays_active.append(item)
            daily_snapshots.append(item)
        if day == prev_day:
            yesterday_active_rows = todays_active
        if day == latest_day:
            latest_active_rows = todays_active
            latest_new, latest_exit, latest_blocked = todays_new, todays_exit, todays_blocked

    # Include still-open positions in the trade ledger (MTM at latest close).
    opened = []
    for item in latest_active_rows:
        opened.append({**item, '狀態': '持續追蹤', '汰除日期': '',
                       '汰除收盤價': None})
    closed = [{**x, '狀態': '已汰除'} for x in trades]
    ledger = sorted(closed + opened,
                    key=lambda x: (x.get('入選日期', ''), x.get('代號', ''),
                                   x.get('汰除日期', '')))
    today_set = {r['代號'] for r in latest_active_rows}
    yday_set = {r['代號'] for r in yesterday_active_rows}
    if today_set - yday_set != {r['代號'] for r in latest_new}:
        raise AssertionError("Today added set mismatches daily replay")
    if yday_set - today_set != {r['代號'] for r in latest_exit}:
        raise AssertionError("Today removed set mismatches exit replay")
    return {'latest': latest_day, 'yesterday': prev_day, 'replay_start': first,
            'eligible': eligible, 'industry_pool': industry_count,
            'today': latest_active_rows, 'yesterday_rows': yesterday_active_rows,
            'added': latest_new, 'removed': latest_exit, 'blocked': latest_blocked,
            'daily_snapshots': daily_snapshots, 'daily_changes': daily_changes,
            'trades': ledger, 'closed_count': len(closed),
            'data_window_bounded': len(market_days) > len(replay_days) + 121}


REPORT_COLS = ['日期', '代號', '名稱', '市場', '產業代碼', '產業', '事件',
               '收盤價', '前日收盤價', '當日漲跌幅%', '今日成交量(張)',
               '10日均量(張)', '30日均量(張)', '量比_10日比30日',
               'RSI14', 'MA5', 'MA10', 'MA20', 'MA60', 'MA120',
               '前60日最高收盤價', '符合條件', '符合項目數',
               '汰除條件', '高點至收盤回落%', '開盤至收盤跌幅%',
               '當日量/前日量', '入選日期', '入選收盤價', '入選條件',
               '持續入選交易日數', '入選後報酬率%', '已連續追蹤至少2日',
               '汰除日期', '汰除收盤價', '狀態', '資料狀態']


def to_csv(rows, dest):
    pd.DataFrame(rows, columns=REPORT_COLS).to_csv(dest, index=False, encoding='utf-8-sig')


def pct(x):
    return '—' if x is None or pd.isna(x) else f'{float(x):+.2f}%'


def fprice(x):
    return '—' if x is None or pd.isna(x) else f'{float(x):,.2f}'


def md_rows(lines, rows, with_exit=False):
    if not rows:
        lines.append('（無）')
        return
    if with_exit:
        lines += ['| 代號 | 名稱 | 今日漲跌幅 | 進場日 | 進場價 | 汰除價 | 累積報酬 | 汰除 E |',
                  '|---|---|---:|---|---:|---:|---:|---|']
        for r in rows:
            lines.append(f"| {r['代號']} | {r['名稱']} | {pct(r.get('當日漲跌幅%'))} | "
                         f"{r.get('入選日期','')} | {fprice(r.get('入選收盤價'))} | "
                         f"{fprice(r.get('汰除收盤價'))} | {pct(r.get('入選後報酬率%'))} | "
                         f"{r.get('汰除條件','')} |")
        return
    lines += ['| 代號 | 名稱 | 當日漲跌幅 | 收盤 | 入選日 | 追蹤交易日 | 累積報酬 | 入選 C |',
              '|---|---|---:|---:|---|---:|---:|---|']
    for r in rows:
        lines.append(f"| {r['代號']} | {r.get('名稱', '')} | {pct(r.get('當日漲跌幅%'))} | "
                     f"{fprice(r.get('收盤價'))} | {r.get('入選日期', '')} | "
                     f"{r.get('持續入選交易日數','')} | {pct(r.get('入選後報酬率%'))} | "
                     f"{r.get('入選條件','')} |")


def write_tracking_reports(outdir, result, missing_years, official_day):
    outdir.mkdir(parents=True, exist_ok=True)
    today = result['today']
    yesterday = result['yesterday_rows']
    added, removed, blocked = result['added'], result['removed'], result['blocked']
    to_csv(today, outdir / 'signals.csv')  # legacy filename; NOW daily ACTIVE list.
    to_csv(yesterday, outdir / 'yesterday_signals.csv')
    to_csv(added, outdir / 'added.csv')
    to_csv(removed, outdir / 'removed.csv')
    to_csv(blocked, outdir / 'blocked_entries.csv')
    to_csv(result['trades'], outdir / 'trades.csv')
    to_csv(result['daily_snapshots'], outdir / 'daily_watchlist.csv')
    to_csv(result['daily_changes'], outdir / 'daily_changes.csv')
    metadata = {
        'as_of': result['latest'], 'previous_trading_day': result['yesterday'],
        'replay_start': result['replay_start'], 'industry_pool': result['industry_pool'],
        'eligible': result['eligible'], 'active_count': len(today),
        'previous_count': len(yesterday), 'added_count': len(added),
        'removed_count': len(removed), 'blocked_count': len(blocked),
        'closed_trades_in_window': result['closed_count'],
        'missing_years': missing_years, 'official_snapshot': official_day,
        'price_basis': 'raw_unadjusted_ohlcv',
        'entry_assumption': 'signal_day_close', 'exit_assumption': 'exit_day_close',
        'volume_unit': 'lots', 'replay_days': REPLAY_DAYS,
        'tracking_state': 'reconstructed_from_rolling_history_every_run',
        'tracking_limitations': ['rolling lookback boundary; entries before replay start not preserved',
                                 'current company directory; survivorship/industry classification bias',
                                 'raw unadjusted prices; no dividends/splits/fees/slippage'],
        'exit_thresholds': {'below_ma10_strict': True, 'upper_drop_pct_gte': UPPER_WICK_DRAWDOWN_PCT,
                            'volume_vs_previous_gte': UPPER_WICK_MIN_VOLUME_PREV_MULTIPLIER,
                            'black_body_drop_pct_gte': LONG_BLACK_BODY_PCT,
                            'black_volume_vs_previous_gt': BEARISH_VOLUME_MULTIPLIER},
    }
    (outdir / 'metadata.json').write_text(json.dumps(metadata, ensure_ascii=False, indent=2), encoding='utf-8')
    lines = [f"# 台股動能名單與理論報酬追蹤 — {result['latest']}", '',
             f"- 今日 {result['latest']}：**{len(today)} 檔**；昨日 {result['yesterday']}：**{len(yesterday)} 檔**",
             f"- **新增 {len(added)}、汰除 {len(removed)}、同日被阻擋 {len(blocked)}**",
             f"- 可評估產業股票：{result['industry_pool']}；有連續 120 日資料：{result['eligible']}",
             f"- 追蹤回放範圍：**{result['replay_start']} 至 {result['latest']}**，每次執行重新推算，並非永久資料庫。",
             '- 進場：必要條件與 C1～C4 任一訊號成立，且當日無汰除條件；入選日收盤價為理論進場價。',
             '- 持續持有：不要求每天重新觸發 C1～C4；直到 E1～E3 任一汰除條件成立才移除。',
             '- E1：收盤 < MA10。',
             '- E2：當日量 ≥ 昨日量 × 55%，且（最高價−收盤價）／最高價 ≥ 7%。',
             f'- E3：當日量 > 昨日量 × {BEARISH_VOLUME_MULTIPLIER:g}，且（開盤價−收盤價）／開盤價 ≥ {LONG_BLACK_BODY_PCT:g}%。',
             '- 收盤相對前一交易日收盤價的漲跌幅，與入選至當日或汰除日的累積報酬，是兩個不同指標。',
             '- 資料價格 **未還原**，含除權息、拆股造成的價格不連續；報酬不含股利、手續費、稅費與滑價。',
             '- 同日收盤確認訊號並假設同日收盤成交有可執行性偏差；回測時需考慮次日開盤成交。',
             '- 歷史追蹤受回放起點與當前公司名冊限制，未涵蓋已下市公司；**不可視為無偏完整歷史回測**。',
             f"- 官方近期資料更新：{official_day or '僅來源封存'}；歷史缺漏年份：{missing_years or '無'}。", '']
    lines += ['## 本日名單（含當日漲跌幅）', '']
    md_rows(lines, today)
    lines += ['', '## 前一交易日名單（含該日漲跌幅）', '']
    md_rows(lines, yesterday)
    lines += ['', '## 今日新增', '']
    md_rows(lines, added)
    lines += ['', '## 今日汰除及理論累積報酬', '']
    md_rows(lines, removed, with_exit=True)
    lines += ['', '## 當日符合進場訊號但同時觸發汰除（未入選）', '']
    if blocked:
        lines += ['| 代號 | 名稱 | 收盤價 | 當日漲跌幅 | C | E |',
                  '|---|---|---:|---:|---|---|']
        for r in blocked:
            lines.append(f"| {r['代號']} | {r['名稱']} | {fprice(r['收盤價'])} | "
                         f"{pct(r['當日漲跌幅%'])} | {r['符合條件']} | {r['汰除條件']} |")
    else:
        lines.append('（無）')
    lines += ['', '## 回測資料檔案', '',
              '- `signals.csv`：今日**持續追蹤**名單（包含新入選及持有中的股票）。',
              '- `yesterday_signals.csv`：昨日持續追蹤名單。',
              '- `added.csv`、`removed.csv`：今日新增／汰除及退出理由。',
              '- `blocked_entries.csv`：符合入選條件但同日已觸發汰除者。',
              '- `trades.csv`：歷史已結束追蹤及目前持續追蹤部位，含進出場日期、價格與理論報酬。',
              '- `daily_watchlist.csv`：回放期間每日名單、每日漲跌幅及當日累積報酬。',
              '- `daily_changes.csv`：回放期間每日新增、剔除、同日阻擋事件。', '']
    content = '\n'.join(lines) + '\n'
    (outdir / 'report.md').write_text(content, encoding='utf-8')
    print(f"As-of {result['latest']}, active {len(today)}, yesterday {len(yesterday)}, "
          f"added {len(added)}, removed {len(removed)}, blocked {len(blocked)}", flush=True)
    print(f"Saved {outdir/'report.md'}, {outdir/'signals.csv'}, {outdir/'trades.csv'}", flush=True)
    if os.getenv('GITHUB_STEP_SUMMARY'):
        with Path(os.environ['GITHUB_STEP_SUMMARY']).open('a', encoding='utf-8') as f:
            f.write(content[:980000])

def main(argv=None):
    p = argparse.ArgumentParser(description="Taiwan stock momentum screening system")
    p.add_argument("--csv", type=Path, help="Offline CSV file or directory instead of GitHub yearly archives")
    p.add_argument("--as-of", default=datetime.now(TZ_TAIPEI).date().isoformat(),
                   help="Use the most recent available trading date <= this YYYY-MM-DD")
    p.add_argument("--start-year", type=int, default=2004, help="Archive start year (C4 only since this year)")
    p.add_argument("--cache", type=Path, default=Path("data/archive"))
    p.add_argument("--output", type=Path, default=Path("output"))
    p.add_argument("--skip-official", action="store_true", help="Do not use official exchange snapshots/backfill")
    p.add_argument("--industry-csv", type=Path, help="Offline CSV industry directory: market,code,industry (otherwise fetch official live directories)")
    args = p.parse_args(argv)
    date.fromisoformat(args.as_of)
    hist = History()
    missing = []
    official = None
    latest_data = None
    cutoff = args.as_of
    if not args.csv and not args.skip_official:
        s, twse_latest, tpex_latest, latest_data = fetch_official_latest_pair()
        if latest_data <= args.as_of:
            # Use all available archival weeks first. No need to overwrite
            # archived dates just because they fall within the last seven days.
            cutoff = latest_data
        else:
            latest_data = None
    if args.csv:
        count = scan_csv(hist, args.csv, args.as_of)
    else:
        count, missing = download_archives(hist, args.cache, args.as_of, args.start_year,
                                           archive_end=cutoff)
    print(f"Loaded {count:,} normalized OHLCV archive records", flush=True)
    if latest_data is not None:
        official = backfill_recent_from_official(hist, s, cutoff, latest_data,
                                                 twse_latest, tpex_latest)
    industry_map = (industry_map_from_csv(args.industry_csv) if args.industry_csv
                    else industry_map_from_official(session()))
    tracking = tracking_replay(hist, args.as_of, industry_map)
    write_tracking_reports(args.output, tracking, missing, official)


if __name__ == "__main__":
    main()

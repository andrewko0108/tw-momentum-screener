#!/usr/bin/env python3
"""台股上市/上櫃電子與設備股動能訊號＋追蹤報酬掃描器 v1.5.1 (2026)
使用歸檔歷史日線 + 官方行情 + 官方公司產業代碼；判斷規則見 README.md。
依賴: pandas, requests。歷史資料源為第三方公開 GitHub 壓縮檔（源於 TWSE/TPEx）。
"""
from __future__ import annotations

import argparse
import csv
import io
import html
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
TRACKING_START = "2026-10-08"
# Before the start date, 350 trading bars suffice for Wilder RSI convergence;
# retain ALL sessions on/after TRACKING_START to keep the ledger reproducible.
PRESTART_BARS = 350
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



class TemporarySourceError(RuntimeError):
    """A data source did not deliver one COMPLETE, parseable JSON response."""


def fetch_json_reliably(s, url, *, params=None, timeout=55, label="資料來源", attempts=4):
    """Retry a WHOLE JSON response, including mid-body ChunkedEncodingError.

    An HTTPAdapter retry alone cannot recover a transfer that dies while
    requests reads the response body. We retry the idempotent GET from the
    beginning; an incomplete JSON body is NEVER treated as a partial quote.
    Fatal HTTP 4xx errors (except 408/429) are reported immediately.
    """
    last = None
    for attempt in range(1, attempts + 1):
        try:
            # Close the response even when parsing/reading raises mid-stream.
            with s.get(url, params=params, timeout=timeout, stream=True,
                       headers={"Connection": "close", "Cache-Control": "no-cache"}) as response:
                response.raise_for_status()
                # .json() reads the ENTIRE response body. Body truncation can
                # raise ChunkedEncodingError *here*, not at HTTP connect time.
                return response.json()
        except requests.exceptions.HTTPError as exc:
            status = exc.response.status_code if exc.response is not None else None
            if status not in (408, 429, 500, 502, 503, 504):
                raise RuntimeError(f"{label}: HTTP {status}; API may have changed") from exc
            last = exc
        except (requests.exceptions.RequestException, ValueError) as exc:
            # ValueError includes JSONDecodeError from incomplete/malformed JSON.
            last = exc
        if attempt < attempts:
            wait = min(2 ** (attempt - 1), 6)
            print(f"[RETRY {attempt}/{attempts}] {label}: {type(last).__name__}: "
                  f"{str(last)[:160]}; {wait}s later", flush=True)
            time.sleep(wait)
    raise TemporarySourceError(
        f"{label}: failed {attempts} complete JSON fetches "
        f"({type(last).__name__}: {str(last)[:220]})") from last

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
        self.bars = defaultdict(lambda: deque(maxlen=PRESTART_BARS))
        self.max_high = {}
        self.first_date = {}
        self.all_market_dates = set()
        self.rows_loaded = 0

    def insert(self, row):
        code, day = row["code"], row["date"]
        arr = self.bars[code]
        if day >= TRACKING_START and arr.maxlen is not None:
            # GitHub runner files are ephemeral; reconstruct complete tracking
            # history since 2026-10-08, without relying on cache/artifact state.
            arr = deque(arr)
            self.bars[code] = arr
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
    payload = fetch_json_reliably(s, RELEASE_API, timeout=45, label="GitHub historical releases")
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
    raw = fetch_json_reliably(s, url, timeout=55, label=f"{market} latest quote OpenAPI")
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
    try:
        tpex, b = official_snapshot(s, TPEX_API, "上櫃")
    except TemporarySourceError as exc:
        # Only fall back for transient/partial-download problems; a fully
        # returned but invalid market snapshot must still fail validation.
        # The dated endpoint must independently assert its actual trade date.
        print(f"[FALLBACK] TPEx OpenAPI transport unavailable: {exc}", flush=True)
        tpex = historical_tpex(s, a)
        b = a
        if len(tpex) < 100:
            raise RuntimeError(f"TPEx dated dailyQuotes {a}: insufficient quotes ({len(tpex)}); "
                               "refuse partial watchlist")
        print(f"[FALLBACK OK] TPEx official dated dailyQuotes {b}: {len(tpex)} stocks", flush=True)
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
    data = fetch_json_reliably(
        s, url, params={"response": "json", "date": day.replace("-", ""),
                        "type": "ALLBUT0999"}, timeout=55,
        label=f"TWSE historical {day}")
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
    payload = fetch_json_reliably(
        s, url, params={"response": "json", "date": day.replace("-", "/")},
        timeout=55, label=f"TPEx historical {day}")
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
        raw = fetch_json_reliably(
            session_obj, url, timeout=65, label=f"{market} company directory")
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
        ma = {k: close.rolling(k, min_periods=k).mean() for k in (5, 10, 20, 30, 60, 120)}
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
                "MA30": round(float(ma[30].iat[i]), 4),
                "MA10/MA30比": round(float(ma[10].iat[i] / ma[30].iat[i]), 5) if float(ma[30].iat[i]) > 0 else None,
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
    # Strict portfolio inception. Never synthesize positions from 2026-10-07
    # or the rolling-480-day window used in previous versions.
    replay_days = [d for d in market_days if TRACKING_START <= d <= as_of]
    if not replay_days:
        raise RuntimeError(f'No trading sessions on/after {TRACKING_START}; portfolio cannot start')
    first = replay_days[0]
    if first != TRACKING_START:
        raise RuntimeError(f'Missing inception trading day {TRACKING_START}; refuse to invent portfolio baseline')
    # Recompute from daily source history (GitHub runner is ephemeral).
    events, quotes_by_day, eligible, industry_count = build_tracking_events(
        history, market_days, industry_map, first)
    day_indices = {d: idx for idx, d in enumerate(market_days)}
    active = {}  # code -> entry metadata
    daily_snapshots, daily_changes, trades = [], [], []
    yesterday_active_rows, latest_active_rows = [], []
    latest_new, latest_exit, latest_blocked = [], [], []
    prev_day = replay_days[-2] if len(replay_days) > 1 else None
    latest_day = replay_days[-1]

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
            duration_sessions = day_indices[day] - day_indices[p['入選日期']] + 1
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
            'data_window_bounded': False}


REPORT_COLS = ['日期', '代號', '名稱', '市場', '產業代碼', '產業', '事件',
               '收盤價', '前日收盤價', '當日漲跌幅%', '今日成交量(張)',
               '10日均量(張)', '30日均量(張)', '量比_10日比30日',
               'RSI14', 'MA5', 'MA10', 'MA30', 'MA10/MA30比', 'MA20', 'MA60', 'MA120',
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


def ten_session_prices(history, code, as_of, market_days):
    """Exactly the most recent ten *market* sessions, with gaps preserved.

    Prices earlier than TRACKING_START are permitted ONLY for this chart or
    technical indicators, never as a portfolio trade or tracking return.
    """
    window = [d for d in market_days if d <= as_of][-10:]
    prices = {b['date']: float(b['close']) for b in history.bars.get(code, [])}
    return [(d, prices.get(d)) for d in window]


def chart_svg(prices, width=168, height=48):
    """Lightweight no-dependency inline SVG; breaks lines at missing days."""
    if not prices:
        return '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 168 48" width="168" height="48"><text x="8" y="25" fill="#64748b">無資料</text></svg>'
    points = [(i, p) for i, (_d,p) in enumerate(prices) if p is not None]
    if not points:
        return '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 168 48" width="168" height="48"><text x="8" y="25" fill="#64748b">無資料</text></svg>'
    bottom, top = min(p for _,p in points), max(p for _,p in points)
    spread = top - bottom
    margin = max(spread * 0.13, top * 0.002, 0.001)
    low, high = bottom - margin, top + margin
    x_at = lambda i: 7 + (width - 14) * i/max(len(prices)-1, 1)
    y_at = lambda v: 5 + (height - 10) * (high-v)/(high-low)
    # Use a group for each contiguous run, never connect through a suspended day.
    runs = []
    current = []
    for i,(_d,price) in enumerate(prices):
        if price is None:
            if current:
                runs.append(current)
                current=[]
        else:
            current.append((x_at(i),y_at(price)))
    if current:
        runs.append(current)
    color = '#168a67' if points[-1][1] >= points[0][1] else '#c65c50'
    parts = [f'<svg xmlns="http://www.w3.org/2000/svg" role="img" aria-label="最近十個交易日收盤價" viewBox="0 0 {width} {height}" width="{width}" height="{height}">',
             f'<path d="M6,{height-5} H{width-6}" stroke="#e2e8f0" stroke-width="1"/>']
    for run in runs:
        coords=' '.join(f'{x:.2f},{y:.2f}' for x,y in run)
        if len(run)>1:
            parts.append(f'<polyline points="{coords}" fill="none" stroke="{color}" stroke-width="2.3" stroke-linecap="round" stroke-linejoin="round"/>')
        for x,y in run:
            parts.append(f'<circle cx="{x:.2f}" cy="{y:.2f}" r="1.7" fill="{color}"/>')
    parts.append('</svg>')
    return ''.join(parts)


def _safe(x):
    return html.escape(str(x if x is not None else '—'), quote=True)


def _ratio(x):
    return '—' if x is None or pd.isna(x) else f'{float(x):.3f}×'


def _lots(x):
    return '—' if x is None or pd.isna(x) else f'{float(x):,.0f}'


def _rsi(x):
    return '—' if x is None or pd.isna(x) else f'{float(x):.1f}'


def _sort_pnl(rows):
    return sorted(rows, key=lambda r: (-(r['入選後報酬率%']) if r.get('入選後報酬率%') is not None else float('inf'), r['代號']))


def write_tracking_reports(outdir, result, missing_years, official_day, history=None):
    """Three-section Markdown + self-contained HTML dashboard + CSV backtests.

    HTML charts are inline SVG and work by double-clicking report.html offline;
    report.md uses small SVG assets relative to its own folder. A GitHub Actions
    step summary may not resolve artifact-relative images, but its HTML report does.
    """
    outdir.mkdir(parents=True, exist_ok=True)
    today = result['today']
    yesterday = result['yesterday_rows']
    added, removed, blocked = result['added'], result['removed'], result['blocked']
    kept = _sort_pnl([r for r in today if r.get('持續入選交易日數',0)>=2
                      and r.get('入選後報酬率%') is not None])
    to_csv(today, outdir / 'signals.csv')
    to_csv(yesterday, outdir / 'yesterday_signals.csv')
    to_csv(added, outdir / 'added.csv')
    to_csv(removed, outdir / 'removed.csv')
    to_csv(blocked, outdir / 'blocked_entries.csv')
    to_csv(result['trades'], outdir / 'trades.csv')
    to_csv(result['daily_snapshots'], outdir / 'daily_watchlist.csv')
    to_csv(result['daily_changes'], outdir / 'daily_changes.csv')
    to_csv(kept, outdir / 'continuous_returns.csv')
    market_days = sorted(d for d in history.all_market_dates if d <= result['latest']) if history is not None else []
    trends = {r['代號']: ten_session_prices(history, r['代號'], result['latest'], market_days)
              for r in today} if history is not None else {}
    charts = outdir / 'charts'
    charts.mkdir(exist_ok=True)
    for code, prices in trends.items():
        (charts / f'{code}.svg').write_text(chart_svg(prices), encoding='utf-8')
    metadata = {
        'as_of': result['latest'], 'previous_trading_day': result['yesterday'],
        'tracking_start': TRACKING_START, 'replay_start': result['replay_start'],
        'industry_pool': result['industry_pool'], 'eligible': result['eligible'],
        'active_count': len(today), 'previous_count': len(yesterday),
        'added_count': len(added), 'removed_count': len(removed),
        'blocked_count': len(blocked), 'continuous_2plus_count': len(kept),
        'closed_trades_since_start': result['closed_count'],
        'missing_years': missing_years, 'official_snapshot': official_day,
        'price_basis': 'raw_unadjusted_ohlcv',
        'volume_unit': 'lots (1000 shares)',
        'price_ma_ratio': 'MA10/MA30 (closing-price SMA, not volume)',
        'volume_ratio': '10-day/30-day average shares',
        'entry_assumption': 'signal_day_close', 'exit_assumption': 'exit_day_close',
        'tracking_state': 'recomputed from 2026-10-08 every run; no prior portfolio records',
        'tracking_limitations': ['historical data before 2026-10-08 used for technical indicators and 10-session charts only',
                                 'current company directory; survivorship/industry-classification bias',
                                 'raw unadjusted prices; no dividends, splits, fees or slippage',
                                 'signal-day close execution is a hypothetical (non-executable) fill',
                                 'missing daily OHLCV: mark missing return rather than fabricate'],
        'exit_thresholds': {'below_ma10_strict': True,
                            'upper_drop_pct_gte': UPPER_WICK_DRAWDOWN_PCT,
                            'volume_vs_previous_gte': UPPER_WICK_MIN_VOLUME_PREV_MULTIPLIER,
                            'black_body_drop_pct_gte': LONG_BLACK_BODY_PCT,
                            'black_volume_vs_previous_gt': BEARISH_VOLUME_MULTIPLIER},
    }
    (outdir / 'metadata.json').write_text(json.dumps(metadata, ensure_ascii=False, indent=2), encoding='utf-8')

    preface = [f'# 台股動能觀察報告｜{result["latest"]}', '',
               f'資料截止日：**{result["latest"]}**；追蹤起點：**{TRACKING_START}**；'
               f'昨日：**{result["yesterday"] or "起始日，無前一日清單"}**。',
               f'觀察 **{len(today)}** 檔；新增 **{len(added)}** 檔；'
               f'剔除 **{len(removed)}** 檔；連續追蹤至少 2 交易日 **{len(kept)}** 檔。',
               '原始（未還原）日線；僅從 2026/10/08 計算名單和收益。'
               '10 日圖可能包含起點之前的價位作為技術參考。', '']
    summary = preface + ['## 一、觀察清單', '',
        '「觸發條件」為當次**首次入選**的 C1～C4；未汰除即繼續留在觀察名單。'
        'MA10/MA30 為收盤價均線比；另列 10 日／30 日**成交均量比**。', '']
    summary += ['| 代號 | 名稱 | 產業 | 收盤價 | 當日量(張) | MA10/MA30(價) | 10/30日均量比 | RSI14 | 入選觸發 | 今日漲跌幅 | 近10日收盤價走勢 |',
                '|---|---|---|---:|---:|---:|---:|---:|---|---:|---|']
    for r in today:
        code=r['代號']
        spark=f'![{code}走勢](charts/{code}.svg)' if code in trends else '—'
        summary.append(f'| {code} | {r.get("名稱","")} | {r.get("產業", "—")} | '
                       f'{fprice(r.get("收盤價"))} | {_lots(r.get("今日成交量(張)"))} | '
                       f'{_ratio(r.get("MA10/MA30比"))} | {_ratio(r.get("量比_10日比30日"))} | '
                       f'{_rsi(r.get("RSI14"))} | C{str(r.get("入選條件", "")).replace(",", ", C")} | '
                       f'{pct(r.get("當日漲跌幅%"))} | {spark} |')
    if not today:
        summary.append('| — | 無符合或持續追蹤標的 | — | — | — | — | — | — | — | — | — |')
    summary += ['', '## 二、新增、剔除清單', '',
                f'**今日新增：{len(added)} 檔**（當日出現 C1～C4，且未觸發 E1～E3）', '']
    if added:
        summary += ['| 代號 | 名稱 | 收盤價 | 當日漲跌幅 | 入選訊號 |', '|---|---|---:|---:|---|']
        for r in added:
            summary.append(f'| {r["代號"]} | {r["名稱"]} | {fprice(r.get("收盤價"))} | '
                           f'{pct(r.get("當日漲跌幅%"))} | C{r.get("符合條件", "").replace(",", ", C")} |')
    else:
        summary.append('（無）')
    summary += ['', f'**今日剔除：{len(removed)} 檔**（出現 E1～E3 任一條件）', '']
    if removed:
        summary += ['| 代號 | 名稱 | 汰除價 | 當日漲跌幅 | 汰除原因 | 入選日 | 入選至汰除報酬 |',
                    '|---|---|---:|---:|---|---|---:|']
        for r in removed:
            summary.append(f'| {r["代號"]} | {r["名稱"]} | {fprice(r.get("收盤價"))} | '
                           f'{pct(r.get("當日漲跌幅%"))} | E{r.get("汰除條件", "").replace(",", ", E")} | '
                           f'{r.get("入選日期", "")} | {pct(r.get("入選後報酬率%"))} |')
    else:
        summary.append('（無）')
    if blocked:
        summary += ['', f'同日觸發入選與汰除，因此**未入選**：{len(blocked)} 檔（詳 `blocked_entries.csv`）。']
    summary += ['', '## 三、連續收益', '',
                '只列當日仍在觀察清單、**包含入選當日在內已追蹤至少 2 個交易日**的股票；'
                '以入選當日收盤價為理論基準，按累積報酬率由高至低排序。', '']
    if kept:
        summary += ['| 排名 | 代號 | 名稱 | 入選日 | 持續交易日 | 入選收盤價 | 今日收盤價 | 累積漲跌幅 |',
                    '|---:|---|---|---|---:|---:|---:|---:|']
        for rank,r in enumerate(kept,1):
            summary.append(f'| {rank} | {r["代號"]} | {r["名稱"]} | {r["入選日期"]} | '
                           f'{r["持續入選交易日數"]} | {fprice(r.get("入選收盤價"))} | '
                           f'{fprice(r.get("收盤價"))} | {pct(r.get("入選後報酬率%"))} |')
    else:
        summary.append('（尚無追蹤滿兩交易日且有當日行情的股票）')
    summary += ['', '---',
                f'資料來源：第三方 GitHub TWSE/TPEx 歷史行情封存及交易所官方近期行情、公司名冊；'
                f'近期官方更新：{official_day or "未使用"}；歷史封存缺漏年份：{missing_years or "無"}。',
                f'產業範圍內 {result["industry_pool"]} 檔，有完整連續 120 交易日資料 {result["eligible"]} 檔。',
                'E1 收盤價<MA10；E2 當日量≥昨日55%且最高價至收盤回落≥7%；'
                'E3 今日量>昨日量且開盤至收盤跌幅≥5%。',
                '價格未還原，累積漲跌幅不含股利、除權息調整、交易成本；'
                '同日收盤產生訊號並以該收盤價模擬進出場，僅供觀察和研究，不等於可成交績效。']
    content='\n'.join(summary)+'\n'
    (outdir/'report.md').write_text(content, encoding='utf-8')

    # An offline-openable HTML dashboard, with no JS or external dependencies.
    styles="""body{font-family:-apple-system,BlinkMacSystemFont,"Noto Sans TC","Microsoft JhengHei",Arial,sans-serif;background:#f5f7fb;color:#17253a;margin:0}main{max-width:1500px;margin:0 auto;padding:30px 20px 55px}header{margin-bottom:24px}h1{font-size:26px;margin:0 0 8px}h2{font-size:22px;margin:0 0 18px}h3{font-size:16px;margin:22px 0 12px}.sub{color:#63748a;font-size:14px;line-height:1.8}.stats{display:flex;gap:12px;flex-wrap:wrap;margin-top:16px}.stat{background:white;border:1px solid #e3e8ef;border-radius:12px;padding:14px 20px;min-width:118px}.stat b{display:block;font-size:23px}.stat span{font-size:12px;color:#63748a}.panel{background:white;border:1px solid #e3e8ef;border-radius:15px;padding:22px;margin:20px 0;box-shadow:0 1px 3px #18364f12}.tablewrap{overflow-x:auto}table{width:100%;border-collapse:collapse;white-space:nowrap;font-size:13px}th{text-align:left;background:#f3f6fa;color:#5a6b80;font-size:12px;position:sticky;top:0}th,td{padding:11px 10px;border-bottom:1px solid #ebeff4}tr:last-child td{border-bottom:0}.num{text-align:right;font-variant-numeric:tabular-nums}.up{color:#078461;font-weight:600}.down{color:#cd4453;font-weight:600}.muted{color:#8291a3}.pill{border-radius:6px;background:#eaf0fb;padding:4px 6px;color:#325997;font-weight:600}.chart{vertical-align:middle}.empty{color:#7a8898;padding:14px 2px}.note{margin-top:18px;font-size:12px;color:#64748b;line-height:1.75}.mini{font-size:12px;color:#6b7a8b;margin-top:8px}footer{color:#64748b;font-size:12px;line-height:1.8;padding:5px 0}@media(max-width:700px){main{padding:16px 10px}.panel{padding:16px 10px}h1{font-size:21px}h2{font-size:19px}}"""
    def color_pct(x):
        if x is None or pd.isna(x):
            return '<span class="muted">—</span>'
        c = 'up' if float(x)>0 else ('down' if float(x)<0 else 'muted')
        return f'<span class="{c}">{_safe(pct(x))}</span>'
    def table(headers, body_rows):
        if not body_rows:
            return '<div class="empty">（無）</div>'
        return '<div class="tablewrap"><table><thead><tr>'+''.join(f'<th>{_safe(h)}</th>' for h in headers)+'</tr></thead><tbody>'+''.join('<tr>'+''.join(f'<td class="{("num" if i in number_cols else "")}">{cell}</td>' for i,cell in enumerate(row))+'</tr>' for row,number_cols in body_rows)+'</tbody></table></div>'
    watch_rows=[]
    for r in today:
        code=r['代號']
        seq=trends.get(code,[])
        tooltip='；'.join(f'{d}: {fprice(v)}' for d,v in seq)
        chart=('<div class="chart" title="'+_safe(tooltip)+'">'+chart_svg(seq)+'</div>') if seq else '—'
        watch_rows.append(([_safe(code),_safe(r.get('名稱')),_safe(r.get('產業')),
            _safe(fprice(r.get('收盤價'))),_safe(_lots(r.get('今日成交量(張)'))),
            _safe(_ratio(r.get('MA10/MA30比'))),_safe(_ratio(r.get('量比_10日比30日'))),
            _safe(_rsi(r.get('RSI14'))),'<span class="pill">'+_safe('C'+str(r.get('入選條件','')).replace(',', ', C'))+'</span>',
            color_pct(r.get('當日漲跌幅%')),chart], {3,4,5,6,7,9}))
    new_rows=[([_safe(r['代號']),_safe(r['名稱']),_safe(fprice(r.get('收盤價'))),
             color_pct(r.get('當日漲跌幅%')),_safe('C'+r.get('符合條件','').replace(',',', C'))], {2,3}) for r in added]
    removed_rows=[([_safe(r['代號']),_safe(r['名稱']),_safe(fprice(r.get('收盤價'))),
                  color_pct(r.get('當日漲跌幅%')),_safe('E'+r.get('汰除條件','').replace(',',', E')),
                  _safe(r.get('入選日期','')),color_pct(r.get('入選後報酬率%'))], {2,3,6}) for r in removed]
    profits=[([_safe(rank),_safe(r['代號']),_safe(r['名稱']),_safe(r.get('入選日期')),
              _safe(r.get('持續入選交易日數')),_safe(fprice(r.get('入選收盤價'))),
              _safe(fprice(r.get('收盤價'))),color_pct(r.get('入選後報酬率%'))], {0,4,5,6,7}) for rank,r in enumerate(kept,1)]
    body=[f'<!doctype html><html lang="zh-Hant"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>台股動能追蹤 {result["latest"]}</title><style>{styles}</style></head><body><main>',
          '<header><h1>台股動能追蹤儀表板</h1>',f'<div class="sub">資料截止日：{_safe(result["latest"])}　｜　追蹤起點：{TRACKING_START}　｜　前一交易日：{_safe(result["yesterday"] or "無")}</div>',
          '<div class="stats">'+''.join(f'<div class="stat"><b>{num}</b><span>{label}</span></div>' for num,label in [(len(today),'觀察標的'),(len(added),'今日新增'),(len(removed),'今日剔除'),(len(kept),'追蹤滿2日')])+'</div></header>',
          '<section class="panel"><h2>一、觀察清單</h2><p class="sub">觸發條件是當次入選時的 C1～C4；折線圖是最近 10 個市場交易日的收盤價。</p>',
          table(['代號','名稱','產業','收盤價','成交量(張)','MA10/MA30 價比','10/30日均量比','RSI(14)','觸發條件','今日漲跌幅','近10日收盤價'],watch_rows),'</section>',
          '<section class="panel"><h2>二、新增、剔除清單</h2>',f'<h3>今日新增（{len(added)}）</h3>',
          table(['代號','名稱','收盤價','今日漲跌幅','入選 C'],new_rows),f'<h3>今日剔除（{len(removed)}）</h3>',
          table(['代號','名稱','汰除價','今日漲跌幅','汰除 E','原入選日','累積報酬'],removed_rows),
          f'<p class="mini">同日符合入選與汰除（未納入）：{len(blocked)} 檔，詳 blocked_entries.csv。</p></section>',
          '<section class="panel"><h2>三、連續收益</h2><p class="sub">僅包含目前仍在觀察清單、連續追蹤至少兩個交易日，且當日有收盤價的標的；依累積漲跌幅降冪排序。</p>',
          table(['排名','代號','名稱','入選日','追蹤交易日','入選價','今日收盤','累積漲跌幅'],profits),'</section>',
          '<footer>價格使用原始未還原日線，理論進出場以訊號日收盤價計算，不含股利、手續費、交易稅與滑價。'+
          f'資料來源：第三方 TWSE／TPEx 封存與交易所官方行情；近期官方更新：{_safe(official_day or "未使用")}；歷史缺漏年份：{_safe(missing_years or "無")}。'+
          f'範圍內 {result["industry_pool"]} 檔、連續120日資料完整 {result["eligible"]} 檔；獨立研究用途。</footer></main></body></html>']
    (outdir/'report.html').write_text(''.join(body), encoding='utf-8')
    print(f'As-of {result["latest"]}, active {len(today)}, added {len(added)}, removed {len(removed)}, 2-day+ {len(kept)}',flush=True)
    print(f'Saved {outdir/"report.html"}, {outdir/"report.md"}, {outdir/"trades.csv"}',flush=True)
    if os.getenv('GITHUB_STEP_SUMMARY'):
        # Github job summaries cannot reliably reference images inside artifacts.
        # The offline report.html contains fully embedded line charts.
        with Path(os.environ['GITHUB_STEP_SUMMARY']).open('a',encoding='utf-8') as f:
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
    write_tracking_reports(args.output, tracking, missing, official, hist)


if __name__ == "__main__":
    main()

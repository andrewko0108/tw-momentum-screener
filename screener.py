#!/usr/bin/env python3
"""台股上市/上櫃動能訊號掃描器 (2026)
使用歸檔歷史日線 + 交易所當日行情；判斷規則見 README.md。
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
CODE = re.compile(r"^[1-9][0-9]{3}$")
EXCLUDED_SUFFIX = ("DR", "R1", "R2", "特")
# Indicator history window: 480+ trading sessions makes Wilder RSI seed effectively irrelevant.
MAX_BARS = 500
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


def calc_signal(bars, history_start):
    """Return a screen row or None. This evaluates the *latest* bar of one ticker."""
    if len(bars) < 241:  # 240MA yesterday needs at least 241 trading bars
        return None
    closes = pd.Series([x["close"] for x in bars], dtype="float64")
    volumes = pd.Series([x["volume"] for x in bars], dtype="float64")
    ma20 = closes.rolling(20).mean()
    ma60 = closes.rolling(60).mean()
    ma120 = closes.rolling(120).mean()
    ma240 = closes.rolling(240).mean()
    rsis = rsi_wilder(closes, 14)
    vol3, vol12 = volumes.tail(3).mean(), volumes.tail(12).mean()
    must = vol3 > vol12
    if not must:
        return None
    a, b = float(rsis.iloc[-2]), float(rsis.iloc[-1])
    cond1 = (ma120.iloc[-1] > ma120.iloc[-2] and ma240.iloc[-1] > ma240.iloc[-2]
             and a <= 30 < b)
    cond2 = ma20.iloc[-1] > ma60.iloc[-1] and a <= 45 < b
    cond3 = ma20.iloc[-2] <= ma60.iloc[-2] and ma20.iloc[-1] > ma60.iloc[-1]
    v10prev = float(volumes.iloc[-11:-1].mean())
    prev_high = bars[-1]["prior_high"]
    cond4 = prev_high is not None and volumes.iloc[-1] > v10prev and closes.iloc[-1] > prev_high
    conditions = [bool(cond1), bool(cond2), bool(cond3), bool(cond4)]
    if not any(conditions):
        return None
    latest = bars[-1]
    return {
        "日期": latest["date"], "代號": latest["code"], "名稱": latest["name"],
        "市場": latest["market"], "收盤價": round(float(closes.iloc[-1]), 4),
        "今日成交量(張)": round(float(volumes.iloc[-1] / 1000), 2),
        "3日均量(張)": round(float(vol3 / 1000), 2),
        "12日均量(張)": round(float(vol12 / 1000), 2),
        "量比_3日比12日": round(float(vol3 / vol12), 4),
        "RSI14_昨日": round(a, 2), "RSI14_今日": round(b, 2),
        "MA20": round(float(ma20.iloc[-1]), 4), "MA60": round(float(ma60.iloc[-1]), 4),
        "MA120": round(float(ma120.iloc[-1]), 4), "MA240": round(float(ma240.iloc[-1]), 4),
        "歷史前高(盤中)": round(float(prev_high), 4) if prev_high else "",
        "前10日均量(張)": round(v10prev / 1000, 2),
        "條件1": conditions[0], "條件2": conditions[1], "條件3": conditions[2], "條件4": conditions[3],
        "符合條件": ",".join(str(i) for i, v in enumerate(conditions, start=1) if v),
        "符合項目數": sum(conditions),
        "資料最早日期": history_start,
    }


def screen(history, as_of):
    if not history.all_market_dates:
        raise RuntimeError("No data loaded")
    date_latest = max(d for d in history.all_market_dates if d <= as_of)
    result = []
    eligible = 0
    # Volume 3/12 windows must refer to the same 12 market sessions;
    # avoid silently using 12 older active bars when a stock was suspended.
    last12market = set(sorted(d for d in history.all_market_dates if d <= date_latest)[-12:])
    for code, arr in history.bars.items():
        if not arr or arr[-1]["date"] != date_latest:
            continue
        if len(arr) < 241 or not last12market.issubset({r["date"] for r in list(arr)[-12:]}):
            continue
        eligible += 1
        x = calc_signal(list(arr), history.first_date[code])
        if x:
            result.append(x)
    result.sort(key=lambda x: (-x["符合項目數"], -x["量比_3日比12日"], x["代號"]))
    return date_latest, eligible, result


def write_reports(outdir, latest, eligible, signals, first_date, missing_years, official_day):
    outdir.mkdir(parents=True, exist_ok=True)
    cols = ["日期", "代號", "名稱", "市場", "收盤價", "今日成交量(張)", "3日均量(張)", "12日均量(張)",
            "量比_3日比12日", "RSI14_昨日", "RSI14_今日", "MA20", "MA60", "MA120", "MA240",
            "歷史前高(盤中)", "前10日均量(張)", "條件1", "條件2", "條件3", "條件4", "符合條件", "符合項目數", "資料最早日期"]
    df = pd.DataFrame(signals, columns=cols)
    df.to_csv(outdir / "signals.csv", index=False, encoding="utf-8-sig")
    lines = [f"# 台股動能篩選報告 — {latest}", "",
             f"- 最近行情日：**{latest}**", f"- 具備足夠歷史資料並於該日有交易的股票：**{eligible} 檔**",
             f"- 必要條件＋至少一項選擇條件：**{len(signals)} 檔**",
             f"- 本次官方快照日期：**{official_day or '未使用（僅歸檔資料）'}**",
             f"- 歷史資料源最早年份：**{first_date[:4] if first_date else '未知'}**",
             "- C4 的歷史最高價僅依實際取得的原始（未還原）歷史日線判斷，不可視為已驗證上市以來最高價。",
             "- 此報告為機械訊號，並非經過回測證實的獲利策略。", ""]
    if missing_years:
        lines.append(f"⚠ 缺少年份 {missing_years}，因此 C4 歷史高判斷可能不完整。")
    if signals:
        lines.extend(["| 代號 | 名稱 | 市場 | 收盤價 | 成交量比(3/12) | RSI14 | 觸發條件 |",
                      "|---|---|---|---:|---:|---:|---|"])
        for s in signals:
            lines.append(f"| {s['代號']} | {s['名稱']} | {s['市場']} | {s['收盤價']} | {s['量比_3日比12日']:.2f} | {s['RSI14_今日']:.2f} | {s['符合條件']} |")
    else:
        lines.append("沒有同時通過必要條件和任一選擇條件的股票。")
    (outdir / "report.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    metadata = {"as_of": latest, "eligible": eligible, "matched": len(signals), "missing_years": missing_years,
                "official_snapshot": official_day, "signal_ids": [x["代號"] for x in signals]}
    (outdir / "metadata.json").write_text(json.dumps(metadata, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"\nAs-of {latest}, eligible {eligible}, matched {len(signals)}")
    print(f"Saved: {outdir / 'signals.csv'} | {outdir / 'report.md'}")
    if os.getenv("GITHUB_STEP_SUMMARY"):
        with Path(os.environ["GITHUB_STEP_SUMMARY"]).open("a", encoding="utf-8") as f:
            f.write("\n".join(lines) + "\n")


def main(argv=None):
    p = argparse.ArgumentParser(description="Taiwan stock momentum screening system")
    p.add_argument("--csv", type=Path, help="Offline CSV file or directory instead of GitHub yearly archives")
    p.add_argument("--as-of", default=datetime.now(TZ_TAIPEI).date().isoformat(),
                   help="Use the most recent available trading date <= this YYYY-MM-DD")
    p.add_argument("--start-year", type=int, default=2004, help="Archive start year (C4 only since this year)")
    p.add_argument("--cache", type=Path, default=Path("data/archive"))
    p.add_argument("--output", type=Path, default=Path("output"))
    p.add_argument("--skip-official", action="store_true", help="Do not use official exchange snapshots/backfill")
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
    latest, eligible, matches = screen(hist, args.as_of)
    start_date = min(hist.all_market_dates) if hist.all_market_dates else None
    write_reports(args.output, latest, eligible, matches, start_date, missing, official)


if __name__ == "__main__":
    main()

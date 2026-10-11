# 台股動能訊號自動篩選系統

這份程式會掃描上市、上櫃 **四碼普通股**，只輸出「最近三日平均成交量 > 最近十二個交易日平均成交量，且 C1～C4 任意一項成立」的個股，逐一列出每個條件的 True/False。包含篩選日、股價、均量比、RSI(14)、均線與歷史前高。沒有真正執行盤後資料掃描時，不會捏造篩選名單。

## 條件（針對收盤資料）

| 名稱 | 判斷 |
|---|---|
| 必要 | 近 3 日（含當日）平均成交股數 > 近 12 日（含當日）平均成交股數 |
| C1 | `MA120_t > MA120_{t-1}` 且 `MA240_t > MA240_{t-1}` 且 `RSI_{t-1} <= 30 < RSI_t` |
| C2 | `MA20_t > MA60_t` 且 `RSI_{t-1} <= 45 < RSI_t` |
| C3 | `MA20_{t-1} <= MA60_{t-1}` 且 `MA20_t > MA60_t` |
| C4 | `Vol_t > mean(Vol_{t-10},...,Vol_{t-1})` 且 `Close_t > max(High_before_t)` |

MA 均為 SMA；RSI 採 14 日 Wilder 平滑法（首 14 個漲跌幅平均初始化）；成交量來源為**股**，輸出換算為**張**。資料若不足 241 根 K 棒（240MA 的當日和前日），不會進入篩選。零成交、無有效收盤價、最近交易日未交易，或最近 12 個市場交易日中缺少 K 棒的股票不會被列入。

注意 C4 的歷史高以 **資料來源能取得的最早 OHLCV 到前一交易日** 做比較。此資料集從 2004 年左右開始，不能聲稱對 2004 年之前已上市的公司完成真正「上市以來」新高查核。使用「未還原」的歷史股價，除權、除息、分割與併股會影響均線與歷史高點。如果需嚴格可比的歷史價或真正上市以來最高價，必須再接公司行動調整及早期資料源。

## 立即在電腦執行

1. 安裝 Python 3.12（Windows 終端機也適用），解壓此壓縮檔，於該資料夾中執行 `pip install -r requirements.txt`。
2. 執行 `python screener.py`，它會向 TWSE、TPEx 官方確認最新收盤日，從公開 GitHub Releases 的年度壓縮檔建立較長期歷史，並以官方每日歷史行情補回最近一週的交易日（避免第三方每週才更新所造成的缺口）。
3. 完成後開啟 `output/report.md` 看摘要、`output/signals.csv` 看逐檔原始指標與 C1～C4 判斷、`output/metadata.json` 看資料品質資訊。

首次下載需要網路及時間；預設會嘗試回溯 2004 年以來的年度封存，已下載的往年檔案會被快取。每次執行將更新當年度資料、用官方每日歷史接口補足最近一週，以及官方最新行情。若歷史 API schema 變更，系統會中止並提示，不會默默跳過。

```
python screener.py
python screener.py --as-of 2026-10-08
python screener.py --start-year 2024  # 加速試跑，但 C4 僅屬 2024 年以來的新高
```

如果只使用自己整理的 CSV（欄位 `date,code,name,volume,open,high,low,close`，volume 單位為**股**；可用 YYYYMMDD.csv 日檔或大檔）：

```
python screener.py --csv ./mydata/daily_prices.csv --as-of 2026-10-08
```

在沒有網路的環境，使用 `--csv` 自行匯入的歷史資料也可跑完整計算。資料須涵蓋 241 日以上才能產生訊號，但 241 日尚不足以反映長期穩定的 RSI 初始值；建議至少 400～500 日。若沒有上市以來的全部資料，C4 只能代表可取得區間的創高。

## GitHub Actions 每日自動化

1. 在 GitHub 建立**自己的私有 Repository**（若不想公開訊號）。
2. 將 zip 內容完整上傳至 Repository **根目錄**，保留 `.github/workflows/daily_scan.yml` 路徑。
3. 進入 `Actions → Taiwan Momentum Daily Scan → Run workflow` 手動測試一次。
4. 此後系統預設每個週一至週五**台灣時間 18:30** 定期嘗試執行。假日交易所會返回最近一個交易日，報告會標示實際日期。排程可能受 GitHub 延遲。
5. 每次結果放在該次 Actions 的 Artifacts，包含 `signals.csv`、`report.md`、`metadata.json`，可下載；執行頁面 Summary 也有表格。

年度資料 zip 來自第三方公開 [tw-stock-data-release](https://github.com/yukishirotsubasa/tw-stock-data-release/releases)，由 TWSE / TPEx 盤後資料彙整；其更新頻率及歷史完整性由第三方決定。最新盤後補丁則使用官方 [TWSE STOCK_DAY_ALL](https://openapi.twse.com.tw/v1/exchangeReport/STOCK_DAY_ALL) / [TPEx tpex_mainboard_daily_close_quotes](https://www.tpex.org.tw/openapi/v1/tpex_mainboard_daily_close_quotes)。因第三方來源可能不完整，系統在歷史當年度壓縮檔缺失、官方最新資料來源回報日期不一致、解析失敗時預設中止，不會輸出貌似完整的虛假報告。

**不保證所有 API、GitHub Release 資產或雲端排程長期可用。** 本環境無法連線下載歷史資料，因此本次僅在人工測試資料下進行邏輯驗證，**沒有**聲稱已對 2026-10-08 的全體台股完成實際盤後掃描。此系統未與券商連接，也不執行買賣。

## 特殊處理 / 可改參數

- 沒有任何人為設定的最低成交量、價位或漲幅門檻，忠實保留使用者的四條規則。
- `--skip-official` 不抓官方快照，可供離線/歷史研究。
- `--start-year` 可加速，但將減少歷史高價比較資料，使 C4 範圍變窄。正式使用請維持 2004。
- 如果你要將 C2 改成「RSI 曾靠近 45 後向上拐頭、未必突破 45」，需調整 `calc_signal()` 中的判斷，不能在沒有討論門檻的情況下混用。

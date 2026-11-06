# Yulang2 の lowering・推論の熱い所と、Yulang3 の設計への含み (2026-11-07)

署名: Claude (Sonnet 5.5), 2026-11-07。Yulang2 の記録(`main:notes/benchmarks/`、`main:notes/design/static-analysis-speed-plan.md`)と
コード(`main:crates/infer/src/lowering/body/mod.rs`、`main:crates/infer/src/analysis/session/lifecycle.rs`)を読んだ整理。
**測定したのではなく、記録とコードの読みに基づく推測を含む。** 実測は Yulang3 の oracle ができてから行う。

## 1. 数字 (Yulang2, 2026-06-23 の基準, `check-poly-std examples/showcase.yu`)

| 段階 | 時間 | コード上の意味 |
| --- | --- | --- |
| `lower.bodies` | 0.88 秒 | 全 binding の本体を走査し、制約を生成する(lowering と制約生成が交互に進む) |
| `lower.drain` | 0.63 秒 | `AnalysisSession` の work queue を drain する(SCC の処理と量化) |
| `lower.resolve` | 1.285 秒 | 未解決の `x.method`(selection)を、固定点のループで解決する |
| 合計 `infer` | 2.85 秒 | |

std の prefix cache が当たると約 0.26 秒(`2026-06-26-compiled-unit-cache-speedup`)。ただし記録に
「clean build では solver も runtime も本質的に安くなっていない」とある。

## 2. 訂正

初めの私の読み(`lower.resolve` = 名前・path・演算子の解決)は誤りだった。コード上の `lower.resolve` は
`resolve_selections` で、`resolve_unresolved_selections_as_record_fields` を指す。

```text
loop {
    drain_work();
    if enqueue_ready_structured_selection_resolutions() { continue }   // 全 selection を走査して準備済みを集める
    enqueue_unresolved_selection_probes(); drain_work();
    if enqueue_ready_structured_selection_resolutions() { continue }
    let record_fields = ready_record_field_selections();
    if record_fields.is_empty() { break }
    apply_record_field_selection_batch(record_fields);
}
```

`collect_ready_structured_selection_resolutions` は `self.selections.iter()` で**全 selection を走査**し、`.sort_by_key` してから、
`enqueue_structured_selection_resolutions` が `ready.first()`(と、batch にできる場合の batch)だけを処理する。
selection が N 個で、反復ごとに 1 つ(または少数)しか進まないなら、走査は N 回。二乗になりうる。
これが `infer` の約 45% を占めていた可能性が高い。

もう一つ、`lower_binding_bodies` のコメントが設計上の制約を述べている:
「全 binding を走査してから queue を drain する。先に drain すると、source 上で後に現れる binding への forward ref が
SCC graph に入る前に earlier binding が量化されることがあるため」。
→ **std 全体を lowering し終えるまで、どの binding も量化できない**。incremental にできない構造になっている。

## 3. Yulang3 の設計への含み

1. **selection の解決は SCC ごとに一度。** 決定 29(未知 receiver は role を先に、解釈は SCC の解決時点で固定)と、
   証明済みの `MethodResolution`(可視 role 候補が 0 / 1 / 複数)は、**各 selection を局所的に決める規則**である。
   SCC が確定した時点で、その SCC の selection を一度ずつ決める。全体の固定点ループも、全 selection の再走査も要らない。
   role の method 名の索引(名前 → 該当する role の一覧)を持てば、各 selection の決定は定数時間に近い。
2. **モジュール単位で量化できる。** forward ref は SCC の構成で扱い、モジュールの公開型は後続に依存しない
   (`accepted_export_independent`)。std 全体を lowering し終えるのを待つ必要がない。
3. **cache の鍵は標準形。** 決定 47(標準形)は、公開型を**推論の順序に依らず同じ表現**にする。これは、モジュールの interface の
   内容ハッシュを安定させる(cache の無効化を、本当に interface が変わったときに限る)性質でもある。
4. **specialization は request を一度だけ intern。** `static-analysis-speed-plan` の Phase 2 と、Yulang3 の scheme の具体化は対応する。

## 4. 測りたいこと (oracle ができてから)

- selection の数 N に対する `resolve` の時間(二乗か)
- `lower.bodies` のうち、制約生成と名前解決の比率
- std の 1 モジュールだけを変えたとき、再計算されるモジュールの数

## 5. 理論面で足せること (Pro / Sol への依頼の候補)

- **局所性の定理:** SCC 確定時の selection 解決が、他の SCC の解決順序に依らない(順序不変)。全体の固定点を回さなくてよい根拠。
- **コスト上界:** 飽和 (`saturate_capacity` は証明済み)に加え、selection 解決・scheme の具体化・簡約のステップ数の上界を
  モジュールの大きさの関数として示す(参照実装の抽象的なコストモデルで)。
- **cache の正しさ:** モジュール M のソースと、依存するモジュールの interface(標準形)が変わらなければ、M の interface も変わらない。
  標準形が interface の同値を完全に決めること(等しい interface ⇔ 同じ標準形)。
- **増分更新の正しさ:** 変更したモジュールの依存先だけを再計算した結果が、全体を再計算した結果と、標準形で等しい。

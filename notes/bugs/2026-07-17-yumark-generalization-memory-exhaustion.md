# Yumark の named generalization が実メモリを枯渇させる

日付: 2026-07-17。発見: Shadow Stage 1 Slice 3 の real-literal performance
characterization 中。
状態: **open / safety-critical / pre-existing production bug**。Yumark redesign の
shadow/algebra-passing 実装とは独立した、現行 role-based Yumark の既存問題。

## 症状

`tests/yulang/regressions/cache/yumark_shadow_literal_performance_workload.yu` の実際の
apostrophe literal を、現行 `std::text::yumark` の renderer 呼び出しを持つ named
definition に包む。以下は Markdown の最小再現形だが、HTML の
`html_tag (render_html_doc (...))` でも同じ症状を確認している。

```yu
my proof() = std::text::yumark::render_markdown_doc (
    <yumark_shadow_literal_performance_workload.yu の literal>
)

proof()
```

この entry を repository std とともに収集し、CURRENT の role-based Yumark path
（shadow lowering scope を有効にしない `infer::check::check_loaded_files`）で check
するだけで、メモリ使用量が増え続ける。specialize や runtime execution へ進む前の
generalization 中に起きるため、build-and-run の caller から入っても同じ failure に至る。
2026-07-17 の確認では、次の外側制限下で RSS が 4 GiB を超える水準まで上昇し、約
51 秒で allocator が SIGABRT した。

```bash
(ulimit -v 4194304; timeout 60 env RUSTC_WRAPPER= \
  cargo test -p yulang --test yumark_shadow_literal_performance \
  real_literal_current_route_reproduces_documented_memory_exhaustion -- \
  --exact --nocapture --test-threads=1)
```

この test は現在、外側 wrapper を忘れても host を危険にさらさないよう、test process
自身が compile 前に `RLIMIT_AS` の soft/hard limit を最大 3 GiB に下げる。危険な
check は同じ limit を継承した worker process へ隔離し、core dump も無効化する。
親 test は allocator の failure message と SIGABRT の組を、この既知バグの期待結果として
明示的に assert する。CURRENT が正常終了した場合や別の failure mode になった場合は失敗し、
shadow の success test が同じ limit に触れた場合も新しい regression として失敗する。

## 再現条件の境界

- 対象は `lib/std/text/yumark.yu` を使う **CURRENT** route。
- real literal を renderer へ渡す call が、`my proof() = ...` という let-generalized
  named definition の body にある。`render_markdown_doc` と `render_html_doc` の両方で
  再現するため、特定の出力 format に固有の問題ではない。
- `infer::check::check_loaded_files` だけで再現する。build-and-run caller でも、その手前の
  同じ check/generalization path で失敗するため、runtime execution の有無には依存しない。
- literal を単なる root expression として置いた比較では、同じ full generalization
  path を通らず、この症状の再現条件にならない。
- Shadow Stage 1 の algebra-passing route は同じ文書構造でこの pathology を示さない。
  その route は document node ごとの recursive role resolution を発生させない。

## 疑われる機構

named / let-generalized definition は、現行 `crates/infer` の role solver を含む full
generalization を起動する。これは 2026-07-17 のより広い調査で既に特徴付けた
`proof` root の pathology と同じ入口である。現行 Yumark は document shape を
`cons_cell` / `*_leaf` の入れ子型として持ち、`YumarkRender` の prerequisites を
document node ごとに再帰解決するため、named root の generalization が大きな role
resolution / associated-bound expansion を抱える。

ただし、本 fixture は、それまでの broader investigation で観測した規模より明確に
悪い。それまでの最大ケースはおおむね 3–5 秒で、構造展開量も数 GiB 相当までだったが、
実 process の OOM / abort には至らなかった。この real document の繰り返しと入れ子構造は、
同じ入口から実メモリ枯渇まで進む substantially worse な blowup を起こす。

ここでの説明は再現条件と既知の solver shape に基づく suspected mechanism であり、
solver-level root cause の確定ではない。本 report の作成時には、追加の root-cause
instrumentation や production solver の変更を行っていない。

## 帰属

これは **新しい shadow/algebra-passing design の defect ではない**。問題の production
path は既存の `lib/std/text/yumark.yu` と `crates/infer` の role solver の組み合わせで、
Shadow Stage 1 より前から存在する。shadow route は document structure を algebra へ
直接渡し、per-node role recursion 自体を作らないため、同じ文書構造でこの blowup を
示さないことを別途確認済みである。

`notes/design/2026-07-17-yumark-converged-design.md` は、recursive document-shaped role
tree を捨てて flat-role algebra passing へ移る設計理由を記録している。本 finding は
その redesign の追加の動機になるが、redesign project が現行 role solver bug を修正する
責任を負うという意味ではない。production path の安全性問題と migration の設計検証は
別の concern として扱う。

## Regression test の責務

safe scale での CURRENT / shadow の byte parity は、Slice 1-2 の
`yumark_nil_text_shadow_matches_current_html_and_markdown_bytes` と
`yumark_full_static_shadow_matches_current_html_and_markdown_bytes` が担う。real-literal file
は、この規模では成立しない parity oracle を持たない。

`crates/yulang/tests/yumark_shadow_literal_performance.rs` は、次の二点だけを固定する。

- shadow route は、同じ named-definition wrapper と real literal を HTML / Markdown の
  両方で compile、specialize、run でき、構造 marker を持つ出力を返す。
- CURRENT route は、同じ wrapper の Markdown entry を check する段階で、3 GiB limit 下の
  allocator SIGABRT を再現する。HTML でも別途同じ再現を確認済みだが、既知の host cost を
  各 test run で二重に払わないため、quarantine test の代表 format は Markdown とする。

## 推奨する follow-up

この role-solver memory exhaustion を、Shadow Stage 1 Slice 3 や Yumark redesign migration
の一部として修正しない。live production path の safety-critical bug なので、専用の
carefully-scoped investigation を別 project として立てる。

その investigation では、今回と同じ discipline を必須にする。

- suspect fixture / driver を読む・実行する command は常に hard memory limit と timeout
  の内側で行う。
- test 内の `RLIMIT_AS` quarantine を外さない。
- root cause が確定する前に role solver、generalization、Yumark lowering へ局所 fallback
  や fixture-specific 分岐を入れない。
- redesign の shadow route が安全だからという理由で、CURRENT production route の bug を
  close しない。

## 関連

- `crates/yulang/tests/yumark_shadow_literal_performance.rs`
- `tests/yulang/regressions/cache/yumark_shadow_literal_performance_workload.yu`
- `lib/std/text/yumark.yu`
- `crates/infer/src/analysis/session/generalize.rs`
- `crates/infer/src/role_solve/`
- `notes/design/2026-07-16-generalize-role-resolve-snapshot-spec.md`
- `notes/design/2026-07-17-yumark-converged-design.md`

# 現在のタスク: cache semantics / diagnostics の次 slice を選ぶ

更新: 2026-07-24

このファイルは、着手中または直ちに着手できる作業だけを置く。
完了履歴は Git、設計判断は `notes/design/`、広い保留案は `notes/todo/` を正本とする。

## 現在地

- Contract v0/v1 の executable contract、host-act/file-resource first surface、release smoke は着地済み。
- Yumark の static core / thin path、runtime、lazy LSP hover は着地済み。
- generic role-impl conformance、method-role owner dirty scheduling、承認済み範囲の
  canonical cache interface は着地済み。
- ordinary-cast resolution、constraint-provenance graph、parameter body-use provenance は、
  OCAST-A〜E、CPROV-A〜J、PUSP-A〜Fまで完了した。`MissingImplicitCast` は
  provenance-gatedで発火し、同一sessionで到達できる場合はcallee bodyの制約元も説明する。
- subtype explanation bridge は SUBP-A〜H まで完了した。general subtype mismatch の
  source cause は CLI と playground の同じ related information surface へ到達する
  （`5cfaa773` / `40dca67a`）。wasm cache test の stale expectation も `bfd9c494` で閉じた。

## 完了した release-readiness

- CI gate: PR / push で fmt、poly / specialize、release gate 相当の parser / infer / yulang tests を実行する
  `.github/workflows/ci.yml` を追加した（`f62e7b41`、`eb5d4097`、`1a958792`）。
- release: `v0.1.0-alpha.10` を [GitHub Release](https://github.com/momota1029/yulang/releases/tag/v0.1.0-alpha.10)
  として公開し、release gate の test-infrastructure false failure を `da770013`、`52537715` で修正した。
- playground / docs: Pages deploy workflow を `75e73daf`、prerelease を含む default latest 解決を
  `77843cb1`、archived playground・crate rename・version pin の stale docs を `c005965b` で更新した（push 済み）。
- Pages deploy は code-complete だが未公開。GitHub Settings → Pages の Source を `GitHub Actions` にし、
  `yulang.momota.pw` を custom domain に追加後、Cloudflare に DNS-only CNAME `yulang` → `momota1029.github.io` を追加する。

## 次の track

優先順位は `notes/todo/index.md` の numbered 0〜8「既存の公開準備 track」を正本とし、item 4 は未着手で低い緊急度とする。

1. cached/cold compilation の意味論的同値性を `notes/design/2026-07-08-std-prefix-cache-generalization-divergence.md` から解決する。
2. `notes/todo/diagnostics-docs.md` の残件を継続する。

着手時に owner、exit witness、検証commandを持つ別 slice を作る。ここでは実装しない。

## 大きい未完trackの入口

- testing / executable contracts: `notes/todo/testing.md`
- diagnostics / type checker: `notes/todo/diagnostics-docs.md`,
  `notes/todo/type-checker-diagnostics.md`
- LSP / editor: `notes/todo/language-server.md`
- release / packaging: `notes/todo/release.md`
- cache / compile latency: `notes/todo/static-analysis-speed.md`,
  `notes/todo/performance-localization.md`
- Yumark command/injection、span provenance、preview: `notes/todo/yumark.md`
- language surface / future features: `notes/todo/language-surface.md`, `notes/todo/index.md`

## 明示的にdeferまたはcloseしたもの

- Predictive suffix-safety oracleはStage 0で中心仮説が反証され、abandoned。再開には
  `notes/design/2026-07-15-suffix-safety-oracle-spec.md` の再設計が必要。
- Per-demand exact role-solve snapshot reuseは性能gate不合格のためdefault-off。
  cheap-demand admissionを別projectとして設計するまで自動再開しない。
- Canonical cache interfaceの承認済みpartial Option 1は実装済み。より広いcandidate
  lifecycleとprogram-sensitive fallbackの完全退役は別判断なしに広げない。
- Contract v1のbytes/range、directory、broader server surfaceはpost-v1のまま。
- clippy CI gateはdefer。2026-07-23時点で既存warning 48+（parser約40: collapsible_if /
  needless_return / needless_question_mark、poly 4、text-tree 3、mono 1）。`cargo clippy --workspace --all-targets -- -D warnings` gate化前に別triage sliceが必要。

## 作業規則

- このファイルに実装日誌を追記しない。
- 具体的なowner、exit witness、検証commandを持つ一sliceだけをactiveにする。
- 完了したsliceはGit/design/progressへ記録し、このファイルから除く。
- solverやruntimeの長い検証には必ず`timeout`を付ける。

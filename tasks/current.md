# 現在のタスク: release readiness の次 slice を選ぶ

更新: 2026-07-23

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
- 現在、実装を承認済みの次sliceはない。

## 次の track

優先順位は `notes/todo/index.md` の numbered 0〜8「既存の公開準備 track」を正本とする。
item 2 の diagnostics は SUBP-H の CLI / playground integration まで前進した。
次に pick up する release-readiness 作業は次の順とする。

1. ordinary PR / branch push に CI gate を追加する。`scripts/release-gate.sh` の core checks を
   接続し、少なくとも fmt、clippy、parser / infer / yulang tests を gate にする。
2. alpha.9 以降 354 commits の checkpoint として `v0.1.0-alpha.10` tag を切る。
3. playground deploy を自動化し、`docs/status.md` の archived wasm 記述と
   `web/docs/guide/install.md` の旧 crate 一覧を現行 workspace に合わせる。
4. 低い緊急度で cached/cold compilation の意味論的同値性を調査し、
   `notes/todo/diagnostics-docs.md` の残件を継続する。

各項目は owner、exit witness、検証commandを決めた別 slice とし、ここでは実装しない。

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

## 作業規則

- このファイルに実装日誌を追記しない。
- 具体的なowner、exit witness、検証commandを持つ一sliceだけをactiveにする。
- 完了したsliceはGit/design/progressへ記録し、このファイルから除く。
- solverやruntimeの長い検証には必ず`timeout`を付ける。

# 現在のタスク: 次の公開準備 track を選ぶ

更新: 2026-07-22

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
- 現在、実装を承認済みの次sliceはない。

## 次の track

優先順位は `notes/todo/index.md` の numbered 0〜8「既存の公開準備 track」を正本とする。
item 0 の hardening は historical / superseded、item 1 の testing は mature but ongoing で、
主な未決事項である Yulang-facing test API は直近の判断対象ではない。

次に調査して具体的な slice を決める track は item 2 の
[`notes/todo/diagnostics-docs.md`](../notes/todo/diagnostics-docs.md) とする。
具体的な slice の選定は別の follow-up investigation で行う。

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

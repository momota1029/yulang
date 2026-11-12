# Cycle150: finite-journal Joint の実履歴回帰

一般 V5 は 6/14 供給・8/14 未解決のまま。この追加は cycle149 の
`GeneralDictionaryFiniteJournalJoint.initial_joint` を、既存の実際の
`Display(List Int)` 一回 install 履歴へ適用する回帰検証である。
意味論・分類・実行規則は変更していない。

## 証明した範囲

- `alias_eq`: この最終状態の alias graph は空なので、任意の alias 証拠は ID の等号を意味する。
- `root_locality`: 実 sites は親と子の二つで、子 ID は親と異なる。このため親の Related site は親 occurrence と一致する。locality を仮定として渡さず、実状態から導出した。
- `root_joint`: 任意の assignment がこの最終 journal の Models を満たせば、親 key 1 の Joint が成立する。既存の InitialSource、ordinary 実 trace、実 packet、現在 selected、および上の locality を有限 journal 定理へ渡す。
- `actual_stable_joint`: 既存の具体 model により、同じ最終状態の reachable・stable・Models・Joint をまとめる。非存在モデルによる空虚な例ではない。

未記録の scalar 子を持つ既存の具体成功例であり、一般の alias locality、任意 reachable state の Joint、V5 の EvidenceNode/GeneratedChildren の完成を主張しない。有限 journal 一般定理の対象は任意長の ordinary 履歴だが、この回帰例の履歴は一回の install である。

## 検証

依存 olean は同じ元 commit `7a7b330` の既存 focused build を利用し、新しいファイルを直接 Lean 4.35.0 で検査した。full build は行っていない。

- `lean -DwarningAsError=true -o /tmp/GeneralDictionaryFiniteJournalJointExample.olean lean/Yulang/GeneralDictionaryFiniteJournalJointExample.lean`: exit 0、出力なし。
- 同じソースに4件の `#print axioms` と完全修飾 `#check @root_joint` を付けた監査を `lean --trust=0 -DwarningAsError=true` で実行: exit 0。
- 4定理とも依存公理は `propext`, `Classical.choice`, `Quot.sound` のみ。
- 最初に direct Lean に `--wfail` を渡した試行は未対応 option で exit 1。Lake の option であるため、direct Lean の `-DwarningAsError=true` に修正した。証明自体の失敗ではない。

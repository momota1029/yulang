# 追加role claims（9列正規化）

| ID | 出典 | 規則 | 例 | 実機結果 | 新spec | Lean | 分類 | 備考 |
|---|---|---|---|---|---|---|---|---|
| ROLE-MORE-001 | role-system:109–124、role_solve/mod.rsの候補探索 | 同一receiverに対するrole実装候補0/1/複数を区別する | R intの候補0/1/2。2候補はbodyの1/2を入れ替えた順でも検査 | missing=check1/run1 unresolved-method、single=0/0 roots[1]、duplicateとreverse=1/1 ambiguous-method | §6.2 複数impl曖昧 | Roles.resolve_none/resolve_many（WellFormed impls前提、抽象Goal） | 一致 | この同一head例はcast-cycle1のnominal先頭選択とは異なる挙動。異なる役割を混同しない。 |
| ROLE-MORE-002 | 同上 | 一般headと具体headが重なる場合、具体head優先ではなく曖昧 | `impl R int` と `impl R 'a` が両方ある `1.r` | check1/run1 ambiguous-method | §6.2 一般/具体候補の重なり拒否 | Roles.resolve_many、head照合は抽象Matches | 一致 | この例では「具体impl優先」にならない。 |
| ROLE-MORE-003 | impl_decl.rs:183–197,272–301、case_07.rs:760–779 | 宣言whereとbody由来prerequisiteの効力を区別する | `impl R (box 'a): where 'a: Q; a.r=1`、Q intなしで `(box {value:1}).r` | check0/run0 roots[1] | §6.3末尾: impl whereは候補の前提 | Roles.resolve_one/resolve_resolved_iffは単一headの全child成功を要求（WellFormed必要） | 違う | 新specの前提を満たさないのに旧定数bodyが通る。nominal boxの縮小条件は増大型X2とは異なりサイズ問題を避ける。 |
| ROLE-MORE-004 | instantiate.rs:97–150、lifecycle.rs:280–295 | bodyに実際のrole需要がある場合、その実装の有無が結果に影響する | 上記bodyを `a.value.q` に変更。Q intなし/追加の正負 | なしcheck1/run1 unresolved-method q at body。追加check0/run0 roots[7] | §6.3 自動残余とchild要求 | Roles.resolve_resolved_iff（モデル内）、surface/body-to-child橋渡しは未検証 | 一致 | 一致する局所例。whereの宣言内容だけでなくbody需要が実際に効く。 |
| ROLE-MORE-005 | impl_declのadvertised分離 | 満たせない宣言whereが候補選別に使われるかを区別する | MORE-003に `impl R (box int): a.r=2` 追加 | check1/run1 ambiguous-method | §6.2 重なる候補曖昧、§6.3前提 | Roles.resolve_many（whereを試す前の複数head） | 未確認 | 部品対応。旧whereが候補へ効かないため、この試験だけでは「満たせない前提で候補を絞らない」という一般則の独立検証にはならない。 |
| ROLE-MORE-006 | method-selection:17–26、selection.rs:890–910、lifecycle.rs:873–934 | 未知receiverで同名methodのroleが複数ある場合の処理 | 同名rを持つR,Sが見える未知receiver `our f(x)=x.r` | check0、dumpは `{r:'a}->'a` と `#field`。別試験 `f {r:9}` はrun roots[9] | §6.4: 未知receiverで同名method role複数なら曖昧エラー | MethodResolution.unknown_ambiguous_iff: 異なる二role Candidate iff ambiguous | 違う | 旧spec文はroleかfieldへ最終化とだけ述べる。新specの曖昧規則へ旧挙動を採用しない。 |
| ROLE-MORE-007 | 同上 | 未知receiverで同名methodのroleが一つならrole制約を保持する | Rだけの未知receiver `f(x)=x.r` | check0、dump `'a -> int where 'a:R`、role ref | §6.4 role一つ優先 | MethodResolution.unknown_role_iff（UniqueRole前提） | 一致 | MORE-006との対照。 |
| ROLE-MORE-008 | 同上 | 既知record receiverはfieldを優先する | R,Sがあっても既知record `{r:9}.r` | check0/run0 roots[9]、dump #field | §6.4 既知receiver field優先 | MethodResolution.known/resolve_exact（既知StructuralBase入力snapshot） | 一致 | 未知receiverでの二role曖昧と既知field優先を区別。 |

対象旧Y2: `d4c8bc8fc8a49173180932cd25921a2c41057354`。実機全文は `runtime-cycle-2-role-boundaries.md`、機械可読原ログは `raw.json` と `extra-raw.json`。Lean対応は読取によるモデル部品の照合であり、今回新規Lean buildは行っていない。詳細な量化・前提と実装追跡は以下。

## 実装経路

- 宣言whereはconformance用advertised predicateに保存されるが、初期candidate.prerequisitesは空。対応する既存unit `lowering::tests::case_07::generic_role_impl_conformance_stage4_p0a_captures_impl_where_with_u_binder` を既存 `target/debug/deps/infer-dfea53230aacf9c4` から完全名指定で実行し、1 passed、exit0、約0.02秒。このunitは `P0-A capture must not activate candidate prerequisites` をassertする。新たにコンパイルした結果ではなく既存test binaryの結果である。
- body由来schemeのrole predicateは `analysis/session/instantiate.rs:97–150` で収集し、`lifecycle.rs:280–295` でcandidateへ追加される。詳細は `x2-demand-boundary.md`。
- 未知receiverの `role_method_for_select` は `selection.rs:890–910` で、候補が一つならTypeclassMethod、0個または複数ならNone。
- `lifecycle.rs:873–890` はそのSomeをstructured resolutionへ送り、`lifecycle.rs:915–934` はNoneの場合record field fallbackに回す。今回の二role例のfield化と整合する。局所scope/globalscopeの相互作用全般までは監査していない。

## Lean主張を過大に読まないための範囲

`Roles.resolve_many` は任意の `impls : List Impl`, `wf : WellFormed impls`, `g : Goal`, `i j : Impl`, `rest : List Impl` について、`candidates impls g = i :: j :: rest` を前提に `resolve impls wf g = .ambiguous` を述べる。

`Roles.resolve_resolved_iff` は任意の `impls`, `wf : WellFormed impls`, `g` について、resolveがresolved iff「あるimpl iだけがhead候補で、i.constraintsに属する全cについてmatchingSubstを適用した子goalのresolveがresolved」。source parser、body推論、SCC driver全体をこの定理が証明するわけではない。

`MethodResolution.unknown_ambiguous_iff` は任意の `scope : Scope`, `name : Nat` について、unknownがambiguous iff「異なるfirst/second roleと各参照が存在し、それぞれCandidate scope nameを満たす」。Scopeの可視roleリストは入力であり、実module visibilityを計算する定理ではない。既知/未知receiverのSCC最終snapshotも入力である。

今回はLeanファイルの読取対応付けのみで、Lean buildを追加実行していない。cast本体の新規試験はしていない。旧nominal cast候補先頭選択（cycle1）からroleも先頭選択だと推論してはならないことを、正負例で確認した。

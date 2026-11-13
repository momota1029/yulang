# Cycle 167: 最終 producer evidence と report 移送の定理索引

## 範囲と記法

以下は新規公開定理23本の索引。`Yulang.` を namespace の先頭で省略する。
定理名は各節の namespace と結合する。記載した変数はすべて全称量化、
「追加前提なし」は当該 fixture の固定定義以外に仮定を置かない意味である。

fixture の `candidate` は保存済み producer packet、`before` はその private context、
`scalarState` / `scalarContext` は slot 2 の scalar 観測を反映した状態/context、
`observed` は実際の producer install と scalar refresh を経た journal。
`finalPacket` は producer の context を `scalarContext` に差し替え、bounds を
`[(3,4)]` とした packet。`declaration`、`producer`、`registry`、`target` は固定実例。
`model` / `assignment : GeneralNominalCommonBridge.Assignment`。
`Models` は特記しない限り `GeneralNominalSaturationState.Models`。
`report` / `namedSchema` / `Ordinary` / `Outputs` は
`GeneralNominalPacketSupport` の同名定義。
`Evidence` / `Instance` は `GeneralDictionaryRecursiveEvidence` の同名定義。

分類は「一般補助」または「fixture 健全性補助」。後者は有限実例の計算・
全 journal モデルに対する意味的性質であり、言語全体の健全性・完全性定理ではない。

## A. `GeneralDictionarySharedCapturedFinalEvidence`（10本）

1. `old_branch`〔fixture 健全性補助〕
   任意の `assignment` と `valid : Models observed.current assignment` に対し、
   `candidate.Holds assignment`。保存済み packet の journal membership から取り出す。
2. `packet_seed`〔一般補助、ただし roles は実例の `GeneralDeclarationExamples.roles` に固定〕
   任意の `p : Packet GeneralDeclarationExamples.roles` に対し、
   `p.privateContext.state.seed = p.context.state.seed`。追加前提なし。
3. `seed_preserved`〔fixture 健全性補助〕
   追加前提なしで `before.state.seed =
   GeneralDictionarySharedCapturedInstallation.after.current.context.state.seed`。
4. `constructors_preserved`〔fixture 健全性補助〕
   追加前提なしで `before.state.constructors = GeneralDeclarationExamples.constructors`。
5. `interpretation_preserved`〔fixture 健全性補助〕
   追加前提なしで `before.interpretation = GeneralNominalExamples.interpretation`。
6. `ordinary`〔fixture 健全性補助〕
   任意の `assignment` と `Models observed.current assignment` に対し、
   `Ordinary finalPacket assignment`。互換性・capture merge 方程式・self-check を含む。
7. `projections`〔fixture 健全性補助〕
   任意の `assignment` と `Models observed.current assignment` に対し、
   `GeneralNominalRecursiveInspection.ProjectionModels scalarState
   (report finalPacket) assignment`。
8. `schema_exact`〔fixture 健全性補助〕
   追加前提なしで `namedSchema finalPacket =
   { tests := [(.source target, .scalar .int)] }`。
   省略された schema フィールドは構造体の既定値（variables は空、unknown は false）。
9. `outputs`〔fixture 健全性補助〕
   任意の `assignment` と `Models observed.current assignment` に対し、
   `Outputs finalPacket assignment`。
10. `branch_models`〔fixture 健全性補助〕
    任意の `assignment` と `Models observed.current assignment` に対し、
    `finalPacket.Holds assignment`。これは最終 context の private-state Models、
    projection Models、named-output materialization Models を合わせた BranchModels。
    目的の BranchModels 自体を仮定しない。

## B. `GeneralDictionarySharedCapturedFinalCurrentEvidence`（6本）

11. `bounds`〔fixture 健全性補助〕
    追加前提なしで `GeneralNominalRecursiveCandidates.arguments scalarContext producer
    = some [(3,4)]`。bounds の各成分は `Fin 5`。
12. `terminal`〔fixture 健全性補助〕
    追加前提なしで `finalPacket.children = []`。
13. `request_ready`〔fixture 健全性補助〕
    追加前提なしで `GeneralNominalRecursiveCandidates.RequestReady registry scalarContext
    producer declaration GeneralDictionaryRecursiveObstruction.declaration_checked [(3,4)]`。
    この RequestReady は root output 定義と materialization の unknown=false であり、
    Trusted readiness とは異なる。
14. `current_instance`〔fixture 健全性補助〕
    任意の `assignment` と `Models observed.current assignment` に対し、
    `Instance registry observed.current.context assignment producer declaration.id []`。
    fresh bounds/report/RequestReady、空の実際の children、SourceFormed から得る metadata、
    A.10 の BranchModels を組み合わせる。
15. `current_evidence`〔fixture 健全性補助〕
    任意の `assignment` と `Models observed.current assignment` に対し、
    `Evidence registry observed.current.context assignment producer (.node declaration.id [])`。
    目的の Evidence も child Evidence も仮定しない（実際に terminal）。
16. `concrete_evidence`〔fixture 健全性補助〕
    追加前提なしで `Evidence registry observed.current.context
    GeneralDictionarySharedCapturedModel.model producer (.node declaration.id [])`。
    B.15 と既存の journal inhabitation の系。

## C. `GeneralNominalReportSourceTransport`（5本）

この節はすべて一般補助定理。暗黙変数は任意の
`before after : GeneralNominalState.State`。共通して任意の
`slots : Fin before.base.slots → Fin after.base.slots` と
`report : GeneralNominalRecursiveInspection.Report before` を取る。
`moveReport slots report` は各 bounds を slots で写し、capture の name/origin、
anchor の origin、tests、arity を保持する。写像の全射性は要求しない。
次の source 保存条件を `sources` と略す：
`∀ slot, after.base.source (slots slot) = before.base.source slot`。

17. `bindings_preserved`〔一般補助〕
    共通変数と `sources` に対し、
    `GeneralNominalRecursiveInspection.bindings after (moveReport slots report) =
    GeneralNominalRecursiveInspection.bindings before report`。
18. `selfChecks_preserved`〔一般補助〕
    共通変数と `sources` に対し、
    `GeneralNominalRecursiveInspection.selfChecks after (moveReport slots report) =
    GeneralNominalRecursiveInspection.selfChecks before report`。
19. `finished_iff`〔一般補助〕
    共通変数のみで `GeneralNominalRecursiveInspection.Finished (moveReport slots report)
    ↔ GeneralNominalRecursiveInspection.Finished report`。`sources` は不要。
20. `projections_iff`〔一般補助〕
    共通変数、`sources`、任意の `model` に対し、
    `GeneralNominalRecursiveInspection.ProjectionModels after (moveReport slots report) model
    ↔ GeneralNominalRecursiveInspection.ProjectionModels before report model`。
21. `materialization_iff`〔一般補助〕
    共通変数に加え任意の `declaration : GeneralDeclarations.Declaration`、
    `capture : GeneralDeclarationDemands.Capture`、
    `schema : GeneralNominalMaterialization.Schema`、`model` に対し、
    `GeneralNominalMaterialization.Models after declaration capture
    (moveReport slots report) schema model ↔
    GeneralNominalMaterialization.Models before declaration capture report schema model`。
    `sources` は不要。両辺の declaration/capture/schema/model は同一である。

## D. `GeneralDictionarySharedCapturedReportTransport`（2本）

22. `exact_relocation`〔fixture 健全性補助〕
    追加前提なしで `report finalPacket =
    GeneralNominalReportSourceTransport.moveReport
    (before := candidate.context.state) (after := scalarState)
    (fun slot => slot) (report candidate)`。
    fresh report の一致を仮定するのではなく、両側の report 計算結果から証明。
23. `projections_equivalent`〔fixture 健全性補助〕
    任意の `model` に対し、
    `GeneralNominalRecursiveInspection.ProjectionModels scalarState (report finalPacket) model
    ↔ GeneralNominalRecursiveInspection.ProjectionModels candidate.context.state
    (report candidate) model`。journal Models の前提なし。
    D.22 と C.20 の恒等 slot 写像への適用。

## 得られない結論・検証範囲

- current Evidence から producer の **Trusted readiness** を導いていない。
  Evidence は特定モデル・source declaration・current context の意味的証明であり、
  I26/I27 の決定ガード、unique candidate、停止状態、実行手順の証明ではない。
- scalar refresh を OrdinaryTrace.Extension と同一視していない。
- C の一般定理は計算済み report の意味的移送。任意の状態変化が inspection を保存する
  とは主張しない。fresh report が moveReport と一致する証明が別途必要で、D は本実例でそれを提供する。
- 全23定理の `#print axioms` と新規4モジュールの `--trust=0` 検証を実施。
  新規 sorry/axiom/native_decide なし。標準公理の範囲。
  新規モジュールは独立出力先でも再コンパイルし、audit 出力の一致を確認。
  旧依存の全体再ビルドを、この索引の検証だけから主張しない。

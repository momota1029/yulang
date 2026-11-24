# Cycle 392: I-69 で残った二つの事実の出所

正本 `4b33692365cddbd8e2c6a16f8c0bc3f74ce8ca43`、I-69 inbox blob `5e202637769e290325b60e4425812e784428f3d7`。最上段と S13 の分割は変更しない。証明を始める前の確認。

| 葉 | 今ある前提から出ない事実（一文） | 本来の出所 |
| --- | --- | --- |
| S13bbba | 選んだその出現の元の explicit body / role default を実捕捉に適用した結果が、その ordinal に載る元の typed/ordinary literal RHS と一致すること。 | **(a)** spec 6.3 の関連型等式を作る独立な宣言的 local source rule。C386 `eventAt` は未具体化で `receiptAt` は `Supplies` と位置まで。canonical な住所や `Fits` では代用できない。 |
| S13bbbb | 同じ出現が作ったその RHS の等式が、同じ declarative State の元 fixed target に成り立つ論理制約として残ること。 | **(a)** spec 6.3 の named output の等式を同じ状態で課す宣言的規則。C365 `Fits` はすでにある論理制約・観測を解釈するだけ。特定の native 物理 origin / release の存在を結論に要求するのは spec からは出ないので、その表現を要求に足さない。 |

根拠: [spec 6.3: 関連型は変数と等式](https://github.com/momota1029/yulang/blob/4b33692365cddbd8e2c6a16f8c0bc3f74ce8ca43/spec/06-roles.md#L88)、[where の子と等式への糖衣展開](https://github.com/momota1029/yulang/blob/4b33692365cddbd8e2c6a16f8c0bc3f74ce8ca43/spec/06-roles.md#L133)、[名前つき output と head の分離](https://github.com/momota1029/yulang/blob/4b33692365cddbd8e2c6a16f8c0bc3f74ce8ca43/spec/06-roles.md#L238)、[実捕捉の中心で共有を表す](https://github.com/momota1029/yulang/blob/4b33692365cddbd8e2c6a16f8c0bc3f74ce8ca43/spec/06-roles.md#L383)。 [C386 LocalSource](https://github.com/momota1029/yulang/blob/4b33692365cddbd8e2c6a16f8c0bc3f74ce8ca43/lean/Yulang/GeneralDeclarativeI65LiteralReplay386.lean#L72) は一般 interface で `localRule` と `eventAt` の間に元 body の評価規則を持たない。 [C365 Fits](https://github.com/momota1029/yulang/blob/4b33692365cddbd8e2c6a16f8c0bc3f74ce8ca43/lean/Yulang/GeneralDeclarativeI65State365.lean#L50) から発生させない。少なくとも source RHS の不足を仮定として増やすのではなく、元の source で等式を導く規則を具体化する。

S13bbba を先に検討する。同じ出力が選択を決めないこと、元の where 子の順、actual capture と入力の使い回し、ordinary と declared mode の区別を保つ。実物の導出なしに C386 の `eventAt` へ `ExactSourceRhs` をそのまま field として入れない。未決の carrier 表現を意味論の決定にしない。S13bbbb の証明、Step 2・3、停止性、追加 fixture は行わない。

## C392 で実装した具体的な source 条件付き規則

[新しい module](https://github.com/momota1029/yulang/blob/08935f6f1f00ef09716e723161e36d6a6456680d/lean/Yulang/GeneralDeclarativeI65NativeAssociatedRhs392.lean) と [独立 audit](https://github.com/momota1029/yulang/blob/08935f6f1f00ef09716e723161e36d6a6456680d/lean/Audit/Cycle392NativeAssociatedRhs.lean)。`ModelFreeNativeOutputAt392` は actual authored `Supplies` と original output ordinal の body を使う。explicit の source name は元 event の capture list、default は元 role demand の実 position を使う。capture の `ValueBind` / `RowBind` は独立 source proof を要求し、同じ名前の数値だけから型/行を相互変換しない。C359 の [実 `Use`・source slot による unary rules](https://github.com/momota1029/yulang/blob/4b33692365cddbd8e2c6a16f8c0bc3f74ce8ca43/lean/Yulang/GeneralDeclarativeWitnessNominalSource359.lean#L43) と同じ declared-mode 区別を使い、logical declaration table の任意長の value/row vector と declared nesting を順に辿る。親から継がれる invariant では元の下端/上端を保つ。元の direct / tagged nominal body を表すとき、`native_source_emits_original_receipt392` が fixed target の literal receipt を**構成する**（既存 receipt の同値を出力生成の仮定にしない）。元 source と同じ slot read の出力は `native_associated_rhs_functional392` で一意、型/行・分散の文脈適合は `native_rhs_wellformed392` で確認した。選択 rule を変更していない。

### exact 一般 leaf に残る実 source 事実

1. **where が生成した名前**: `Declaration.Scoped` は associated RHS の変数を input head だけでなく `outputNames` からも認める。元 declaration の `Produced` と C386 の `whereAt/whereCount` からは actual where 子の *元 clause ordinal* と、その元 output equation ordinal を得られる（下の検証）。`whereAt` に残るのは元 clause と子 role まで。さらに actual 子の出力が `EmissionForest322.children` であるとき、元の `OutputBinder` から同じ clause/output ordinal の emitted target を得る。capture list が `ProducedNames325.table` の元の head/output names から実際に作られたとき、その同じ target が actual body slot と一致する。これらの source 生成の証拠自体（及び typed capture）を全 `LocalSource` に与える規則はまだない。ここは (a) の actual where/output emission rule が供給すべきで、lookup 失敗や `Fits` で補わない。[C371 `exact_source_child_and_output_at`](https://github.com/momota1029/yulang/blob/4b33692365cddbd8e2c6a16f8c0bc3f74ce8ca43/lean/Yulang/GeneralDeclarativeI65SourceBodyProduction371.lean#L41) は既存 ordinary の named placement で使える源であって、任意の選択・native where capture に読み替えない。
2. **typed binder の出所と混在した source 形**: scoped module は explicit/default の actual slot を読み、value/row source proof が与えられる native app を展開する。C386 の untyped capture list だけでは actual chosen source の kind が出ない。root の native app/tagged app を超える record/join などに native を組み込む一般の literal RHS 規則（及びその event 化）は未実装。語形を拒否に変えたり、型付き vector を C334 ordinary coercion で置き換えたりしない。これは新しい言語の意味・順序を決める質問ではなく、既存規則へ追いつけていない範囲。

S13bbba の元の all-state 文は閉じていない。scoped rule だけを `Classifies` の制限として挿入しない。S13bbbb の retention theorem はこの周は扱わず、上の不足・出所のみ記録。分割なし、checklist 閉鎖ラベル変更なし。

## where producer の strict 診断

別の repo module/fixture は追加せず、下の三つの一般形を新 module の exact replay に対して Lean 4.35.0 `--stdin --trust=0 -DwarningAsError=true` で検証。exit 0。元の source/where 位置と exact emitted target は各 `[propext, Quot.sound]`、actual body slot は `[propext, Classical.choice, Quot.sound]`。子の target は actual child/capture 生成の前提からだけ得る。

```lean
import Yulang.GeneralDeclarativeI65NativeAssociatedRhs392

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Equation OutputBinder)

/-- The independent real declaration rules allow an associated RHS
variable to be produced by an exact where equation, not just captured
from the input head. This does not choose that child's current target. -/
theorem original_rhs_name_has_input_or_where_producer392
    {s : State} {q : Request} (event : LiteralLocalEvent s q)
    (inScope : event.declaration.Scoped) (produced : event.declaration.Produced)
    {body : Equation} (authored : body ∈ event.declaration.associated)
    {name : Nat} (used : name ∈ (normalize body.rhs).variables) :
    name ∈ event.declaration.inputNames ∨
      ∃ binder ∈ event.declaration.outputBinders,
        binder.name = name ∧
        ∃ (i j : Nat) (entry : LiteralWhereEntry) (eqn : Equation),
          event.whereEntries[i]? = some entry ∧
          event.declaration.requirements[i]? = some entry.clause ∧
          entry.clause.id = binder.clause ∧
          entry.clause.outputs[j]? = some eqn ∧
          eqn.id = binder.equation ∧ eqn.rhs = .var name := by
  rcases inScope.2.1 body authored name used with input | output
  · exact .inl input
  · right
    obtain ⟨binder,member,binderName⟩ := List.mem_map.mp output
    obtain ⟨clause,declared,clauseId,eqn,clauseEqn,eqnId,rhs⟩ := produced binder member
    obtain ⟨i,atClause⟩ := List.getElem?_of_mem declared
    obtain ⟨j,atEqn⟩ := List.getElem?_of_mem clauseEqn
    have within : i < event.declaration.requirements.length :=
      (List.getElem?_eq_some_iff.mp atClause).1
    have inside : i < event.whereEntries.length := by simpa only [event.whereCount] using within
    let entry := event.whereEntries[i]
    have atEntry : event.whereEntries[i]? = some entry := List.getElem?_eq_getElem inside
    have atSame := (event.whereAt i entry atEntry).1
    have sameClause : entry.clause = clause := Option.some.inj (atSame.symm.trans atClause)
    refine ⟨binder,member,binderName,i,j,entry,eqn,atEntry,atSame,?_,?_,eqnId,?_⟩
    · simpa only [sameClause] using clauseId
    · simpa only [sameClause] using atEqn
    · simpa only [binderName] using rhs

/-- When the actual child demands are independently produced by the
literal declaration rule, the where-produced binder denotes the exact
emitted target of its original equation, not a selected equal model row. -/
theorem where_binder_has_exact_emitted_target392
    {s : State} {q : Request} (event : LiteralLocalEvent s q)
    (produced : event.declaration.Produced)
    (names : GeneralDeclarativeSourceEmission322.Names)
    (placement : GeneralDeclarativeEmissionForest322.Placement)
    (actualChildren : event.whereEntries.map LiteralWhereEntry.demand =
      GeneralDeclarativeEmissionForest322.children event.declaration names placement)
    {binder : OutputBinder} (member : binder ∈ event.declaration.outputBinders) :
    ∃ (i j : Nat) (entry : LiteralWhereEntry) (eqn : Equation) (out : GeneralSourceState.Output),
      event.whereEntries[i]? = some entry ∧
      event.declaration.requirements[i]? = some entry.clause ∧
      entry.clause.id = binder.clause ∧
      entry.clause.outputs[j]? = some eqn ∧ eqn.id = binder.equation ∧
      eqn.rhs = .var binder.name ∧
      entry.demand.outputs[j]? = some out ∧ out.name = eqn.name ∧
      out.target = names.output binder.name := by
  obtain ⟨clause,declared,clauseId,eqn,clauseEqn,eqnId,rhs⟩ := produced binder member
  obtain ⟨i,atClause⟩ := List.getElem?_of_mem declared
  obtain ⟨j,atEqn⟩ := List.getElem?_of_mem clauseEqn
  have within : i < event.declaration.requirements.length := (List.getElem?_eq_some_iff.mp atClause).1
  have inside : i < event.whereEntries.length := by simpa only [event.whereCount] using within
  let entry := event.whereEntries[i]
  have atEntry : event.whereEntries[i]? = some entry := List.getElem?_eq_getElem inside
  have atSame := (event.whereAt i entry atEntry).1
  have sameClause : entry.clause = clause := Option.some.inj (atSame.symm.trans atClause)
  have childProduced : entry.demand =
      GeneralDeclarativeSourceEmission322.demand event.declaration clause names
        (placement.compound clause) (placement.targets clause) := by
    have h := congrArg (fun (ds : List GeneralDeclarativeDemand320.Demand) => ds[i]?) actualChildren
    simpa only [GeneralDeclarativeEmissionForest322.children,List.getElem?_map,
      atEntry,atClause,Option.map_some,Option.some.injEq] using h
  let out := GeneralDeclarativeSourceEmission322.useOutput event.declaration names (placement.targets clause) eqn
  have outPosition : entry.demand.outputs[j]? = some out := by
    rw [childProduced]
    simp only [GeneralDeclarativeSourceEmission322.demand,List.getElem?_map,atEqn,Option.map_some,out]
  have outputName : out.name = eqn.name := rfl
  have declaredName : binder.name ∈ event.declaration.outputNames :=
    List.mem_map.mpr ⟨binder,member,rfl⟩
  have outTarget : out.target = names.output binder.name := by
    simp [out,GeneralDeclarativeSourceEmission322.useOutput,GeneralDeclarationDemands.outputTarget,
      GeneralDeclarativeSourceEmission322.Names.old,rhs,normalize,declaredName]
  exact ⟨i,j,entry,eqn,out,atEntry,atSame,sameClause ▸ clauseId,sameClause ▸ atEqn,eqnId,rhs,
    outPosition,outputName,outTarget⟩

private theorem input_lookup_from_name_table392
    (names : Nat → GeneralDeclarativeWhere319.Capture) (selected : List Nat)
    {name : Nat} (member : name ∈ selected) :
    (selected.map fun n => (n,names n)).lookup name = some (names name) := by
  induction selected with
  | nil => cases member
  | cons head rest ih =>
    by_cases same : name = head
    · subst head
      simp
    · have more : name ∈ rest := (List.mem_cons.mp member).resolve_left same
      simp [List.lookup_cons,beq_eq_false_iff_ne.mpr same,ih more]

/-- A where-produced binder in the actual existing logical placement
table reads as the same fixed output point in the authored RHS.
The exact child demands and materialized binder list must come from
the selected source, not from a matching later model or target. -/
theorem exact_where_output_supplies_body_capture392
    {s : State} {q : Request} (event : LiteralLocalEvent s q)
    (produced : event.declaration.Produced)
    (placement : GeneralDeclarativeEmissionForest322.Placement)
    (addresses : Nat → Nat → Nat)
    (input : Nat → GeneralDeclarativeWhere319.Capture)
    (actualChildren : event.whereEntries.map LiteralWhereEntry.demand =
      GeneralDeclarativeEmissionForest322.children event.declaration
        (GeneralDeclarativeProducedNames325.table event.declaration addresses input) placement)
    (actualCaptures : event.captures =
      ((event.declaration.inputNames ++ event.declaration.outputNames).map fun n =>
        (n,(GeneralDeclarativeProducedNames325.table event.declaration addresses input).input n)))
    {binder : OutputBinder} (member : binder ∈ event.declaration.outputBinders)
    (body : Equation) :
    ∃ (i j : Nat) (entry : LiteralWhereEntry) (eqn : Equation) (out : GeneralSourceState.Output),
      event.whereEntries[i]? = some entry ∧
      entry.clause.id = binder.clause ∧
      entry.clause.outputs[j]? = some eqn ∧ eqn.id = binder.equation ∧
      eqn.rhs = .var binder.name ∧ entry.demand.outputs[j]? = some out ∧
      out.name = eqn.name ∧
      writtenBodySlot392 event (.explicit body) binder.name = some ⟨out.target,out.target,out.target⟩ := by
  let names := GeneralDeclarativeProducedNames325.table event.declaration addresses input
  obtain ⟨i,j,entry,eqn,out,atEntry,_,clauseId,atEqn,eqnId,rhs,atOutput,sourceName,target⟩ :=
    where_binder_has_exact_emitted_target392 event produced names placement actualChildren member
  have declared : binder.name ∈ event.declaration.outputNames :=
    List.mem_map.mpr ⟨binder,member,rfl⟩
  have found : event.captures.lookup binder.name = some (names.input binder.name) := by
    rw [actualCaptures]
    exact input_lookup_from_name_table392 names.input _ (List.mem_append_right _ declared)
  have point : names.input binder.name = ⟨out.target,out.target,out.target⟩ := by
    rw [target]
    simp [names,GeneralDeclarativeProducedNames325.table,declared]
  exact ⟨i,j,entry,eqn,out,atEntry,clauseId,atEqn,eqnId,rhs,atOutput,sourceName,by
    simpa only [writtenBodySlot392,point] using found⟩

end Yulang.GeneralDeclarativeI65
#print axioms Yulang.GeneralDeclarativeI65.original_rhs_name_has_input_or_where_producer392

#print axioms Yulang.GeneralDeclarativeI65.where_binder_has_exact_emitted_target392

#print axioms Yulang.GeneralDeclarativeI65.exact_where_output_supplies_body_capture392
```

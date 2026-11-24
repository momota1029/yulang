# Cycle 394: record/join 内の宣言型を元 RHS の構造に残す

I-69 の先頭 S13bbba のみ。正本 `9546c99d2ce53db79b1493046f850cb5c818f75d`、inbox `5e202637769e290325b60e4425812e784428f3d7`。[二つの不足の出所](https://github.com/momota1029/yulang/blob/e44176405150be94e27ea50b306dd534ebbde340/notes/design/dots-cycle-392-i69-missing-source-facts.md) は C392 の (a) のまま。局所 rule は元の source body/capture から RHS を作るもの。retention の S13bbbb は変更しない。

## 新しい構造的な論理 RHS

`SourceRhsCode394` は元 binder と実 logical center、record のラベル・payload/tail、variant の tag、join の左右、宣言済み nominal application の順つき引数を再帰的に保つ。record/join の中の実名目型を、普通の translation に誤って回したり、内側の native 型を scalar に潰したりしない。さらに native の value argument 自体が構造式でも subexpression を保持できる。type/row を区別し、捕捉点と inherited invariant の下端/上端を残す。構造式を勝手に interval の点に評価するのではなく、式として別に持つ。古い pure native に戻せる場合だけ、C392 と同じく型式は explicit point に射影する。

`CompoundSourceRhs394` の actual 元 source rule は、C392 と同じ actual `Use` と現 (kind/variance) table、C393 の actual head/where/default slot read と、その位置の independent `TypedBodyCapture392` を使う。候補選択は行わない。構造 node は子の証拠を独立に再帰して元順を保持する。元 Body は `Supplies`、same original output `Fin` ordinal/target は actual demand から読む。`OriginalCompoundOutput394.emit` がこれらと typed RHS tree を持つ **論理的中間式**を作り、`compound_emit_is_original_source394` が元の normalized source を正確に取り戻す。`compound_source_rhs_functional394` は同じ source と同じ actual capture/context でこの code が一意。

## 元 wire を変更しない

`native_rhs_embeds_in_original_compound394` で既存 C392 の pure-native RHS の任意長/任意深さの実導出を埋め込み、端点/元 vector をそのまま復元する。 `existing_native_output_has_same_wire394` は実 C393 `AuthoredOutput` の native/tagged branch から、same Body / same requested のまま、**既存 C386 の literal write と同じ bytes-level syntax**（Lean の write 値の等式）へ射影する。新しい compound に flat vector の順や出力 constructor を勝手に与えない。 `none` は既存 wire への部分射影がないということに限り、言語の拒否ではない。

## 残る本物の論点

この新しい tree で元の structural RHS を作る規則は追加したが、既存 `.declared target Pattern Arguments` は bare/tagged root の flat typed vector。任意の compound/code を同じ receipt に運ぶ全体の実生成規則と、型付き source の primitive 等の参加、及び **全ての実選択**からこの source frame/typed body proof が出る事実がまだない。C393 の `AuthoredBodyFrame` は実 source 宣言と actual placement を要求するが、C384 key/kids・C386 arbitrary eventAt から勝手にそれを得ない。既存 wire、固定 theorem の文、`LocalSource` の全域、受理条件、再帰/停止性、S13bbbb、Step 2/3 を変更しない。これは spec の意味未決ではなく、論理中間表現から固定 receipt への対応の未実装。S13bbba の全称は未完で、追加分割なし。

## 元 Body から typed code と証拠を直接作る

同じ open obligation の `deriveOriginalCompoundOutput394` は、既に計算した code や per-output body proof を受け取らない。actual authored original binder の `SourceBindingReads394` が名前/型種の evidence を返し、元 output ordinal の名前で actual `Supplies` を取得する。その original explicit/default body の normalized syntax を、`readUse` と declaration table、再帰する record/variant/join/value/row bound に沿って処理し、生成した logical typed tree と `CompoundSourceRhs394` の証拠を同時に返す。構造 node は前後の実 subexpression から作ることも証明した。成功は original output target の model-free source rule に限る。source binding evidence から任意の選択全てへ広げたわけでも、新しい checker/refusal を登録したわけでもない。full tree の旧 wire 対応は変わらず未実装。

## strict source/where と wire projection の確認

元宣言の associated name が well-formed（重複なし）なら、同じ actual ordinal における compound equation は、元 Body と typed tree の双方が一意。nested native の value argument のどこかに record/join がある場合、元の bare/tagged native projection は **子構造を失わずには動かない**（ここで計算した旧 projection の `none`、言語の拒否ではない）。

`compound_where_binder_is_kinded_original_slot394` は、元 `OutputBinder` が指定する **同じ where clause/output equation** から発行される child target と、compound RHS が読む capture を同一 point にする。既存の C393 実 source frame の where/name table を直接使い、**親の既成 C386 receipt や全 output batch を仮定しない**。actual typed argument proof の value/row kind は同じ point に運ぶ。これが全実選択から独立に生成されること、及び compound equation の same literal wire への一般対応はまだ別。

以下は固定 source module の immutable replay input で Lean 4.35.0 `--stdin --trust=0 -DwarningAsError=true` PASS。wire projection の二件は `[propext, Quot.sound]`、exact source uniqueness と where kind の二件は `[propext, Classical.choice, Quot.sound]`。新規 fixture/別 module なし。

```lean
import Yulang.GeneralDeclarativeI65CompoundSourceRhs394

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarations (Equation)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

/-- Same actual source supplier and same generated logical RHS at
this original requested output in an identified declaration. -/
theorem fixed_compound_source_output_unique394 {s q f ordinal}
    (first last : OriginalCompoundOutput394 (s := s) (q := q) f ordinal)
    (unique : (f.decl.associated.map Equation.name).Nodup) :
    first.emit = last.emit := by
  let roles := (authoredRegistry s.current).roles
  have source₁ := (GeneralDictionaryAssociatedProvenance.lookup_exact
    roles f.decl unique _ _).mpr first.supplied
  have source₂ := (GeneralDictionaryAssociatedProvenance.lookup_exact
    roles f.decl unique _ _).mpr last.supplied
  have body : first.body = last.body := Option.some.inj (source₁.symm.trans source₂)
  have rhs₂ := last.derived
  rw [← body] at rhs₂
  have code := compound_source_rhs_functional394 first.derived _ rhs₂
  simp only [OriginalCompoundOutput394.emit,body,code]

mutual
/-- A logical path to record/join anywhere in a typed value
argument. Do not flatten it out to manufacture the older wire. -/
inductive StructureDescendant394 : SourceRhsCode394 → Prop where
  | record : StructureDescendant394 (.record label payload tail)
  | join : StructureDescendant394 (.join first last)
  | variant : StructureDescendant394 payload → StructureDescendant394 (.variant tag payload)
  | nominal : StructureInArguments394 args → StructureDescendant394 (.nominal ctor args)

inductive StructureInArguments394 : List SourceRhsArg394 → Prop where
  | head : StructureDescendant394 value → StructureInArguments394 (.valueExpression value :: rest)
  | tail : StructureInArguments394 rest → StructureInArguments394 (first :: rest)
end

theorem nested_structure_has_no_plain_endpoint394 {code : SourceRhsCode394}
    (path : StructureDescendant394 code) : plainEndpoint394 code = none := by
  exact StructureDescendant394.rec
    (motive_1 := fun c _ => plainEndpoint394 c = none)
    (motive_2 := fun args _ => plainArgs394 args = none)
    rfl
    rfl
    (fun _ _ => rfl)
    (fun _ noArgs => by simp only [plainEndpoint394,noArgs,Option.map_none])
    (fun _ cannot => by simp [plainArgs394,plainArg394,cannot])
    (fun _ cannot => by simp [plainArgs394,cannot])
    path

theorem structural_native_subterm_is_not_flat_wire394
    {args : List SourceRhsArg394} (path : StructureInArguments394 args)
    (target tag ctor : Nat) :
    projectOldNativeLiteral394 target (.nominal ctor args) = none ∧
      projectOldNativeLiteral394 target (.variant tag (.nominal ctor args)) = none := by
  have blocked := nested_structure_has_no_plain_endpoint394
    (StructureDescendant394.nominal (ctor := ctor) path)
  have noArguments : plainArgs394 args = none := by simpa [plainEndpoint394] using blocked
  simp [projectOldNativeLiteral394,noArguments]

open GeneralDeclarations (OutputBinder)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (normalize)
open CommonDeclaredNominalInspection (Parameter)

private theorem capture_table_lookup394 (actual : Nat → Capture) (names : List Nat)
    {binder : Nat} (member : binder ∈ names) :
    (names.map fun n => (n,actual n)).lookup binder = some (actual binder) := by
  induction names with
  | nil => cases member
  | cons head rest ih =>
    by_cases same : binder = head
    · subst head
      simp
    · have later : binder ∈ rest := (List.mem_cons.mp member).resolve_left same
      simp [List.lookup_cons,beq_eq_false_iff_ne.mpr same,ih later]

theorem compound_used_binder_keeps_actual_kind394 {s : State} {slots : Nat → Option Capture}
    {context : Bool} {p : Parameter} {binder : Nat} {arg : SourceRhsArg394}
    {captured : Capture} (read : slots binder = some captured)
    (used : CompoundSourceArg394 s slots context p (.var binder) arg) :
    TypedBodyCapture392 s captured p.kind := by
  cases used with
  | pointValue mode _ found shape =>
    cases Option.some.inj (read.symm.trans found)
    simpa only [mode] using shape
  | intervalValue mode _ found shape =>
    cases Option.some.inj (read.symm.trans found)
    simpa only [mode] using shape
  | pointRow mode _ found shape =>
    cases Option.some.inj (read.symm.trans found)
    simpa only [mode] using shape
  | intervalRow mode _ found shape =>
    cases Option.some.inj (read.symm.trans found)
    simpa only [mode] using shape
  | valueExpression _ notVar _ => exact False.elim (notVar _ rfl)

/-- The original where-only binder used by the compound body
hits the actual generated child output point; no already emitted
root receipt/batch or model is needed to derive it. -/
theorem compound_where_binder_is_kinded_original_slot394
    {s q} (f : AuthoredBodyFrame393 s q) (produced : f.decl.Produced)
    {binder : OutputBinder} (member : binder ∈ f.decl.outputBinders)
    (body : Equation) {context : Bool} {p : Parameter} {argument : SourceRhsArg394}
    (used : CompoundSourceArg394 s (f.slots (.explicit body)) context p (.var binder.name) argument) :
    ∃ (i j : Nat) (entry : LiteralWhereEntry) (eqn : Equation) (out : GeneralSourceState.Output),
      f.clauses[i]? = some entry ∧ entry.clause.id = binder.clause ∧
      entry.clause.outputs[j]? = some eqn ∧ eqn.id = binder.equation ∧
      eqn.rhs = .var binder.name ∧ entry.demand.outputs[j]? = some out ∧
      out.name = eqn.name ∧
      f.slots (.explicit body) binder.name = some ⟨out.target,out.target,out.target⟩ ∧
      TypedBodyCapture392 s ⟨out.target,out.target,out.target⟩ p.kind := by
  obtain ⟨clause,inDecl,clauseId,eqn,inClause,eqnId,rhs⟩ := produced binder member
  obtain ⟨i,pos⟩ := List.getElem?_of_mem inDecl
  obtain ⟨j,eqPos⟩ := List.getElem?_of_mem inClause
  let entry := f.whereFor clause
  let out := GeneralDeclarativeSourceEmission322.useOutput f.decl f.names (f.placement.targets clause) eqn
  have named : binder.name ∈ f.decl.outputNames := List.mem_map.mpr ⟨binder,member,rfl⟩
  have atEntry : f.clauses[i]? = some entry := by
    simp [AuthoredBodyFrame393.clauses,pos,entry]
  have atOut : entry.demand.outputs[j]? = some out := by
    simp [entry,AuthoredBodyFrame393.whereFor,GeneralDeclarativeSourceEmission322.demand,eqPos,out]
  have target : out.target = f.names.output binder.name := by
    simp [out,GeneralDeclarativeSourceEmission322.useOutput,GeneralDeclarationDemands.outputTarget,
      GeneralDeclarativeSourceEmission322.Names.old,rhs,normalize,named]
  have point : f.names.input binder.name = ⟨out.target,out.target,out.target⟩ := by
    rw [target]
    simp [AuthoredBodyFrame393.names,GeneralDeclarativeFrameReadback325.sourceNames,
      GeneralDeclarativeProducedNames325.table,named]
  have read := capture_table_lookup394 f.names.input _ (List.mem_append_right f.decl.inputNames named)
  have slot : f.slots (.explicit body) binder.name = some ⟨out.target,out.target,out.target⟩ := by
    simpa only [AuthoredBodyFrame393.slots,AuthoredBodyFrame393.captures,point] using read
  exact ⟨i,j,entry,eqn,out,atEntry,clauseId,eqPos,eqnId,rhs,atOut,rfl,slot,
    compound_used_binder_keeps_actual_kind394 slot used⟩

end Yulang.GeneralDeclarativeI65

#print axioms Yulang.GeneralDeclarativeI65.fixed_compound_source_output_unique394
#print axioms Yulang.GeneralDeclarativeI65.nested_structure_has_no_plain_endpoint394
#print axioms Yulang.GeneralDeclarativeI65.structural_native_subterm_is_not_flat_wire394

#print axioms Yulang.GeneralDeclarativeI65.compound_where_binder_is_kinded_original_slot394
```

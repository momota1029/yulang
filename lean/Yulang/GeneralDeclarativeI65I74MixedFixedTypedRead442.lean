import Yulang.GeneralDeclarativeI65I74MixedFixedRead442

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.MixedFixed442
open GeneralDeclarativeI65
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open GeneralDictionaryAssociatedProvenance (Body supplies_unique)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarations (DeclarationChecked)
open CommonDeclaredNominalInspection (Parameter)
open RefPositions441 (pattern layout rowCov valueInv)

structure OriginalRefPlan {s : GeneralDeclarativeI65.State} {key rowBinder valueBinder}
    (plan : B6MixedRhs401 s false (pattern key rowBinder valueBinder)) where
  use : Use s.current.environment key 2
  mode : names use.mode 2 = some layout
  table : s.modes[key]? = some layout
  exactPlan : plan = refPlan key rowBinder valueBinder use mode table

private def planConfirmed {s : GeneralDeclarativeI65.State} {key rowBinder valueBinder}
    (a b : Parameter) (use : Use s.current.environment key 2)
    (mode : names use.mode 2 = some [a,b]) (table : s.modes[key]? = some [a,b])
    (rk : a.kind = .row) (rm : (CommonRecursiveNominalIntervals.effectiveParameter false a).variance ≠ .invariant)
    (vk : b.kind = .value) (vm : (CommonRecursiveNominalIntervals.effectiveParameter false b).variance = .invariant)
    (h : [a,b] = layout) :
    OriginalRefPlan (.declaredApp key use mode table
      (.cons (.rowPoint rowBinder rk rm ()) (.cons (.valueInterval valueBinder vk vm ()) .nil))) := by
  have eq := List.cons.inj h
  have aEq : a = rowCov := eq.1
  have bEq : b = valueInv := (List.cons.inj eq.2).1
  subst a
  subst b
  exact ⟨use,mode,table,rfl⟩

/-- Check mode and written argument kinds on the original indexed plan,
reading neither a value nor the output target as a source of annotations. -/
def readRefPlan442 {s : GeneralDeclarativeI65.State} {key rowBinder valueBinder}
    (plan : B6MixedRhs401 s false (pattern key rowBinder valueBinder)) :
    Option (OriginalRefPlan plan) :=
  match plan with
  | @MixedRhs401.declaredApp _ _ [a,b] _ _ _ use mode table
      (.cons (.rowPoint _ rk rm ()) (.cons (.valueInterval _ vk vm ()) .nil)) =>
    if h : [a,b] = layout then some (planConfirmed a b use mode table rk rm vk vm h) else none
  | _ => none

private def explicitRefBody {q : Request} (i : Fin q.demand.outputs.length)
    (bodyId key rowBinder valueBinder : Nat) : Body :=
  .explicit ⟨bodyId,q.demand.outputs[i].name,pattern key rowBinder valueBinder⟩

structure CheckedRefOutput {s : I72.State} {q : Request}
    (f : AuthoredBodyFrame393 s.core q) (i : Fin q.demand.outputs.length)
    (key rowBinder valueBinder bodyId : Nat) where
  out : OriginalOutput (s := s) f i
  exactKey : out.key = key
  exactRow : out.rowBinder = rowBinder
  exactValue : out.valueBinder = valueBinder
  exactBodyId : out.bodyId = bodyId

def replayedOriginalRef442 {s : I72.State} {q : Request}
    {f : AuthoredBodyFrame393 s.core q} {i : Fin q.demand.outputs.length}
    (key rowBinder valueBinder bodyId : Nat) (distinct : rowBinder ≠ valueBinder)
    (o : NamedMixedOutput401 s.b6 f i) : Option (CheckedRefOutput (s := s) f i key rowBinder valueBinder bodyId) := by
  rcases o with ⟨body,supplied,plan,original,rhs,formed⟩
  by_cases h : body = explicitRefBody i bodyId key rowBinder valueBinder
  · subst body
    exact do
      let cert ← readRefPlan442 plan
      match hr : f.slots (explicitRefBody i bodyId key rowBinder valueBinder) rowBinder,
          hv : f.slots (explicitRefBody i bodyId key rowBinder valueBinder) valueBinder with
      | some row, some value =>
        some ⟨⟨key,rowBinder,valueBinder,distinct,cert.use,cert.mode,cert.table,bodyId,supplied,
          original.trans (congrArg some cert.exactPlan),row,value,hr,hv⟩,rfl,rfl,rfl,rfl⟩
      | _,_ => none
  · exact none

theorem original_ref_encoded_output_nonflattened442
    {s : I72.State} {q : Request} {f : AuthoredBodyFrame393 s.core q} {i : Fin q.demand.outputs.length}
    (a : OriginalOutput (s := s) f i) :
    Check408.encodeRhs a.named.rhs = .node 4 [a.key] [
      .node 11 ([1,0] ++ Check408.nameTriple a.rowBinder a.rowCap) [],
      .node 10 ([0,2] ++ Check408.nameTriple a.valueBinder a.valueCap) []] :=
  rfl

/-- Same declared output slot and exact checked source body determine the
read indexed plan and its exact substitution, independently of a report. -/
theorem original_named_output_unique442 {s : I72.State} {q : Request}
    {f : AuthoredBodyFrame393 s.core q} {i : Fin q.demand.outputs.length}
    (checked : DeclarationChecked (authoredRegistry s.core.current).constructors
      (authoredRegistry s.core.current).roles f.decl)
    (a b : NamedMixedOutput401 s.b6 f i) : a = b := by
  have body := supplies_unique (authoredRegistry s.core.current).roles f.decl
    checked.identified.2.2.1 q.demand.outputs[i].name a.body b.body a.supplied b.supplied
  rcases a with ⟨bodyA,supA,planA,readA,rhsA,formedA⟩
  rcases b with ⟨bodyB,supB,planB,readB,rhsB,formedB⟩
  dsimp at body
  subst bodyB
  have plan := Option.some.inj (readA.symm.trans readB)
  subst planB
  have rhs := Option.some.inj (formedA.symm.trans formedB)
  subst rhsB
  rfl

def Replay.i0 {p : Checker408.Problem} (r : Replay p) : Fin p.root.demand.outputs.length :=
  ⟨0,by rw [r.onlyOutput]; decide⟩

/-- The originally resolved head determines the only two binder IDs.
The original literal output determines its own body ID. -/
abbrev ReplayReadOwnOutput {p : Checker408.Problem} (r : Replay p) :=
    Σ bodyId, CheckedRefOutput (s := p.state) r.event.frame r.i0
      r.original.key r.original.rowBinder r.original.valueBinder bodyId

def Replay.readOwnRefOutput {p : Checker408.Problem} (r : Replay p) :
    Option (ReplayReadOwnOutput r) :=
  let output := r.event.outputs r.i0
  match output.body with
  | .explicit eq =>
    (replayedOriginalRef442 r.original.key r.original.rowBinder r.original.valueBinder
      eq.id r.original.separateBinders output).map (fun o => ⟨eq.id,o⟩)
  | .default _ _ _ => none

theorem original_replayed_ref_equates_same_event_output442 {p : Checker408.Problem}
    (r : Replay p) (a : OriginalOutput (s := p.state) r.event.frame r.i0) :
    a.named = r.event.outputs r.i0 := by
  apply original_named_output_unique442
  exact r.exactDecl ▸ r.original.checked

theorem original_replayed_ref_is_the_fixed_target_slice442 {p : Checker408.Problem}
    (r : Replay p) (a : OriginalOutput (s := p.state) r.event.frame r.i0) (m : I72.Model) :
    I72.FixedTargets m r.event ↔
      CommonNominalFullCarrier.Equivalent (m.assignment p.root.demand.outputs[r.i0].target).1
        (a.actualValue m) := by
  have same (j : Fin p.root.demand.outputs.length) : j = r.i0 := Fin.ext (by
    have top : j.val < 1 := Nat.lt_of_lt_of_eq j.isLt r.onlyOutput
    change j.val = 0
    omega)
  have output := original_replayed_ref_equates_same_event_output442 r a
  have result := original_output_fixed_iff_same_target_equals_mixed_value442 a m
  rw [output] at result
  exact ⟨fun h => result.mp (h r.i0),fun h j => same j ▸ result.mpr h⟩

theorem exact_ref_output_uses_original_head_centers442 {p : Checker408.Problem}
    (r : Replay p) (a : ReplayReadOwnOutput r) :
    a.2.out.rowCap = GeneralDeclarativeWitnessDeclaredState357.point r.original.rowName ∧
    a.2.out.valueCap = GeneralDeclarativeWitnessDeclaredState357.point r.original.valueName := by
  have written : r.event.frame.decl.head = [pattern r.original.key
      r.original.rowBinder r.original.valueBinder] := by
    rw [r.exactDecl]
    exact r.original.written
  have separate : r.event.frame.decl.OutputOnly := by
    rw [r.exactDecl]
    exact r.original.checked.outputOnly
  have locale (n : Nat) (side : n = r.original.rowBinder ∨ n = r.original.valueBinder) :
      n ∈ r.event.frame.decl.inputNames := by
    rw [GeneralDeclarations.Declaration.inputNames,written]
    rcases side with h | h <;> simp [h,pattern,GeneralDeclarationPatterns.normalizeArgs,
      GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.variablesArgs,
      GeneralDeclarationPatterns.Pattern.variables]
  have pointRow := explicit_authored_head_slot395 r.event.frame separate
    (body := ⟨a.2.out.bodyId,p.root.demand.outputs[r.i0].name,
      pattern a.2.out.key a.2.out.rowBinder a.2.out.valueBinder⟩)
    a.2.out.rowBinder (locale _ (.inl a.2.exactRow))
  have pointValue := explicit_authored_head_slot395 r.event.frame separate
    (body := ⟨a.2.out.bodyId,p.root.demand.outputs[r.i0].name,
      pattern a.2.out.key a.2.out.rowBinder a.2.out.valueBinder⟩)
    a.2.out.valueBinder (locale _ (.inr a.2.exactValue))
  have row := Option.some.inj (a.2.out.row.symm.trans pointRow)
  have val := Option.some.inj (a.2.out.value.symm.trans pointValue)
  rw [a.2.exactRow,r.exactInput,r.original.rowCapture] at row
  rw [a.2.exactValue,r.exactInput,r.original.valueCapture] at val
  exact ⟨row,val⟩

end Yulang.GeneralDeclarativeI65.I72.MixedFixed442

import Yulang.GeneralDeclarativeI65I74RefPositionRule441
import Yulang.GeneralDeclarativeI65I72TypedTargetRows403
import Yulang.GeneralDeclarativeI65I74RefPositionFidelity441

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.MixedFixed442
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration Equation)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open GeneralDictionaryAssociatedProvenance (Body Supplies)
open CommonNominalFullCarrier (Ty Equivalent nominal)
open RefPositions441 (layout rowCov valueInv pattern)

/-- Real ordered mixed B6 syntax, before instantiation: these are two original
lexical binders and a genuine declared Use, not a flattened ordinary Expr. -/
def refPlan {s : GeneralDeclarativeI65.State} (key rowBinder valueBinder : Nat)
    (use : Use s.current.environment key 2) (modes : names use.mode 2 = some layout)
    (table : s.modes[key]? = some layout) :
    B6MixedRhs401 s false (pattern key rowBinder valueBinder) :=
  .declaredApp key use modes table (.cons (.rowPoint rowBinder rfl (by decide) ())
    (.cons (.valueInterval valueBinder rfl rfl ()) .nil))

def refTree {s : GeneralDeclarativeI65.State} {slots : Nat → Option Capture}
    (key rowBinder valueBinder : Nat)
    (use : Use s.current.environment key 2) (modes : names use.mode 2 = some layout)
    (table : s.modes[key]? = some layout) {rowCap valueCap : Capture}
    (r : slots rowBinder = some rowCap) (v : slots valueBinder = some valueCap) :
    NamedMixedTree401 s slots false (pattern key rowBinder valueBinder) :=
  .declaredApp key use modes table (.cons (.rowPoint rowBinder rfl (by decide) ⟨rowCap,r⟩)
    (.cons (.valueInterval valueBinder rfl rfl ⟨valueCap,v⟩) .nil))

theorem ref_tree_instantiates_exact_slots442 {s : GeneralDeclarativeI65.State} {slots : Nat → Option Capture} {key rowBinder valueBinder : Nat}
    {use : Use s.current.environment key 2} {modes : names use.mode 2 = some layout}
    {table : s.modes[key]? = some layout} {rowCap valueCap : Capture}
    (r : slots rowBinder = some rowCap) (v : slots valueBinder = some valueCap) :
    substituteMixedRhs401 (instantiateName401 slots) (refPlan (s := s) key rowBinder valueBinder use modes table)
      = some (refTree key rowBinder valueBinder use modes table r v) := by
  simp [refPlan,refTree,substituteMixedRhs401,substituteMixedArgs401,substituteMixedArg401,
    instantiateName401_of_some r,instantiateName401_of_some v]

theorem actual_ref_value_reads_own_typed_centers442
    {s : GeneralDeclarativeI65.State} {slots : Nat → Option Capture} {key rowBinder valueBinder : Nat}
    {use : Use s.current.environment key 2} {modes : names use.mode 2 = some layout}
    {table : s.modes[key]? = some layout} {rowCap valueCap : Capture}
    (r : slots rowBinder = some rowCap) (v : slots valueBinder = some valueCap) (m : I72.Model) :
    evaluateMixedRhs401 (actualNamedMixedRead401 m) (refTree (s := s) key rowBinder valueBinder
      use modes table r v) =
        some (nominal key [.inr (m.assignment rowCap.center).2,.inl (m.assignment valueCap.center).1]) :=
  rfl

theorem ref_tree_has_no_legacy_code442
    {s : GeneralDeclarativeI65.State} {slots : Nat → Option Capture} {key rowBinder valueBinder : Nat}
    {use : Use s.current.environment key 2} {modes : names use.mode 2 = some layout}
    {table : s.modes[key]? = some layout} {rowCap valueCap : Capture}
    (r : slots rowBinder = some rowCap) (v : slots valueBinder = some valueCap) :
    fixedValueCode403 (refTree (s := s) key rowBinder valueBinder use modes table r v) = none := rfl

/-- The annotation is read at the actual declaration ordinal and original
output index. The row/value names come from the frame of that same body. -/
structure OriginalOutput {s : I72.State} {q : Request}
    (f : AuthoredBodyFrame393 s.core q) (i : Fin q.demand.outputs.length) where
  key : Nat
  rowBinder : Nat
  valueBinder : Nat
  independent : rowBinder ≠ valueBinder
  use : Use s.core.current.environment key 2
  mode : names use.mode 2 = some layout
  table : s.core.modes[key]? = some layout
  bodyId : Nat
  supplied : Supplies (authoredRegistry s.core.current).roles f.decl q.demand.outputs[i].name
    (.explicit ⟨bodyId,q.demand.outputs[i].name,pattern key rowBinder valueBinder⟩)
  original : s.b6.read q f.ordinal i (.explicit ⟨bodyId,q.demand.outputs[i].name,pattern key rowBinder valueBinder⟩) =
    some (refPlan (s := s.core) key rowBinder valueBinder use mode table)
  rowCap : Capture
  valueCap : Capture
  row : f.slots (.explicit ⟨bodyId,q.demand.outputs[i].name,pattern key rowBinder valueBinder⟩) rowBinder = some rowCap
  value : f.slots (.explicit ⟨bodyId,q.demand.outputs[i].name,pattern key rowBinder valueBinder⟩) valueBinder = some valueCap

def OriginalOutput.named {s q f i} (a : OriginalOutput (s := s) (q := q) f i) :
    NamedMixedOutput401 s.b6 f i :=
  ⟨_,a.supplied,refPlan a.key a.rowBinder a.valueBinder a.use a.mode a.table,a.original,
    refTree a.key a.rowBinder a.valueBinder a.use a.mode a.table a.row a.value,
    ref_tree_instantiates_exact_slots442 a.row a.value⟩

def OriginalOutput.actualValue {s q f i} (a : OriginalOutput (s := s) (q := q) f i)
    (m : I72.Model) : Ty :=
  nominal a.key [.inr (m.assignment a.rowCap.center).2,.inl (m.assignment a.valueCap.center).1]

theorem original_output_keeps_occurrence_and_order442 {s q f i}
    (a : OriginalOutput (s := s) (q := q) f i) :
    a.named.receipt.occurrence = q.occurrence ∧ a.named.receipt.outputOrdinal = i.val ∧
    a.named.receipt.original = q.demand.outputs[i] ∧
    s.b6.read q f.ordinal i a.named.body = some a.named.plan :=
  ⟨rfl,rfl,rfl,a.original⟩

theorem original_output_receipt_reads_a_mixed_rhs442 {s q f i}
    (a : OriginalOutput (s := s) (q := q) f i) (m : I72.Model) :
    a.named.receipt.actualEquation m = some (q.demand.outputs[i].target,a.actualValue m) ∧
    evaluateMixedRhs401 (sourceRead401 m (f.slots a.named.body)) a.named.plan =
      some (a.actualValue m) := by
  refine ⟨rfl,?_⟩
  obtain ⟨x,receipt,typed⟩ := named_mixed_output_is_fixed_equation401 a.named m
  have same : a.actualValue m = x := (Prod.mk.inj (Option.some.inj
    ((show a.named.receipt.actualEquation m = some (_,a.actualValue m) from rfl).symm.trans receipt))).2
  simpa only [same] using typed

/-- Semantic equality at the original assignment target is exactly the
missing obligation. A typed receipt alone does not prove this statement. -/
theorem original_output_fixed_iff_same_target_equals_mixed_value442 {s q f i}
    (a : OriginalOutput (s := s) (q := q) f i) (m : I72.Model) :
    (∃ v, a.named.receipt.actualEquation m = some (q.demand.outputs[i].target,v) ∧
      Equivalent (m.assignment q.demand.outputs[i].target).1 v) ↔
    Equivalent (m.assignment q.demand.outputs[i].target).1 (a.actualValue m) := by
  rw [(original_output_receipt_reads_a_mixed_rhs442 a m).1]
  exact ⟨fun ⟨v,h,eq⟩ => (Prod.mk.inj (Option.some.inj h)).2.symm ▸ eq,
    fun eq => ⟨a.actualValue m,rfl,eq⟩⟩

theorem original_output_has_no_value_only_fixed_code442 {s q f i}
    (a : OriginalOutput (s := s) (q := q) f i) : fixedValueCode403 a.named.rhs = none := rfl

end Yulang.GeneralDeclarativeI65.I72.MixedFixed442

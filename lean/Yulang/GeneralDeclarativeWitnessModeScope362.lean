import Yulang.GeneralDeclarativeWitnessUnaryVarianceLaws362
import Yulang.GeneralDeclarativeWitnessNativeInvariantCut362

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 70000
set_option maxHeartbeats 76000000
namespace Yulang.GeneralDeclarativeWitnessModeScope362
open GeneralDeclarativeWitnessThreeNative362 (Run run authority)
open GeneralDeclarativeWitnessOrderedNativeRelease362 (Opened read)
open GeneralDeclarativeWitnessNativeOrder362 (low high atom holds_yields_typed_context)
open GeneralDeclarativeWitnessNativeInvariantCut362 (bad_in_this_fit emitted_bad_row_obstructs_derivation)
open GeneralDeclarativeWitnessNativeThreeModel362 (model every_fit_retains_source_window)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessSparseVariance357 (Source)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessSparseIntervals357 (Compiled Legal)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives)
open GeneralDeclarativeWitnessNativeInstall360 (Fits NativeViews)
open CommonDeclaredNominalInspection (Registry)
open CommonRecursiveNominalIntervals (ContextWellFormed)
open CommonNominalFullCarrier (subtype_trans)
open GeneralNominalCommonBridge (Assignment)
open PresenceNormalForm (Atom)

def changedBodies : Source 3 2 0 :=
  let authored := GeneralDeclarativeWitnessVarianceFixtures357.source
  {authored with bodies := fun i =>
    if i.val = 0 then .arrow (.inr 0) .empty (.inl 2) .empty else authored.bodies i}

def foreign (e : Environment) : Option Environment := do
  let changed ← GeneralDeclarativeWitnessSparseVariance357.compile changedBodies
  pure ⟨3,2,0,changedBodies,changed,e.source⟩

def foreignTable : Registry := table.set 20 [⟨.value,.contravariant⟩]

structure Tested (r : Run false) where
  old : Opened r authority
  other : Environment
  sourceChanged : foreign r.environment = some other
  originalPoint : Compiled r.environment table false (low r) (high r)
  foreignPoint : Compiled other foreignTable false (low r) (high r)
  originalInherited : Compiled r.environment table true (low r) (high r)
  foreignInherited : Compiled other foreignTable true (low r) (high r)

/-- Even a legitimate declaration table in a separately authored
environment cannot replace the producer's declared modes silently.
The frozen native Code and exact current release remain the same. -/
def measure (r : Run false) : Option (Tested r) := do
  let auth ← read r authority
  match swapped : foreign r.environment with
  | none => none
  | some other =>
    let originalPoint ← GeneralDeclarativeWitnessSparseIntervals357.compile r.environment table false (low r) (high r)
    let foreignPoint ← GeneralDeclarativeWitnessSparseIntervals357.compile other foreignTable false (low r) (high r)
    let originalInherited ← GeneralDeclarativeWitnessSparseIntervals357.compile r.environment table true (low r) (high r)
    let foreignInherited ← GeneralDeclarativeWitnessSparseIntervals357.compile other foreignTable true (low r) (high r)
    pure ⟨auth,other,swapped,originalPoint,foreignPoint,originalInherited,foreignInherited⟩

def verified {r} (x : Tested r) : Bool :=
  decide (x.originalPoint.rows = [atom 60 62] ∧ x.foreignPoint.rows = [atom 62 60] ∧
    x.originalInherited.rows = x.foreignInherited.rows) &&
  (GeneralDeclarativeWitnessSparseIntervals357.compile x.other table true (low r) (high r)).isNone &&
  (GeneralDeclarativeWitnessSparseIntervals357.compile r.environment foreignTable true (low r) (high r)).isNone

theorem unchanged_effective_rows_do_not_authenticate_declared_modes :
    ((run false).bind fun r => (measure r).map verified).getD false = true := by decide +kernel

theorem origin_mode_changes_a_real_model_outcome {r : Run false} {x : Tested r}
    (made : run false = some r) (trial : measure r = some x) (upper : Bool) (v : NativeViews)
    (fit : Fits r.final (model false upper) v) :
    ContextDerives table (model false upper) false (low r) (high r) ∧
    ¬(ContextWellFormed foreignTable false (low r) ∧ ContextWellFormed foreignTable false (high r) ∧
      ContextDerives foreignTable (model false upper) false (low r) (high r)) ∧
    x.originalInherited.rows = x.foreignInherited.rows := by
  have verified := unchanged_effective_rows_do_not_authenticate_declared_modes
  rw [made] at verified
  change ((measure r).map GeneralDeclarativeWitnessModeScope362.verified).getD false = true at verified
  rw [trial] at verified
  have stated := of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
    (show GeneralDeclarativeWitnessModeScope362.verified x = true from verified)).1).1
  obtain ⟨_,h,l⟩ := every_fit_retains_source_window r _ v fit
  have yes := holds_yields_typed_context x.originalPoint _ (by
    intro a included
    rw [stated.1] at included
    cases List.mem_singleton.mp included
    exact subtype_trans h l)
  have bad : atom 62 60 ∈ x.foreignPoint.rows := by rw [stated.2.1]; exact List.mem_cons_self
  have no := (GeneralDeclarativeWitnessFullIntervals357.compiled_full_exact foreignTable (model false upper)
    false (low r) (high r)).mpr
  refine ⟨yes.2.2,?_,stated.2.2⟩
  intro derived
  have out := no derived
  rw [x.foreignPoint.exact,CommonRecursiveNominalIntervals.result_some] at out
  exact bad_in_this_fit false upper (out _ bad)

theorem one_authorized_table_cannot_change_comparison_rows {e f : Environment} {t : Registry} {c a b}
    (authored : Compiled e t c a b) (reader : Compiled f t c a b) :
    reader.rows = authored.rows := Option.some.inj (reader.exact.symm.trans authored.exact)

theorem one_authorized_table_fixes_every_checked_site {e f : Environment} {t : Registry} {c a b}
    (authored : Compiled e t c a b) (reader : Compiled f t c a b)
    (site : GeneralDeclarativeWitnessSparseIntervals357.Site)
    (visited : site ∈ GeneralDeclarativeWitnessSparseIntervals357.visited a ++ GeneralDeclarativeWitnessSparseIntervals357.visited b) :
    ∃ use₁ : GeneralDeclarativeWitnessConstructorModes357.Use e site.1 site.2,
    ∃ use₂ : GeneralDeclarativeWitnessConstructorModes357.Use f site.1 site.2,
    ∃ parameters : List CommonDeclaredNominalInspection.Parameter,
      GeneralDeclarativeWitnessSparseIntervals357.names use₁.mode site.2 = some parameters ∧
      GeneralDeclarativeWitnessSparseIntervals357.names use₂.mode site.2 = some parameters := by
  obtain ⟨x,m,hx,tx⟩ := authored.authority site visited
  obtain ⟨y,n,hy,ty⟩ := reader.authority site visited
  have same := Option.some.inj (tx.symm.trans ty)
  exact ⟨x,y,m,hx,same.symm ▸ hy⟩

end Yulang.GeneralDeclarativeWitnessModeScope362

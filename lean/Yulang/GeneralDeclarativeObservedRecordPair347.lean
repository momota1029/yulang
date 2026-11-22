import Yulang.GeneralDeclarativeObservedRecord347
import Yulang.GeneralDeclarativeEndpointProgram336

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeObservedRecordPair347
open GeneralNominalState (State Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeOrigins321 (Supported Origin)
open GeneralDeclarativeObservedSupport347 (arg attach child_view)
open GeneralDeclarativeObservedRecord347 (Walk rows_backed creates_spine)
open GeneralDeclarativeWherePairView346 (extendBounds preserve)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeEndpointRecord336 (Read)
open GeneralDeclarativeEndpointProgram336 (ready from_supported)
open GeneralDeclarativeOrderedRecord326 (order lookup_unique)
open GeneralNominalCenters (Site)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleCanonicalRows (Row lookup normalize normalize_unique)

theorem order_complete {row : Row α} (unique : (row.map Prod.fst).Nodup)
    (keys : List Nat) (covered : keys ⊆ row.map Prod.fst) :
    ∃ result, order row keys = some result := by
  induction keys with
  | nil => exact ⟨[],rfl⟩
  | cons k more ih =>
    obtain ⟨entry,inRow,same⟩ := List.mem_map.mp (covered List.mem_cons_self)
    obtain ⟨tail,done⟩ := ih (fun _ used => covered (List.mem_cons_of_mem _ used))
    obtain ⟨label,value⟩ := entry
    change label = k at same
    subst label
    have key := lookup_unique unique inRow
    exact ⟨(k,value)::tail,by simp [order,key,done]⟩

/-- Actual independently attributed low/high spines, plus the named
physical interval of their genuine stored site, are sufficient for the
existing I-61 field/residual compiler. All field occurrences are in
source order; no center lookup and no output-based authorization. -/
theorem produces {raw : State} {base : GeneralDeclarativeHead320.State}
    {author : Equation → Origin → Prop} (prior : Supported base done)
    (site : Site rs) (index : Fin (rs site.occurrence.demand.role).arity)
    {ls us : Row Expr} {le ue : Expr} {lowRows highRows : List Equation}
    (lower : Walk raw done author (arg site index).lower ls le lowRows)
    (upper : Walk raw done author (arg site index).upper us ue highRows)
    (shape : List (Nat × Nat)) (tail : Nat) (distinct : (shape.map Prod.fst).Nodup)
    (loKeys : shape.map Prod.fst ⊆ (normalize ls).map Prod.fst)
    (hiKeys : shape.map Prod.fst ⊆ (normalize us).map Prod.fst)
    (m : Assignment) (typed : site.Holds m) (rawModel : Models raw m)
    (fit : GeneralDeclarativeHead320.Models base m) :
    let cap := arg site index
    let rows := lowRows ++ highRows
    let supported := attach (preserve prior cap) raw author rows
    ∃ l h jobs,
      Read supported cap (shape.map Prod.fst) ls us l h le ue ∧
      ready cap shape tail ls us l h le ue = some jobs ∧
      GeneralDeclarativeHead320.Models (appendFacts (extendBounds base cap) rows) m := by
  dsimp only
  obtain ⟨l,orderedL⟩ := order_complete (normalize_unique ls) _ loKeys
  obtain ⟨h,orderedH⟩ := order_complete (normalize_unique us) _ hiKeys
  have all : ∀ row ∈ lowRows ++ highRows, GeneralDeclarativeObservedSyntax347.Appears raw row := by
    intro row used
    rcases List.mem_append.mp used with lo|hi
    · exact (rows_backed lower row lo).choose_spec.1.1
    · exact (rows_backed upper row hi).choose_spec.1.1
  obtain ⟨valid,grown,_⟩ := child_view prior site index author (lowRows++highRows) m typed fit rawModel all
  have input : Read (attach (preserve prior (arg site index)) raw author (lowRows++highRows))
      (arg site index) (shape.map Prod.fst) ls us l h le ue :=
    ⟨valid,distinct,creates_spine _ lower (fun _ used => List.mem_append_left _ used),
      creates_spine _ upper (fun _ used => List.mem_append_right _ used),orderedL,orderedH⟩
  obtain ⟨jobs,made⟩ := from_supported input tail
  exact ⟨l,h,jobs,input,made,grown⟩

end Yulang.GeneralDeclarativeObservedRecordPair347

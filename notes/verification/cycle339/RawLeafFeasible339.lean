import Yulang.GeneralDeclarativeStoppedOrder339
namespace Cycle339LeafProbe
open Yulang
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedBoundary234 (Local local_iff)
open GeneralNominalVersionedDiagnostic232 (OutputConflict ChosenHead ChosenEffects)

/-- A selected raw leaf rules out output conflict. This converts an
independently established head witness to an existential effect model;
it neither uses installation nor transports to an arbitrary given model. -/
theorem exists_effect_model (s : State roles) (r : Registry) (leaf : Occurrence roles)
    (selected : Local r s leaf (.selected k []))
    (head : ∃ m, Models s m ∧ ChosenHead r s leaf k m) :
    ∃ m, Models s m ∧ ChosenEffects r s leaf k m := by
  classical
  have clean : ¬OutputConflict r s leaf k := by
    have found := local_iff.mp selected
    cases found with
    | ordinary _ outer =>
      cases outer with
      | ordinary _ inner =>
        cases inner with
        | selected _ _ noConflict => exact noConflict
  exact Classical.byContradiction (fun noEffects => clean ⟨head,noEffects⟩)

open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalCenteredHeadMatEffects (compileBody bodySchema)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralDeclarativeStoppedOutput339 (ordinary ordinary_holds fixed_target)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDictionaryAssociatedProvenance (lookup)
open GeneralNominalCenters (Plan)

/-- Exact current target/RHS receipts can come from a selected leaf's
current frame witness, even when no effect was installed for that leaf.
The assignment in this bridge is still existential. -/
theorem exists_current_rows (s : State roles) (r : Registry) (leaf : Occurrence roles)
    (selected : Local r s leaf (.selected k []))
    (head : ∃ m, Models s m ∧ ChosenHead r s leaf k m) :
    ∃ (m : GeneralNominalCommonBridge.Assignment) (plan : Plan roles),
      Models s m ∧ Frame r s.core leaf k plan ∧
      ∀ output ∈ requests s.core leaf, ∃ body row,
        lookup roles plan.packet.declaration output.name = some body ∧
        ordinary plan output body = some row ∧ row.left = output.target ∧ Holds m row := by
  obtain ⟨m,fit,_,plan,current,ready,_,accepted⟩ := exists_effect_model s r leaf selected head
  refine ⟨m,plan,fit,current,?_⟩
  intro output requested
  obtain ⟨body,matched,known⟩ := ready output requested
  cases ran : compileBody plan body with
  | none => simp [bodySchema,ran] at known
  | some rhs =>
    have eq := GeneralNominalVersionedEffects231.body_holds_iff plan output.target m body
    let row : GeneralDeclarativeHead320.Equation := ⟨output.target,
      GeneralDeclarativeSubstitution320.logical (GeneralDeclarativeStoppedOutput339.captureFor plan body) .actual rhs⟩
    have compiled : ordinary plan output body = some row := by simp [ordinary,ran,row]
    exact ⟨body,row,matched,compiled,fixed_target compiled,ordinary_holds compiled (eq.mp (accepted.1 output requested body matched))⟩

open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeStoppedOrder339 (compileRequests)
open GeneralSourceState (Output)

theorem ordered_of_current {roles : Roles.RoleDecls} (plan : Plan roles)
    (m : GeneralNominalCommonBridge.Assignment) (items : List Output)
    (authored : ∀ o ∈ items, ∃ body row,
      lookup roles plan.packet.declaration o.name = some body ∧
      ordinary plan o body = some row ∧ row.left = o.target ∧ Holds m row) :
    ∃ rows, compileRequests plan items = some rows ∧
      rows.map Equation.left = items.map Output.target ∧
      ∀ row ∈ rows, Holds m row := by
  induction items with
  | nil => exact ⟨[],rfl,rfl,fun _ no => False.elim (List.not_mem_nil no)⟩
  | cons first rest ih =>
    obtain ⟨b,one,found,written,exactName,trueRow⟩ := authored first List.mem_cons_self
    obtain ⟨tail,more,names,valid⟩ := ih (fun o h => authored o (List.mem_cons_of_mem _ h))
    refine ⟨one::tail,by simp [compileRequests,found,written,more],
      by rw [List.map_cons,List.map_cons,exactName,names],?_⟩
    intro row existsIn
    rcases List.mem_cons.mp existsIn with rfl|later
    · exact trueRow
    · exact valid _ later

theorem exists_ordered_rows (s : State roles) (r : Registry) (leaf : Occurrence roles)
    (selected : Local r s leaf (.selected k []))
    (head : ∃ m, Models s m ∧ ChosenHead r s leaf k m) :
    ∃ (m : GeneralNominalCommonBridge.Assignment) (plan : Plan roles) (rows : List Equation),
      Models s m ∧ Frame r s.core leaf k plan ∧
      compileRequests plan (requests s.core leaf) = some rows ∧
      rows.map Equation.left = (requests s.core leaf).map Output.target ∧
      ∀ row ∈ rows, Holds m row := by
  obtain ⟨m,plan,fit,frame,each⟩ := exists_current_rows s r leaf selected head
  obtain ⟨rows,computed,names,held⟩ := ordered_of_current plan m _ each
  exact ⟨m,plan,rows,fit,frame,computed,names,held⟩

#print axioms exists_effect_model
#print axioms exists_current_rows
#print axioms exists_ordered_rows
end Cycle339LeafProbe

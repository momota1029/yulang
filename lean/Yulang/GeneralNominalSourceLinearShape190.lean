import Yulang.GeneralNominalSourceVariableInstall189
import Yulang.GeneralNominalLinearNamedPlan189

/-! Finite source variable-head declarations determine all query, name and
point-bound plumbing of the initial linear installation theorem. -/
namespace Yulang.GeneralNominalSourceLinearShape190
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadWFBoundary (boundary)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

theorem normalize_variables (names : List Nat) :
    normalizeArgs (names.map Pattern.var) = names.map Pattern.var := by
  induction names with
  | nil => rfl
  | cons name names ih => simp [normalizeArgs,normalize,ih]

theorem variables_variables (names : List Nat) :
    variablesArgs (names.map Pattern.var) = names := by
  induction names with
  | nil => rfl
  | cons name names ih => simp [variablesArgs,Pattern.variables,ih]

theorem source_shape (candidate : Plan roles) (names : List Nat)
    (head : candidate.packet.declaration.head = names.map Pattern.var) :
    GeneralNominalInspection.queries candidate.packet.context.state candidate.packet.context.interpretation
      candidate.packet.declaration = names.map (fun name => .variables [name]) ∧
      candidate.packet.declaration.inputNames = names := by
  constructor
  · simp [GeneralNominalInspection.queries,Declaration.normalHead,head,normalize_variables,
      List.map_map,GeneralNominalInspection.translate]
  · simp [Declaration.inputNames,head,normalize_variables,variables_variables]

theorem initial_entries (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (names : List Nat) (head : candidate.packet.declaration.head = names.map Pattern.var) :
    ∃ entries : List (Nat × Fin candidate.packet.context.state.base.slots),
      entries.map Prod.fst = names ∧
      candidate.packet.bounds = entries.map (fun entry => (entry.2,entry.2)) ∧
      GeneralNominalInspection.queries candidate.packet.context.state candidate.packet.context.interpretation
        candidate.packet.declaration = entries.map (fun entry => .variables [entry.1]) ∧
      candidate.packet.declaration.inputNames = entries.map Prod.fst := by
  have arity : (roles root.demand.role).arity = names.length := by
    have signature := candidate.packet.checked.signature.1
    simpa only [head,List.length_map,frame.role_eq] using signature.symm
  have mapped := GeneralNominalPacketCaptureReadback.locate_sources
    candidate.packet.context.state.base (List.ofFn root.demand.arguments) candidate.packet.bounds frame.located
  have length : candidate.packet.bounds.length = names.length := by
    have sizes := congrArg List.length mapped
    simpa only [List.length_map,List.length_ofFn,arity] using sizes
  have point : ∀ interval ∈ candidate.packet.bounds, interval.1 = interval.2 := by
    intro interval member
    obtain ⟨index,bound,equal⟩ := List.mem_iff_getElem.mp member
    exact (GeneralNominalHeadPointBounds188.boundary_initial_point_bounds state source candidate frame index interval
      (List.getElem?_eq_some_iff.mpr ⟨bound,equal⟩)).1
  let slots := candidate.packet.bounds.map Prod.fst
  let entries := names.zip slots
  have first : entries.map Prod.fst = names := List.map_fst_zip (by simp [slots,length])
  have second : entries.map Prod.snd = slots := List.map_snd_zip (by simp [slots,length])
  have diagonals : slots.map (fun slot => (slot,slot)) = candidate.packet.bounds := by
    simp only [slots,List.map_map]
    calc
      _ = candidate.packet.bounds.map (fun interval => interval) := by
        apply List.map_congr_left
        intro interval member
        exact Prod.ext rfl (point interval member)
      _ = candidate.packet.bounds := List.map_id' _
  have shape := source_shape candidate names head
  refine ⟨entries,first,?_,?_,?_⟩
  · calc
      candidate.packet.bounds = slots.map (fun slot => (slot,slot)) := diagonals.symm
      _ = (entries.map Prod.snd).map (fun slot => (slot,slot)) := by rw [second]
      _ = entries.map (fun entry => (entry.2,entry.2)) := by simp only [List.map_map,Function.comp_def]
  · rw [shape.1,← first]
    simp only [List.map_map,Function.comp_def]
  · exact shape.2.trans first.symm

end Yulang.GeneralNominalSourceLinearShape190

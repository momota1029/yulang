import Yulang.GeneralRebaseReceiptCounted289

/-! Generic consequences of acceptance of an extracted wire, unlike the
fixture-specific full certification theorem. Identity coincidence is kept
separate from equality of occurrence records. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28800
set_option maxHeartbeats 18500000
namespace Yulang.GeneralRebaseReceiptExtractLaws289
open GeneralRebaseReceiptWire289
open GeneralRebaseReceiptExtract289
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalSaturationState (Alias)
open GeneralDeclarations (Registry)
open GeneralNominalRecursiveCandidates (arguments report)
open GeneralNominalVersionedCandidates231 (inputs)
open GeneralRebaseExecutableRequests262 (requests)

variable {r : Registry} {s : State roles} {focus : Occurrence roles} {ask : Offer}

abbrev Accepted (r : Registry) (s : State roles) (focus : Occurrence roles) (ask : Offer) : Prop :=
  check (extract r s focus) ask = .ready

theorem owning_effect_exists (accepted : Accepted r s focus ask) :
    ∃ (e : Effect roles), e ∈ s.effects ∧ (effectSummary e).matches ask = true := by
  have fields := (check_ready _ _).mp accepted
  obtain ⟨item,member,compares⟩ := fields.2.1
  change item ∈ s.effects.map effectSummary at member
  obtain ⟨e,recorded,rfl⟩ := List.mem_map.mp member
  exact ⟨e,recorded,compares⟩

theorem actual_edge_with_ids (accepted : Accepted r s focus ask) :
    ∃ up down : Occurrence roles,
      (up,down) ∈ s.core.erased.current.edges ∧
      up.identity = ask.parent ∧ down.identity = ask.child ∧ focus.identity = ask.child := by
  have fields := (check_ready _ _).mp accepted
  have edge := fields.2.2.2.1
  change (ask.parent,ask.child) ∈ s.core.erased.current.edges.map
    (fun (a,b) => (a.identity,b.identity)) at edge
  obtain ⟨⟨a,b⟩,present,ids⟩ := List.mem_map.mp edge
  exact ⟨a,b,present,congrArg Prod.fst ids,congrArg Prod.snd ids,fields.2.2.1⟩

theorem no_effective_requests (accepted : Accepted r s focus ask) :
    GeneralNominalCenteredHeadOutputs.requests s.core focus = [] := by
  have fields := (check_ready _ _).mp accepted
  obtain ⟨d,_,_,_,empty,_,_⟩ := fields.2.2.2.2
  change (requests s.core focus).map GeneralSourceState.Output.target = [] at empty
  rw [← GeneralRebaseExecutableRequests262.requests_eq]
  exact List.map_eq_nil_iff.mp empty

theorem nonempty_alias_request_blocks (site : GeneralNominalDemandMerging.Site roles)
    (recorded : site ∈ s.core.erased.current.sites)
    (merged : Alias s.core.erased.current focus.identity site.occurrence.identity)
    (out : GeneralSourceState.Output) (effective : out ∈ site.occurrence.demand.outputs) :
    ¬ Accepted r s focus ask := by
  intro accepted
  have seen := (GeneralRebaseExecutableRequests262.mem_iff s.core focus out).mpr ⟨site,recorded,merged,effective⟩
  rw [GeneralRebaseExecutableRequests262.requests_eq,no_effective_requests accepted] at seen
  cases seen

theorem actual_inspection_finished (accepted : Accepted r s focus ask) :
    ∃ d, candidates r focus = [d] ∧ d.id = ask.childKey ∧ d.requirements = [] ∧
      ∃ bounds, arguments s.core.erased.current.context (inputs focus) = some bounds ∧
        GeneralNominalRecursiveInspection.Finished (report s.core.erased.current.context d bounds) := by
  have fields := (check_ready _ _).mp accepted
  obtain ⟨d,one,id,children,_,_,summary,read,done⟩ := fields.2.2.2.2
  change candidates r focus = [d] at one
  change (match candidates r focus with
    | [candidate] => diagnostic s.core.erased.current.context focus candidate
    | _ => none) = some summary at read
  rw [one] at read
  refine ⟨d,one,id,children,?_⟩
  cases located : arguments s.core.erased.current.context (inputs focus) with
  | none =>
    unfold diagnostic at read
    rw [located] at read
    cases read
  | some bounds =>
    exact ⟨bounds,rfl,(diagnostic_finished located).mp ⟨summary,read,done⟩⟩

end Yulang.GeneralRebaseReceiptExtractLaws289

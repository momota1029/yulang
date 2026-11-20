import Yulang.GeneralObservedMetadataRegistryFixture290

/-! Soundness for arbitrary fixed raw journals is deliberately phrased
as the selected existing class-effect equations. Entailment of the mark
itself uses the separately checked two-source fixture witness. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedMetadataPublic290
open GeneralDeclarations (Registry Declaration)
open GeneralNominalInspection (Interpretation Bounds)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Models effect_models)
open GeneralRebaseReceiptWire289 (Offer)
open GeneralRebaseReceiptCompile289 (Mark)
open GeneralObservedMetadataGate290 (context)
open GeneralObservedMetadataSeal290 (Seal)
open GeneralObservedMetadataReport290 (reportFrom)
open GeneralObservedMetadataLive290 (ProposedModels)
open GeneralObservedMetadataStrict290 (strictPublish actual_owner_total)
open GeneralNominalCenteredHeadMatEffects (Ready)

theorem strict_live_sound {r : Registry} {s : State roles} {up down : Occurrence roles}
    {ask : Offer} {proposal : Interpretation} {saved : Seal} {value : Mark}
    (done : strictPublish r s up down ask proposal saved = .released value) :
    value.target = ask.output ∧ (up,down) ∈ s.core.erased.current.edges ∧
    (∀ d ∈ r.declarations, d.role = down.demand.role →
      ∀ bounds : List (Bounds (context s).state),
      reportFrom (context s).state r.constructors proposal d bounds =
        GeneralNominalRecursiveCandidates.report (context s) d bounds) ∧
    ∃ e ∈ s.effects, e.plan.packet.site.occurrence = up ∧
      down ∈ GeneralNominalVersionedFrame231.children e.plan.packet ∧ Ready s.core up e.plan ∧
      ∀ model, Models s model → ProposedModels s.core up e.plan r.constructors proposal model := by
  obtain ⟨ordinary,e,present,parent,child,total,models⟩ := actual_owner_total done
  have ready := GeneralObservedMetadataPublication290.ready_release ordinary
  have newGate := ((GeneralObservedMetadataHistorical290.ready_exact ..).mp ready.1).1
  have coverage := GeneralObservedMetadataGate290.ready_has_provenance newGate
  refine ⟨ready.2,coverage.1.1,coverage.2,e,present,parent,child,total,?_⟩
  intro model valid
  exact (models model).mpr (effect_models valid present).2

theorem strict_fixture_mark_sound (choice : Bool) {s : GeneralNominalVersionedJournal232.State
    GeneralRebaseRowChildSource287.roles}
    (path : GeneralRebaseReceiptWitness289.ActualPath choice s) (saved : Seal) (value : Mark)
    (done : strictPublish (GeneralRebaseRowChildSource287.registry choice) s
      GeneralRebaseRowChildSource287.root (GeneralRebaseRowParentPacket287.child choice)
      (GeneralRebaseReceiptFixture289.request choice) GeneralRebaseRowChildSource287.interp saved =
        .released value) :
    GeneralRebaseReceiptWitness289.Witness choice s ∧
      (∀ m, Models s m ↔ GeneralRebaseInertLeaf288.SourceSlice s m ∧ value.Holds m) ∧
      ¬ GeneralNominalState.Known s.core.erased.current.context.state value.target := by
  rw [GeneralObservedMetadataStrictActual290.strict_publish_preserves_actual choice path] at done
  exact GeneralObservedMetadataReleased290.public_models choice path saved value done

end Yulang.GeneralObservedMetadataPublic290

import Yulang.GeneralDictionarySharedCapturedProducer
import Yulang.GeneralDictionaryOrdinaryTrace

/-! A precise post-producer observation bridge. The journal-wide scalar fact is
an explicit premise, not asserted of the old captured-parent state. No producer
installation or I26 trusted readiness is assumed to have been proved here. -/
noncomputable section
namespace Yulang.GeneralDictionaryCapturedScalarRefresh
open GeneralNominalSaturationState GeneralNominalSupport CommonNominalFullCarrier
open GeneralDictionarySharedCapturedTargets GeneralDictionarySharedCapturedRefresh
open GeneralDictionarySharedCapturedProducer
open GeneralDictionarySharedOutputBinderScope
open GeneralDeclarationExamples (roles)

abbrev before := candidate.privateContext
abbrev scalarBase : GeneralSourceState.State where
  slots := 5
  source := identifiers
  source_injective := identifiers_injective
  rowSource := identifiers
  ordinary := GeneralSourceState.equationAtoms 2 (.base .int)
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun slot => if slot.val = 2 then .scalar .int else .unresolved
  intervals := []
  heads_sound := by
    intro assignment valid slot term recorded
    change (if slot.val = 2 then GeneralSourceState.Head.scalar .int else .unresolved).equation = some term at recorded
    split at recorded
    · cases Option.some.inj recorded
      have same : slot = (2 : Fin 5) := Fin.ext ‹slot.val = 2›
      subst slot
      exact (GeneralSourceState.equationAtoms_exact 2 (.base .int) assignment).mp valid
    · cases recorded
  intervals_sound := by intro _ _ _ impossible; cases impossible

abbrev scalarView : GeneralNormalizedObservation.Snapshot scalarBase where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun slot => if slot.val = 2 then .scalar .int else .deferred .unresolved
  checked := by
    intro slot term recorded
    split at recorded
    · cases Option.some.inj recorded
      exact .head (by change (if slot.val = 2 then GeneralSourceState.Head.scalar .int else .unresolved).equation = _; rw [ite_eq_left ‹slot.val = 2›]; rfl)
    · cases recorded

abbrev scalarState : GeneralNominalState.State where
  base := scalarBase
  view := scalarView
  constructors := before.state.constructors
  nominals := before.state.nominals
  catalogue := before.state.catalogue
  bodies_opaque := by
    intro slot d recorded
    change (if slot.val = 2 then GeneralNormalizedObservation.Head.scalar .int else .deferred .unresolved) = _
    by_cases h : slot.val = 2
    · have same : slot = (2 : Fin 5) := Fin.ext h
      subst slot
      cases recorded
    · rw [ite_eq_right h]
  seed := before.state.seed
  allocated := before.state.allocated
  reserved := before.state.reserved
  ordinary := before.state.ordinary
abbrev scalarContext : GeneralNominalCandidates.Context := ⟨scalarState,before.interpretation⟩

private theorem renamed (d : GeneralNominalState.Descriptor 5) :
    GeneralNominalRefinements.renameDescriptor id d = d := by
  have h : GeneralNominalRefinements.renameParameter (id : Fin 5 → Fin 5) = id := by
    funext p; cases p <;> rfl
  cases d
  simp [GeneralNominalRefinements.renameDescriptor,h]

def refines : GeneralNominalRefinements.Refines before.state scalarState where
  base := ⟨id,(by intro _; rfl),(by intro _; rfl),
    (by intro atom impossible; cases impossible),
    (by intro slot known; exact False.elim (known rfl)),
    (by intro bounds impossible; cases impossible)⟩
  heads := by intro slot term impossible; cases impossible
  nominals := by
    intro slot d recorded
    change before.state.nominals slot = some (GeneralNominalRefinements.renameDescriptor id d)
    exact recorded.trans (congrArg some (renamed d)).symm
  ordinary := fun _ member => member
  known := by
    rintro source ⟨slot,equal,head|⟨d,recorded⟩⟩
    · exact False.elim (head rfl)
    · exact ⟨slot,equal,Or.inr ⟨d,recorded⟩⟩
  reserved := fun _ member => member
  allocated := fun _ member => member
  seed := rfl
  constructors := rfl

theorem raw_models (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models before.state m)
    (learned : Equivalent (m 2).1 (.base .int)) :
    GeneralNominalState.Models scalarState m := by
  refine ⟨⟨?_,?_,?_⟩,?_,valid.2.2⟩
  · intro atom member
    change atom ∈ GeneralSourceState.equationAtoms (2 : Fin 5) (.base .int) at member
    simp only [GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact learned.1
    · exact learned.2
  · intro slot term recorded
    change (if slot.val = 2 then GeneralSourceState.Head.scalar .int else .unresolved).equation = some term at recorded
    split at recorded
    · cases Option.some.inj recorded
      have same : slot = (2 : Fin 5) := Fin.ext ‹slot.val = 2›
      subst slot; exact learned
    · cases recorded
  · intro bounds impossible; cases impossible
  · intro slot descriptor recorded
    obtain ⟨arguments, fits, eq⟩ := valid.2.1 slot descriptor recorded
    refine ⟨arguments,?_,eq⟩
    exact GeneralNominalState.FitsAll.rec (state := before.state.base) (model := m)
      (motive := fun ps args _ => GeneralNominalState.FitsAll scalarBase m ps args)
      .nil (fun {parameter} {value} {parameters} {values} fit _ ih => .cons (by
        cases parameter <;> cases value <;> exact fit) ih) fits

/-- The scalar fact is quantified over all models of the actual current journal. -/
def certificate (current : Tracked roles) (context : current.current.context = before)
    (learned : ∀ m, Models current.current m → Equivalent (m 2).1 (.base .int)) :
    GeneralNominalFeedbackSteps.Refresh current.current scalarContext where
  refines := by rw [context]; exact refines
  interpretation := by rw [context]
  exact := by
    intro m valid
    apply raw_models m
    · simpa only [context] using valid.1
    · exact learned m valid
  support := by
    rw [context]
    intro identity member
    exact member

theorem newly_known : ¬ GeneralNominalState.Known before.state 2 ∧
    GeneralNominalState.Known scalarState 2 := by
  refine ⟨?_,⟨2,rfl,Or.inl ?_⟩⟩
  · exact captured_unknown
  · simp [GeneralNormalizedObservation.Snapshot.graph,GeneralNormalizedObservation.Head.node]

abbrev refreshed (current : Tracked roles) : Tracked roles :=
  {current with current := regenerate current.current scalarContext}

theorem step (current : Tracked roles) (context : current.current.context = before)
    (learned : ∀ m, Models current.current m → Equivalent (m 2).1 (.base .int)) :
    GeneralNominalSharedSteps.Step registry root current (refreshed current) := by
  refine ⟨root,.root,.administrative root _ (.refresh root scalarContext (certificate current context learned) 2 ?_ ?_ newly_known.2)⟩
  · rw [context]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_ofFn.mpr ⟨(2 : Fin 5),rfl⟩)))
  · rw [context]; exact newly_known.1

theorem models_exact (current : Tracked roles) (context : current.current.context = before)
    (learned : ∀ m, Models current.current m → Equivalent (m 2).1 (.base .int))
    (m : GeneralNominalCommonBridge.Assignment) :
    Models (refreshed current).current m ↔ Models current.current m :=
  GeneralNominalCycleSteps.refresh_models (certificate current context learned) m

theorem source_formed (current : Tracked roles) (context : current.current.context = before)
    (learned : ∀ m, Models current.current m → Equivalent (m 2).1 (.base .int))
    (formed : GeneralNominalSharedSteps.SourceFormed registry root current) :
    GeneralNominalSharedSteps.SourceFormed registry root (refreshed current) :=
  .update formed (step current context learned)

theorem packets_retained (current : Tracked roles) :
    (refreshed current).current.packets = current.current.packets := rfl

/-- Learning a scalar is an actual inspection change, not an ordinary extension. -/
theorem not_ordinary_extension :
    ¬ GeneralDictionaryOrdinaryTrace.Extension before scalarContext := by
  rintro ⟨reserved,atoms,allocated,equal⟩
  have lengths := congrArg (fun ctx : GeneralNominalCandidates.Context => ctx.state.base.ordinary.length) equal
  change 2 = 0 at lengths
  contradiction

theorem consumer_raw_ready : ¬ GeneralNominalState.RootPending scalarState consumer.demand := by
  rintro ⟨index,unknown⟩
  rw [consumer_input] at unknown
  exact unknown newly_known.2

end Yulang.GeneralDictionaryCapturedScalarRefresh

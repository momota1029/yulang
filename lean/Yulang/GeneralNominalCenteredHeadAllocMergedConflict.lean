import Yulang.GeneralNominalCenteredHeadAllocComposition
import Yulang.B4TargetV7

/-! A feasible slice of the recorded journal witnesses which alias class makes
its output equations inconsistent. Other recorded classes may support the
slice; unrelated contradictory classes and later feedback need not be included.
No prospective candidate or unrecorded implementation enters the slice. -/
namespace Yulang.GeneralNominalCenteredHeadAllocMergedConflict
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal (State Effect Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSaturationState (Alias)
open GeneralNominalCenteredHeadOutputs (EqualOutputs)
open GeneralNominalCenteredHeadMatPermutationLedger
variable {roles : Roles.RoleDecls}
variable {state first last : State roles} {relation : Plan roles → Plan roles → Prop} {focus : Occurrence roles}

def HistoryModels (state : State roles) (model : Assignment) : Prop :=
  GeneralNominalState.Models state.core.erased.source.state model ∧
  (∀ site ∈ state.core.sourceSites, site.Holds model) ∧
  (∀ plan ∈ state.core.plans, GeneralNominalCenteredHeadMatStepPackets.Holds plan model) ∧
  ∀ effect ∈ state.effects, effect.Holds model

def ClassEquations (state : State roles) (focus : Occurrence roles) (model : Assignment) : Prop :=
  EqualOutputs state.core focus model ∧
  ∀ effect ∈ state.effects, Alias state.core.erased.current focus.identity effect.plan.packet.site.occurrence.identity →
    effect.Live state.core model

def MergedClass (state : State roles) (focus : Occurrence roles) : Prop :=
  ∃ first last, (first,last) ∈ state.core.erased.current.aliases ∧ first ≠ last ∧
    Alias state.core.erased.current focus.identity first

def Registered (state : State roles) (focus : Occurrence roles) : Prop :=
  ∃ site ∈ state.core.erased.current.sites, site.occurrence = focus

def ContextPresent (state : State roles) (atoms : List (PresenceNormalForm.Atom Nat))
    (classes : List (Occurrence roles)) : Prop :=
  atoms ⊆ state.core.erased.current.context.state.ordinary ∧ ∀ focus ∈ classes, Registered state focus

def ContextModels (state : State roles) (atoms : List (PresenceNormalForm.Atom Nat))
    (classes : List (Occurrence roles)) (model : Assignment) : Prop :=
  HistoryModels state model ∧ PresenceNormalForm.All CommonNominalFullCarrier.model model atoms ∧
    ∀ focus ∈ classes, ClassEquations state focus model

def MergedOutputConflict (state : State roles) (focus : Occurrence roles) : Prop :=
  MergedClass state focus ∧ ∃ atoms classes, ContextPresent state atoms classes ∧
    (∃ model, ContextModels state atoms classes model) ∧
    ¬ ∃ model, ContextModels state atoms classes model ∧ ClassEquations state focus model

theorem models_history (valid : Models state model) : HistoryModels state model :=
  ⟨valid.2.1,fun site member => valid.2.2.2.1 site (state.core.sourceRecorded site member),
    valid.2.2.2.2.1,fun effect member => (valid.2.2.2.2.2 effect member).1⟩

theorem base_conflict (merged : MergedClass state focus) (inhabited : ∃ model, HistoryModels state model)
    (impossible : ¬ ∃ model, HistoryModels state model ∧ ClassEquations state focus model) :
    MergedOutputConflict state focus := by
  refine ⟨merged,[],[],⟨List.nil_subset _,by simp⟩,?_,?_⟩
  · obtain ⟨model,valid⟩ := inhabited
    exact ⟨model,valid,PresenceNormalForm.all_nil _ _,by simp⟩
  · rintro ⟨model,valid,equations⟩; exact impossible ⟨model,valid.1,equations⟩

theorem conflict_has_feasible_context (conflict : MergedOutputConflict state focus) :
    ∃ model, HistoryModels state model := by
  obtain ⟨_,_,_,_,⟨model,valid⟩,_⟩ := conflict
  exact ⟨model,valid.1⟩

theorem class_models_exclude_conflict (valid : Models state model)
    (classes : ∀ focus, Registered state focus → ClassEquations state focus model)
    (focusEquations : ClassEquations state focus model) : ¬ MergedOutputConflict state focus := by
  rintro ⟨_,atoms,others,present,_,impossible⟩
  exact impossible ⟨model,⟨models_history valid,fun atom member => valid.1.2.2 atom (present.1 member),
    fun demand member => classes demand (present.2 demand member)⟩,focusEquations⟩

theorem history_related (same : Related relation first last) (model) :
    HistoryModels first model ↔ HistoryModels last model := by
  have plans := all_models same.plans (fun plan => GeneralNominalCenteredHeadMatStepPackets.Holds plan model)
    (fun plan => GeneralNominalCenteredHeadMatStepPackets.Holds plan model) (fun _ _ pair => pair.2.holds model)
  have effects := all_models same.effects (fun effect => effect.Holds model) (fun effect => effect.Holds model)
    (fun _ _ pair => pair.holds model)
  simp only [HistoryModels,same.core.source,same.core.roots,plans,effects]

theorem equations_related (same : Related relation first last) (focus model) :
    ClassEquations first focus model ↔ ClassEquations last focus model := by
  have effects := all_models same.effects
    (fun effect => Alias first.core.erased.current focus.identity effect.plan.packet.site.occurrence.identity → effect.Live first.core model)
    (fun effect => Alias last.core.erased.current focus.identity effect.plan.packet.site.occurrence.identity → effect.Live last.core model)
    (fun a b pair => by
      have identity := congrArg (fun site : GeneralNominalDemandMerging.Site roles => site.occurrence.identity) pair.plan.2.matched.packet.site
      exact imp_congr (by rw [same.core.snapshot.alias,identity]) (pair.live same.core.snapshot model))
  simp only [ClassEquations,EqualOutputs,same.core.snapshot.requests,effects]

theorem merged_related (same : Related relation first last) (focus) : MergedClass first focus ↔ MergedClass last focus := by
  simp only [MergedClass,same.core.current.aliases,same.core.snapshot.alias]

theorem context_related (same : Related relation first last) (atoms classes) :
    ContextPresent first atoms classes ↔ ContextPresent last atoms classes := by
  have ordinary : first.core.erased.current.context.state.ordinary = last.core.erased.current.context.state.ordinary := by
    obtain ⟨_,_,equal,_,_⟩ := same.core.current.context.state
    rw [equal]; rfl
  simp only [ContextPresent,Registered,ordinary,same.core.current.sites]

theorem context_models_related (same : Related relation first last) (atoms classes model) :
    ContextModels first atoms classes model ↔ ContextModels last atoms classes model := by
  simp only [ContextModels,history_related same,equations_related same]

theorem conflict_related (same : Related relation first last) (focus) :
    MergedOutputConflict first focus ↔ MergedOutputConflict last focus := by
  simp only [MergedOutputConflict,merged_related same,context_related same,context_models_related same,equations_related same]

theorem history_entails_clear
    (entailed : ∀ model, HistoryModels state model → ClassEquations state focus model) :
    ¬ MergedOutputConflict state focus := by
  rintro ⟨_,_,_,_,⟨model,valid⟩,impossible⟩
  exact impossible ⟨model,valid,entailed model valid.1⟩

theorem equations_same_class {aFocus bFocus : Occurrence roles} (alias : Alias state.core.erased.current aFocus.identity bFocus.identity) (model) :
    ClassEquations state aFocus model ↔ ClassEquations state bFocus model := by
  have equalOutputs : EqualOutputs state.core aFocus model ↔ EqualOutputs state.core bFocus model := by
    simp only [EqualOutputs,GeneralNominalCenteredHeadOutputs.same_class_requests alias]
  apply and_congr equalOutputs
  apply forall_congr'; intro effect
  apply forall_congr'; intro member
  apply imp_congr _ Iff.rfl
  exact ⟨fun path => .trans (.symm alias) path,fun path => .trans alias path⟩

theorem merged_same_class {aFocus bFocus : Occurrence roles} (alias : Alias state.core.erased.current aFocus.identity bFocus.identity) :
    MergedClass state aFocus ↔ MergedClass state bFocus := by
  constructor
  · rintro ⟨a,b,member,different,path⟩
    exact ⟨a,b,member,different,.trans (.symm alias) path⟩
  · rintro ⟨a,b,member,different,path⟩
    exact ⟨a,b,member,different,.trans alias path⟩

theorem conflict_same_class {aFocus bFocus : Occurrence roles} (alias : Alias state.core.erased.current aFocus.identity bFocus.identity) :
    MergedOutputConflict state aFocus ↔ MergedOutputConflict state bFocus := by
  simp only [MergedOutputConflict,merged_same_class alias,equations_same_class alias]

end Yulang.GeneralNominalCenteredHeadAllocMergedConflict

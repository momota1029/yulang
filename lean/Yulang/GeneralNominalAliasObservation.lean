import Yulang.GeneralNominalValueSteps

/-! Recording a reserved alias of a known nominal value. The observation adds
one slot, keeps every old descriptor and journal entry, and uses a journal
equality certificate. It does not allocate a value inside an interval. -/
namespace Yulang.GeneralNominalAliasObservation
open GeneralNominalSaturationState GeneralNominalState GeneralNominalRefinements
open CommonNominalFullCarrier

/-- The nominal-only source fixtures have no raw structural observations.
Ordinary global atoms and nominal parameters are unrestricted. -/
structure Flat (state : GeneralNominalState.State) : Prop where
  ordinary : state.base.ordinary = []
  intervals : state.base.intervals = []
  raw : ∀ slot, state.base.heads slot = .unresolved
  normalized : ∀ slot, state.view.heads slot = .deferred .unresolved

def identifiers (state : GeneralNominalState.State) (fresh : Nat) : Fin (state.base.slots+1) → Nat :=
  Fin.lastCases fresh state.base.source

def base (state : GeneralNominalState.State) (fresh : Nat)
    (absent : ∀ slot, state.base.source slot ≠ fresh) : GeneralSourceState.State where
  slots := state.base.slots+1
  source := identifiers state fresh
  source_injective := by
    intro first
    refine Fin.lastCases ?_ (fun first => ?_) first
    · intro last
      refine Fin.lastCases ?_ (fun last => ?_) last
      · intro _; rfl
      · intro equal; exact False.elim (absent last (by simpa [identifiers] using equal.symm))
    · intro last
      refine Fin.lastCases ?_ (fun last => ?_) last
      · intro equal; exact False.elim (absent first (by simpa [identifiers] using equal))
      · intro equal; exact congrArg Fin.castSucc (state.base.source_injective (by simpa [identifiers] using equal))
  rowSource := Fin.lastCases fresh state.base.rowSource
  ordinary := []
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun _ => .unresolved
  intervals := []
  heads_sound := by intro _ _ _ _ impossible; cases impossible
  intervals_sound := by intro _ _ _ impossible; cases impossible

def view (state : GeneralNominalState.State) (fresh : Nat)
    (absent : ∀ slot, state.base.source slot ≠ fresh) : GeneralNormalizedObservation.Snapshot (base state fresh absent) where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun _ => .deferred .unresolved
  checked := by intro _ _ impossible; cases impossible

def snapshot (state : GeneralNominalState.State) (fresh : Nat)
    (absent : ∀ slot, state.base.source slot ≠ fresh)
    (old : Fin state.base.slots) (descriptor : Descriptor state.base.slots)
    (recorded : state.nominals old = some descriptor) : GeneralNominalState.State where
  base := base state fresh absent
  view := view state fresh absent
  constructors := state.constructors
  nominals := Fin.lastCases (some (renameDescriptor (@Fin.castSucc state.base.slots) descriptor))
    (fun slot => (state.nominals slot).map (renameDescriptor (@Fin.castSucc state.base.slots)))
  catalogue := by
    intro slot
    refine Fin.lastCases ?_ (fun slot => ?_) slot
    · intro actual found
      simp only [Fin.lastCases_last] at found
      cases Option.some.inj found
      exact state.catalogue old descriptor recorded
    · intro actual found
      cases prior : state.nominals slot with
      | none => simp [prior] at found
      | some priorDescriptor =>
        have same : renameDescriptor (@Fin.castSucc state.base.slots) priorDescriptor = actual := by
          simp only [Fin.lastCases_castSucc,prior,Option.map_some] at found
          exact Option.some.inj found
        subst actual
        exact state.catalogue slot priorDescriptor prior
  bodies_opaque := by intro _ _ _; rfl
  seed := state.seed
  allocated := state.allocated
  reserved := state.reserved
  ordinary := state.ordinary

def refines (state : GeneralNominalState.State) (flat : Flat state) (fresh : Nat)
    (absent : ∀ slot, state.base.source slot ≠ fresh)
    (old : Fin state.base.slots) (descriptor : Descriptor state.base.slots)
    (recorded : state.nominals old = some descriptor) :
    Refines state (snapshot state fresh absent old descriptor recorded) where
  base := ⟨Fin.castSucc,(by intro slot; simp [base,identifiers,snapshot]),
    (by intro slot; simp [base,snapshot]),
    (by intro _ member; rw [flat.ordinary] at member; cases member),
    (by intro slot known; exact False.elim (known (by simp [GeneralSourceState.State.graph,flat.raw slot,GeneralSourceState.Head.node]))),
    (by intro _ member; rw [flat.intervals] at member; cases member)⟩
  heads := by intro slot term equation; rw [flat.raw slot] at equation; cases equation
  nominals := by intro slot actual found; simp [snapshot,found]
  ordinary := fun _ member => member
  known := by
    rintro source ⟨slot,equal,head | ⟨actual,found⟩⟩
    · exact False.elim (head (by simp [GeneralNormalizedObservation.Snapshot.graph,flat.normalized slot,GeneralNormalizedObservation.Head.node]))
    · refine ⟨slot.castSucc,?_,Or.inr ⟨renameDescriptor (@Fin.castSucc state.base.slots) actual,?_⟩⟩
      · simpa [snapshot,base,identifiers] using equal
      · simp [snapshot,found]
  reserved := fun _ member => member
  allocated := fun _ member => member
  seed := rfl
  constructors := rfl

private theorem fits_renamed (state : GeneralNominalState.State) (fresh : Nat)
    (absent : ∀ slot, state.base.source slot ≠ fresh)
    (model : GeneralNominalCommonBridge.Assignment) (parameter : Parameter state.base.slots)
    (actual : CommonNominalFullCarrier.Argument) :
    Fits (base state fresh absent) model (renameParameter Fin.castSucc parameter) actual ↔
      Fits state.base model parameter actual := by
  cases parameter <;> cases actual <;> simp [Fits,renameParameter,base,identifiers]

private theorem all_renamed (state : GeneralNominalState.State) (fresh : Nat)
    (absent : ∀ slot, state.base.source slot ≠ fresh)
    (model : GeneralNominalCommonBridge.Assignment)
    {parameters : List (Parameter state.base.slots)} {values : List CommonNominalFullCarrier.Argument}
    (valid : FitsAll state.base model parameters values) :
    FitsAll (base state fresh absent) model (parameters.map (renameParameter Fin.castSucc)) values := by
  induction valid with
  | nil => exact .nil
  | cons head tail ih => exact .cons ((fits_renamed state fresh absent model _ _).mpr head) ih

theorem snapshot_models (state : GeneralNominalState.State) (fresh : Nat)
    (absent : ∀ slot, state.base.source slot ≠ fresh)
    (old : Fin state.base.slots) (descriptor : Descriptor state.base.slots)
    (recorded : state.nominals old = some descriptor)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models state model)
    (equal : Equivalent (model fresh).1 (model (state.base.source old)).1) :
    GeneralNominalState.Models (snapshot state fresh absent old descriptor recorded) model := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_,?_⟩,?_,valid.2.2⟩
  · intro _ _ impossible; cases impossible
  · intro _ impossible; cases impossible
  · intro slot
    refine Fin.lastCases ?_ (fun slot => ?_) slot
    · intro actual found
      simp only [snapshot,Fin.lastCases_last] at found
      cases Option.some.inj found
      obtain ⟨arguments,fits,denotes⟩ := valid.2.1 old descriptor recorded
      refine ⟨arguments,all_renamed state fresh absent model fits,?_⟩
      simpa [snapshot,base,identifiers,renameDescriptor] using
        (show Equivalent (model fresh).1 (nominal descriptor.declaration.name arguments) from
          ⟨subtype_trans equal.1 denotes.1,subtype_trans denotes.2 equal.2⟩)
    · intro actual found
      cases prior : state.nominals slot with
      | none => simp [snapshot,prior] at found
      | some priorDescriptor =>
        have same : renameDescriptor (@Fin.castSucc state.base.slots) priorDescriptor = actual := by
          simp only [snapshot,Fin.lastCases_castSucc,prior,Option.map_some] at found
          exact Option.some.inj found
        subst actual
        obtain ⟨arguments,fits,denotes⟩ := valid.2.1 slot priorDescriptor prior
        refine ⟨arguments,all_renamed state fresh absent model fits,?_⟩
        simpa [snapshot,base,identifiers,renameDescriptor] using denotes

theorem basis (state : GeneralNominalState.State) (fresh : Nat)
    (absent : ∀ slot, state.base.source slot ≠ fresh)
    (old : Fin state.base.slots) (descriptor : Descriptor state.base.slots)
    (recorded : state.nominals old = some descriptor)
    (reserved : fresh ∈ GeneralNominalState.sources state) :
    ∀ source ∈ GeneralNominalState.sources (snapshot state fresh absent old descriptor recorded),
      source ∈ GeneralNominalState.sources state := by
  intro source member
  simp only [GeneralNominalState.sources,List.mem_append] at member ⊢
  rcases member with ((first | last) | allocated) | ordinary
  · obtain ⟨slot,equal⟩ := List.mem_ofFn.mp first
    revert equal
    refine Fin.lastCases ?_ (fun slot => ?_) slot
    · intro equal
      have same : fresh = source := by simpa [snapshot,base,identifiers] using equal
      exact same ▸ (by simpa only [GeneralNominalState.sources,List.mem_append] using reserved)
    · intro equal
      exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨slot,by simpa [snapshot,base,identifiers] using equal⟩)))
  · obtain ⟨slot,equal⟩ := List.mem_ofFn.mp last
    revert equal
    refine Fin.lastCases ?_ (fun slot => ?_) slot
    · intro equal
      have same : fresh = source := by simpa [snapshot,base] using equal
      exact same ▸ (by simpa only [GeneralNominalState.sources,List.mem_append] using reserved)
    · intro equal
      exact Or.inl (Or.inl (Or.inr (List.mem_ofFn.mpr ⟨slot,by simpa [snapshot,base] using equal⟩)))
  · exact Or.inl (Or.inr allocated)
  · exact Or.inr ordinary

def context (state : GeneralNominalSaturationState.State roles) (fresh : Nat)
    (absent : ∀ slot, state.context.state.base.source slot ≠ fresh)
    (old : Fin state.context.state.base.slots) (descriptor : Descriptor state.context.state.base.slots)
    (recorded : state.context.state.nominals old = some descriptor) : GeneralNominalCandidates.Context :=
  ⟨snapshot state.context.state fresh absent old descriptor recorded,state.context.interpretation⟩

def certificate (state : GeneralNominalSaturationState.State roles) (flat : Flat state.context.state) (fresh : Nat)
    (absent : ∀ slot, state.context.state.base.source slot ≠ fresh)
    (old : Fin state.context.state.base.slots) (descriptor : Descriptor state.context.state.base.slots)
    (recorded : state.context.state.nominals old = some descriptor)
    (reserved : fresh ∈ GeneralNominalState.sources state.context.state)
    (equal : GeneralNominalFeedbackK2.Equal state fresh (state.context.state.base.source old)) :
    GeneralNominalFeedbackSteps.Refresh state (context state fresh absent old descriptor recorded) :=
  ⟨refines _ flat fresh absent old descriptor recorded,rfl,
    fun model valid => snapshot_models _ fresh absent old descriptor recorded model valid.1 (equal model valid),
    basis _ fresh absent old descriptor recorded reserved⟩

theorem known (state : GeneralNominalState.State) (fresh : Nat)
    (absent : ∀ slot, state.base.source slot ≠ fresh)
    (old : Fin state.base.slots) (descriptor : Descriptor state.base.slots)
    (recorded : state.nominals old = some descriptor) :
    Known (snapshot state fresh absent old descriptor recorded) fresh :=
  ⟨Fin.last _,by simp [snapshot,base,identifiers],Or.inr ⟨renameDescriptor (@Fin.castSucc state.base.slots) descriptor,by simp [snapshot]⟩⟩

theorem snapshot_flat (state : GeneralNominalState.State) (fresh : Nat)
    (absent : ∀ slot, state.base.source slot ≠ fresh)
    (old : Fin state.base.slots) (descriptor : Descriptor state.base.slots)
    (recorded : state.nominals old = some descriptor) :
    Flat (snapshot state fresh absent old descriptor recorded) :=
  ⟨rfl,rfl,fun _ => rfl,fun _ => rfl⟩

theorem same_models (state : GeneralNominalSaturationState.State roles) (flat : Flat state.context.state) (fresh : Nat)
    (absent : ∀ slot, state.context.state.base.source slot ≠ fresh)
    (old : Fin state.context.state.base.slots) (descriptor : Descriptor state.context.state.base.slots)
    (recorded : state.context.state.nominals old = some descriptor)
    (reserved : fresh ∈ GeneralNominalState.sources state.context.state)
    (equal : GeneralNominalFeedbackK2.Equal state fresh (state.context.state.base.source old))
    (model : GeneralNominalCommonBridge.Assignment) :
    Models (regenerate state (context state fresh absent old descriptor recorded)) model ↔ Models state model :=
  GeneralNominalCycleSteps.refresh_models
    (certificate state flat fresh absent old descriptor recorded reserved equal) model

theorem actual_step (state : GeneralNominalSupport.Tracked roles) (registry : GeneralDeclarations.Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (flat : Flat state.current.context.state) (fresh : Nat)
    (absent : ∀ slot, state.current.context.state.base.source slot ≠ fresh)
    (old : Fin state.current.context.state.base.slots) (descriptor : Descriptor state.current.context.state.base.slots)
    (recorded : state.current.context.state.nominals old = some descriptor)
    (reserved : fresh ∈ GeneralNominalState.sources state.current.context.state)
    (equal : GeneralNominalFeedbackK2.Equal state.current fresh (state.current.context.state.base.source old)) :
    GeneralNominalValueSteps.Step registry root state
      {state with current := regenerate state.current (context state.current fresh absent old descriptor recorded)} := by
  refine ⟨root,.root,.administrative root _ (.refresh root _
    (certificate state.current flat fresh absent old descriptor recorded reserved equal) fresh reserved ?_ ?_)⟩
  · rintro ⟨slot,same,_⟩
    exact absent slot same
  · exact known _ fresh absent old descriptor recorded

end Yulang.GeneralNominalAliasObservation

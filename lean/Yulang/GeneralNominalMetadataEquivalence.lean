import Yulang.GeneralNominalCenteredPlanReordering

/-! Reservation and ownership enumeration can change without changing the
observation core. Their membership is retained for freshness and refinement. -/
namespace Yulang.GeneralNominalMetadataEquivalence
open GeneralNominalState

def replace (state : State) (allocated : List GeneralNominalIdentities.Origin)
    (reserved : List Nat) : State :=
  {state with allocated := allocated, reserved := reserved}

def Same (first last : State) : Prop :=
  ∃ allocated reserved, last = replace first allocated reserved ∧
    (∀ key, key ∈ allocated ↔ key ∈ first.allocated) ∧
    ∀ name, name ∈ reserved ↔ name ∈ first.reserved

theorem refl (state : State) : Same state state :=
  ⟨state.allocated,state.reserved,by cases state; rfl,fun _ => Iff.rfl,fun _ => Iff.rfl⟩

theorem symm (same : Same first last) : Same last first := by
  obtain ⟨allocated,reserved,rfl,keys,names⟩ := same
  refine ⟨first.allocated,first.reserved,?_,fun key => (keys key).symm,fun name => (names name).symm⟩
  cases first
  rfl

theorem trans (one : Same first middle) (two : Same middle last) : Same first last := by
  obtain ⟨allocated,reserved,rfl,keys,names⟩ := one
  obtain ⟨nextKeys,nextNames,rfl,moreKeys,moreNames⟩ := two
  exact ⟨nextKeys,nextNames,rfl,
    fun key => (moreKeys key).trans (keys key),fun name => (moreNames name).trans (names name)⟩

theorem models (same : Same first last) (model) : Models first model ↔ Models last model := by
  obtain ⟨_,_,rfl,_,_⟩ := same
  rfl

theorem known (same : Same first last) (name) : Known first name ↔ Known last name := by
  obtain ⟨_,_,rfl,_,_⟩ := same
  rfl

theorem pending (same : Same first last) (demand : GeneralSourceState.Demand roles) :
    RootPending first demand ↔ RootPending last demand := by
  obtain ⟨_,_,rfl,_,_⟩ := same
  rfl

theorem sources (same : Same first last) (name) : name ∈ GeneralNominalState.sources first ↔
    name ∈ GeneralNominalState.sources last := by
  obtain ⟨_,_,rfl,_,names⟩ := same
  simp only [GeneralNominalState.sources,replace,List.mem_append,names]

theorem linked (same : Same first last) (demand : GeneralSourceState.Demand roles) :
    Linked first demand ↔ Linked last demand := by
  unfold Linked
  simp only [sources same]

theorem fresh (same : Same first last) (registry root) :
    GeneralNominalAllocation.Fresh first registry root ↔ GeneralNominalAllocation.Fresh last registry root := by
  obtain ⟨allocated,reserved,rfl,keys,names⟩ := same
  have support := sources (first := first) (last := replace first allocated reserved)
    ⟨allocated,reserved,rfl,keys,names⟩
  constructor
  · intro fresh key member present
    exact (keys key).mpr (fresh key member ((support _).mpr present))
  · intro fresh key member present
    exact (keys key).mp (fresh key member ((support _).mp present))

noncomputable def refines_left (same : Same first last) (certificate : GeneralNominalRefinements.Refines first after) :
    GeneralNominalRefinements.Refines last after := Classical.choice (by
  obtain ⟨allocated,reserved,rfl,keys,names⟩ := same
  exact ⟨⟨certificate.base,certificate.heads,certificate.nominals,certificate.ordinary,certificate.known,
    fun name member => certificate.reserved name ((names name).mp member),
    fun key member => certificate.allocated key ((keys key).mp member),certificate.seed,certificate.constructors⟩⟩)

noncomputable def refines_right (same : Same first last) (certificate : GeneralNominalRefinements.Refines before first) :
    GeneralNominalRefinements.Refines before last := Classical.choice (by
  obtain ⟨allocated,reserved,rfl,keys,names⟩ := same
  exact ⟨⟨certificate.base,certificate.heads,certificate.nominals,certificate.ordinary,certificate.known,
    fun name member => (names name).mpr (certificate.reserved name member),
    fun key member => (keys key).mpr (certificate.allocated key member),certificate.seed,certificate.constructors⟩⟩)

theorem extend (same : Same first last) (one two : List Nat)
    (reserved : ∀ name, name ∈ one ↔ name ∈ two) (atoms) :
    Same (GeneralNominalState.extend first one atoms) (GeneralNominalState.extend last two atoms) := by
  obtain ⟨allocated,names,rfl,keys,present⟩ := same
  refine ⟨allocated,names ++ two,rfl,keys,?_⟩
  intro name
  simp only [GeneralNominalState.extend,List.mem_append,present,reserved]

end Yulang.GeneralNominalMetadataEquivalence

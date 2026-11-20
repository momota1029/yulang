import Yulang.GeneralObservedMetadataReleased290

/-! Equality of read tables does not promise a successful compiler.
This additional test reflects the old Ready predicate on the actual
request class when its metadata inputs agree. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedMetadataTotal290
open GeneralDeclarationPatterns (Constructors)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredSteps (State)
open GeneralNominalCenters (Plan)
open GeneralSourceDictionaries (Occurrence)
open GeneralDictionaryAssociatedProvenance (Body lookup)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalCenteredHeadMatEffects (Ready compileBody bodySchema)
open GeneralObservedMetadataBodies290 (compileFrom compile_current compile_eq bodyKeys)
open GeneralObservedMetadataLive290 (liveKeys live_key)
open GeneralObservedMetadataRequestBook290 (requestBook matches_request)
open GeneralObservedMetadataEntry290 (LocalEqual)

def total (s : State roles) (up : Occurrence roles) (plan : Plan roles)
    (c : Constructors) (i : Interpretation) : Bool :=
  (requestBook s up plan).all fun entry =>
    match entry.2 with
    | none => false
    | some body => (compileFrom c i body).isSome

theorem total_exact (s : State roles) (up : Occurrence roles) (plan : Plan roles)
    (c : Constructors) (i : Interpretation) :
    total s up plan c i = true ↔
    ∀ out ∈ requests s up, ∃ body, lookup roles plan.packet.declaration out.name = some body ∧
      (compileFrom c i body).isSome = true := by
  unfold total
  rw [List.all_eq_true]
  constructor
  · intro checked out requested
    cases contents : lookup roles plan.packet.declaration out.name with
    | none =>
      have bad := checked _ (matches_request.mpr ⟨requested,contents⟩)
      cases bad
    | some body =>
      exact ⟨body,rfl,checked _ (matches_request.mpr ⟨requested,contents⟩)⟩
  · intro totalRead entry named
    obtain ⟨out,opt⟩ := entry
    obtain ⟨requested,content⟩ := matches_request.mp named
    obtain ⟨body,found,compiled⟩ := totalRead out requested
    rw [← content,found]
    exact compiled

theorem compiled_iff (plan : Plan roles) (target : Nat) (b : Body) :
    (compileBody plan b).isSome = true ↔ (bodySchema plan target b).unknown = false := by
  unfold bodySchema
  cases compileBody plan b <;> simp

theorem total_iff_ready (s : State roles) (up : Occurrence roles) (plan : Plan roles)
    (c : Constructors) (i : Interpretation)
    (metadata : LocalEqual (liveKeys s up plan) plan.packet.registry.constructors
      plan.packet.context.interpretation c i) :
    total s up plan c i = true ↔ Ready s up plan := by
  rw [total_exact]
  constructor
  · intro successful out requested
    obtain ⟨body,found,operational⟩ := successful out requested
    refine ⟨body,found,(compiled_iff plan out.target body).mp ?_⟩
    rw [← compile_current,compile_eq body (metadata.restrict (fun _ seen => live_key requested found seen))]
    exact operational
  · intro successful out requested
    obtain ⟨body,found,compiled⟩ := successful out requested
    refine ⟨body,found,?_⟩
    rw [← compile_eq body (metadata.restrict (fun _ seen => live_key requested found seen)),compile_current]
    exact (compiled_iff plan out.target body).mpr compiled

theorem certified_total_iff_ready (s : State roles) (up : Occurrence roles) (plan : Plan roles)
    (c : Constructors) (i : Interpretation)
    (metadata : GeneralObservedMetadataScope290.certify (liveKeys s up plan) plan.packet.registry.constructors
      plan.packet.context.interpretation c i = .good) :
    total s up plan c i = true ↔ Ready s up plan :=
  total_iff_ready s up plan c i ((GeneralObservedMetadataScope290.good_exact ..).mp metadata).1

end Yulang.GeneralObservedMetadataTotal290

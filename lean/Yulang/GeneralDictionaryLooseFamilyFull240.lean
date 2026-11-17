import Yulang.GeneralDictionaryLooseFamilyHead240
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryLooseFamilyFull240
open GeneralDictionaryLooseFamilyBase240 GeneralDictionaryLooseFamilySnapshot240
open GeneralDictionaryLooseFamilyPacket240 GeneralDictionaryLooseFamilyHead240
open GeneralDictionaryLooseLoopSource240 (roles registry declaration root model F)
open GeneralDictionaryLooseFamilyNames240 (lower upper)
open GeneralDictionaryLooseLoopPacket240 (origin0 origin1 actual actual_value seen0 seen1 observed_value)
open GeneralNominalCenters GeneralDeclarations CommonNominalFullCarrier
variable (n : Nat) (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat) (ordinary : List (PresenceNormalForm.Atom Nat))
theorem head_schema : (plan n allocated reserved ordinary).headSchema =
    { tests := [(.source 3,.nominal 5 2)]
      variables := [⟨0,origin0,.actual⟩,⟨0,origin1,.actual⟩] } := by
  unfold Plan.headSchema
  rw [show GeneralNominalInspection.queries (snapshot n allocated reserved ordinary) GeneralDictionaryLooseLoopSource240.interpretation declaration =
 [.nominal 5 [.variables [0],.variables [0]]] from query n allocated reserved ordinary]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,List.ofFn_succ,plan,rootSite,origin0,origin1]

theorem binder_exact : (plan n allocated reserved ordinary).binder 0 = actual := by
 unfold Plan.binder GeneralNominalPacketSupport.capture
 dsimp only
 rw [bindings_exact]
 rfl

theorem head_holds : GeneralNominalVersionedPlans231.SchemaHolds (plan n allocated reserved ordinary) (plan n allocated reserved ordinary).headSchema model := by
  rw [head_schema]
  constructor
  · intro test member
    cases List.mem_singleton.mp member
    refine ⟨⟨_,.source 3⟩,?_⟩
    intro value seen
    cases seen
    exact ⟨[.inl F,.inl F],rfl,subtype_refl _,subtype_refl _⟩
  · intro entry member
    rcases List.mem_cons.mp member with rfl | member
    all_goals first | cases List.mem_singleton.mp member | skip
    all_goals
      simp only [ite_true]
      refine ⟨?_,⟨_,.source _⟩,?_⟩
      · first | exact ⟨_,seen0⟩ | exact ⟨_,seen1⟩
      · intro x y seenX seenY
        cases seenY
        rw [GeneralNominalVersionedFrame231.binder_eq,binder_exact,actual_value]
        first | exact observed_value 0 (by decide) seenX | exact observed_value 1 (by decide) seenX


theorem emitted_empty : GeneralNominalVersionedPlans231.emittedSchema (plan n allocated reserved ordinary) = ⟨[],false⟩ := by
 unfold GeneralNominalVersionedPlans231.emittedSchema GeneralNominalVersionedPlans231.emittedRequests
 simp only [GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
   GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
 rfl

theorem packet_holds (atoms : PresenceNormalForm.All CommonNominalFullCarrier.model model ordinary) : GeneralNominalVersionedPlans231.Holds (plan n allocated reserved ordinary) model := by
 have head : GeneralNominalVersionedPlans231.HeadModels (packet n allocated reserved ordinary) model := head_model n allocated reserved ordinary atoms
 have rawOrdinary := ((GeneralNominalVersionedPlans231.private_models_iff (packet n allocated reserved ordinary) model).mp head.1).2
 refine ⟨raw_models n allocated reserved ordinary atoms,⟨rawOrdinary,head.2,?_,?_,head_holds n allocated reserved ordinary,?_,?_⟩,?_⟩
 · intro index; exact ⟨subtype_refl _,subtype_refl _⟩
 · intro name needed
   have same : name=0 := by
     rcases needed with named | ⟨clause,member,_⟩
     · simpa [Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
         GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
         GeneralDeclarationPatterns.Pattern.variables] using named
     · cases member
   subst name
   rw [GeneralNominalVersionedFrame231.binder_eq,binder_exact,actual_value]
   change GeneralNominalCaptureMerges.Fits model ((GeneralNominalVersionedAllocation231.capture _ _ _ _ (packet n allocated reserved ordinary).bindings).inputs 0) F
   rw [bindings_exact]
   change Subtype (model (lower (n+1))).1 F ∧ Subtype F (model (upper n)).1
   rw [model_lower,model_upper]
   exact ⟨subtype_refl _,subtype_refl _⟩
 · intro equation member _; rw [emitted_empty] at member; cases member
 · intro clause member; cases member
 · intro equation member; rw [emitted_empty] at member; cases member

end Yulang.GeneralDictionaryLooseFamilyFull240

import Yulang.GeneralWherePhysicalHead319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 34000000
namespace Yulang.GeneralWherePhysicalCurrentModel319
open CommonNominalFullCarrier
open GeneralWherePhysicalPatch319 (n compatible_update ordinary_same patch_preserves different_mid prior_raw)
open GeneralWherePhysicalCurrentRead319 (plan packet bindings low high reads address_lo address_hi)
open GeneralWhereOriginSingleSource318 (declaration)
open GeneralWhereOriginSingleRead318 (firstOrigin secondOrigin)
open GeneralDictionaryJournalRefinement228Source (root root_point foo)
open GeneralNominalVersionedFrame231 (capture binder)
open GeneralNominalVersionedPlans231 (variables SchemaHolds childSchema)
open GeneralNominalRecursiveInspection (Observes nominal_observation_unique)
open GeneralNominalCenters
open GeneralWhereOriginSingleModel318 (new_write)
open GeneralWhereOriginSingleCells318 (loNow sig)
open GeneralWherePhysicalOldModel319 (m actual_m)
open GeneralWhereVersionCase317 (expr)
open GeneralWhereVersionCompiler317 (schema emissions emit child)
open GeneralLiveCompoundRegistry316 (otherChild)
open GeneralDictionaryOptionalExpression229 (expression)
open GeneralMixedCompoundChildEquality307 (mid)

theorem capture_now (i) (known : i = 0 ∨ i = 1) :
    (capture packet).inputs i = (2,2) := by
  change (GeneralNominalVersionedAllocation231.capture _ _ _ _ packet.bindings).inputs i = _
  rw [bindings]
  rcases known with rfl|rfl <;> rfl

theorem binder_now (i) (known : i = 0 ∨ i = 1) : binder plan i = 2 := by
  have notOutput : i ∉ packet.declaration.outputNames := by
    rcases known with rfl|rfl <;> decide +kernel
  unfold binder
  rw [ite_eq_right notOutput]
  change (if ((capture packet).inputs i).1 = ((capture packet).inputs i).2 then
    ((capture packet).inputs i).1 else _) = _
  rw [capture_now _ known]
  rfl

theorem captures (i : Nat) (used : i ∈ packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed packet i) :
    GeneralNominalCaptureMerges.Fits n ((capture packet).inputs i) (n (binder plan i)).1 := by
  have known : i = 0 ∨ i = 1 := by
    rcases used with h|⟨c,seen,read⟩
    · change i ∈ [0,1] at h
      simpa using h
    · cases List.mem_singleton.mp seen
      change i ∈ [0] at read
      exact .inl (List.mem_singleton.mp read)
  rw [capture_now _ known,binder_now _ known]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem schema_code : plan.headSchema =
    { tests := [(.source 0,.nominal 0 2)]
      variables := [⟨0,firstOrigin,.actual⟩,⟨1,secondOrigin,.actual⟩] } := by
  have eq := GeneralNominalCenteredHeadMatPlanData.head_schema GeneralWherePhysicalCurrentRead319.same
  rw [← eq]
  unfold Plan.headSchema
  rw [GeneralWhereOriginSingleRead318.new_query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,List.ofFn_succ,
    GeneralWhereOriginSingleSource318.newPlan,rootSite,firstOrigin,secondOrigin]

theorem root_value : Equivalent (n 0).1 foo :=
  GeneralDictionaryJournalRefinement228Source.root_fixed n prior_raw

theorem width : Equivalent (n 2).1 .emptyRecord :=
  GeneralDictionaryJournalRefinement228Source.width_two n prior_raw

theorem sees (i : Nat) (known : i = 0 ∨ i = 1) :
    Observes n (.nominal (.source 0) 0 i) .emptyRecord := by
  rcases known with rfl|rfl <;> exact .nominal (.source 0) root_value rfl

theorem origin_actual (i : Nat) (known : i = 0 ∨ i = 1) :
    GeneralNominalOriginTerms.Same n (.nominal (.source 0) 0 i) (.source (binder plan i)) := by
  refine ⟨⟨_,sees i known⟩,⟨_,.source _⟩,?_⟩
  intro a b left right
  cases right
  rw [binder_now _ known]
  exact equivalent_trans (nominal_observation_unique n (.argument (.source 0) 0 i) a .emptyRecord left (sees i known)) ⟨width.2,width.1⟩
where equivalent_trans {a b c : Ty} (ab : Equivalent a b) (bc : Equivalent b c) : Equivalent a c :=
    ⟨subtype_trans ab.1 bc.1,subtype_trans bc.2 ab.2⟩

theorem tests : SchemaHolds plan plan.headSchema n := by
  rw [schema_code]
  constructor
  · intro entry present
    cases List.mem_singleton.mp present
    refine ⟨⟨_,.source 0⟩,?_⟩
    intro value seen
    cases seen
    exact ⟨[.inl .emptyRecord,.inl .emptyRecord],rfl,root_value.1,root_value.2⟩
  · intro entry present
    rcases List.mem_cons.mp present with rfl|last
    · exact origin_actual 0 (.inl rfl)
    · cases List.mem_singleton.mp last
      exact origin_actual 1 (.inr rfl)

theorem one_emission : emissions plan = [emit plan otherChild sig] := by
  unfold emissions GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  rfl

theorem emitted_rows : (schema plan).equations = [⟨4,.actual,expression⟩,low.row,high.row] := by
  unfold schema
  rw [one_emission]
  rfl

theorem complete : (schema plan).unknown = false := by
  unfold schema
  rw [one_emission]
  rfl

theorem actual_n : Equivalent (n 4).1 GeneralDictionaryOptionalOutput229.value :=
  congrArg (fun x : CommonNominalFullCarrier.Ty × CommonNominalFullCarrier.Row => Equivalent x.1 _) (ordinary_same 4 (by decide)) ▸ actual_m

theorem current_lower : low.row.Holds (variables plan n) n := by
  change Equivalent (n (GeneralVersionedEndpointAddress315.atCell plan .lower otherChild.id 0 expr)).1
    (variant 0 (variables plan n .lower 0))
  rw [address_lo,GeneralNominalVersionedExpressionFrame236.variable_value,reads.1,← ordinary_same 2 (by decide)]
  exact new_write m

theorem rows : (schema plan).Holds (variables plan n) n := by
  intro row found
  rw [emitted_rows] at found
  simp only [List.mem_cons,List.not_mem_nil,or_false] at found
  rcases found with rfl|rfl|rfl
  · exact actual_n
  · exact current_lower
  · exact GeneralWherePhysicalTicket319.current_upper_stored n compatible_update

theorem exact_child (check : otherChild.Signature GeneralDictionaryJournalRefinement228Source.roles) :
    childSchema plan otherChild check = ⟨[⟨mid,.actual,expr⟩],false⟩ := rfl

theorem child_holds (check : otherChild.Signature GeneralDictionaryJournalRefinement228Source.roles) :
    (childSchema plan otherChild check).Holds (variables plan n) n := by
  rw [exact_child check]
  intro row found
  cases List.mem_singleton.mp found
  change Equivalent (n mid).1 (variant 0 (variables plan n .actual 0))
  have value : variables plan n .actual 0 = (n 2).1 := by
    unfold variables
    change (n (binder plan 0)).1 = _
    rw [binder_now 0 (.inl rfl)]
  rw [value,← patch_preserves mid different_mid,← GeneralWherePhysicalOldModel319.center_saved]
  apply GeneralDictionaryDefaultExpression209.equivalent_trans GeneralLiveCompoundLeafProof316.center_value
  exact ⟨(common_variant_iff ..).mpr width.2,(common_variant_iff ..).mpr width.1⟩

theorem full : GeneralWhereVersionSemantics317.Holds plan n := by
  refine ⟨GeneralWherePhysicalHead319.current_head,point_root_holds _ _ root_point _,captures,tests,complete,rows,?_⟩
  intro c visible check
  cases List.mem_singleton.mp visible
  refine ⟨?_,child_holds check⟩
  intro i
  have z : i = 0 := Fin.ext (by have b := i.isLt; change i.val < 1 at b; change i.val = 0; omega)
  subst i
  apply GeneralWhereOriginChild318.argument_fits plan n otherChild (List.mem_singleton_self _) check
    0 expr rfl _ rows (child_holds check)
  intro name read
  change name ∈ [0] at read
  cases List.mem_singleton.mp read
  exact captures 0 (.inl List.mem_cons_self)

end Yulang.GeneralWherePhysicalCurrentModel319

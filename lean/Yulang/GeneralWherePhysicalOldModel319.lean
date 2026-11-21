import Yulang.GeneralWherePhysicalOldPick319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 32000000
namespace Yulang.GeneralWherePhysicalOldModel319
open GeneralWhereOriginSingleSource318
open GeneralWhereOriginSingleModel318 (previous previousLo previousHi previous_outside old_oldSources)
open GeneralWhereOriginSingleCommon318 (recorded_lo recorded_hi)
open GeneralWherePhysicalOldValues319 (baseline_raw old_head old_binder bounded binder_value)
open GeneralWherePhysicalOldHead319 (schema_code schema_holds all_captures)
open GeneralWherePhysicalOldPick319 (actual_output)
open GeneralDictionaryJournalRefinement228Source (roles root snapshot root_point)
open GeneralLiveCompoundLeafProof316 (w center_value)
open GeneralLiveCompoundRegistry316 (otherChild)
open GeneralWhereOriginSingleCells318 (loOld hi sig)
open GeneralWhereVersionCompiler317 (schema emissions emit child)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralNominalIdentities (Origin source)
open GeneralNominalVersionedPlans231 (variables childSchema HeadModels SchemaHolds)
open GeneralNominalVersionedFrame231 (capture binder)
open GeneralNominalCenteredHeadMatSchemas (Equation)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralWhereVersionCase317 (expr)
open CommonNominalFullCarrier

noncomputable abbrev m := previous w

theorem raw_same (n : Nat) (found : n ∈ GeneralNominalState.sources snapshot) : w n = m n :=
  old_oldSources w n found

theorem source_value (i : Fin 5) : w i.val = m i.val :=
  raw_same _ (GeneralNominalAllocationSupport.slot_source snapshot i)

theorem same_small (k : Origin) (small : k.2.2.1 ≤ 9) :
    w (source snapshot.seed k) = m (source snapshot.seed k) := by
  apply previous_outside
  · obtain ⟨a,large,eq⟩ := previousLo.high (t := snapshot) rfl
    change loOld = source snapshot.seed a at eq
    rw [eq]
    exact GeneralVersionedHighOrigins315.distinct (by omega) _
  · obtain ⟨a,large,eq⟩ := previousHi.high (t := snapshot) rfl
    change hi = source snapshot.seed a at eq
    rw [eq]
    exact GeneralVersionedHighOrigins315.distinct (by omega) _

theorem binder_same (n) (known : n = 0 ∨ n = 1) : w (binder oldPlan n) = m (binder oldPlan n) := by
  rw [old_binder n known]
  apply same_small
  change (8:Nat) ≤ 9
  decide

theorem private_head : HeadModels older m := by
  apply (GeneralNominalVersionedPacketFrame236.head_models_iff
    (first := w) (last := m) older ?_).mp old_head
  intro n used
  apply previous_outside
  · intro eq
    have impossible := GeneralWhereOriginHeadAgree318.head_not_written
      (p := oldPlan) List.mem_cons_self (previousLo.high rfl)
      (GeneralWhereOriginSingleModel318.older_absent loOld (previousLo.high rfl))
    change loOld ∉ GeneralNominalVersionedPacketFrame236.headSources older at impossible
    exact impossible (eq.symm ▸ used)
  · intro eq
    have impossible := GeneralWhereOriginHeadAgree318.head_not_written
      (p := oldPlan) List.mem_cons_self (previousHi.high rfl)
      (GeneralWhereOriginSingleModel318.older_absent hi (previousHi.high rfl))
    change hi ∉ GeneralNominalVersionedPacketFrame236.headSources older at impossible
    exact impossible (eq.symm ▸ used)

theorem saved_captures (n : Nat)
    (used : n ∈ older.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed older n) :
    GeneralNominalCaptureMerges.Fits m ((capture older).inputs n) (m (binder oldPlan n)).1 := by
  have known : n = 0 ∨ n = 1 := by
    rcases used with h|⟨c,present,found⟩
    · change n ∈ [0,1] at h
      simpa using h
    · cases List.mem_singleton.mp present
      change n ∈ [0] at found
      exact .inl (List.mem_singleton.mp found)
  have original := bounded n known
  rw [GeneralWherePhysicalOldValues319.old_capture n known] at original ⊢
  unfold GeneralNominalCaptureMerges.Fits at original ⊢
  dsimp only at original ⊢
  have four : w 4 = m 4 := source_value (4 : Fin 5)
  have two : w 2 = m 2 := source_value (2 : Fin 5)
  rw [← binder_same n known,← four,← two]
  exact original

theorem saved_schema : SchemaHolds oldPlan oldPlan.headSchema m := by
  apply (GeneralNominalVersionedHeadFrame236.schema_iff (first := w) (last := m)
    oldPlan oldPlan.headSchema ?_).mp schema_holds
  intro n found
  rw [schema_code] at found
  change n ∈ [0,0,binder oldPlan 0,0,binder oldPlan 1] at found
  simp only [List.mem_cons,List.not_mem_nil,or_false] at found
  rcases found with rfl|rfl|rfl|rfl|rfl
  · exact source_value 0
  · exact source_value 0
  · exact binder_same 0 (.inl rfl)
  · exact source_value 0
  · exact binder_same 1 (.inr rfl)

theorem compiled_emission : emissions oldPlan = [emit oldPlan otherChild sig] := by
  unfold emissions GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  rfl

theorem emitted_rows : (schema oldPlan).equations =
    [⟨4,.actual,GeneralDictionaryOptionalExpression229.expression⟩,previousLo.row,previousHi.row] := by
  unfold schema
  rw [compiled_emission]
  rfl

theorem complete : (schema oldPlan).unknown = false := by
  unfold schema
  rw [compiled_emission]
  rfl

theorem actual_m : Equivalent (m 4).1 GeneralDictionaryOptionalOutput229.value := by
  have four : w 4 = m 4 := source_value (4 : Fin 5)
  rw [← four]
  exact actual_output

theorem rows : (schema oldPlan).Holds (variables oldPlan m) m := by
  intro row found
  rw [emitted_rows] at found
  simp only [List.mem_cons,List.not_mem_nil,or_false] at found
  rcases found with rfl|rfl|rfl
  · exact actual_m
  · exact recorded_lo w
  · exact recorded_hi w

theorem child_row :
    childSchema oldPlan otherChild sig = ⟨[⟨GeneralMixedCompoundChildEquality307.mid,.actual,expr⟩],false⟩ := rfl

theorem center_saved : w GeneralMixedCompoundChildEquality307.mid = m GeneralMixedCompoundChildEquality307.mid :=
  same_small (GeneralNominalAllocation.origin root.identity declaration.id 9 otherChild.id 0) (by decide)

theorem child_holds (check : otherChild.Signature roles) :
    (childSchema oldPlan otherChild check).Holds (variables oldPlan m) m := by
  change (childSchema oldPlan otherChild sig).Holds (variables oldPlan m) m
  rw [child_row]
  intro row found
  cases List.mem_singleton.mp found
  change Equivalent (m GeneralMixedCompoundChildEquality307.mid).1
    (variant 0 (variables oldPlan m .actual 0))
  have operand : variables oldPlan m .actual 0 = .emptyRecord := by
    unfold variables
    change (m (binder oldPlan 0)).1 = _
    rw [← binder_same 0 (.inl rfl)]
    exact binder_value 0 (.inl rfl)
  rw [operand,← center_saved]
  exact center_value

theorem full : Holds oldPlan m := by
  refine ⟨private_head,GeneralNominalCenters.point_root_holds _ _ root_point _,saved_captures,saved_schema,complete,rows,?_⟩
  intro c listed sig'
  cases List.mem_singleton.mp listed
  refine ⟨?_,child_holds sig'⟩
  intro i
  have idx : i = 0 := Fin.ext (by
    change i.val = 0
    have b := i.isLt
    change i.val < 1 at b
    omega)
  subst i
  apply GeneralWhereOriginChild318.argument_fits oldPlan m otherChild (List.mem_singleton_self _) sig'
    0 expr rfl _ rows (child_holds sig')
  intro n used
  change n ∈ [0] at used
  cases List.mem_singleton.mp used
  exact saved_captures 0 (.inl List.mem_cons_self)

end Yulang.GeneralWherePhysicalOldModel319

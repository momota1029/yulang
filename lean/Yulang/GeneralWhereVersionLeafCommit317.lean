import Yulang.GeneralWhereVersionJournal317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32000
set_option maxHeartbeats 43000000
/-! The repaired leaf is committed under the existing operational predicate,
not only in a singled-out parent model. Its bound point captures source 2;
the old private binder need not be overwritten or reused. -/
namespace Yulang.GeneralWhereVersionLeafCommit317
open GeneralWhereVersionCase317 (site occ lower upper)
open GeneralWhereVersionBase317 (loSlot hiSlot two source source_old source_lo source_hi endpointTerm)
open GeneralWhereVersionSnapshot317 (snap context)
open GeneralWhereVersionCommit317 (core framedState)
open GeneralWhereVersionJournal317 (prior)
open GeneralWhereVersionLeafHead317 (packet plan binding binder capture projections report_exact)
open GeneralWhereVersionLeafProof317 (head_schema emitted terminal projection ref mid)
open GeneralLiveCompoundRegistry316 (leaf)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedPlans231
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveCandidates (report)
open GeneralNominalRecursiveInspection (selfChecks Observes)
open CommonNominalFullCarrier

theorem actual_ports (m : Assignment) (valid : Models framedState m) :
    Equivalent (m lower).1 (variant 0 (m 2).1) ∧ Equivalent (m upper).1 (variant 0 (m 2).1) := by
  have a := valid.1.1.1.2.1 loSlot endpointTerm rfl
  have b := valid.1.1.1.2.1 hiSlot endpointTerm rfl
  change Equivalent (m (source loSlot)).1 (variant 0 (m (source two)).1) at a
  change Equivalent (m (source hiSlot)).1 (variant 0 (m (source two)).1) at b
  rw [source_lo,source_old] at a
  rw [source_hi,source_old] at b
  exact ⟨a,b⟩

theorem registered (m : Assignment) (valid : Models framedState m) : site.Holds m :=
  valid.1.2.2.2.1 site (List.mem_append_right _ (List.mem_singleton_self _))

theorem ordinary (m : Assignment) (valid : Models framedState m) : Ordinary packet m := by
  refine ⟨?_,?_,?_⟩
  · rw [binding]
    intro a ha b hb _
    cases List.mem_singleton.mp ha
    cases List.mem_singleton.mp hb
    exact subtype_refl _
  · unfold GeneralNominalVersionedAllocation231.merges
    rw [binding]
    exact PresenceNormalForm.all_nil _ _
  · change PresenceNormalForm.All CommonNominalFullCarrier.model m
      (selfChecks snap (report context leaf [(loSlot,hiSlot)]))
    rw [report_exact]
    intro atom member
    simp only [selfChecks,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    have fits : Subtype (m (source loSlot)).1 (m (source hiSlot)).1 := by
      rw [source_lo,source_hi]
      exact subtype_trans (actual_ports m valid).1.1 (actual_ports m valid).2.2
    rcases member with rfl|rfl|rfl
    · exact fits
    · exact fits
    · exact subtype_refl _

theorem mid_value (m : Assignment) (valid : Models framedState m) :
    Equivalent (m mid).1 (variant 0 (m 2).1) := by
  have old := GeneralLiveCompoundPostFeedback316.old_valid m (prior m valid)
  exact GeneralMixedCompoundChildEquality307.historical_child_center m
    (GeneralMixedCompoundUpperSupport307.child_history m old)
theorem observed (m : Assignment) (valid : Models framedState m) : Observes m projection (m 2).1 :=
  .structural (.source _) (values := [(m 2).1]) rfl (mid_value m valid) rfl

theorem schema (m : Assignment) (valid : Models framedState m) :
    SchemaHolds plan plan.headSchema m := by
  rw [head_schema]
  constructor
  · intro test member
    cases List.mem_singleton.mp member
    refine ⟨⟨_,.source _⟩,?_⟩
    intro _ seen
    cases seen
    exact ⟨[(m 2).1],rfl,mid_value m valid⟩
  · intro entry member
    cases List.mem_singleton.mp member
    change GeneralNominalOriginTerms.Same m projection (.source (GeneralNominalVersionedFrame231.binder plan 0))
    rw [binder]
    refine ⟨⟨_,observed m valid⟩,⟨_,.source _⟩,?_⟩
    intro x y hx hy
    cases hy
    exact GeneralLiveCompoundDepth316.variant_child
      (root := ref) (tag := 0)
      (by intro v seen; cases seen; exact mid_value m valid)
      (.structural (.variant 0)) (0 : Fin 1) hx
theorem holds (m : Assignment) (valid : Models framedState m) : Holds plan m := by
  refine ⟨valid.1.1,⟨ordinary m valid,projections m,registered m valid,?_,schema m valid,?_,?_⟩,?_⟩
  · intro name member
    rcases member with input | ⟨clause,present,_⟩
    · have eq : name = 0 := List.mem_singleton.mp input
      subst name
      rw [capture,binder]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · cases present
  · rw [emitted]; intro _ absent; cases absent
  · intro _ absent; cases absent
  · unfold Outputs; rw [emitted]; intro _ absent; cases absent

theorem committed : GeneralNominalVersionedMixedKernel234.Committed framedState plan := by
  refine ⟨fun m valid => ⟨holds m valid,GeneralWhereVersionLeafRegistry317.classes m⟩,?_⟩
  intro child member
  change child ∈ GeneralNominalVersionedFrame231.children packet at member
  rw [terminal] at member
  cases member

end Yulang.GeneralWhereVersionLeafCommit317

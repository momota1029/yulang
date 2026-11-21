import Yulang.GeneralWhereVersionJournal317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 48000000
/-! The C316 regression through the isolated repaired commit:
actual old root choice, recompiled children, actual new leaf choice, and
recursive evidence under every model of the repaired journal. This is not
the global successor boundary or a claim about the concrete Sat driver. -/
namespace Yulang.GeneralWhereVersionRegression317
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry declaration leaf)
open GeneralLiveCompoundChildSite316 (child)
open GeneralLiveCompoundLeafInstall316 (after)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralWhereVersionCase317 (occ ordered_children)
open GeneralWhereVersionCommit317 (core framedState produced)
open GeneralWhereVersionInstall317 (before fixed step Models mixed_eq)
open GeneralWhereVersionJournal317 (fixed_iff)
open GeneralWhereVersionCompiler317 (children)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralNominalCenters GeneralSourceDictionaries
open GeneralDictionaryReadback (Payload erased_evidence_node)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂)

inductive Frontier : Occurrence roles → Nat → List (Occurrence roles) → Prop where
  | recompiled :
      GeneralWhereVersionInstall317.InstallStep sourceRegistry before fixed →
      GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry after root
        (.selected declaration.id [child]) →
      Frontier root declaration.id (children rootPlan)
  | leaf :
      GeneralNominalVersionedDiagnostic232.Local registry framedState occ (.selected leaf.id []) →
      Frontier occ leaf.id []

inductive Accepts : Occurrence roles → Payload → Prop where
  | node : Frontier focus key kids →
      All₂ Accepts kids payloads → Accepts focus (.node key payloads)

def LeafCommitted (m : Assignment) : Prop :=
  GeneralNominalVersionedPlans231.Holds GeneralWhereVersionLeafHead317.plan m ∧
    GeneralNominalVersionedEffects231.ClassEffects core occ GeneralWhereVersionLeafHead317.plan m ∧
    GeneralNominalSaturationState.Generated core.erased.current root occ

structure RootCertificate (m : Assignment) : Prop where
  entry : rootPlan ∈ fixed.versionedWhere
  original : Frame registry after.core root declaration.id rootPlan
  typed : Holds rootPlan m
  effects : GeneralNominalVersionedEffects231.ClassEffects core root rootPlan m
  outputs : ∀ out ∈ root.demand.outputs, GeneralDictionaryDefaultEvidence204.OutputWitness rootPlan m out
  emitted : ∀ d ∈ children rootPlan, GeneralNominalSaturationState.Generated core.erased.current root d

def Instance (m : Assignment) : LocalInstance roles :=
  fun focus key kids =>
    (focus = root ∧ key = declaration.id ∧ kids = children rootPlan ∧ RootCertificate m) ∨
    GeneralNominalVersionedEvidence231.Instance registry core m focus key kids

def Evidence (m : Assignment) (focus : Occurrence roles) (payload : Payload) : Prop :=
  ErasedEvidence (Instance m) focus payload

theorem committed_child (m : Assignment) (valid : Models fixed m) : LeafCommitted m := by
  have parent := (fixed_iff m).mp valid
  exact ⟨GeneralWhereVersionLeafProof317.holds m parent,GeneralWhereVersionLeafRegistry317.classes m,produced⟩

theorem recorded (m : Assignment) (valid : Models fixed m) : RootCertificate m := by
  have parent := (fixed_iff m).mp valid
  have member : rootPlan ∈ fixed.versionedWhere := List.mem_singleton_self _
  obtain ⟨typed,live⟩ := valid.2 rootPlan member
  rw [mixed_eq] at live
  refine ⟨member,GeneralLiveCompoundPostRootHead316.frame,typed,live,
    GeneralWhereVersionSemantics317.outputs m parent,?_⟩
  intro d emitted
  rw [ordered_children] at emitted
  exact (List.mem_singleton.mp emitted).symm ▸ produced

theorem accepted_leaf : Accepts occ (.node leaf.id []) :=
  .node (.leaf GeneralWhereVersionLeafSelect317.selected) .nil

theorem accepted_root : Accepts root GeneralLiveCompoundFullResult316.dictionary := by
  have picked := Frontier.recompiled step GeneralLiveCompoundPostRootSelect316.selected
  rw [ordered_children] at picked
  exact .node picked (.cons accepted_leaf .nil)

theorem semantic_node (m : Assignment) (valid : Models fixed m)
    (selection : Frontier focus key kids)
    (children : All₂ (Evidence m) kids payloads) :
    Evidence m focus (.node key payloads) := by
  apply erased_evidence_node _ _ _ _ _ _ children
  cases selection with
  | recompiled _ _ => exact Or.inl ⟨rfl,rfl,rfl,recorded m valid⟩
  | leaf _ =>
    have parent := (fixed_iff m).mp valid
    exact Or.inr ⟨_,GeneralWhereVersionLeaf317.certificate m parent⟩

theorem acceptance_sound (m : Assignment) (valid : Models fixed m)
    (accepted : Accepts focus payload) : Evidence m focus payload := by
  cases accepted with
  | node selection next =>
    apply semantic_node m valid selection
    cases selection with
    | recompiled _ _ =>
      rw [ordered_children] at next ⊢
      cases next with
      | cons one none =>
        cases one with
        | node choice children =>
          cases choice with
          | leaf _ =>
            cases children
            cases none
            exact .cons (semantic_node m valid (.leaf GeneralWhereVersionLeafSelect317.selected) .nil) .nil
    | leaf _ => cases next; exact .nil

theorem regression :
    GeneralWhereVersionInstall317.InstallStep sourceRegistry before fixed ∧
    Accepts root GeneralLiveCompoundFullResult316.dictionary ∧
    (∃ m, Models fixed m) ∧
    (∀ m, Models fixed m → Evidence m root GeneralLiveCompoundFullResult316.dictionary) ∧
    ¬ B4SkeletonV8.EvidenceNode (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) := by
  obtain ⟨m,p⟩ := GeneralWhereVersionWitness317.inhabited
  refine ⟨step,accepted_root,⟨m,(fixed_iff m).mpr p⟩,
    fun m valid => acceptance_sound m valid accepted_root,?_⟩
  exact GeneralLiveCompoundCounterexample316.not_evidenceNode

end Yulang.GeneralWhereVersionRegression317

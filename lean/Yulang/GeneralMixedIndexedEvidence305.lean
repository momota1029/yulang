import Yulang.GeneralMixedIndexedPlanSemantics305

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedIndexedEvidence305
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedEvidence231 (Certificate Frame)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)
open GeneralNominalCenteredHeadMatPlanData (Same)
open GeneralNominalCenteredHeadMatEffects (compileBody)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralDictionaryDefaultEvidence204 (OutputWitness)
open GeneralMixedIndexedFrame305 (IndexedView coordinates relocate relocated_same relocated_frame reverse)
open GeneralDeferredLadderTransport302 (children_eq held_of_reindex)
open GeneralMixedIndexedPlanSemantics305 (body_same)
open GeneralNominalVersionedEffects231 (body_holds_iff)
variable {roles : Roles.RoleDecls} {a b : State roles} {p q : Plan roles}

theorem compilation_exact (same : Same p q) (body : Body) :
    compileBody p body = compileBody q body := by
  cases body <;> simp only [compileBody,same.registry,same.interpretation]

theorem witness_forward (same : Same p q) (m : Assignment) (o : GeneralSourceState.Output)
    (given : OutputWitness p m o) : OutputWitness q m o := by
  obtain ⟨body,found,⟨e,compiled⟩,held⟩ := given
  refine ⟨body,same.declaration ▸ found,⟨e,(compilation_exact same body).symm.trans compiled⟩,?_⟩
  exact (body_holds_iff q o.target m body).mp
    ((body_same same o.target body m).mp ((body_holds_iff p o.target m body).mpr held))

theorem certificate_forward (view : IndexedView a b)
    (given : Certificate r a.core m o k cs p) :
    Certificate r b.core m o k cs (relocate view given.frame) := by
  have same := relocated_same view given.frame
  refine ⟨relocated_frame view given.frame,given.children_eq.trans (children_eq same),?_,?_⟩
  · exact held_of_reindex same m given.packet
      ((GeneralNominalReportContext305.model_iff (coordinates view given.frame) m).mp given.packet.1)
  · exact fun out listed => witness_forward same m out (given.outputs out listed)

theorem instance_forward (view : IndexedView a b) (r : Registry) (m : Assignment)
    (o : Occurrence roles) (k : Nat) (cs : List (Occurrence roles))
    (given : GeneralNominalVersionedEvidence231.Instance r a.core m o k cs) :
    GeneralNominalVersionedEvidence231.Instance r b.core m o k cs :=
  let ⟨_,source⟩ := given
  ⟨_,certificate_forward view source⟩

theorem indexed_tree_iff (view : IndexedView a b) (r : Registry) (m : Assignment)
    (tree : Dictionary roles) :
    Evidence (GeneralNominalVersionedEvidence231.Instance r a.core m) tree ↔
      Evidence (GeneralNominalVersionedEvidence231.Instance r b.core m) tree :=
  ⟨evidence_mono _ _ (instance_forward view r m),
   evidence_mono _ _ (instance_forward (reverse view) r m)⟩

theorem evidence_iff (view : IndexedView a b) (r : Registry) (m : Assignment)
    (o : Occurrence roles) (dictionary : GeneralDictionaryReadback.Payload) :
    GeneralNominalVersionedEvidence231.Evidence r a.core m o dictionary ↔
      GeneralNominalVersionedEvidence231.Evidence r b.core m o dictionary :=
  ⟨fun ⟨tree,readback,given⟩ => ⟨tree,readback,(indexed_tree_iff view r m tree).mp given⟩,
   fun ⟨tree,readback,given⟩ => ⟨tree,readback,(indexed_tree_iff view r m tree).mpr given⟩⟩

end Yulang.GeneralMixedIndexedEvidence305

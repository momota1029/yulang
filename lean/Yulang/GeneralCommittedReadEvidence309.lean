import Yulang.GeneralGeneratedDictionaryNodes299
import Yulang.GeneralNominalVersionedMixedReady235

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralCommittedReadEvidence309
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedMixedKernel234 (Committed)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedFrame231 (children)
open GeneralNominalCenteredHeadAllocEncoding renaming registry → compileRegistry
open GeneralGeneratedDictionaryRun299 (Read run)
open GeneralGeneratedDictionaryScope299 (Faithful)
open GeneralGeneratedDictionaryNodes299 (Nodes)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)
open GeneralDictionaryReadback (Payload)
open B4TargetV8 (Reachable)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls} {r : Registry} {s : State roles} {root : Occurrence roles}

/-- The row's exact current frame and ordered children are independently
certified. Commitment supplies the packet and current output facts for
every full model, not one existential witness per child. -/
structure CommittedRow (r : Registry) (s : State roles) (focus : Occurrence roles)
    (k : Nat) (ordered : List (Occurrence roles)) : Prop where
  packet : ∃ p : Plan roles, Frame (compileRegistry r) s.core focus k p ∧
    children p.packet = ordered ∧ Committed s p

def CommittedRead (r : Registry) (s : State roles) (read : Read) (decode : Nat → Occurrence roles) : Prop :=
  ∀ i e, read i = some e → CommittedRow r s (decode i) e.key (e.children.map decode)

/-- No stability or ledger-settlement premise enters this local node rule.
The certificate consumes child evidence in the very same full model. -/
theorem node (checked : (boundary roles).Checked r) (reached : Reachable (boundary roles) r root s)
    {f : Occurrence roles} {k : Nat} {ordered : List (Occurrence roles)}
    (row : CommittedRow r s f k ordered) (m : Assignment) (valid : Models s m) (ds : List Payload)
    (given : All₂ ((boundary roles).Evidence r s m) ordered ds) :
    (boundary roles).Evidence r s m f (.node k ds) := by
  obtain ⟨p,frame,orderedEq,committed⟩ := row.packet
  have ready := GeneralNominalVersionedMixedReady235.ready checked reached frame
  have actual := (committed.1 m valid)
  have classNow : GeneralNominalVersionedEffects231.ClassEffects s.core f p m :=
    frame.occurrence_eq ▸ actual.2
  exact GeneralNominalVersionedEvidence231.evidence_node
    ⟨p,GeneralNominalVersionedEvidence231.certificate_of_semantics
      frame orderedEq.symm actual.1 ready classNow⟩ given

theorem child_generated {f : Occurrence roles} {k : Nat} {ordered : List (Occurrence roles)}
    (row : CommittedRow r s f k ordered)
    (atParent : GeneralNominalSaturationState.Generated s.core.erased.current root f)
    (c : Occurrence roles) (member : c ∈ ordered) :
    GeneralNominalSaturationState.Generated s.core.erased.current root c := by
  obtain ⟨p,frame,ord,committed⟩ := row.packet
  have edge := committed.2 c (ord.symm ▸ member)
  exact .child atParent (frame.occurrence_eq ▸ edge)

theorem nodes (checked : (boundary roles).Checked r) (reached : Reachable (boundary roles) r root s)
    (read : Read) (decode : Nat → Occurrence roles) (current : CommittedRead r s read decode) :
    Nodes (boundary roles) r s read decode := by
  intro i e seen m valid ds given
  exact node checked reached (current i e seen) m valid ds given

theorem sound (checked : (boundary roles).Checked r) (reached : Reachable (boundary roles) r root s)
    (read : Read) (decode : Nat → Occurrence roles) (view : Faithful (b:=boundary roles) (r:=r) (s:=s) read decode)
    (current : CommittedRead r s read decode) (fuel i : Nat) (d : Payload) (found : run read fuel i = some d) :
    B4TargetV8.Classify (boundary roles) r s (decode i) (.selected d) ∧
    ∀ m, Models s m → (boundary roles).Evidence r s m (decode i) d := by
  exact ⟨GeneralGeneratedDictionaryScope299.classifies _ _ view _ _ _ found,
    fun m valid => GeneralGeneratedDictionaryNodes299.same_model _ _ (nodes checked reached _ _ current) m valid _ _ _ found⟩

end Yulang.GeneralCommittedReadEvidence309

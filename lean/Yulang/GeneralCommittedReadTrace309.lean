import Yulang.GeneralCommittedReadEvidence309
import Yulang.GeneralOrderedDictionaryCheck309

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralCommittedReadTrace309
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedEvidence231 (Certificate)
open GeneralNominalCenteredHeadAllocEncoding renaming registry → compileRegistry
open GeneralGeneratedDictionaryRun299 (Entry Read run run_exact)
open GeneralGeneratedDictionaryScope299 (Faithful)
open GeneralCommittedReadEvidence309 (CommittedRead CommittedRow child_generated)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)
open GeneralDictionaryReadback (Payload)
open B4TargetV8 (Reachable Classify)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls} {r : Registry} {s : State roles} {root : Occurrence roles}

def FrameProof (r : Registry) (s : State roles) (m : Assignment) (read : Read)
    (decode : Nat → Occurrence roles) (i : Nat) (row : Entry) : Prop :=
  read i = some row ∧ ∃ p : Plan roles,
    Certificate (compileRegistry r) s.core m (decode i) row.key (row.children.map decode) p

/-- Full proof trace: each ordered position carries its actual generated
occurrence and a current local certificate (including associated outputs).
All occurrences use one fixed assignment. This is stronger data than a proof
that the erased dictionary typechecks or that its keys were found. -/
inductive Trace (r : Registry) (s : State roles) (root : Occurrence roles)
    (m : Assignment) (read : Read) (decode : Nat → Occurrence roles) : Nat → Payload → Prop where
  | node (i : Nat) (e : Entry) (ds : List Payload) :
      GeneralNominalSaturationState.Generated s.core.erased.current root (decode i) →
      FrameProof r s m read decode i e →
      All₂ (Trace r s root m read decode) e.children ds →
      Trace r s root m read decode i (.node e.key ds)

theorem frameProof (checked : (boundary roles).Checked r) (path : Reachable (boundary roles) r root s)
    (read : Read) (decode : Nat → Occurrence roles) (certified : CommittedRead r s read decode)
    (m : Assignment) (valid : Models s m) (i : Nat) (row : Entry) (readback : read i = some row) :
    FrameProof r s m read decode i row := by
  obtain ⟨p,f,pkids,commit⟩ := (certified i row readback).packet
  obtain ⟨holds,effects⟩ := commit.1 m valid
  have required := GeneralNominalVersionedMixedReady235.ready checked path f
  have same : GeneralNominalVersionedEffects231.ClassEffects s.core (decode i) p m := f.occurrence_eq ▸ effects
  exact ⟨readback,p,GeneralNominalVersionedEvidence231.certificate_of_semantics
    f pkids.symm holds required same⟩

theorem strengthen {α β : Type} {P Q : α → β → Prop} {xs : List α} {ys : List β}
    (given : All₂ P xs ys) (emit : ∀ x ∈ xs, ∀ y, P x y → Q x y) : All₂ Q xs ys := by
  induction given with
  | nil => exact .nil
  | cons head tail ih =>
    exact .cons (emit _ List.mem_cons_self _ head)
      (ih (fun x mem y h => emit x (List.mem_cons_of_mem _ mem) y h))

theorem construct (checked : (boundary roles).Checked r) (path : Reachable (boundary roles) r root s)
    (read : Read) (decode : Nat → Occurrence roles) (certified : CommittedRead r s read decode)
    (m : Assignment) (valid : Models s m) (fuel i : Nat) (d : Payload)
    (reached : GeneralNominalSaturationState.Generated s.core.erased.current root (decode i))
    (ok : run read fuel i = some d) : Trace r s root m read decode i d := by
  induction fuel generalizing i d with
  | zero => cases ok
  | succ n ih =>
    obtain ⟨row,ds,hit,legit,rfl⟩ := (run_exact ..).mp ok
    refine .node i row ds reached (frameProof checked path read decode certified m valid i row hit)
      (strengthen legit ?_)
    intro child member dict result
    exact ih child dict (child_generated (certified i row hit) reached _ (List.mem_map.mpr ⟨child,member,rfl⟩)) result

theorem verified (checked : (boundary roles).Checked r) (path : Reachable (boundary roles) r root s)
    (read : Read) (decode : Nat → Occurrence roles) (certified : CommittedRead r s read decode)
    (faithful : Faithful (b:=boundary roles) (r:=r) (s:=s) read decode)
    (fuel i : Nat) (d : Payload)
    (reached : GeneralNominalSaturationState.Generated s.core.erased.current root (decode i))
    (ok : GeneralOrderedDictionaryCheck309.validate read fuel i d = .ok ()) :
    Classify (boundary roles) r s (decode i) (.selected d) ∧
    ∀ m, Models s m → Trace r s root m read decode i d ∧ (boundary roles).Evidence r s m (decode i) d := by
  have ran := (GeneralOrderedDictionaryCheck309.exact ..).mp ok
  have recognized := GeneralCommittedReadEvidence309.sound checked path read decode faithful certified fuel i d ran
  exact ⟨recognized.1,fun m valid => ⟨construct checked path read decode certified m valid fuel i d reached ran,
    recognized.2 m valid⟩⟩

end Yulang.GeneralCommittedReadTrace309

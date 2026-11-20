import Yulang.GeneralMixedIndexedDiagnosticLocal305
import Yulang.GeneralMixedIndexedEvidence305
import Yulang.GeneralNominalVersionedMixedSourceBoundary234

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedIndexedEvidenceAt305
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalVersionedJournal232 (State)
open GeneralMixedIndexedFrame305 (IndexedView reverse)
open GeneralMixedDiagnosticSlice304 (Semantics)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalSaturationState (Generated)
open GeneralDeferredLadderOperationalView304 (View alias_forward)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralMixedIndexedEvidence305 (evidence_iff)
variable {roles : Roles.RoleDecls} {a b : State roles}

theorem generated_forward (rel : View a b) (given : Generated a.core.erased.current root o) :
    Generated b.core.erased.current root o := by
  induction given with
  | root => exact .root
  | child _ edge ih => exact .child ih (rel.edges ▸ edge)
  | alias _ first last alias ih =>
    exact .alias ih (rel.sites ▸ first) (rel.sites ▸ last) (alias_forward rel alias)

theorem generated_iff (rel : View a b) (root o : Occurrence roles) :
    Generated a.core.erased.current root o ↔ Generated b.core.erased.current root o :=
  ⟨generated_forward rel,generated_forward rel.symm⟩

theorem local_iff (rel : IndexedView a b) (slices : Semantics a b)
    (r : Registry) (o : Occurrence roles) (f : Frontier (Occurrence roles)) : Local r a o f ↔ Local r b o f :=
  GeneralNominalVersionedMixedSourceBoundary234.local_iff.trans
    (GeneralNominalVersionedMixedBoundary234.local_iff.trans
      ((GeneralMixedIndexedDiagnosticLocal305.local_iff rel slices (registry r) o f).trans
        (GeneralNominalVersionedMixedBoundary234.local_iff.symm.trans
          GeneralNominalVersionedMixedSourceBoundary234.local_iff.symm)))

theorem allChildren_forward (rel : IndexedView a b) (r : Registry)
    (m : GeneralNominalCommonBridge.Assignment)
    (given : All₂ (fun o p => (boundary roles).Evidence r a m o p) children payloads) :
    All₂ (fun o p => (boundary roles).Evidence r b m o p) children payloads := by
  induction given with
  | nil => exact .nil
  | cons first _ ih => exact .cons ((evidence_iff rel (registry r) m _ _).mp first) ih

/-- Does not infer raw stability from exact diagnostics. A source-side
EvidenceAt proof can be reused given the separate stability direction. -/
theorem evidenceAt_forward (rel : IndexedView a b) (slices : Semantics a b)
    (r : Registry) (root : Occurrence roles)
    (stableBack : ∀ o, (boundary roles).Stable r b o → (boundary roles).Stable r a o)
    (old : B4SkeletonV8.EvidenceAt (boundary roles) r a root) :
    B4SkeletonV8.EvidenceAt (boundary roles) r b root := by
  intro m valid o k children payloads reached stable childrenStable selected supplied
  have oldEvidence := old m ((rel.raw.models m).mpr valid) o k children payloads
    (reached.imp id (generated_forward rel.raw.symm))
    (stableBack o stable) (fun child inTree => stableBack child (childrenStable child inTree))
    ((local_iff rel slices r o _).mpr selected)
    (allChildren_forward (reverse rel) r m supplied)
  exact (evidence_iff rel (registry r) m o _).mp oldEvidence

theorem evidenceAt_iff (rel : IndexedView a b) (slices : Semantics a b)
    (r : Registry) (root : Occurrence roles)
    (stable : ∀ o, (boundary roles).Stable r a o ↔ (boundary roles).Stable r b o) :
    B4SkeletonV8.EvidenceAt (boundary roles) r a root ↔
      B4SkeletonV8.EvidenceAt (boundary roles) r b root :=
  ⟨evidenceAt_forward rel slices r root (fun o => (stable o).mpr),
    evidenceAt_forward (reverse rel) slices.symm r root (fun o => (stable o).mp)⟩

end Yulang.GeneralMixedIndexedEvidenceAt305

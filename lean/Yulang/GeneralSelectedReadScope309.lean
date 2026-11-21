import Yulang.GeneralSelectedReadEvidence309
import Yulang.GeneralOrderedDictionaryFootprint309

namespace Yulang.GeneralSelectedReadScope309
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralGeneratedDictionaryRun299 (Read)
open GeneralOrderedDictionaryFootprint309 (need AgreeOn validate_agrees)
open GeneralSelectedReadEvidence309 (SelectedRead)
open GeneralCommittedReadTrace309 (Trace)
open GeneralOrderedDictionaryCheck309 (validate)
open GeneralDictionaryReadback (Payload)
open B4TargetV8 (Reachable Classify)
variable {roles : Roles.RoleDecls} {r : Registry} {s : State roles} {root : Occurrence roles}

/-- Extra unread entries of a supplied table are not trusted. A certificate
from a trusted reference reader covers exactly this rooted check. -/
theorem checked_on_footprint (checked : (boundary roles).Checked r)
    (path : Reachable (boundary roles) r root s) (reference supplied : Read)
    (decode : Nat → Occurrence roles) (rows : SelectedRead r s reference decode)
    (witness : ∃ m, Models s m) (fuel i : Nat) (p : Payload)
    (needed : AgreeOn (need reference fuel i) reference supplied)
    (started : GeneralNominalSaturationState.Generated s.core.erased.current root (decode i))
    (found : validate supplied fuel i p = .ok ()) :
    Classify (boundary roles) r s (decode i) (.selected p) ∧
    ∀ m, Models s m → Trace r s root m reference decode i p ∧
      (boundary roles).Evidence r s m (decode i) p := by
  have transferred : validate reference fuel i p = .ok () :=
    (validate_agrees reference supplied fuel i needed p).trans found
  exact GeneralSelectedReadEvidence309.selected_checker checked path reference decode rows witness fuel i p started transferred

end Yulang.GeneralSelectedReadScope309

import Yulang.GeneralRebaseSignedHistory297
import Yulang.GeneralRebaseDepthPathKeep285

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseSignedRefresh297
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedRefresh232 (refresh refresh_requests)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalRefinements (Refines)
open GeneralNominalVersionedEffects231 (ClassEffects)
open GeneralRebaseRetarget275 (Observed retarget)
open GeneralRebaseSignedModels297 (Sign Conditions Test)

variable {s : State roles} {p : Plan roles} {ctx : GeneralNominalCandidates.Context}

def refinement (cert : Refresh s ctx) (current : p.packet.context = s.core.erased.current.context) :
    Refines p.packet.context.state ctx.state :=
  current.symm ▸ cert.refines

abbrev moved (cert : Refresh s ctx) (current : p.packet.context = s.core.erased.current.context) :=
  retarget p (refinement cert current)

theorem interp (cert : Refresh s ctx) (current : p.packet.context = s.core.erased.current.context) :
    ctx.interpretation = p.packet.context.interpretation :=
  cert.interpretation.trans (congrArg GeneralNominalCandidates.Context.interpretation current).symm

theorem class_exact (cert : Refresh s ctx) (current : p.packet.context = s.core.erased.current.context)
    (seen : Observed p) (m : Assignment) :
    ClassEffects (refresh s ctx).core p.packet.site.occurrence (moved cert current) m ↔
    ClassEffects s.core p.packet.site.occurrence p m := by
  let q := moved cert current
  have keep := GeneralNominalVersionedFrameTransport232.class_effects_iff
    (before := (refresh s ctx).core) (after := s.core) (fun _ => refresh_requests s ctx)
    (root := p.packet.site.occurrence) (plan := q) (model := m)
  refine keep.trans ⟨?_,GeneralRebaseRetargetEffects275.class_effects p (refinement cert current)
    (interp cert current) s.core seen m⟩
  intro valid
  refine ⟨?_,valid.2⟩
  intro o listed body lookup
  exact (GeneralRebaseRetargetEffects275.body_holds p (refinement cert current) (interp cert current)
    seen o.target m body).mp (valid.1 o listed body lookup)

theorem candidate_exact (cert : Refresh s ctx) (current : p.packet.context = s.core.erased.current.context)
    (seen : Observed p) (m : Assignment) (prior : Models s m) :
    Conditions (refresh s ctx) (moved cert current) m ↔ Conditions s p m := by
  have oldBase : GeneralNominalState.Models p.packet.context.state m :=
    current.symm ▸ prior.1.1
  have afterBase : GeneralNominalState.Models ctx.state m := ((refresh_models cert).mpr prior).1.1
  apply and_congr _ (class_exact cert current seen m)
  rw [GeneralRebaseNonleafRetarget276.holds_iff p (refinement cert current) (interp cert current) seen m]
  exact ⟨fun h => ⟨oldBase,h.2⟩,fun h => ⟨afterBase,h.2⟩⟩

theorem preserves_test (cert : Refresh s ctx) (current : p.packet.context = s.core.erased.current.context)
    (seen : Observed p) (sign : Sign) (m : Assignment) :
    Test (refresh s ctx) (moved cert current) sign m ↔ Test s p sign m := by
  have models : Models (refresh s ctx) m ↔ Models s m := refresh_models cert
  cases sign with
  | pass =>
    exact ⟨fun h => ⟨models.mp h.1,(candidate_exact cert current seen m (models.mp h.1)).mp h.2⟩,
      fun h => ⟨models.mpr h.1,(candidate_exact cert current seen m h.1).mpr h.2⟩⟩
  | reject =>
    exact ⟨fun h => ⟨models.mp h.1,fun yes => h.2 ((candidate_exact cert current seen m (models.mp h.1)).mpr yes)⟩,
      fun h => ⟨models.mpr h.1,fun yes => h.2 ((candidate_exact cert current seen m h.1).mp yes)⟩⟩

theorem preserves_covers (cert : Refresh s ctx) (current : p.packet.context = s.core.erased.current.context)
    (seen : Observed p) (xs : List Assignment) (sign : Sign)
    (cover : (∃ m, Test s p sign m) → ∃ m ∈ xs, Test s p sign m) :
    (∃ m, Test (refresh s ctx) (moved cert current) sign m) →
      ∃ m ∈ xs, Test (refresh s ctx) (moved cert current) sign m := by
  rintro ⟨m,found⟩
  obtain ⟨n,nm,test⟩ := cover ⟨m,(preserves_test cert current seen sign m).mp found⟩
  exact ⟨n,nm,(preserves_test cert current seen sign n).mpr test⟩

end Yulang.GeneralRebaseSignedRefresh297

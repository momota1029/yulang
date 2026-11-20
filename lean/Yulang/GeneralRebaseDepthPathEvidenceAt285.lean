import Yulang.GeneralRebaseDepthPathEvidence285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 12500000
namespace Yulang.GeneralRebaseDepthPathEvidenceAt285
open GeneralDictionaryOutputDepth252 (registry sourceRegistry root roles)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedCandidates231 (Survivor Unique)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralRebaseDepthPathEvidence285 (Witness witness_any query)
open GeneralRebaseDepthPathAnchor285 (Anchor snapshot)

theorem move_location (before after : GeneralNominalCandidates.Context)
    (same : before = after) (bounds : List (GeneralNominalInspection.Bounds before.state))
    (located : GeneralNominalRecursiveCandidates.arguments before (GeneralNominalVersionedCandidates231.inputs root) = some bounds) :
    GeneralNominalRecursiveCandidates.arguments after (GeneralNominalVersionedCandidates231.inputs root) =
      some (same ▸ bounds) := by
  cases same
  exact located

theorem kept_survivor {s : State roles} (a : Anchor s) (w : Witness s) :
    Survivor registry s.core.erased.current.context root 0 [] := by
  obtain ⟨p,frame,_,_,_,_⟩ := w
  have rootKnown : ¬ GeneralNominalState.RootPending (snapshot s) root.demand := by
    rintro ⟨_,missing⟩
    obtain ⟨slot,identity,desc,recorded⟩ := a.nominal_two
    exact missing ⟨slot,identity,Or.inr ⟨desc,recorded⟩⟩
  let bounds : List (GeneralNominalInspection.Bounds s.core.erased.current.context.state) :=
    frame.context_eq ▸ p.packet.bounds
  have location : GeneralNominalRecursiveCandidates.arguments s.core.erased.current.context
      (GeneralNominalVersionedCandidates231.inputs root) = some bounds :=
    move_location _ _ frame.context_eq p.packet.bounds frame.located
  refine ⟨rootKnown,p.packet.declaration,frame.visible,frame.registry_eq ▸ p.packet.checked,
    frame.key_eq,frame.role_eq,bounds,location,frame.prepared,?_⟩
  symm
  unfold GeneralNominalVersionedCandidates231.children GeneralNominalVersionedFrame231.children
    GeneralDictionaryEmissionPlans.children
  have noReq : p.packet.declaration.requirements = [] := by
    have eq := List.mem_singleton.mp frame.visible
    rw [eq]
    rfl
  rw [GeneralRebaseRetarget275.no_emission _ _ _ _ _ noReq]
  rfl

theorem selected_unique {s : State roles} {key : Nat} {children}
    (selection : Local sourceRegistry s root (.selected key children)) :
    Unique registry s.core.erased.current.context root key children := by
  have raw := GeneralNominalVersionedMixedBoundary234.local_iff.mp
    (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selection)
  cases raw with
  | ordinary _ middle =>
    cases middle with
    | ordinary _ shallow =>
      cases shallow with
      | selected _ unique _ => exact unique

theorem evidence_at {s : State roles} {n : Nat} (path : ActualPath installed s n) :
    B4SkeletonV8.EvidenceAt (boundary roles) sourceRegistry s root := by
  intro m valid focus key children dictionaries scope _ _ selection supply
  have cert := witness_any path
  have same : focus = root := scope.elim id
    (GeneralNominalVersionedMixedTerminalStable234.generated_only cert.1.sites cert.1.edges)
  subst focus
  have uniq := selected_unique selection
  obtain ⟨sameKey,sameChildren⟩ := uniq.2 0 [] (kept_survivor cert.1 cert.2.2)
  subst key
  subst children
  cases supply
  have origin := (cert.1.models m).mp valid
  have leaf := (GeneralRebaseDepthPayload285.evidence_exact m origin (.node 0 [])).mpr rfl
  exact ((query path m (.node 0 [])).mpr ⟨origin,leaf⟩).2

end Yulang.GeneralRebaseDepthPathEvidenceAt285

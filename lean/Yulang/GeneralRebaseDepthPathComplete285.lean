import Yulang.GeneralRebaseDepthPathSelection285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 12500000
namespace Yulang.GeneralRebaseDepthPathComplete285
open GeneralDictionaryOutputDepth252 (sourceRegistry registry root roles)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Step Stable)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralRebaseDepthPathRank285 (ActualPath accessible all_after_install)
open GeneralRebaseDepthPathEvidence285 (witness_any)
open GeneralRebaseDepthPathSelection285 (selected)
open GeneralRebaseDepthPathEvidenceAt285 (evidence_at)

theorem concat {s t u : State roles} {m n : Nat} (x : ActualPath s t m) (y : ActualPath t u n) :
    ActualPath s u (m+n) := by
  induction y with
  | empty => exact x
  | more _ step ih => exact .more ih step

theorem terminates (s : State roles) (proof : Acc (fun next prev => Step registry root prev next) s) :
    ∃ last count, ActualPath s last count ∧ ∀ next, ¬ Step registry root last next := by
  classical
  induction proof with
  | intro start _ ih =>
    by_cases hasMore : ∃ next, Step registry root start next
    · obtain ⟨next,reaches⟩ := hasMore
      obtain ⟨last,count,path,stops⟩ := ih next reaches
      exact ⟨last,1+count,concat (.more (.empty _) reaches) path,stops⟩
    · exact ⟨start,0,.empty _,fun next action => hasMore ⟨next,action⟩⟩

theorem actual_total {s : State roles} {n : Nat} (path : ActualPath installed s n) :
    ∃ last later, ActualPath s last later ∧ n + later ≤ 2 ∧
      Stable registry last root ∧ Local sourceRegistry last root (.selected 0 []) ∧
      B4SkeletonV8.EvidenceAt (boundary roles) sourceRegistry last root := by
  have cert := witness_any path
  obtain ⟨finish,k,steps,halted⟩ := terminates s (accessible cert.1 cert.2.1)
  have full := concat path steps
  exact ⟨finish,k,steps,(all_after_install full).1,
    (GeneralNominalVersionedMixedKernel234.closure halted).1,selected full,evidence_at full⟩

end Yulang.GeneralRebaseDepthPathComplete285

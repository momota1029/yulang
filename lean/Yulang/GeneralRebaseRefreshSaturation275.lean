import Yulang.GeneralRebaseRefreshPublic275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 9400000
namespace Yulang.GeneralRebaseRefreshSaturation275
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryOptionalInitial229 (registry sourceRegistry declaration)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedKernel234 (Step Stable)
open GeneralRebaseRefreshAcc275 (ActualPath accessible actual_path actual_bound)
open GeneralRebaseRefreshRank275 (rank)
open GeneralRebaseRefreshPublic275 (After)
open GeneralRebaseRefreshEvidence275 (all_histories kept)
open GeneralRebaseCompoundRowsMeaning273 (Public)
open GeneralNominalCommonBridge (Assignment)

theorem path_append {s t u : State roles} {n k : Nat}
 (one : ActualPath s t n) (two : ActualPath t u k) : ActualPath s u (n+k) := by
 induction two with
 | empty => simpa only [Nat.add_zero] using one
 | more _ hop ih =>
   exact .more ih hop

theorem path_unbounded {s t : State roles} {n : Nat} (hops : ActualPath s t n) :
 B4Target.Steps (Step registry root) s t := by
 induction hops with
 | empty => exact .refl
 | more _ hop ih => exact .tail ih hop

theorem stable_completion {s : State roles} (well : Acc (fun after before => Step registry root before after) s) :
 ∃ t n, ActualPath s t n ∧ Stable registry t root := by
 classical
 induction well with
 | intro s _ ih =>
   by_cases outgoing : ∃ next, Step registry root s next
   · obtain ⟨next,hop⟩ := outgoing
     obtain ⟨target,count,tail,closed⟩ := ih next hop
     exact ⟨target,1+count,path_append (.more (.empty _) hop) tail,closed⟩
   · exact ⟨s,0,.empty _,fun focus generated next action => outgoing ⟨next,focus,generated,action⟩⟩

theorem remaining_budget {s : State roles} {n : Nat} (previous : ActualPath installed s n) :
 ∃ t k, ActualPath s t k ∧ n + k ≤ 3 ∧ Stable registry t root ∧
   GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry t root (.selected declaration.id []) ∧
   B4SkeletonV8.EvidenceAt (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry t root := by
 have prior := all_histories (path_unbounded previous)
 obtain ⟨t,k,tail,closed⟩ := stable_completion (accessible ⟨prior.1,kept prior.2⟩)
 have combined := path_append previous tail
 have result := GeneralRebaseRefreshSelected275.all_post_install (path_unbounded combined)
 exact ⟨t,k,tail,actual_bound combined,closed,result.1,result.2⟩

theorem no_steps_when_rank_zero {s : State roles} (path : After s) (finished : rank s = 0) :
 Stable registry s root := by
 intro focus generated next operation
 have p := all_histories path
 have hop := (GeneralRebaseRefreshAcc275.exact_hop ⟨p.1,kept p.2⟩).mp ⟨focus,generated,operation⟩
 have drop := GeneralRebaseRefreshRank275.rank_drop p.1.anchor hop
 omega

theorem all_diagnostics_equal {a b : State roles} (one : After a) (two : After b) (f) :
 GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry a root f ↔
 GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry b root f := by
 have first := (GeneralRebaseRefreshSelected275.all_post_install one).1
 have last := (GeneralRebaseRefreshSelected275.all_post_install two).1
 constructor
 · intro chosen
   exact (B4TargetV8.local_functional first chosen) ▸ last
 · intro chosen
   exact (B4TargetV8.local_functional last chosen) ▸ first

end Yulang.GeneralRebaseRefreshSaturation275

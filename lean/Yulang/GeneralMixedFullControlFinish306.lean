import Yulang.GeneralMixedFullControlScheduler306

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedFullControlFinish306
open GeneralDictionaryOutputDepth252 (roles initial root registry sourceRegistry)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedKernel234 (Step Stable)
open GeneralRebaseDepthPhase286 (Post)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralMixedFullControlCode306 (Code Event Action action_step code marker)
open GeneralMixedFullControlTrace306 (RawRoute concat check decode)
open GeneralMixedFullControlScheduler306 (terminal fast slow leastCost schedules)
open GeneralMixedFullControlMinimal306 (obligations)
open GeneralMixedControlMask306 (bit Mask project)
open GeneralNominalVersionedMixedSourceBoundary234 (Local boundary)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralRebaseDepthGroundModels285 (FinalTypeCheck)
open GeneralRebaseDepthSchedule286 (Halted Both)

variable {s t : State roles} {n : Nat}

theorem terminal_exact (path : ActualPath initial s n) : code s = terminal ↔ Halted s := by
  rw [GeneralRebaseDepthSchedule286.exact_terminal path]
  constructor
  · intro tag
    have done : (code s).installed = true := congrArg Code.installed tag
    have mask : project s = GeneralMixedControlLiveness306.full := congrArg Code.scalars tag
    exact ⟨(marker path).1.mp done,
      (bit s 0).mp (by rw [mask]; rfl),(bit s 1).mp (by rw [mask]; rfl)⟩
  · rintro ⟨done,zero,one⟩
    exact Code.ext ((marker path).1.mpr done) (Mask.ext ((bit s 0).mpr zero) ((bit s 1).mpr one))

theorem verified_endpoint (path : ActualPath initial s n) (sealed : code s = terminal) :
    Halted s ∧ Stable registry s root ∧ Local sourceRegistry s root (.selected 0 []) ∧
      B4SkeletonV8.EvidenceAt (boundary roles) sourceRegistry s root ∧
      (∀ m p, Models s m ∧ Evidence registry s.core m root p ↔ FinalTypeCheck m ∧ p = .node 0 []) := by
  have halt := (terminal_exact path).mp sealed
  have post := (GeneralRebaseDepthSchedule286.exact_terminal path).mp halt |>.1
  exact ⟨halt,(GeneralNominalVersionedMixedKernel234.closure halt).1,
    GeneralRebaseDepthPostQueries286.selected post,GeneralRebaseDepthPostQueries286.evidence_at post,
    GeneralRebaseDepthPostQueries286.concrete post⟩

theorem compiled_route (path : ActualPath initial s n) (trace : List (Event × Code))
    (checked : check (code s) terminal trace = true) :
    ∃ dest, RawRoute s trace dest ∧ Halted dest ∧ Stable registry dest root ∧
      Local sourceRegistry dest root (.selected 0 []) ∧
      (∀ m p, Models dest m ∧ Evidence registry dest.core m root p ↔ FinalTypeCheck m ∧ p = .node 0 []) := by
  obtain ⟨dest,given,sealed⟩ := decode path checked
  obtain ⟨stopped,stable,selected,_,evidence⟩ := verified_endpoint (concat path given) sealed
  exact ⟨dest,given,stopped,stable,selected,evidence⟩

theorem fast_compiled (path : ActualPath initial s n) :
    ∃ dest, RawRoute s (fast (code s)) dest ∧ Halted dest ∧ Local sourceRegistry dest root (.selected 0 []) := by
  obtain ⟨dest,path,stop,_,sel,_⟩ := compiled_route path _ (schedules (code s)).1.1
  exact ⟨dest,path,stop,sel⟩

theorem slow_compiled (path : ActualPath initial s n) :
    ∃ dest, RawRoute s (slow (code s)) dest ∧ Halted dest ∧ Local sourceRegistry dest root (.selected 0 []) := by
  obtain ⟨dest,path,stop,_,sel,_⟩ := compiled_route path _ (schedules (code s)).2.1
  exact ⟨dest,path,stop,sel⟩

end Yulang.GeneralMixedFullControlFinish306

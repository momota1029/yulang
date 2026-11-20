import Yulang.GeneralRebaseDepthBatch286

/-! Count only actual steps: installation, a scalar refresh which changes one
raw Known flag, or a scalar refresh which changes both. The bulk case is not
an extra kernel rule; it is observed from the old and new certified snapshots. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseDepthTraceCost286
open GeneralDictionaryOutputDepth252 (roles root registry initial)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseDepthPhase286 (Covered Hop InstallHop Pre Post)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralRebaseDepthSchedule286 (Halted)
open GeneralRebaseDepthFullRank286 (weight)
open GeneralRebaseDepthPathRank285 renaming rank → scalarRank

inductive Counts : State roles → State roles → Nat → Nat → Nat → Prop
  | empty (s) : Counts s s 0 0 0
  | install {s t u i j k} :
      Counts s t i j k → InstallHop t u → weight t = 1 → weight u = 0 →
      scalarRank t = scalarRank u → Counts s u (i+1) j k
  | single {s t u i j k} :
      Counts s t i j k → Hop t u → weight t = weight u →
      scalarRank t = scalarRank u + 1 → Counts s u i (j+1) k
  | batch {s t u i j k} :
      Counts s t i j k → Hop t u → weight t = weight u →
      scalarRank t = scalarRank u + 2 → Counts s u i j (k+1)

theorem laws {s t : State roles} {i j k : Nat} (c : Counts s t i j k) :
    weight s = weight t + i ∧ scalarRank s = scalarRank t + j + 2*k := by
  induction c with
  | empty => simp
  | install _ _ _ _ _ ih => omega
  | single _ _ _ _ ih => omega
  | batch _ _ _ _ ih => omega

theorem quiet_cost {s t : State roles} (b : Covered s) (h : Hop s t) :
    weight s = weight t ∧ (scalarRank s = scalarRank t + 1 ∨ scalarRank s = scalarRank t + 2) := by
  have same : weight s = weight t := by
    rcases b with pre|post
    · rw [GeneralRebaseDepthFullRank286.weight_pre pre,
        GeneralRebaseDepthFullRank286.weight_pre (GeneralRebaseDepthPhase286.pre_refresh pre h)]
    · rw [GeneralRebaseDepthFullRank286.weight_post post,
        GeneralRebaseDepthFullRank286.weight_post (GeneralRebaseDepthPhase286.post_refresh post h)]
  have less : scalarRank t < scalarRank s := by
    rcases b with pre|post
    · exact GeneralRebaseDepthFullRank286.pre_drop pre h
    · exact GeneralRebaseDepthPathRank285.drop post.anchor h
  have upper := GeneralRebaseDepthPathRank285.le_two s
  exact ⟨same,by omega⟩

theorem extend_quiet {s t u : State roles} {i j k : Nat}
    (counts : Counts s t i j k) (b : Covered t) (h : Hop t u) :
    ∃ j' k', Counts s u i j' k' ∧ j' + k' = j + k + 1 := by
  obtain ⟨same,one|both⟩ := quiet_cost b h
  · exact ⟨j+1,k,.single counts h same one,by omega⟩
  · exact ⟨j,k+1,.batch counts h same both,by omega⟩

theorem classify_counts {s : State roles} {n : Nat} (path : ActualPath initial s n) :
    ∃ installs singles batches, Counts initial s installs singles batches ∧ n = installs+singles+batches := by
  induction path with
  | empty => exact ⟨0,0,0,.empty _,rfl⟩
  | more prior move ih =>
    obtain ⟨is,ss,bs,known,number⟩ := ih
    have b := GeneralRebaseDepthPhase286.path_covered (.inl GeneralRebaseDepthPhase286.start) prior
    rcases b with pre|post
    · rcases GeneralRebaseDepthPhase286.pre_partition pre move with h|hit
      · obtain ⟨ss',bs',trace,eq⟩ := extend_quiet known (.inl pre) h
        exact ⟨is,ss',bs',trace,by omega⟩
      · exact ⟨is+1,ss,bs,.install known hit (GeneralRebaseDepthFullRank286.weight_pre pre)
          (GeneralRebaseDepthFullRank286.weight_post (GeneralRebaseDepthPhase286.cross pre hit))
          (GeneralRebaseDepthFullRank286.scalar_same_at_install pre hit).symm,by omega⟩
    · obtain ⟨ss',bs',trace,eq⟩ := extend_quiet known (.inr post)
        (GeneralRebaseDepthPhase286.post_step post move)
      exact ⟨is,ss',bs',trace,by omega⟩

theorem initial_scalar_rank : scalarRank initial = 2 := by
  classical
  have zer : ¬ GeneralNominalState.Known (GeneralRebaseDepthPathAnchor285.snapshot initial) 0 :=
    GeneralRebaseDepthPreSharp286.previously_unknown 0 (by decide)
  have one : ¬ GeneralNominalState.Known (GeneralRebaseDepthPathAnchor285.snapshot initial) 1 :=
    GeneralRebaseDepthPreSharp286.previously_unknown 1 (by decide)
  simp only [scalarRank,GeneralRebaseDepthPathRank285.pending,zer,one,ite_false,Nat.reduceAdd]

theorem maximal_trace_exact {s : State roles} {n : Nat}
    (path : ActualPath initial s n) (stop : Halted s) :
    (n = 2 ∧ Counts initial s 1 0 1) ∨ (n = 3 ∧ Counts initial s 1 2 0) := by
  obtain ⟨ins,single,batch,counts,total⟩ := classify_counts path
  have terminal := (GeneralRebaseDepthSchedule286.exact_terminal path).mp stop
  have book := laws counts
  rw [initial_scalar_rank,GeneralRebaseDepthSchedule286.scalar_rank_zero terminal.2,
    GeneralRebaseDepthFullRank286.weight_pre GeneralRebaseDepthPhase286.start,
    GeneralRebaseDepthFullRank286.weight_post terminal.1] at book
  have oneInstall : ins = 1 := by omega
  subst ins
  have casesCount : (single = 0 ∧ batch = 1) ∨ (single = 2 ∧ batch = 0) := by omega
  rcases casesCount with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact Or.inl ⟨by omega,counts⟩
  · exact Or.inr ⟨by omega,counts⟩

end Yulang.GeneralRebaseDepthTraceCost286

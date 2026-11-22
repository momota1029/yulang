import Yulang.GeneralDeclarativeCurrentRoot343

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 7800000
namespace Yulang.GeneralDeclarativeCurrentWorld343
open GeneralDeclarativePlacement343 (view kept_model)
open GeneralDeclarativeFreshModel343 (kept names_survive)
open GeneralDeclarativeLogicalChild343 (child fallback targets)
open GeneralDeclarativeFrameShape343 (edges)
open GeneralDeclarativeVersionedRootShape342 (typePoint)
open GeneralDeclarativeFrameRank343 (level level2_here)
open GeneralDeclarativeFrameGuard343 (ranked)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeAggregate324 (ready aligned span aggregate_model)
open GeneralDeclarativeFreshTerms324 (first second protectedNames)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)
open GeneralDeclarativeOpaqueGroup328 (aggregate_grows)
open GeneralDeclarativeGrowth327 (Extends)
open GeneralDeclarativeFootprint321 (stateNames atomSources typeSources equationNames)
open GeneralDeclarativeNewNames321 (before_after)
open GeneralDeclarativeTaggedElection340 (Ranked)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeStableAssemble329 (merged)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralWhereOriginSingleSource318 (sourceRegistry)
open GeneralDictionaryJournalRefinement228Source (interpretation)
open GeneralLiveCompoundRegistry316 (leaf)
open GeneralWherePhysicalCommit319 (final)
open GeneralWhereVersionInstall317 (Models)
open GeneralNominalCommonBridge (Assignment)
open PresenceNormalForm (Atom)

noncomputable abbrev now := ready view kept typePoint []
noncomputable abbrev added := span view kept typePoint []
noncomputable def rank (n : Nat) : Nat := if n = added.lower ∨ n = added.upper then 0 else level n

theorem grows : Extends view now := aggregate_grows _ _ _ _

theorem regular {n : Nat} (old : n ∈ stateNames view) : rank n = level n := by
  have less : n < added.lower := by
    apply before_after
    unfold protectedNames
    apply List.mem_append_left _
    apply List.mem_append_left _
    apply List.mem_append_left _
    unfold stateNames GeneralDeclarativeAggregate324.aligned GeneralDeclarativeCaptureClosure320.withOrdinary
    show n ∈ ((view.normal.ordinary ++ GeneralDeclarativeMergeCenters324.align typePoint []).flatMap atomSources ++
      view.normal.intervals.flatMap (fun p => [p.1,p.2])) ++ view.equations.flatMap equationNames
    rw [List.flatMap_append]
    rcases List.mem_append.mp old with old | other
    · apply List.mem_append_left _
      rcases List.mem_append.mp old with aa | bb
      · exact List.mem_append_left _ (List.mem_append_left _ aa)
      · exact List.mem_append_right _ bb
    · exact List.mem_append_right _ other
  have after : added.upper = added.lower+1 := rfl
  have skip : n ≠ added.lower ∧ n ≠ added.upper := by omega
  simp [rank,skip.1,skip.2]

theorem new_lo : rank added.lower = 0 := by simp [rank]
theorem new_hi : rank added.upper = 0 := by simp [rank]

theorem root_low : rank 2 = 0 := by
  have member : 2 ∈ stateNames view := by
    unfold stateNames
    apply List.mem_append_right _
    apply List.mem_flatMap.mpr
    exact ⟨GeneralDeclarativeVersionedRootRead342.publicRow,
      by rw [GeneralDeclarativeFrameShape343.exact_rows]; exact List.mem_cons_self,
      List.mem_cons_of_mem _ List.mem_cons_self⟩
  rw [regular member,level2_here]

theorem member_atom {a : Atom Nat} (there : a ∈ view.normal.ordinary)
    {name : Nat} (used : name ∈ atomSources a) : name ∈ stateNames view :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨a,there,used⟩))

theorem member_interval {a b : Nat} (there : (a,b) ∈ view.normal.intervals) :
    a ∈ stateNames view ∧ b ∈ stateNames view :=
  ⟨List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨(a,b),there,List.mem_cons_self⟩)),
   List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨(a,b),there,List.mem_cons_of_mem _ List.mem_cons_self⟩))⟩

theorem member_row {row : GeneralDeclarativeHead320.Equation} (there : row ∈ view.equations)
    {name : Nat} (used : name ∈ equationNames row) : name ∈ stateNames view :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨row,there,used⟩)

theorem new_constraints : now.normal.ordinary = view.normal.ordinary ++ edges added := by
  simp only [GeneralDeclarativeAggregate324.ready,GeneralDeclarativeAggregate324.aggregates,
    GeneralDeclarativeAggregate324.aligned,GeneralDeclarativeCaptureClosure320.withOrdinary,
    GeneralDeclarativeFreshTerms324.updated,List.append_assoc]
  rfl

theorem added_bound {a b : Nat} (e : Atom.tyLe (.var a) (.var b) ∈ edges added) :
    rank a ≤ rank b := by
  simp only [edges,List.mem_cons,List.not_mem_nil,or_false] at e
  rcases e with one | one | one | one | one | one | one | one <;> cases one <;>
    simp only [root_low,new_lo,new_hi,Nat.le_refl]

theorem current_rank : Ranked now rank := by
  refine ⟨?_,?_,?_⟩
  · intro a b h
    induction h with
    | refl _ => exact Nat.le_refl _
    | trans _ _ x y => exact Nat.le_trans x y
    | constraint specified =>
      rw [new_constraints,List.mem_append] at specified
      rcases specified with old | new
      · have x := member_atom old (name := _) List.mem_cons_self
        have y := member_atom old (name := _) (List.mem_cons_of_mem _ List.mem_cons_self)
        rw [regular x,regular y]
        exact ranked.bounded (.constraint old)
      · exact added_bound new
    | interval specified =>
      have old : (_ , _) ∈ view.normal.intervals := specified
      rw [regular (member_interval old).1,regular (member_interval old).2]
      exact ranked.bounded (.interval old)
  · intro a b h
    have old : (⟨a,.variable b⟩ : GeneralDeclarativeHead320.Equation) ∈ view.equations := h
    rw [regular (member_row old List.mem_cons_self),
      regular (member_row old (List.mem_cons_of_mem _ List.mem_cons_self))]
    exact ranked.flat old
  · intro row it n uses notVar
    have old : row ∈ view.equations := it
    rw [regular (member_row old (List.mem_cons_of_mem _ uses)),
      regular (member_row old List.mem_cons_self)]
    exact ranked.compound row old n uses notVar

abbrev leafSpans : List (Nat × Capture) := [(0,typePoint)]

theorem child_compile :
    compileBody sourceRegistry interpretation (child kept) leaf view leafSpans kept fallback targets =
      some (now,[]) := by
  unfold compileBody
  rw [show merged view kept leafSpans fallback = ⟨now,fun n => if n = 0 then added else fallback n⟩ from rfl]
  simp [GeneralDeclarativeClauseBatch327.prepare,GeneralDeclarativeWhereOutputBatch327.whole,
    GeneralDeclarativeBatch320.collect,GeneralDeclarativeEmissionForest322.children,
    GeneralDeclarativeEntailment320.appendFacts,leaf,child]

theorem stays (m : Assignment) (fit : Models final m) :
    ∃ n, GeneralDeclarativeHead320.Models now n ∧ (∀ k ∈ kept, n k = m k) ∧ Models final n := by
  obtain ⟨u,rawOrd,old,raw⟩ := kept_model m fit
  have valid : ∀ a ∈ [typePoint], Bounds view a := GeneralDeclarativeInitialModels343.singleton_bounds
  have linked : GeneralDeclarativeMergeCenters324.Linked view typePoint [] := by
    intro basis _ entry used
    cases List.mem_singleton.mp used
    exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
  obtain ⟨n,ordinary,keep⟩ := (GeneralDeclarativeOpaqueGroup328.form_group valid linked kept).lifts u rawOrd
  have same : ∀ k ∈ kept, n k = m k := fun k h => (keep k (List.mem_append_right _ h)).trans (old k h)
  exact ⟨n,ordinary,same,(names_survive same).mp fit⟩

end Yulang.GeneralDeclarativeCurrentWorld343

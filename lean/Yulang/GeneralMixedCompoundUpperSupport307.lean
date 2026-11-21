import Yulang.GeneralMixedCompoundUpperChild307
import Yulang.GeneralNominalTopObservation

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralMixedCompoundUpperSupport307
open GeneralDictionaryJournalRefinement228Source (snapshot roles root top_three)
open GeneralDictionaryCompoundSource238 (registry declaration)
open GeneralDictionaryCompoundSites238 (childSite)
open GeneralDictionaryCompoundObstruction238 (oldPlan old_lower associated_value)
open GeneralDictionaryCompoundRefresh239 (refreshed)
open GeneralDictionaryCompoundBase239 (lo hi)
open GeneralDictionaryCompoundSnapshot239 (extendedSnapshot)
open GeneralMixedCompoundUpperBase307 (upper base source)
open GeneralMixedCompoundUpperSnapshot307 (snap context)
open GeneralMixedCompoundUpperRefresh307 (upperState models_iff)
open GeneralNominalVersionedMixedTerminalStable234 (HeadlessUnknown no_refresh)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)
open GeneralNominalState (Known sources)
open CommonNominalFullCarrier

abbrev lower := GeneralDictionaryCompoundVersionedModel238.names 0
abbrev identity := childSite.occurrence.identity

theorem reserved_exact : snap.reserved = [lower,upper,lower,upper,identity,lo,hi] := by
  change GeneralNominalVersionedAllocation231.reserved snapshot registry root.identity oldPlan.packet.bindings = _
  rw [GeneralDictionaryCompoundPacket238.bindings_exact]
  rfl

theorem ordinary_subset : snap.ordinary.flatMap GeneralNominalState.atomSources ⊆
    [0,1,2,3,4,lower,upper,identity,lo,hi] := by
  change (GeneralNominalVersionedInstallation231.atoms oldPlan.packet).flatMap GeneralNominalState.atomSources ⊆ _
  have exactBindings := GeneralDictionaryCompoundPacket238.bindings_exact
  have includes (p : GeneralNominalSaturationState.Packet roles)
      (hp : p.context = oldPlan.packet.context) (hreg : p.registry = registry)
      (hid : p.site.occurrence = root) (hd : p.declaration = declaration)
      (hb : p.bindings = [(0,4,2),(0,4,2)])
      (checks : (GeneralNominalRecursiveInspection.selfChecks p.context.state
        (GeneralNominalPacketSupport.report p)).flatMap GeneralNominalState.atomSources ⊆
          [0,1,2,3,4,lower,upper,identity,lo,hi]) :
      (GeneralNominalVersionedInstallation231.atoms p).flatMap GeneralNominalState.atomSources ⊆
          [0,1,2,3,4,lower,upper,identity,lo,hi] := by
    unfold GeneralNominalVersionedInstallation231.atoms
    intro n h
    simp only [List.flatMap_append,List.mem_append] at h
    rcases h with (cross|merge)|check
    · rw [hb] at cross
      exact (by decide +kernel : (GeneralNominalAllocation.cross [(0,4,2),(0,4,2)]).flatMap
        GeneralNominalState.atomSources ⊆ [0,1,2,3,4,lower,upper,identity,lo,hi]) cross
    · rw [hp,hreg,hid,hd,hb] at merge
      exact (by decide +kernel : (GeneralNominalVersionedAllocation231.merges snapshot registry root.identity
        declaration [(0,4,2),(0,4,2)]).flatMap GeneralNominalState.atomSources ⊆
          [0,1,2,3,4,lower,upper,identity,lo,hi]) merge
    · exact checks check
  exact includes oldPlan.packet rfl rfl rfl rfl exactBindings (by decide +kernel)

theorem base_subset :
    List.ofFn base.source ⊆ [0,1,2,3,4,lower,upper,identity,lo,hi] := by decide +kernel

theorem support_subset : sources snap ⊆ [0,1,2,3,4,lower,upper,identity,lo,hi] := by
  intro n h
  simp only [sources,List.mem_append] at h
  rcases h with ((types|rows)|reserved)|ordinary
  · exact base_subset types
  · exact base_subset rows
  · change n ∈ snap.reserved at reserved
    rw [reserved_exact] at reserved
    simp only [List.mem_cons,List.not_mem_nil,or_false] at reserved
    rcases reserved with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  · exact ordinary_subset ordinary

theorem known_0 : Known snap 0 := ⟨0,rfl,Or.inr ⟨_,rfl⟩⟩
theorem known_1 : Known snap 1 := ⟨1,rfl,Or.inr ⟨_,rfl⟩⟩
theorem known_2 : Known snap 2 := ⟨2,rfl,Or.inl (by decide +kernel)⟩
theorem known_lo : Known snap lo := ⟨5,rfl,Or.inl (by decide +kernel)⟩
theorem known_hi : Known snap hi := ⟨6,rfl,Or.inl (by decide +kernel)⟩

theorem unknown_cases (n : Nat) (inside : n ∈ sources snap) (unknown : ¬ Known snap n) :
    n = 3 ∨ n = 4 ∨ n = lower ∨ n = identity := by
  have member := support_subset inside
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact (unknown known_0).elim
  · exact (unknown known_1).elim
  · exact (unknown known_2).elim
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact (unknown GeneralMixedCompoundUpperSnapshot307.upper_known).elim
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact (unknown known_lo).elim
  · exact (unknown known_hi).elim

def putId (m : Assignment) (ty : Ty) : Assignment := fun n =>
  if n = identity then (ty,(m n).2) else m n

theorem outside : identity ∉ GeneralDictionaryCompoundPointModel238.pool := by decide +kernel

theorem putId_models {m : Assignment} (valid : Models upperState m) (replacement : Ty) :
    Models upperState (putId m replacement) := by
  apply (models_iff _).mpr
  apply (GeneralDictionaryCompoundRefresh239.models_iff _).mpr
  apply (GeneralDictionaryCompoundPoint238.models_iff _).mpr
  apply (GeneralNominalVersionedJournalFrame236.models_iff _ ?_).mp
    ((GeneralDictionaryCompoundPoint238.models_iff _).mp
      ((GeneralDictionaryCompoundRefresh239.models_iff _).mp ((models_iff _).mp valid)))
  intro n present
  have ne : n ≠ identity := fun h => outside (h ▸ GeneralDictionaryCompoundPointModel238.support present)
  rw [putId,ite_eq_right ne]

theorem witness : Models upperState GeneralDictionaryCompoundVersionedModel238.extended :=
  (models_iff _).mpr GeneralDictionaryCompoundRefreshStep239.inhabited

theorem child_history (m : Assignment) (valid : Models upperState m) :
    GeneralNominalVersionedPlans231.Holds oldPlan m :=
  valid.2.1 _ GeneralMixedCompoundUpperTrust307.retained

theorem lower_read (m : Assignment) (valid : Models upperState m) :
    Equivalent (m lower).1 GeneralDictionaryOptionalOutput229.value := by
  have held := child_history m valid
  have key : ((GeneralNominalVersionedFrame231.capture oldPlan.packet).inputs 0).1 = lower := by decide +kernel
  have read := old_lower m held
  rw [key] at read
  exact equivalent_trans read (associated_value m held)

theorem headless : HeadlessUnknown upperState := by
  let m := putId GeneralDictionaryCompoundVersionedModel238.extended .top
  have valid := putId_models witness .top
  refine ⟨m,valid,?_⟩
  intro n present missing test seen
  rcases unknown_cases n present missing with rfl|rfl|rfl|rfl
  · exact GeneralDictionaryGroundCopy218Refresh.top_no_head test
      ((GeneralNominalOriginCongruence238.test_iff (top_three m (child_history m valid).1) test).mp seen)
  · exact GeneralDictionaryOptionalOutput229.no_test test
      ((GeneralNominalOriginCongruence238.test_iff (associated_value m (child_history m valid)) test).mp seen)
  · exact GeneralDictionaryOptionalOutput229.no_test test
      ((GeneralNominalOriginCongruence238.test_iff (lower_read m valid) test).mp seen)
  · exact GeneralDictionaryGroundCopy218Refresh.top_no_head test (by simpa only [m,putId,ite_true] using seen)

theorem impossible_further_refresh (ctx : GeneralNominalCandidates.Context)
    (cert : GeneralNominalVersionedMixedObservations233.Refresh upperState ctx)
    (n : Nat) (present : n ∈ sources snap) (unknown : ¬ Known snap n) :
    ¬ Known ctx.state n :=
  no_refresh headless cert present unknown

end Yulang.GeneralMixedCompoundUpperSupport307

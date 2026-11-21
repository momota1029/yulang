import Yulang.GeneralDeclarativeStableCrossResolve329

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDeclarativeStableCrossCut329
open GeneralDeclarativeStableCrossCompile329 (final requested)
open GeneralDeclarativeStableCrossBridge329 (current bridge aggregate_value conserves)
open GeneralDeclarativeStableCrossResolve329 (table constraints aggregateAtoms support child_ready no_cycle)
open GeneralDeclarativeStableCrossSource329 (oldRows)
open GeneralDeclarativeRepeatedSource323 (registry)
open GeneralDeclarativeExampleSource320 (interp)
open GeneralDeclarativeHead320 (Equation State Models)
open GeneralDeclarativeOrigins321 (Supported restriction backed_iff)
open GeneralDeclarativeGrowth327 (aliases ordinary)
open GeneralDeclarativeLowerKnown321 (Alias Knows Ready Delayed)
open GeneralDeclarativeK2Graph321 (Path aliasView Descends)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativePriority321 (Candidates Recurs)
open GeneralDeclarativeStableSelect329 (Rule)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open CommonNominalFullCarrier (Equivalent)

def beforeSupport : Supported final (fun _ => False) :=
  ⟨support.derivesFrom,fun h => support.ordinary h⟩

def rank (n : Nat) : Nat := if n = 13 then 0 else 1

theorem bound_rank {a b : Nat} (p : GeneralDeclarativeBounds319.Bound final.normal a b) :
    rank a ≤ rank b := by
  induction p with
  | refl => exact Nat.le_refl _
  | trans _ _ x y => exact Nat.le_trans x y
  | interval there =>
    change _ ∈ [(0,1),(1,2),(10,11),(11,12)] at there
    simp only [List.mem_cons,List.not_mem_nil,or_false] at there
    rcases there with h|h|h|h <;> cases h <;> decide +kernel
  | constraint there =>
    change _ ∈ aggregateAtoms 13 14 ++ aggregateAtoms 15 16 at there
    simp only [aggregateAtoms,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at there
    rcases there with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> cases h <;> decide +kernel

theorem allowed_row {e : Equation} (seen : e ∈ (restriction beforeSupport).equations) :
    e ∈ oldRows := ((backed_iff _ _).mp seen).choose_spec.1.1

theorem before_alias_rank {a b : Nat} (p : Alias (restriction beforeSupport) a b) :
    rank a = rank b := by
  have oldMap {x y : Nat} (seen : (⟨x,.variable y⟩ : Equation) ∈ oldRows) : rank x = rank y := by
    simp only [oldRows,List.mem_cons,List.not_mem_nil,or_false] at seen
    rcases seen with h|h|h|h|h|h|h|h <;> cases h <;> rfl
  induction p with
  | bounds f b => exact Nat.le_antisymm (bound_rank f) (bound_rank b)
  | forward h => exact oldMap (allowed_row h)
  | backward h => exact (oldMap (allowed_row h)).symm
  | trans _ _ h k => exact h.trans k

theorem before_unknown (tag) : ¬Knows (restriction beforeSupport) 13 tag := by
  rintro ⟨row,found,alias,_⟩
  have t := before_alias_rank alias
  have genuine := allowed_row found
  simp only [oldRows,List.mem_cons,List.not_mem_nil,or_false] at genuine
  rcases genuine with h|h|h|h|h|h|h|h <;> cases h <;> cases t

theorem old_delayed : Delayed beforeSupport requested :=
  ⟨⟨13,3,14⟩,List.mem_cons_self,before_unknown⟩

theorem pure_before (n : Nat) : ¬AliasCycle final (observed final) n := by
  let more := ordinary final bridge
  have transport {a b : Nat} (start : Descends (aliasView final (observed final)) a b) :
      Descends (aliasView current (observed current)) a b := by
    obtain ⟨tag,⟨supportAt,link,seen⟩,child⟩ := start
    exact ⟨tag,⟨supportAt,aliases more link,seen⟩,child⟩
  have transportPath {a b : Nat} (walk : Path (aliasView final (observed final)) a b) :
      Path (aliasView current (observed current)) a b := by
    induction walk with
    | refl => exact .refl _
    | next one _ rest => exact .next (transport one) rest
  rintro ⟨step,arrive,next,rest,loops⟩
  exact no_cycle n ⟨step,arrive,transport next,transportPath rest,aliases more loops⟩

def tests : Candidates :=
  ⟨HeadMatches (restriction beforeSupport) registry.constructors interp,
    fun d decl => ¬HeadMatches (restriction beforeSupport) registry.constructors interp d decl⟩

theorem pre_diagnostic : Rule final registry interp beforeSupport tests requested .pending := by
  refine .unsupported old_delayed ?_
  rintro (⟨arg,_,loop⟩|⟨_,_,_,_,_,_,_,_,_,site,_,loop⟩)
  · exact pure_before arg.lower loop
  · exact pure_before site loop

/-- An independently conservative ordinary closure restores access to
the pre-existing supported scalar anchor. Before closure the raw
named-atom fragment cannot read the aggregate endpoint, even though
its value is known in every ordinary model. Not a new language rule. -/
theorem exact_cut : (∀ m, Models current m ↔ Models final m) ∧
    (∀ m, Models final m → Equivalent (m 13).1 (m 3).1) ∧
    Rule final registry interp beforeSupport tests requested .pending ∧
    Ready support requested :=
  ⟨conserves,fun m fit => (aggregate_value m fit).1,pre_diagnostic,child_ready⟩

end Yulang.GeneralDeclarativeStableCrossCut329

import Yulang.GeneralSourceMetadataReport291

/-! All materialized projection constraints and captures survive report
reindexing, not just whether the report is finished. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralSourceMetadataReportMeaning291
open GeneralNominalState (State)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Report ProjectionModels bindings selfChecks Finished)
open GeneralSourceMetadataRows291 (Source)
open GeneralSourceMetadataSnapshot291 (Fits retag)
open GeneralSourceMetadataReport291 (lower lowerCapture)

theorem lower_bindings (s : State) (src : Source) (fit : Fits s src)
    (q : Report (retag s src fit)) :
    bindings s (lower s src fit q) = bindings (retag s src fit) q := by
  simp only [bindings,lower,List.map_map]
  rfl

theorem lower_self_checks (s : State) (src : Source) (fit : Fits s src)
    (q : Report (retag s src fit)) :
    selfChecks s (lower s src fit q) = selfChecks (retag s src fit) q := rfl

theorem lower_finished (s : State) (src : Source) (fit : Fits s src)
    (q : Report (retag s src fit)) :
    Finished (lower s src fit q) ↔ Finished q := Iff.rfl

theorem lower_projection (s : State) (src : Source) (fit : Fits s src)
    (q : Report (retag s src fit)) (m : Assignment) :
    ProjectionModels s (lower s src fit q) m ↔ ProjectionModels (retag s src fit) q m := by
  constructor
  · intro old
    refine ⟨old.1,old.2.1,?_⟩
    constructor
    · intro a am b bm name ref atRef val seen
      exact old.2.2.1 (lowerCapture s src fit a) (List.mem_map.mpr ⟨a,am,rfl⟩)
        (lowerCapture s src fit b) (List.mem_map.mpr ⟨b,bm,rfl⟩) name ref atRef val seen
    · intro a am b bm name ra rb ha hb x y hx hy
      exact old.2.2.2 (lowerCapture s src fit a) (List.mem_map.mpr ⟨a,am,rfl⟩)
        (lowerCapture s src fit b) (List.mem_map.mpr ⟨b,bm,rfl⟩) name ra rb ha hb x y hx hy
  · intro mapped
    refine ⟨mapped.1,mapped.2.1,?_⟩
    constructor
    · intro a am b bm name ref atRef val seen
      change a ∈ q.captures.map (lowerCapture s src fit) at am
      change b ∈ q.captures.map (lowerCapture s src fit) at bm
      obtain ⟨u,ua,au⟩ := List.mem_map.mp am
      obtain ⟨v,ub,bv⟩ := List.mem_map.mp bm
      subst a; subst b
      exact mapped.2.2.1 u ua v ub name ref atRef val seen
    · intro a am b bm name ra rb ha hb x y hx hy
      change a ∈ q.captures.map (lowerCapture s src fit) at am
      change b ∈ q.captures.map (lowerCapture s src fit) at bm
      obtain ⟨u,ua,au⟩ := List.mem_map.mp am
      obtain ⟨v,ub,bv⟩ := List.mem_map.mp bm
      subst a; subst b
      exact mapped.2.2.2 u ua v ub name ra rb ha hb x y hx hy

end Yulang.GeneralSourceMetadataReportMeaning291

import Yulang.GeneralWhereOriginEnumerate318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 4500000
namespace Yulang.GeneralWhereOriginLayout318
open GeneralNominalState (State sources)
open GeneralNominalCenters (Plan)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralWhereOriginDelta318 (Delta Cell)
open GeneralWhereOriginEnumerate318 (enumerate)

def freshCells (before : State) (p : Plan rs) : List (Cell p) :=
  (enumerate p).filter (fun c => decide (c.row.target ∉ sources before))

/-- Internal layout checker. It is deliberately conservative: an endpoint
install using this checker permits no *other* new type slot. Existing
source slots can change position through a checked refinement. -/
def matchSlots (before after : State) (p : Plan rs) : Bool :=
  (freshCells before p).all (fun c => (sourceSlot after.base c.row.target).isSome) &&
  (List.ofFn after.base.source).all (fun n => (sourceSlot before.base n).isSome ||
    (freshCells before p).any (fun c => c.row.target == n))

theorem mem_fresh {p : Plan rs} (c : Cell p) :
    c ∈ freshCells before p ↔ c.row.target ∉ sources before := by
  simp [freshCells,GeneralWhereOriginEnumerate318.includes c]

theorem source_iff {s : State} {n : Nat} :
    (sourceSlot s.base n).isSome = true ↔ ∃ i, s.base.source i = n := by
  constructor
  · intro present
    cases found : sourceSlot s.base n with
    | none => simp [found] at present
    | some i => exact ⟨i,(sourceSlot_exact ..).mp found⟩
  · rintro ⟨i,proof⟩
    rw [(sourceSlot_exact ..).mpr proof]
    rfl

theorem check_spec {before after : State} (p : Plan rs) :
    matchSlots before after p = true ↔
      (∀ c ∈ freshCells before p, ∃ i, after.base.source i = c.row.target) ∧
      (∀ i : Fin after.base.slots, (∃ j, after.base.source i = before.base.source j) ∨
        ∃ c ∈ freshCells before p, after.base.source i = c.row.target) := by
  unfold matchSlots
  simp only [Bool.and_eq_true,List.all_eq_true,source_iff,Bool.or_eq_true,List.any_eq_true,beq_iff_eq]
  constructor
  · rintro ⟨placed,scan⟩
    refine ⟨placed,fun i => ?_⟩
    rcases scan _ (List.mem_ofFn.mpr ⟨i,rfl⟩) with ⟨old,eq⟩|⟨c,found,eq⟩
    · exact .inl ⟨old,eq.symm⟩
    · exact .inr ⟨c,found,eq.symm⟩
  · rintro ⟨placed,scan⟩
    refine ⟨placed,?_⟩
    intro n member
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
    rcases scan i with ⟨old,eq⟩|⟨c,found,eq⟩
    · exact .inl ⟨old,eq.symm⟩
    · exact .inr ⟨c,found,eq.symm⟩

def checkedDelta {p : Plan rs}
    (refinement : GeneralNominalRefinements.Refines before after)
    (current : p.packet.context.state = before)
    (ok : matchSlots before after p = true) : Delta before after p where
  refinement := refinement
  current := current
  cells := freshCells before p
  absent := fun c h => (mem_fresh c).mp h
  fresh_slot := (check_spec p).mp ok |>.1
  split_slot := fun i _ => (check_spec p).mp ok |>.2 i

end Yulang.GeneralWhereOriginLayout318

import Yulang.GeneralDeclarativeWitnessCycle350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeK2Graph321 (Descends Path)
open GeneralDeclarativeGraphRows321 (structural observed shapeOf)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativePriority321 (RootRecurs)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessCycle350 (Link Hop Wire checksLink checksHop close)

theorem bound_replay_from_actual_derivation450 {s : State} {a b : Nat}
    (h : Bound s.normal a b) :
    ∃ w : GeneralDeclarativeWitnessBound349.Path,
      ∃ p : GeneralDeclarativeWitnessBound349.Checked s,
        GeneralDeclarativeWitnessBound349.replay s w = some p ∧ p.lower = a ∧ p.upper = b := by
  induction h with
  | interval present =>
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp present
    exact ⟨.interval i,⟨_,_,.interval present⟩,by
      unfold GeneralDeclarativeWitnessBound349.replay
      split <;> rename_i actual <;> simp_all,rfl,rfl⟩
  | constraint present =>
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp present
    exact ⟨.constraint i,⟨_,_,.constraint present⟩,by
      unfold GeneralDeclarativeWitnessBound349.replay
      split <;> rename_i actual <;> simp_all,rfl,rfl⟩
  | refl a => exact ⟨.refl a,_,rfl,rfl,rfl⟩
  | trans _ _ ha hb =>
    obtain ⟨l,lp,hl,e1,e2⟩ := ha
    obtain ⟨r,rp,hr,e3,e4⟩ := hb
    have same := e2.trans e3.symm
    exact ⟨.compose l r,⟨lp.lower,rp.upper,.trans lp.fact (same.symm ▸ rp.fact)⟩,by simp [GeneralDeclarativeWitnessBound349.replay,hl,hr,Bind.bind,Option.bind,same],e1,e4⟩

theorem bound_wire_from_actual_derivation450 {s : State} {a b : Nat} (h : Bound s.normal a b) :
    ∃ w, GeneralDeclarativeWitnessBound349.check s a b w = true := by
  obtain ⟨w,_,read,lo,hi⟩ := bound_replay_from_actual_derivation450 h
  exact ⟨w,by simp [GeneralDeclarativeWitnessBound349.check,read,lo,hi]⟩

theorem alias_wire_from_actual_derivation450 {s : State} {a b : Nat} (h : Alias s a b) :
    ∃ w, checksLink s a b w = true := by
  induction h with
  | bounds there back =>
    obtain ⟨a,ha⟩ := bound_wire_from_actual_derivation450 there
    obtain ⟨b,hb⟩ := bound_wire_from_actual_derivation450 back
    exact ⟨.bounds ⟨a,b⟩,by simp [checksLink,GeneralDeclarativeWitnessBound349.tied,ha,hb]⟩
  | forward present =>
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp present
    exact ⟨.forward i,by simp [checksLink,hi]⟩
  | backward present =>
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp present
    exact ⟨.backward i,by simp [checksLink,hi]⟩
  | @trans a b c _ _ ha hb =>
    obtain ⟨l,hl⟩ := ha
    obtain ⟨r,hr⟩ := hb
    exact ⟨.compose b l r,by simp [checksLink,hl,hr]⟩

theorem structural_wire_from_actual_row450 {s : State} {a b : Nat}
    (h : Descends (structural s) a b) :
    ∃ w : Hop, w.child = b ∧ checksHop s a w = true := by
  obtain ⟨shape,⟨owner,same,expr,present,named⟩,inside⟩ := h
  obtain ⟨ix,indexed⟩ := List.mem_iff_getElem?.mp present
  obtain ⟨w,hw⟩ := alias_wire_from_actual_derivation450 same
  exact ⟨⟨ix,w,b⟩,rfl,by simp [checksHop,indexed,named,hw,inside]⟩

theorem path_wire_from_actual_derivation450 {s : State} {a b root : Nat}
    (h : Path (structural s) a b) (last : Alias s b root) :
    ∃ trail finish, close s a root finish trail = true := by
  induction h with
  | refl a =>
    obtain ⟨w,hw⟩ := alias_wire_from_actual_derivation450 last
    exact ⟨[],w,hw⟩
  | next edge rest ih =>
    obtain ⟨head,same,yes⟩ := structural_wire_from_actual_row450 edge
    obtain ⟨tail,endWire,endOK⟩  := ih last
    exact ⟨head::tail,endWire,by simp [close,yes,same,endOK]⟩

theorem raw_child_cycle_has_finite_original_wire450 (s : State) (d : Demand) :
    RootRecurs s d ↔ ∃ w : Wire, GeneralDeclarativeWitnessCycle350.check s d w = true := by
  constructor
  · rintro ⟨arg,atArgs,child,last,first,rest,returns⟩
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp atArgs
    obtain ⟨head,same,yes⟩ := structural_wire_from_actual_row450 first
    obtain ⟨tail,finish,finishOK⟩ := path_wire_from_actual_derivation450 rest returns
    exact ⟨⟨i,head,tail,finish⟩,by simp [GeneralDeclarativeWitnessCycle350.check,hi,yes,same,finishOK]⟩
  · rintro ⟨w,ok⟩
    exact GeneralDeclarativeWitnessCycle350.rooted ok
end Yulang.GeneralDeclarativeI65.I72.WhereSites450

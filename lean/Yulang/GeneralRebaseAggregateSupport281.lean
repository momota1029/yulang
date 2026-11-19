import Yulang.GeneralRebaseAggregateCompile281
import Yulang.GeneralRebaseOwnedSupport277

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
namespace Yulang.GeneralRebaseAggregateSupport281
open GeneralNominalSaturationState (Packet)
open GeneralNominalAllocation (occurrences)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceState (Interval)
open GeneralNominalIdentities (Origin source source_identity)
open GeneralNominalAggregateVersion231 (key slot)
open GeneralRebaseAggregateCompile281 (compile compileBinder collect repeated)
open GeneralRebasePortCopy280 (Write PairWrites Apart Isolated Unambiguous)
open GeneralNominalVersionedFrame231 (capture)
open GeneralNominalVersionedAllocation231 (Fresh input_keys)

def endKey (p : Packet roles) (name : Nat) (upper : Bool) : Origin :=
  key p.site.occurrence.identity p.declaration.id (if upper then 1 else 0) name p.bindings

def endpoint (bounds : Interval) (upper : Bool) : Nat := if upper then bounds.2 else bounds.1

theorem binder_write {p : Packet roles} {row : Write}
    (found : compileBinder p name = some ws) (write : row ∈ ws) :
    ∃ representative, ∃ high : Bool,
      (∃ tail, occurrences p.bindings name = representative :: tail) ∧
      row = (source p.context.state.seed (endKey p name high),endpoint representative high) := by
  cases observed : occurrences p.bindings name with
  | nil => simp [compileBinder,observed] at found
  | cons first rest =>
    cases rest with
    | nil =>
      have eq : [] = ws := Option.some.inj (by simpa only [compileBinder,observed] using found)
      subst ws; cases write
    | cons second tail =>
      by_cases same : repeated first (second :: tail) = true
      · have eq : PairWrites ((capture p).inputs name) first = ws :=
          Option.some.inj (by simpa only [compileBinder,observed,same,ite_true] using found)
        subst ws
        have named :
            (capture p).inputs name =
              (source p.context.state.seed (endKey p name false),
               source p.context.state.seed (endKey p name true)) := by
          change (GeneralNominalVersionedAllocation231.capture _ _ _ _ _).inputs name = _
          simp only [GeneralNominalVersionedAllocation231.capture,observed]
          rfl
        rw [named] at write
        simp only [PairWrites,List.mem_cons,List.not_mem_nil,or_false] at write
        rcases write with rfl|rfl
        · exact ⟨first,false,⟨_,rfl⟩,rfl⟩
        · exact ⟨first,true,⟨_,rfl⟩,rfl⟩
      · simp [compileBinder,observed,same] at found

theorem collect_member {p : Packet roles} {names : List Nat} {row : Write}
    (found : collect p names = some ws) (used : row ∈ ws) :
    ∃ name ∈ names, ∃ localWrites, compileBinder p name = some localWrites ∧ row ∈ localWrites := by
  induction names generalizing ws with
  | nil =>
    have eq : [] = ws := Option.some.inj found
    subst ws; cases used
  | cons first rest ih =>
    unfold collect at found
    cases head : compileBinder p first with
    | none => simp [head] at found
    | some one =>
      cases tail : collect p rest with
      | none => simp [head,tail] at found
      | some two =>
        rw [head,tail] at found
        have eq : one ++ two = ws := Option.some.inj found
        subst ws
        rcases List.mem_append.mp used with early|remaining
        · exact ⟨first,List.mem_cons_self,one,head,early⟩
        · obtain ⟨name,listed,later,run,belongs⟩ := ih tail remaining
          exact ⟨name,List.mem_cons_of_mem _ listed,later,run,belongs⟩

theorem footprint {p : Packet roles} {row : Write}
    (compiled : compile p = some ws) (listed : row ∈ ws) :
    ∃ name ∈ p.declaration.inputNames, ∃ sample, ∃ high : Bool,
      (∃ tail, occurrences p.bindings name = sample :: tail) ∧
      row = (source p.context.state.seed (endKey p name high),endpoint sample high) := by
  obtain ⟨name,used,localWrites,found,has⟩ := collect_member compiled listed
  obtain ⟨rep,upper,h,eq⟩ := binder_write found has
  exact ⟨name,used,rep,upper,h,eq⟩

theorem unique {p : Packet roles} (compiled : compile p = some ws) : Unambiguous ws := by
  intro a first b second same
  obtain ⟨i,_,rep,upper,⟨tail,ai⟩,rfl⟩ := footprint compiled first
  obtain ⟨j,_,other,low,⟨rest,bj⟩,rfl⟩ := footprint compiled second
  have keys := (source_identity p.context.state.seed _ _).mp same
  have nameEq : i = j := congrArg (fun k : Origin => k.2.2.2.1) keys
  have dir : (if upper then (1 : Nat) else 0) = (if low then 1 else 0) :=
    congrArg (fun k : Origin => k.2.2.1) keys
  have sideEq : upper = low := by cases upper <;> cases low <;> simp_all
  subst j
  subst low
  have sameHead := List.cons.inj (ai.symm.trans bj)
  rw [sameHead.1]

theorem source_read {p : Packet roles} {row : Write}
    (compiled : compile p = some ws) (listed : row ∈ ws) :
    row.2 ∈ GeneralNominalState.sources p.context.state := by
  obtain ⟨name,_,bounds,side,⟨tail,recorded⟩,rfl⟩ := footprint compiled listed
  have covered := GeneralNominalAllocationSupport.report_endpoints p.context.state
    (GeneralNominalPacketSupport.report p)
  have all := GeneralNominalAllocationSupport.occurrences_endpoints covered name
  have front : bounds ∈ occurrences p.bindings name := recorded.symm ▸ List.mem_cons_self
  cases side
  · exact (all bounds front).1
  · exact (all bounds front).2

theorem source_fresh {p : Packet roles}
    (compiled : compile p = some ws) (visible : p.declaration ∈ p.registry.declarations)
    (nominal : Fresh p.context.state p.registry p.site.occurrence.identity p.bindings)
    (new : ∀ name ∈ p.declaration.inputNames, ∀ side, endKey p name side ∉ p.context.state.allocated) :
    Apart ws (GeneralNominalState.sources p.context.state) := by
  intro row listed collision
  obtain ⟨name,used,_,side,_,rfl⟩ := footprint compiled listed
  have both := input_keys (root := p.site.occurrence.identity) (bindings := p.bindings) visible used
  have reserved : endKey p name side ∈
      GeneralNominalVersionedAllocation231.keys p.registry p.site.occurrence.identity p.bindings := by
    cases side
    · exact both.1
    · exact both.2
  exact new name used side (nominal _ reserved collision)

theorem isolated_of_source_apart {p : Packet roles}
    (compiled : compile p = some ws) (apart : Apart ws (GeneralNominalState.sources p.context.state)) :
    Isolated ws := by
  intro written member clash
  obtain ⟨other,used,same⟩ := List.mem_map.mp clash
  exact apart written member (same ▸ source_read compiled used)

end Yulang.GeneralRebaseAggregateSupport281

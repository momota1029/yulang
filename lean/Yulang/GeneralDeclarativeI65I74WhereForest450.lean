import Yulang.GeneralDeclarativeI65I74WhereSource450
import Yulang.GeneralDeclarativeI65I74WhereCycleWire450

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450
open Yulang.GeneralDeclarativeI65
open ListSites449.Frame (FramedSelection FrameWire readListFrameChoice selectedFrameEvent)
open Checker408 (Problem Result)
open CommonRoleOutermostResolver (Tree Dictionary Summarizes)
open GeneralDeclarativeWitnessCycle350 (Wire)

inductive ChildPlan (s : I72.State) : I72.Request → Tree → Type where
  | cycle {q} : RootCycle s q → ChildPlan s q .rejected
  | leaf {q} (a : FramedSelection ⟨s,q⟩) : ChildPlan s q (.selected a.decl.id [])

inductive OrderedPlan (s : I72.State) : List I72.Request → List Tree → Type where
  | nil : OrderedPlan s [] []
  | cons {q qs t ts} : ChildPlan s q t → OrderedPlan s qs ts → OrderedPlan s (q::qs) (t::ts)

inductive ChildWire where
  | raw (cycle : Wire)
  | leaf (proof : FrameWire)

def readChild (s : I72.State) (q : I72.Request) :
    ChildWire → Option (Σ t, ChildPlan s q t)
  | .raw w =>
    if cy : GeneralDeclarativeWitnessCycle350.check s.core.current.ordinary q.demand w = true
    then some ⟨.rejected,.cycle (GeneralDeclarativeWitnessCycle350.rooted cy)⟩ else none
  | .leaf w =>
    match whole : visible s.core q with
    | [d] => (readListFrameChoice ⟨s,q⟩ d whole w).map fun valid => ⟨.selected d.id [],.leaf ⟨d,valid⟩⟩
    | _ => none

theorem every_actual_child_has_ordered_wire450 {s q t} (p : ChildPlan s q t) :
    ∃ w, readChild s q w = some ⟨t,p⟩ := by
  cases p with
  | cycle h =>
    have root : GeneralDeclarativePriority321.RootRecurs s.core.current.ordinary q.demand := h
    obtain ⟨w,yes⟩ := (raw_child_cycle_has_finite_original_wire450 _ _).mp root
    exact ⟨.raw w,by simp [readChild,yes]⟩
  | leaf a =>
    obtain ⟨w,yes⟩ := ListSites449.Frame.independent_list_frame_replays_exactly449 a.chosen
    refine ⟨.leaf w,?_⟩
    simp only [readChild]
    split
    · rename_i d shape
      have same : d = a.decl := List.singleton_inj.mp (shape.symm.trans a.chosen.only)
      subst d
      rw [yes]
      rfl
    · rename_i missing
      exact (missing _ a.chosen.only).elim

def readOrdered (s : I72.State) : (qs : List I72.Request) → List ChildWire →
    Option (Σ ts, OrderedPlan s qs ts)
  | [],[] => some ⟨[],.nil⟩
  | q::qs,w::ws => do
    let ⟨t,first⟩ ← readChild s q w
    let ⟨ts,tail⟩ ← readOrdered s qs ws
    some ⟨t::ts,.cons first tail⟩
  | _,_ => none

theorem all_original_children_have_ordered_wires450 {s qs ts} (p : OrderedPlan s qs ts) :
    ∃ ws, readOrdered s qs ws = some ⟨ts,p⟩ := by
  induction p with
  | nil => exact ⟨[],rfl⟩
  | cons c _ ih =>
    obtain ⟨h,yes⟩ := every_actual_child_has_ordered_wire450 c
    obtain ⟨t,rest⟩ := ih
    exact ⟨h::t,by simp [readOrdered,yes,rest,Bind.bind,Option.bind]⟩

theorem read_order_cannot_truncate_or_invent450 {s qs ws ts} {p : OrderedPlan s qs ts}
    (ok : readOrdered s qs ws = some ⟨ts,p⟩) : ws.length = qs.length := by
  induction qs generalizing ws ts with
  | nil => cases ws <;> simp_all [readOrdered]
  | cons q tail ih =>
    cases ws with
    | nil => simp [readOrdered] at ok
    | cons w rest =>
      cases first : readChild s q w with
      | none => simp [readOrdered,first,Bind.bind,Option.bind] at ok
      | some pair =>
        cases restOK : readOrdered s tail rest with
        | none => simp [readOrdered,first,restOK,Bind.bind,Option.bind] at ok
        | some next =>
          rw [List.length_cons,List.length_cons]
          exact congrArg Nat.succ (ih restOK)

theorem ChildPlan.treeSound {s q t} (a : ChildPlan s q t) :
    ∃ e, Nonempty (SourceTrace parentWhereRule450 s q t e) := by
  cases a with
  | cycle cycle => exact ⟨none,⟨.rootK2 cycle⟩⟩
  | leaf a =>
    obtain ⟨origin⟩ := selected_head_original_origin395
      (ListSites449.Frame.actual_single_declaration_list_frame_is_settled449 a.chosen)
    let e := selectedFrameEvent a origin
    have noKids : e.kids = [] := by
      simp [e,selectedFrameEvent,Event.kids,frameWhereKids400,AuthoredBodyFrame393.clauses,
        preoutputFrameOfOrigin399,frameAtSource395,a.chosen.noWhere,children]
    let rule : parentWhereRule450.elected s q e [] := ⟨rfl,.inr ⟨rfl,a,origin,rfl⟩⟩
    exact ⟨some e,⟨.selected e a.chosen.safe rule .nil (noKids ▸ .nil)⟩⟩

theorem OrderedPlan.forestSound {s qs ts} (a : OrderedPlan s qs ts) :
    Nonempty (WhereForest parentWhereRule450 s qs ts) := by
  induction a with
  | nil => exact ⟨.nil⟩
  | cons first _ ih =>
    obtain ⟨_,⟨read⟩⟩ := first.treeSound
    obtain ⟨rest⟩ := ih
    exact ⟨.cons read rest⟩

def hasRawRejection : List Tree → Bool
  | [] => false
  | .rejected::_ => true
  | _::rest => hasRawRejection rest

theorem raw_rejection_is_same_position450 (trees : List Tree) :
    hasRawRejection trees = true ↔ Tree.rejected ∈ trees := by
  induction trees with
  | nil => simp [hasRawRejection]
  | cons first rest ih =>
    cases first <;> simp [hasRawRejection,ih]

theorem where_summary_keeps_every_child450 (d : Nat) {trees : List Tree}
    (contains : Tree.rejected ∈ trees) : Summarizes (.selected d trees) .rejected := by
  apply Summarizes.selected ((CommonRoleOutermostResolver.classifications_exact _ _).mp rfl)
  apply CommonRoleOutermostResolver.Combine.rejected
  induction trees with
  | nil => cases contains
  | cons first rest ih =>
    rcases List.mem_cons.mp contains with rfl|tail
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih tail)

end Yulang.GeneralDeclarativeI65.I72.WhereSites450

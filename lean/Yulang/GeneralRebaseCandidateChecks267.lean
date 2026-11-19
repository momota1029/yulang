import Yulang.GeneralRebaseEnumeratePlans267

namespace Yulang.GeneralRebaseCandidateChecks267
open GeneralNominalState (State sources Linked Known RootPending)
open GeneralSourceState (Demand)
open GeneralNominalIdentities (Origin source)
open GeneralNominalVersionedAllocation231 (Fresh keys)
open GeneralNominalRecursiveInspection (Report Finished)

def linked (state : State) (demand : Demand roles) : Bool :=
 (List.finRange (roles demand.role).arity).all (fun i =>
   decide ((demand.arguments i).1 ∈ sources state) && decide ((demand.arguments i).2 ∈ sources state)) &&
 demand.outputs.all (fun output => decide (output.target ∈ sources state))

theorem linked_exact (state : State) (demand : Demand roles) :
 linked state demand = true ↔ Linked state demand := by
 simp [linked,Linked,List.all_eq_true]

def known (state : State) (id : Nat) : Bool :=
 (List.finRange state.base.slots).any fun slot =>
   (state.base.source slot == id) &&
   ((match state.view.graph slot with | .unresolved => false | _ => true) ||
     (state.nominals slot).isSome)

theorem nonunresolved (state : State) (slot : Fin state.base.slots) :
 (match state.view.graph slot with | .unresolved => false | _ => true) = true ↔
 state.view.graph slot ≠ .unresolved := by
 cases h : state.view.graph slot <;> simp

theorem known_exact (state : State) (id : Nat) : known state id = true ↔ Known state id := by
 simp only [known,List.any_eq_true,List.mem_finRange,true_and,Bool.and_eq_true,beq_iff_eq,
   Bool.or_eq_true,nonunresolved,Option.isSome_iff_exists,Known]

def allKnown (state : State) (demand : Demand roles) : Bool :=
 (List.finRange (roles demand.role).arity).all fun i => known state (demand.arguments i).1

theorem allKnown_exact (state : State) (demand : Demand roles) :
 allKnown state demand = true ↔ ¬ RootPending state demand := by
 classical
 simp [allKnown,List.all_eq_true,known_exact,RootPending]

def fresh (state : State) (registry : GeneralDeclarations.Registry) (root : Nat)
 (bindings : GeneralNominalAllocation.Bindings) : Bool :=
 (keys registry root bindings).all fun key =>
   !decide (source state.seed key ∈ sources state) || decide (key ∈ state.allocated)

theorem fresh_exact (state : State) (registry : GeneralDeclarations.Registry) (root : Nat)
 (bindings : GeneralNominalAllocation.Bindings) :
 fresh state registry root bindings = true ↔ Fresh state registry root bindings := by
 simp only [fresh,Fresh,List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,decide_eq_true_eq]
 constructor
 · intro each key listed present
   exact (each key listed).resolve_left (fun notPresent => notPresent present)
 · intro each key listed
   by_cases present : source state.seed key ∈ sources state
   · exact Or.inr (each key listed present)
   · exact Or.inl present

def finished {state : State} (report : Report state) : Bool :=
 report.blocked.isEmpty && (report.conflicts.isEmpty && report.arity.isEmpty)

theorem finished_exact {state : State} (report : Report state) :
 finished report = true ↔ Finished report := by
 simp [finished,Finished]

end Yulang.GeneralRebaseCandidateChecks267

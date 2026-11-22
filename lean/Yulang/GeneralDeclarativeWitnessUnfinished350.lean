import Yulang.GeneralDeclarativeWitnessNoHead350
import Yulang.GeneralDeclarativeWitnessTree349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessUnfinished350
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessOrigins350 (Table Attached attach support)
open GeneralDeclarativeWitnessCycle350 (Link link rooted checksLink)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralDeclarativeLowerKnown321 (constructorTag)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeUnfinishedRoot330 (UnfinishedRoot)
open CommonRoleOutermostResolver (Frontier Classify)

structure Wire where
  cycle : GeneralDeclarativeWitnessCycle350.Wire
  pendingIndex : Nat
  ownerAlias : Link
  separator : List Nat

theorem atRoot {s : State} {d : Demand} {w : GeneralDeclarativeWitnessCycle350.Wire}
    {a : Capture} (arg : d.arguments[w.argument]? = some a)
    (ok : GeneralDeclarativeWitnessCycle350.check s d w = true) :
    AliasCycle s (observed s) a.lower := by
  unfold GeneralDeclarativeWitnessCycle350.check at ok
  rw [arg] at ok
  obtain ⟨step,tail⟩ := splitAnd ok
  obtain ⟨last,walk,l⟩ := GeneralDeclarativeWitnessCycle350.path tail
  exact ⟨w.first.child,last,GeneralDeclarativeWitnessCycle350.hop step,walk,l⟩

def applicable {s : State} {t : Table} (_a : Attached s t) (d : Demand) (w : Wire) : Bool :=
  match d.arguments[w.cycle.argument]?,t.produced[w.pendingIndex]? with
  | some arg,some (row,owner) =>
    ((GeneralDeclarativeWitnessCycle350.check s d w.cycle &&
      GeneralDeclarativeWitnessNoHead350.check s t arg.lower w.separator) &&
      (!t.released.contains owner && checksLink s arg.lower row.left w.ownerAlias)) &&
      (constructorTag row.right).isSome
  | _,_ => false

theorem sound {s : State} {t : Table} {a : Attached s t} {d : Demand} {w : Wire}
    (yes : applicable a d w = true) : UnfinishedRoot (support a) d := by
  unfold applicable at yes
  cases arg : d.arguments[w.cycle.argument]? with
  | none => simp [arg] at yes
  | some capture =>
    cases pending : t.produced[w.pendingIndex]? with
    | none => simp [arg,pending] at yes
    | some record =>
      obtain ⟨row,owner⟩ := record
      rw [arg,pending] at yes
      have ⟨h,isCtor⟩ := splitAnd yes
      have ⟨r,q⟩ := splitAnd h
      have ⟨cycle,missing⟩ := splitAnd r
      have ⟨withheld,linked⟩ := splitAnd q
      cases rendered : constructorTag row.right with
      | none => simp [rendered] at isCtor
      | some tag =>
        refine ⟨capture,List.mem_iff_getElem?.mpr ⟨w.cycle.argument,arg⟩,
          GeneralDeclarativeWitnessNoHead350.unseen missing,atRoot arg cycle,
          row,owner,tag,List.mem_iff_getElem?.mpr ⟨w.pendingIndex,pending⟩,?_,link linked,rendered⟩
        simpa using withheld

def check (s : State) (provenance : Table) (d : Demand) (w : Wire) : Bool :=
  ((attach s provenance).map fun a => applicable a d w).getD false

theorem checked {s : State} {provenance : Table} {d : Demand} {w : Wire}
    (ok : check s provenance d w = true) :
    ∃ a : Attached s provenance, UnfinishedRoot (support a) d := by
  unfold check at ok
  cases chosen : attach s provenance with
  | none => simp [chosen] at ok
  | some a => exact ⟨a,sound (by simpa [chosen] using ok)⟩

/-- Its only conclusion is the approved specific I-59 rejection
reason. Neither a failed certificate nor a missing source read is a
diagnostic. No legacy classification correspondence is needed. -/
def Rule {s : State} {t : Table} (a : Attached s t) (d : Demand) (f : Frontier Demand) : Prop :=
  f = .rejected ∧ UnfinishedRoot (support a) d

theorem rejected {s : State} {provenance : Table} {d : Demand} {w : Wire}
    (ok : check s provenance d w = true) :
    ∃ a : Attached s provenance, Classify (Rule a) d .rejected := by
  obtain ⟨a,why⟩ := checked ok
  exact ⟨a,.rejected,.rejected ⟨rfl,why⟩,.rejected⟩

open GeneralDeclarativeWitnessProblem349 (Problem)
open GeneralDeclarativeWitnessTree349 (Report agrees exact_report)

def checkResult (p : Problem) (provenance : Table) (w : Wire) (report : Report) : Bool :=
  check p.state provenance p.demand w && agrees p .rejected report

theorem agrees_rejected {p : Problem} {provenance : Table} {w : Wire} {report : Report}
    (ok : checkResult p provenance w report = true) :
    report.tree = .rejected ∧ report.result = .rejected ∧ report.outputs = p.demand.outputs ∧
      ∃ a : Attached p.state provenance, Classify (Rule a) p.demand report.result := by
  obtain ⟨proof,matching⟩ := splitAnd ok
  have result := exact_report matching
  refine ⟨result.1,result.2.1,result.2.2,?_⟩
  rw [result.2.1]
  exact rejected proof

end Yulang.GeneralDeclarativeWitnessUnfinished350

import Yulang.GeneralDeclarativeWitnessIdentity351

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCatalog351
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessIdentity351 (Stamp Owned Key select table unique select_sound)
open GeneralDeclarativeWitnessForest350 (ProblemTree Global Code Fixed)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralDeclarativeWitnessRecordWhole350 (Accepted decode)
open GeneralDeclarativeWitnessOrigins350 (Table Attached attach support)
open GeneralNominalCommonBridge (Assignment)

structure WriteAnchor where
  producer : Stamp
  ordinal : Nat

/-- The producer has its own normalized source and allocation layout,
but is checked against exactly the consumer's fixed declarative state. -/
structure Anchor where
  roles : ProblemTree
  root : Demand
  required : List WriteAnchor
  authored : List Equation
  releases : List Key

def publishWrites (p : Anchor) (trace : List Fixed) : Option (List Owned) :=
  p.required.mapM (fun w => select trace w.producer w.ordinal)

structure Receipt (p : Anchor) (witness : Code) (report : Report) where
  producer : Accepted p.roles p.root report
  accepted : decode p.roles p.root witness report = some producer
  owned : List Owned
  computed : publishWrites p producer.diagnostic.fixed = some owned
  catalogue : Attached p.roles.current (table p.authored owned p.releases)

def check (p : Anchor) (code : Code) (report : Report) : Option (Receipt p code report) := do
  match accepted : decode p.roles p.root code report with
  | none => none
  | some prior =>
    match ran : publishWrites p prior.diagnostic.fixed with
    | none => none
    | some rows =>
      if unique rows then
        let catalogue ← attach p.roles.current (table p.authored rows p.releases)
        pure ⟨prior,accepted,rows,ran,catalogue⟩
      else none

theorem from_required {p : Anchor} {trace : List Fixed} {owned : List Owned}
    (found : publishWrites p trace = some owned) :
    ∀ w ∈ owned, ∃ anchor ∈ p.required, select trace anchor.producer anchor.ordinal = some w := by
  unfold publishWrites at found
  generalize p.required = input at found ⊢
  induction input generalizing owned with
  | nil =>
    cases Option.some.inj found
    intro x none
    cases none
  | cons a as ih =>
    rw [List.mapM_cons] at found
    cases first : select trace a.producer a.ordinal with
    | none => simp [first] at found
    | some next =>
      cases rest : as.mapM (fun w => select trace w.producer w.ordinal) with
      | none => simp [first,rest] at found
      | some written =>
        have eq : next :: written = owned := by simpa [first,rest] using found
        subst owned
        intro x member
        rcases List.mem_cons.mp member with rfl|later
        · exact ⟨a,List.mem_cons_self,first⟩
        · obtain ⟨k,listed,read⟩ := ih rest _ later
          exact ⟨k,List.mem_cons_of_mem _ listed,read⟩

theorem proves_writes {p : Anchor} {code : Code} {report : Report}
    (receipt : Receipt p code report) (m : Assignment) (fit : Models p.roles.current m) :
    ∀ w ∈ receipt.owned, ∃ loc ∈ p.required, ∃ block ∈ receipt.producer.diagnostic.fixed,
      block.path = loc.producer.path ∧ block.demand.role = loc.producer.role ∧
      block.equations[loc.ordinal]? = some w.equation ∧
      w.key = ⟨loc.producer.path,loc.producer.role,loc.producer.version,loc.ordinal,w.equation.left⟩ ∧
      GeneralDeclarativeEntailment320.Holds m w.equation := by
  intro w listed
  obtain ⟨loc,requested,selected⟩ := from_required receipt.computed w listed
  obtain ⟨block,known,path,role,ord,key⟩ := select_sound selected
  exact ⟨loc,requested,block,known,path,role,ord,key,
    (receipt.producer.diagnostic.fixedMeaning block known).2 m fit _
      (List.mem_iff_getElem?.mpr ⟨_,ord⟩)⟩

end Yulang.GeneralDeclarativeWitnessCatalog351

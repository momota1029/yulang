import Yulang.GeneralDeclarativeI65I74PreparedDeclarations463
import Yulang.GeneralDeclarativeI65I74FiniteSourceShell461

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
open Yulang.GeneralDeclarativeI65
open EligibleFieldStart461 WrittenPattern460
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataRoles291 (Valid)
open Checker408 (Problem)

structure AtRequest {p : Problem} (a : OriginalAnchor p) : Prop where
  singletonPoint : CurrentAddressShape p a
  noGoalOutput : p.root.demand.outputs = []
  noWhereOutput : a.clause.outputs = []
  originalRole : ∃ row ∈ p.state.core.current.environment.source.roles.rows, row.role = p.root.demand.role
  validRoles : Valid p.state.core.current.environment.source.roles

def checkRequestOnly {p : Problem} (a : OriginalAnchor p) : Bool :=
  decide (CurrentAddressShape p a) && p.root.demand.outputs.isEmpty &&
  a.clause.outputs.isEmpty && (Checker408.originalRole p).isSome &&
  GeneralSourceMetadataRoles291.check p.state.core.current.environment.source.roles

private theorem actual_role_exact (p : Problem) :
    (Checker408.originalRole p).isSome = true ↔
      ∃ row ∈ p.state.core.current.environment.source.roles.rows, row.role = p.root.demand.role := by
  constructor
  · intro yes
    cases found : Checker408.originalRole p with
    | none => simp [found] at yes
    | some row =>
      have seen := GeneralSourceMetadataRoles291.indexed found
      exact ⟨row,seen.1,seen.2⟩
  · exact Opaque448.original_role_is_read448 (p := p)

theorem request_only_exact {p : Problem} (a : OriginalAnchor p) :
    checkRequestOnly a = true ↔ AtRequest a := by
  simp only [checkRequestOnly,Bool.and_eq_true,decide_eq_true_eq,List.isEmpty_iff,
    actual_role_exact,GeneralSourceMetadataRoles291.check_exact]
  exact ⟨fun ⟨⟨⟨⟨sh,g⟩,w⟩,r⟩,v⟩ => ⟨sh,g,w,r,v⟩,
    fun ⟨sh,g,w,r,v⟩ => ⟨⟨⟨⟨sh,g⟩,w⟩,r⟩,v⟩⟩

private theorem singleton_by_original_index {α : Type} {xs : List α} {i : Nat} {a : α}
    (n : xs.length = 1) (ok : xs[i]? = some a) : i = 0 ∧ xs = [a] := by
  cases xs with
  | nil => cases n
  | cons h rest =>
    cases rest with
    | cons _ _ => simp at n
    | nil =>
      cases i with
      | zero => have same := Option.some.inj ok; subst a; exact ⟨rfl,rfl⟩
      | succ i => simp at ok

def prepareRequest {p : Problem} (tab : CheckedTable p.state.core.current)
    (a : OriginalAnchor p) (request : AtRequest a) (isPrepared : a.declaration ∈ tab.rows) :
    EligibleStart p :=
  let s := request.singletonPoint
  ⟨a.declaration,a.original,a.clause,a.capture,a.code,
    (singleton_by_original_index s.1 a.actualVisible).2,
    (singleton_by_original_index s.2.1 a.actualHead).2,
    (singleton_by_original_index s.2.2.1 a.actualClause).2,
    (singleton_by_original_index s.2.2.2.1 a.actualArgument).2,
    s.2.2.2.2,request.noGoalOutput,request.noWhereOutput,request.originalRole,request.validRoles,
    tab.prepared _ isPrepared,a.compiled⟩

theorem checking_request_preserves_entire_original_anchor {p : Problem}
    (tab : CheckedTable p.state.core.current) (a : OriginalAnchor p)
    (request : AtRequest a) (ok : a.declaration ∈ tab.rows) :
    (prepareRequest tab a request ok).anchor = a := by
  have s := request.singletonPoint
  have v := (singleton_by_original_index s.1 a.actualVisible).1
  have h := (singleton_by_original_index s.2.1 a.actualHead).1
  have w := (singleton_by_original_index s.2.2.1 a.actualClause).1
  have loc : a.location = ⟨0,0,0⟩ := by
    cases which : a.location
    simp_all
  cases a
  simp_all [prepareRequest,EligibleStart.anchor]

def readPrepared {p : Problem} (tab : CheckedTable p.state.core.current)
    (atSource : AnchorAddress) : Option (EligibleStart p) := do
  let a ← readOriginalAnchor p atSource
  if usingRequest : checkRequestOnly a = true then
    if already : tableContains tab a.declaration = true then
      some (prepareRequest tab a ((request_only_exact a).mp usingRequest) (of_decide_eq_true already))
    else none
  else none

def PreparedSource {p : Problem} (tab : CheckedTable p.state.core.current)
    (e : EligibleStart p) : Prop :=
    ∃ (a : OriginalAnchor p) (req : AtRequest a) (member : a.declaration ∈ tab.rows),
      prepareRequest tab a req member = e

theorem prepared_source_iff_exact_finite_original_address {p : Problem}
    (tab : CheckedTable p.state.core.current) (e : EligibleStart p) :
    (∃ a : AnchorAddress, readPrepared tab a = some e) ↔ PreparedSource tab e := by
  constructor
  · rintro ⟨atSource,read⟩
    cases h : readOriginalAnchor p atSource with
    | none => simp [readPrepared,h,Option.bind] at read
    | some a =>
      by_cases req : checkRequestOnly a = true <;> by_cases ready : tableContains tab a.declaration = true
      · have exact : prepareRequest tab a ((request_only_exact a).mp req) (of_decide_eq_true ready) = e := by
          simpa [readPrepared,h,req,ready,Option.bind] using read
        exact ⟨a,(request_only_exact a).mp req,of_decide_eq_true ready,exact⟩
      all_goals simp [readPrepared,h,req,ready,Option.bind] at read
  · rintro ⟨a,req,inTable,rfl⟩
    refine ⟨a.location,?_⟩
    have r := (request_only_exact a).mpr req
    have ready : tableContains tab a.declaration = true := decide_eq_true inTable
    simp [readPrepared,every_independent_anchor_replays a,r,ready,Option.bind]

def preparedReader {p : Problem} (tab : CheckedTable p.state.core.current) : ReadyRead p :=
  ⟨AnchorAddress,PreparedSource tab,readPrepared tab,prepared_source_iff_exact_finite_original_address tab⟩

end Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463

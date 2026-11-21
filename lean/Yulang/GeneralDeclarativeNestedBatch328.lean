import Yulang.GeneralDeclarativeOpaqueBatch328
import Yulang.GeneralDeclarativeNestedModels328
import Yulang.GeneralDeclarativeVisibleCode325

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
namespace Yulang.GeneralDeclarativeNestedBatch328
open GeneralDeclarativeNestedDecl328 (reg impl root rootArg normalized checked raw normalCode clause body eqOut interpret)
open GeneralDeclarativeNestedState328 (keep initial chosenPlan prepared child grow_tail rootRow childRow base
  final original_range built)
open GeneralDeclarativeNestedResolve328 (certified declared dict)
open GeneralDeclarativeOpaqueBatch328 (check accepted)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralDeclarativeAppliedClause327 (targetsOnly)
open GeneralDeclarativeClauseBatch327 (prepare make)
open GeneralDeclarativeClausePlacement327 (placement)
open GeneralDeclarativeWhereOutputBatch327 (whole)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeNFComplete324 (facts)
open GeneralDeclarativeAssembly320 (Meaning)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalCenteredHeadMatExpressions (translateMany Expr)
open GeneralDeclarativeVisibleCode325 (codes_were_covered)
open GeneralDeclarationExamples (constructors roles bareRole binaryRole outputRole)
open GeneralDeclarations (Clause)
open GeneralDeclarativeWhere319 (Capture)

theorem covered : Coverage reg interpret := by
  constructor
  · intro d visible
    rcases List.mem_cons.mp visible with rfl|rest
    · refine ⟨(codes_were_covered (xs := [normalCode])
        (show translateMany constructors interpret [raw] = _ from rfl)).1,?_,?_⟩
      · intro cl needed
        cases List.mem_singleton.mp needed
        refine ⟨⟨trivial,trivial⟩,?_⟩
        intro eq wanted
        cases List.mem_singleton.mp wanted
        trivial
      · intro eq present
        cases List.mem_singleton.mp present
        trivial
    · cases List.mem_singleton.mp rest
      exact ⟨⟨trivial,trivial⟩,fun _ absent => False.elim (List.not_mem_nil absent),
        fun eq found => by cases List.mem_singleton.mp found; trivial⟩
  · intro role name term h
    by_cases isP : role = 1
    · subst role
      by_cases eq : name = 0 <;> simp [roles,outputRole,eq] at h
    by_cases isC : role = 2
    · subst role
      by_cases eq : name = 1 <;> simp [roles,outputRole,eq] at h
    by_cases isB : role = 4 <;> simp [roles,bareRole,binaryRole,isP,isC,isB] at h

abbrev targets (_ : Clause) (_ : Nat) : Nat := 5
abbrev fallback (_ : Nat) : Capture := ⟨99,99,99⟩
abbrev actualInput := (sourceNames impl (targetsOnly targets) base).input
abbrev ports := [make prepared keep actualInput clause [.variable 0]]
abbrev actualPlace := placement impl.requirements ports targets
abbrev concrete := sourceNames impl actualPlace base

theorem actual_ports : prepare reg.constructors interpret keep actualInput prepared impl.requirements =
    some (prepared,ports) := rfl
theorem no_where_rows : whole reg interpret impl concrete targets = some [] := rfl
theorem actual_return : collect (one reg interpret impl root concrete.input) root.outputs =
    some [rootRow] := rfl
theorem independently_checked : check (children impl concrete actualPlace) [child] = true := rfl
theorem wrong_target_fails :
    check (children impl concrete actualPlace) [⟨2,[GeneralDeclarativeNestedState328.left],[⟨1,6⟩]⟩] = false := rfl

theorem compiles : Result final (facts reg interpret concrete.input impl root [child]) ∧
    (∀ m, Models final m → Meaning reg interpret m root impl concrete.input [child]) ∧
    ∀ actual ∈ [child], Declared reg actual := by
  exact accepted checked covered List.mem_cons_self rfl declared rfl rfl original_range
    built (by decide +kernel) normalized fallback targets keep grow_tail grow_tail
    actual_ports no_where_rows (fun _ impossible => False.elim (List.not_mem_nil impossible))
    actual_return (fun row h => List.mem_append_left _ (List.mem_append_right _ h)) independently_checked

theorem full (m) (fit : Models final m) :
    Meaning reg interpret m root impl concrete.input [child] ∧ Evidence reg interpret m root dict :=
  ⟨compiles.2.1 m fit,certified m fit⟩

end Yulang.GeneralDeclarativeNestedBatch328

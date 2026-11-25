import Yulang.GeneralDeclarativeI65I74StructuralWhereOrdered427
import Yulang.GeneralDeclarativeI65I74RecordDeclaration412

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere427
open GeneralDeclarations (Declaration DeclarationChecked)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralDeclarativeWitnessSignature349 (checked_signature)
open GeneralDeclarativeWitnessChecks349 (identified produced output_only scope_sound)
open I72.RecordK2412 (header412 closedHead412 closedWhere412 recordDescent412 checked_closed_record_descent412)

/-- Reuse X10's structural descent proof for each actual authored clause,
not the conservative generic stableSchema which can miss this compound.
The premise applies to all original positions, not a chosen prefix. -/
theorem every_original_closed_where_clause_passes_parent_header427
    {s : GeneralDeclarativeWitnessDeclaredState357.Current} {d : Declaration}
    {box tick empty binder : Nat}
    (cov : DeclarationCovered s.environment d) (header : header412 s d = true)
    (head : d.head = [closedHead412 box tick empty binder])
    (all : ∀ c ∈ d.requirements,
      c.arguments = [closedWhere412 box empty binder] ∧ recordDescent412 d.head c.arguments = true) :
    DeclarationChecked (authoredRegistry s).constructors (authoredRegistry s).roles d := by
  obtain ⟨top,tail⟩ := splitAnd header
  obtain ⟨sg,ix⟩ := splitAnd top
  obtain ⟨b,scope⟩ := splitAnd tail
  obtain ⟨prod,lex⟩ := splitAnd b
  have each (c) (seen : c ∈ d.requirements) := checked_closed_record_descent412
    (head ▸ (all c seen).1 ▸ (all c seen).2)
  refine ⟨checked_signature sg,identified ix,produced prod,output_only lex,scope_sound scope,
    GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cov,?_,?_,?_,?_⟩
  all_goals
    intro c present
    have trueParts := each c present
    rw [head,(all c present).1]
  · exact trueParts.1
  · exact trueParts.2.1
  · exact trueParts.2.2.1
  · exact trueParts.2.2.2

def originalNoOutputEvent427 {s q} (atlas : B6OccurrenceAtlas401 s)
    (f : AuthoredBodyFrame393 s q) (h : SourceHead s q f.decl)
    (noOutputs : q.demand.outputs = []) : I72.Event ⟨s,atlas⟩ q :=
  ⟨f,h,fun i => by
    have impossible := i.isLt
    simp [noOutputs] at impossible⟩

/-- Compile the existing semantic dictionary constructor on this exact
parent and all original emitted children. This does not provide a
parent classification or a public R15 checker; no election is assumed
from a matching result. -/
theorem original_structural_parent_and_all_children_share_given_model427
    {s q f atlas data xs}
    (h : SourceHead s q f.decl)
    (empty : q.demand.outputs = [])
    (replay : readAllOriginalWhere427 (s:=s) (q:=q) f atlas data = some xs)
    (m : Model) (fit : Fits s m) :
    I72.DictionaryEvidence ⟨s,atlas⟩ m q (.node f.decl.id xs.dictionaries) := by
  let e := originalNoOutputEvent427 atlas f h empty
  have localFact : I72.LocalMeaning m e := by
    refine ⟨source_head_sound h m fit,?_⟩
    intro i
    exact Fin.elim0 (Fin.cast (congrArg List.length empty) i)
  have retained : I72.FixedTargets m e := by
    intro i
    exact Fin.elim0 (Fin.cast (congrArg List.length empty) i)
  exact .node e localFact retained (checked_original_where_list_has_exact_same_model_forest427 replay m fit)

end Yulang.GeneralDeclarativeI65.StructuralWhere427

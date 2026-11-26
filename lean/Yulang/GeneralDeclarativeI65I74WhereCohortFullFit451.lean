import Yulang.GeneralDeclarativeI65I74WhereCohortMarks451
import Yulang.GeneralDeclarativeAliasMeaning321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem)
open RetainedFull445
open GeneralDeclarations (Clause)
open GeneralDeclarativeWitnessDeclaredState357 (point authoredRegistry)
open GeneralNominalDemandMerging (Site SameInputs SameOrigin)
open CommonNominalFullCarrier (Equivalent)

def allAssignments (s : FullState) (a : GeneralNominalCommonBridge.Assignment) : Prop :=
  ∃ m, FitsFull s m ∧ m.assignment = a

theorem actual_link_from_raw_same_has_full_model_equal_centers451 {s : FullState} {l r : RolePoint}
    (same : RawSame s.base.core.current.ordinary l r) (m : I72.Model) (fit : FitsFull s m) :
    Equivalent (m.assignment l.2).1 (m.assignment r.2).1 :=
  GeneralDeclarativeAliasMeaning321.alias_sound same.2 m.assignment fit.1.1.1

theorem raw_same_implies_independent_source_origin_agreement451 {s : FullState} {l r : RolePoint}
    (same : RawSame s.base.core.current.ordinary l r) :
    SameOrigin (allAssignments s) (.source l.2) (.source r.2) := by
  intro assignment fromFit
  obtain ⟨m,fit,rfl⟩ := fromFit
  refine ⟨⟨_,.source _⟩,⟨_,.source _⟩,?_⟩
  intro _ _ read other
  cases read
  cases other
  exact actual_link_from_raw_same_has_full_model_equal_centers451 same m fit

def roleDecls (p : Problem) : Roles.RoleDecls :=
  (authoredRegistry p.state.core.current).roles

structure SourcePointAt {p : Problem} (a : ParentSelection p) (i : Nat) where
  original : Clause
  indexed : a.decl.requirements[i]? = some original
  litBinder : Nat
  capture : Nat
  header : original.arguments = [.var litBinder]
  realCapture : (litBinder,capture) ∈ a.chosen.roster.bindings
  one : (roleDecls p original.role).arity = 1
  sameRequest : a.children[i]? = some ⟨p.root.occurrence ++ [i],⟨original.role,[point capture],[]⟩⟩

def SourcePointAt.request {p : Problem} {a : ParentSelection p} {i}
    (x : SourcePointAt a i) : I72.Request :=
  ⟨p.root.occurrence ++ [i],⟨x.original.role,[point x.capture],[]⟩⟩

/-- Legacy Site cannot retain full occurrence path: it is provided by the
separate indexed Request field, and no numeric id is assumed equal to it. -/
def SourcePointAt.site {p : Problem} {a : ParentSelection p} {i}
    (x : SourcePointAt a i) : Site (roleDecls p) where
  occurrence := ⟨x.original.id,⟨x.original.role,fun _ => (x.capture,x.capture),[],by
    intro output absent
    cases absent⟩⟩
  inputs := [some (.source x.capture)]
  arity := x.one.symm

def SourcePointAt.actual {p : Problem} {a : ParentSelection p} {i}
    (x : SourcePointAt a i) : ActualPoint x.request :=
  ⟨x.capture,rfl⟩

theorem original_clause_projected_as_same_input_site451 {p : Problem} (a : ParentSelection p)
    {i : Nat} {c : Clause} (atClause : a.decl.requirements[i]? = some c) :
    ∃ x : SourcePointAt a i, x.original = c := by
  obtain ⟨binder,payload,lit,owned,_,read⟩ := known_original_clause_has_actual_payload451 a atClause
  have count := (a.chosen.checked.signature.2.2.2 c (List.mem_of_getElem? atClause)).1
  rw [lit] at count
  exact ⟨⟨c,atClause,binder,payload,lit,owned,count.symm,read⟩,rfl⟩

theorem indexed_cohort_label_proves_same_input_from_actual_source451 {p : FullProblem}
    {a : ParentSelection p.old} (r : OriginalCohort a) {i j : Nat}
    (one : SourcePointAt a i) (two : SourcePointAt a j) (label : Nat)
    (left : r.labelled[i]? = some (one.actual.tag,label))
    (right : r.labelled[j]? = some (two.actual.tag,label)) :
    SameInputs (allAssignments p.state) one.site two.site ∧
      (RootCycle p.state.base one.request ↔ RootCycle p.state.base two.request) := by
  have bin := r.exactSame _ (List.mem_of_getElem? left) _ (List.mem_of_getElem? right)
  have raw : RawSame p.state.base.core.current.ordinary one.actual.tag two.actual.tag := bin.mp rfl
  have equal := raw_same_implies_independent_source_origin_agreement451
    (s := p.state) raw
  refine ⟨⟨raw.1,.cons ⟨_,_,rfl,rfl,equal⟩ .nil⟩,?_⟩
  exact (root_cycle_exact_named_point451 one.actual).trans
    ((GeneralDeclarativeK2Alias321.alias_cycle_iff raw.2).trans
      (root_cycle_exact_named_point451 two.actual).symm)

end Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451

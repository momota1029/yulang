import Yulang.GeneralDeclarativeWitnessSignature349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessChecks349
open GeneralDeclarations GeneralDeclarationPatterns

def ids (d : Declaration) : Bool :=
  decide (d.requirements.map Clause.id).Nodup &&
  (decide (d.associated.map Equation.id).Nodup &&
   (decide (d.associated.map Equation.name).Nodup &&
    (decide d.outputNames.Nodup &&
     d.requirements.all (fun c => decide (c.outputs.map Equation.id).Nodup))))

theorem identified {d : Declaration} (h : ids d = true) : d.Identified := by
  simp only [ids,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at h
  exact h

def binds (d : Declaration) : Bool :=
  d.outputBinders.all fun b =>
    d.requirements.any fun c =>
      decide (c.id = b.clause) &&
      c.outputs.any (fun q => decide (q.id = b.equation ∧ q.rhs = .var b.name))

theorem produced {d : Declaration} (h : binds d = true) : d.Produced := by
  intro b used
  obtain ⟨clause,member,expr⟩ := List.any_eq_true.mp (List.all_eq_true.mp h b used)
  obtain ⟨ix,options⟩ := GeneralDeclarativeWitnessProblem349.splitAnd expr
  obtain ⟨row,there,valid⟩ := List.any_eq_true.mp options
  have eq := of_decide_eq_true valid
  exact ⟨clause,member,of_decide_eq_true ix,row,there,eq.1,eq.2⟩

def lexical (d : Declaration) : Bool :=
  d.outputNames.all (fun n => decide (n ∉ variablesArgs d.head)) &&
    d.requirements.all (fun c => d.outputNames.all (fun n => decide (n ∉ variablesArgs c.arguments)))

theorem output_only {d : Declaration} (h : lexical d = true) : d.OutputOnly := by
  simp only [lexical,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at h
  exact h

def rhsScope (d : Declaration) (rhs : Pattern) : Bool :=
  rhs.variables.all (fun n => decide (n ∈ d.inputNames ∨ n ∈ d.outputNames))

theorem rhs_scope {d : Declaration} {rhs : Pattern} (h : rhsScope d rhs = true) :
    ∀ n ∈ rhs.variables, n ∈ d.inputNames ∨ n ∈ d.outputNames := by
  simpa only [rhsScope,List.all_eq_true,decide_eq_true_eq] using h

def names (d : Declaration) : Bool :=
  (d.requirements.all (fun c => (variablesArgs (normalizeArgs c.arguments)).all
    (fun n => decide (n ∈ d.inputNames)))) &&
  (d.associated.all (fun e => rhsScope d (normalize e.rhs)) &&
    d.requirements.all (fun c => c.outputs.all (fun e => rhsScope d e.rhs)))

theorem scope_sound {d : Declaration} (h : names d = true) : d.Scoped := by
  simp only [names,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at h
  exact ⟨h.1,fun e eM => rhs_scope (h.2.1 e eM),fun c cM e eM => rhs_scope (h.2.2 c cM e eM)⟩

/-- A syntactic sufficient schema for universal stability. The other
declaration checks still run; an unmatched schema is not language
rejection and is not silently accepted. -/
def stableSchema (head child : List Pattern) : Bool :=
  match head, child with
  | [.app _ [.var x]], [.var y] => decide (x = y)
  | _, _ => false

theorem stable_sound {head child : List Pattern} (h : stableSchema head child = true) :
    StableSmaller head child := by
  unfold stableSchema at h
  split at h
  · rename_i c x y
    cases of_decide_eq_true h
    exact unary_descent _ _
  · cases h

def counts (head child : List Pattern) : Bool :=
  coveredArgs (normalizeArgs head) && coveredArgs (normalizeArgs child)

def checkedDescent (head child : List Pattern) : Bool :=
  (counts head child && checkSmaller head child) &&
    (CheckedRoles.checkCondition (lowerArgs (normalizeArgs head)) ⟨0,counted child⟩ &&
       stableSchema head child)

theorem descent_parts {head child : List Pattern} (h : checkedDescent head child = true) :
    CountsCovered head child ∧ Smaller head child ∧ ConservativeSmaller head child ∧ StableSmaller head child := by
  obtain ⟨front,last⟩ := GeneralDeclarativeWitnessProblem349.splitAnd h
  obtain ⟨bothCount,smaller⟩ := GeneralDeclarativeWitnessProblem349.splitAnd front
  obtain ⟨conservative,stable⟩ := GeneralDeclarativeWitnessProblem349.splitAnd last
  exact ⟨GeneralDeclarativeWitnessProblem349.splitAnd bothCount,(checkSmaller_exact ..).mp smaller,conservative,stable_sound stable⟩

end Yulang.GeneralDeclarativeWitnessChecks349

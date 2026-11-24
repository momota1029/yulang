import Yulang.GeneralDeclarativeI65SelectedHeadBindings395
import Yulang.GeneralDeclarativeI65FiniteCompletion383

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (Dictionary)
open GeneralDeclarations (Declaration OutputBinder Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeSourceEmission322 (useOutput)

private theorem lookupMap395 (v : Nat → Capture) {l : List Nat} {n : Nat} (mem : n ∈ l) :
    (l.map fun m => (m,v m)).lookup n = some (v n) := by
  induction l with
  | nil => cases mem
  | cons a tail ih =>
    by_cases eq : a = n
    · subst a
      simp
    · have h : (n == a) = false := beq_eq_false_iff_ne.mpr (Ne.symm eq)
      simp only [List.map_cons,List.lookup,h,ih ((List.mem_cons.mp mem).resolve_left (Ne.symm eq))]

structure OriginalWhereBinder395 {s q} (frame : AuthoredBodyFrame393 s q)
    (binder : OutputBinder) (body : Equation) where
  clauseOrdinal : Nat
  outputOrdinal : Nat
  entry : LiteralWhereEntry
  equation : Equation
  output : GeneralSourceState.Output
  atClause : frame.clauses[clauseOrdinal]? = some entry
  clauseId : entry.clause.id = binder.clause
  atEquation : entry.clause.outputs[outputOrdinal]? = some equation
  equationId : equation.id = binder.equation
  binderRhs : equation.rhs = .var binder.name
  outputAt : entry.demand.outputs[outputOrdinal]? = some output
  outputName : output.name = equation.name
  slot : frame.slots (.explicit body) binder.name = some ⟨output.target,output.target,output.target⟩

/-- The genuine scope production rule identifies the original where
equation and exact lexical slot before the parent RHS is evaluated.
This result does not use the target of a compiled/model-equivalent row. -/
theorem original_where_produces_lexical_slot395 {s q} (frame : AuthoredBodyFrame393 s q)
    (produced : frame.decl.Produced) (body : Equation)
    {binder : OutputBinder} (member : binder ∈ frame.decl.outputBinders) :
    Nonempty (OriginalWhereBinder395 frame binder body) := by
  obtain ⟨clause,inDecl,clauseId,eqn,inClause,eqnId,rhs⟩ := produced binder member
  obtain ⟨i,atDecl⟩ := List.getElem?_of_mem inDecl
  obtain ⟨j,atEqn⟩ := List.getElem?_of_mem inClause
  let entry := frame.whereFor clause
  let out := useOutput frame.decl frame.names (frame.placement.targets clause) eqn
  have named : binder.name ∈ frame.decl.outputNames := List.mem_map.mpr ⟨binder,member,rfl⟩
  have entryHere : frame.clauses[i]? = some entry := by
    simp [AuthoredBodyFrame393.clauses,atDecl,entry]
  have outputHere : entry.demand.outputs[j]? = some out := by
    simp [entry,AuthoredBodyFrame393.whereFor,GeneralDeclarativeSourceEmission322.demand,atEqn,out]
  have originalTarget : out.target = frame.names.output binder.name := by
    simp [out,useOutput,GeneralDeclarationDemands.outputTarget,
      GeneralDeclarativeSourceEmission322.Names.old,rhs,normalize,named]
  have point : frame.names.input binder.name = ⟨out.target,out.target,out.target⟩ := by
    rw [originalTarget]
    simp [AuthoredBodyFrame393.names,GeneralDeclarativeFrameReadback325.sourceNames,
      GeneralDeclarativeProducedNames325.table,named]
  have read := lookupMap395 frame.names.input (List.mem_append_right frame.decl.inputNames named)
  have slot : frame.slots (.explicit body) binder.name = some ⟨out.target,out.target,out.target⟩ := by
    simpa only [AuthoredBodyFrame393.slots,AuthoredBodyFrame393.captures,point] using read
  exact ⟨⟨i,j,entry,eqn,out,entryHere,clauseId,atEqn,eqnId,rhs,outputHere,rfl,slot⟩⟩

def OriginalWhereBinder395.child {s q f binder body}
    (origin : OriginalWhereBinder395 (s := s) (q := q) f binder body) : Request :=
  ⟨q.occurrence ++ [origin.clauseOrdinal], origin.entry.demand⟩

theorem OriginalWhereBinder395.child_position {s q f binder body}
    (origin : OriginalWhereBinder395 (s := s) (q := q) f binder body) :
    (children q (f.clauses.map LiteralWhereEntry.demand))[origin.clauseOrdinal]? = some origin.child := by
  have hit : (f.clauses.map LiteralWhereEntry.demand)[origin.clauseOrdinal]? = some origin.entry.demand := by
    rw [List.getElem?_map,origin.atClause]
    rfl
  have index := (List.getElem?_eq_some_iff.mp hit).1
  unfold children OriginalWhereBinder395.child
  rw [List.getElem?_map]
  rw [List.getElem?_zipIdx]
  simp [hit]

/-- The dependent dictionary at the same child position is
recovered from the genuinely finite proof tree, not a chosen
dictionary from another occurrence with an equal output name. -/
def completed_forest_at395 {rules s qs ds child}
    (forest : SelectedSourceForest383 rules s qs ds)
    (i : Nat) (position : qs[i]? = some child) :
    {d : Dictionary // ds[i]? = some d ∧
      Nonempty (SelectedSourceProof383 rules s child d)} := by
  cases forest with
  | nil => simp at position
  | cons head rest =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at position
      subst child
      exact ⟨_,rfl,⟨head⟩⟩
    | succ i =>
      exact completed_forest_at395 rest i (by simpa using position)

structure CompletedWhereBinder395 {s q f binder body}
    (origin : OriginalWhereBinder395 (s := s) (q := q) f binder body)
    {rules : SelectedSourceRule383} {dicts : List Dictionary}
    (forest : SelectedSourceForest383 rules s
      (children q (f.clauses.map LiteralWhereEntry.demand)) dicts) where
  dictionary : Dictionary
  dictionaryAt : dicts[origin.clauseOrdinal]? = some dictionary
  proof : Nonempty (SelectedSourceProof383 rules s origin.child dictionary)

/-- Literal where position -> the same strictly subordinate finite
selected derivation in the current state. No release, version, model
or parent's output proof is supplied or reconstructed. -/
def selectWhereBinderProducer395 {s q f binder body rules dicts}
    (origin : OriginalWhereBinder395 (s := s) (q := q) f binder body)
    (forest : SelectedSourceForest383 rules s
      (children q (f.clauses.map LiteralWhereEntry.demand)) dicts) :
    CompletedWhereBinder395 origin forest :=
  let read := completed_forest_at395 forest origin.clauseOrdinal origin.child_position
  ⟨read.val,read.2.1,read.2.2⟩

def OriginalWhereBinder395.outputIndex {s q f binder body}
    (origin : OriginalWhereBinder395 (s := s) (q := q) f binder body) :
    Fin origin.child.demand.outputs.length :=
  ⟨origin.outputOrdinal,(List.getElem?_eq_some_iff.mp origin.outputAt).1⟩

theorem same_where_request_ordinal_names_lexical_slot395 {s q f binder body rules dicts}
    (origin : OriginalWhereBinder395 (s := s) (q := q) f binder body)
    (forest : SelectedSourceForest383 rules s
      (children q (f.clauses.map LiteralWhereEntry.demand)) dicts)
    {childFrame : AuthoredBodyFrame393 s origin.child}
    (made : OriginalCompoundOutput394 childFrame origin.outputIndex) :
    ∃ d : Dictionary, dicts[origin.clauseOrdinal]? = some d ∧
      Nonempty (SelectedSourceProof383 rules s origin.child d) ∧
      made.emit.occurrence = q.occurrence ++ [origin.clauseOrdinal] ∧
      made.emit.ordinal = origin.outputOrdinal ∧
      made.emit.requested = origin.output ∧
      f.slots (.explicit body) binder.name =
        some ⟨made.emit.requested.target,made.emit.requested.target,made.emit.requested.target⟩ := by
  let p := selectWhereBinderProducer395 origin forest
  have same : made.emit.requested = origin.output := by
    exact (List.getElem?_eq_some_iff.mp origin.outputAt).2
  exact ⟨p.dictionary,p.dictionaryAt,p.proof,rfl,rfl,same,by rw [same]; exact origin.slot⟩

end Yulang.GeneralDeclarativeI65

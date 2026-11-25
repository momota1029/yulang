import Yulang.GeneralDeclarativeI65I74StructuralWhereIdentity428
import Yulang.GeneralDeclarativeI65I74RepeatedCentersEntry421

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere428
open StructuralWhere427
open GeneralDeclarations (Clause)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open I72.List410 (checkExactEscape exact_escape_refutes_raw_root_K2410)
open CommonRoleOutermostResolver (Tree)
open I72 (Event SourcePrimitives SourceTrace WhereForest)

/-- A real second source clause, not a reassignment of the first
structural child's role or input. These literal variable clauses use
the same parent lexical capture without any position allocation. -/
structure LiteralVariableArgumentAt428 {s q} (f : AuthoredBodyFrame393 s q) (k : Nat) where
  clause : Clause
  onSource : f.decl.requirements[k]? = some clause
  binder : Nat
  argument : clause.arguments = [.var binder]
  noOutputs : clause.outputs = []

def LiteralVariableArgumentAt428.child {s q f k}
    (w : LiteralVariableArgumentAt428 (s:=s) (q:=q) f k) : Request :=
  ⟨q.occurrence ++ [k],⟨w.clause.role,[f.names.input w.binder],[]⟩⟩

theorem literal_variable_sibling_at_author_position428 {s q f k}
    (w : LiteralVariableArgumentAt428 (s:=s) (q:=q) f k) :
    (frameWhereKids400 f)[k]? = some w.child := by
  have exactDemand := I72.literal_variable_where_uses_actual_names403 f
    (c:=w.clause) (binders:=[w.binder]) w.argument w.noOutputs
  have rowAt : (f.clauses.map LiteralWhereEntry.demand)[k]? = some (f.whereFor w.clause).demand := by
    simp [AuthoredBodyFrame393.clauses,w.onSource]
  unfold frameWhereKids400 children
  rw [List.getElem?_map,List.getElem?_zipIdx]
  simp only [rowAt,Option.map_some,LiteralVariableArgumentAt428.child,
    exactDemand,List.map_cons,List.map_nil,Nat.zero_add]

theorem literal_mixed_where_order_has_original_distinct_children428 {s q f}
    (a : OriginalRecordArgument427 (s:=s) (q:=q) f 0 0)
    (b : LiteralVariableArgumentAt428 f 1)
    (two : f.decl.requirements.length = 2) :
    frameWhereKids400 f = [a.child,b.child] := by
  have first := structural_where_keeps_original_child_at_ordinal427 a
  have second := literal_variable_sibling_at_author_position428 b
  have count : (frameWhereKids400 f).length = 2 := by
    simpa [frameWhereKids400,children,AuthoredBodyFrame393.clauses] using two
  generalize hx : frameWhereKids400 f = xs at first second count ⊢
  cases xs with
  | nil => simp at count
  | cons xx tail =>
    cases tail with
    | nil => simp at count
    | cons y tail =>
      have noTail : tail = [] := List.length_eq_zero_iff.mp (by simpa using count)
      subst tail
      have one : xx = a.child := by simpa using first
      have two : y = b.child := by simpa using second
      rw [one,two]

/-- Compose actual local named source proofs at known original
destinations. Neither child can be inserted at the other's
Request; the WhereForest index is the actual emitted list. -/
def assembleActualMixedSiblings428 {R : SourcePrimitives} {s : I72.State} {q : Request}
    (e : Event s q)
    (a : OriginalRecordArgument427 e.frame 0 0)
    (b : LiteralVariableArgumentAt428 e.frame 1)
    (two : e.frame.decl.requirements.length = 2)
    (safe : ¬ I72.RootCycle s q) (picked : R.elected s q e [])
    {ta tb oa ob} (first : SourceTrace R s a.child ta oa) (second : SourceTrace R s b.child tb ob) :
    SourceTrace R s q (.selected e.frame.decl.id [ta,tb]) (some e) := by
  have exactList : e.kids = [a.child,b.child] :=
    literal_mixed_where_order_has_original_distinct_children428 a b two
  let ordered : WhereForest R s [a.child,b.child] [ta,tb] := .cons first (.cons second .nil)
  exact .selected e safe picked .nil (exactList.symm ▸ ordered)

theorem mixed_original_siblings_preserve_empty_support_and_outputs428
    {R : SourcePrimitives} {s : I72.State} {q : Request}
    (e : Event s q) (a : OriginalRecordArgument427 e.frame 0 0)
    (b : LiteralVariableArgumentAt428 e.frame 1)
    (two : e.frame.decl.requirements.length = 2)
    (safe : ¬ I72.RootCycle s q) (picked : R.elected s q e [])
    {ta tb oa ob} (first : SourceTrace R s a.child ta oa) (second : SourceTrace R s b.child tb ob)
    (empty : q.demand.outputs = []) (firstEmpty : ZeroSupportSelected428 first)
    (secondEmpty : ZeroSupportSelected428 second) :
    ZeroSupportSelected428 (assembleActualMixedSiblings428 e a b two safe picked first second) := by
  let ordered : WhereForest R s [a.child,b.child] [ta,tb] := .cons first (.cons second .nil)
  exact ⟨rfl,empty,no_support_where_cast428
    (literal_mixed_where_order_has_original_distinct_children428 a b two).symm ordered
     ⟨firstEmpty,secondEmpty,True.intro⟩⟩

/-- The structural child is ordinary, but another visible role in
the same State can mention declared nominals. Check this child's
actual declaration with mode-aware coverage; a global ordinary-only
coverage pass cannot authorize or reject such mixed source. -/
def readModeClosedChild428 {s q f k}
    (a : OriginalRecordArgument427 (s:=s) (q:=q) f k 0)
    (atlas : B6OccurrenceAtlas401 s) (w : LeafWire427) :
    Option (ReadClosedChild427 a atlas) := do
  let env := s.current.environment
  let orig := env.source
  let registry := authoredRegistry s.current
  if roleTable : GeneralSourceMetadataRoles291.check orig.roles = true then
    match onRow : registry.declarations[w.declarationOrdinal]? with
    | none => none
    | some d =>
      if modeCoverage : GeneralDeclarativeWitnessModeCoverage357.checkDecl env d = true then
        if legal : GeneralDeclarativeWitnessCovariantDescent353.legal orig d = true then
         if only : visible s a.child = [d] then
          match head : d.head with
          | [.record label (.var binder) (.app empty [])] =>
            if same : label = a.label then
              match compiled : translateWhere427 s (writtenRecord427 a.label binder empty) with
              | none => none
              | some code =>
                if verbatim : eqExpr code (recordCode427 a.label binder) = true then
                  match inputArity : a.child.demand.arguments with
                  | [arg] =>
                    if emptyOutputs : a.child.demand.outputs = [] then
                      if emptyWhere : d.requirements = [] then
                        if raw : checkExactEscape s.current.ordinary a.name w.escape = true then
                          let atFirst := structural_where_child_argument_is_placed_point427 a
                          have atPoint : arg = point a.name := by simpa only [inputArity,List.getElem?_cons_zero,Option.some.injEq] using atFirst
                          have args : a.child.demand.arguments = [point a.name] :=
                            inputArity.trans (congrArg (fun c => [c]) atPoint)
                          have rawSafe : ¬ I72.RootCycle ⟨s,atlas⟩ a.child := by
                            rintro ⟨c,member,cycle⟩
                            change c ∈ a.child.demand.arguments at member
                            rw [args] at member
                            cases List.mem_singleton.mp member
                            exact exact_escape_refutes_raw_root_K2410 raw cycle
                          let wellCovered :=
                            (GeneralDeclarativeWitnessModeCoverage357.declaration_exact _ _).mp modeCoverage
                          let ready := GeneralDeclarativeWitnessModeDeclaration357.declaration_ready wellCovered legal
                          have declaration : GeneralDeclarations.DeclarationChecked
                              registry.constructors registry.roles d := by
                            exact ⟨ready.signature,ready.identified,ready.produced,ready.outputOnly,
                              ready.scopeOK,ready.constructorScoped,
                              fun c member => by simp [emptyWhere] at member,
                              fun c member => by simp [emptyWhere] at member,
                              fun c member => by simp [emptyWhere] at member,
                              fun c member => by simp [emptyWhere] at member⟩
                          pure ⟨⟨d,w.declarationOrdinal,onRow,only,declaration,binder,empty,
                            by simpa only [same,writtenRecord427] using head,
                            compiled.trans (congrArg some ((eq_expr ..).mp verbatim)),
                            args,emptyOutputs,emptyWhere⟩,rawSafe⟩
                        else none
                      else none
                    else none
                  | _ => none
                else none
            else none
          | _ => none
         else none
        else none
      else none
  else none


/-- The existing R1 bare-name local evidence is still a positive case
of the current pre-R14 R13 primitive. No historical request, solver
step or diagnostic is manufactured when taking this inclusion. -/
theorem old_named_local_election_is_still_R13_428 {s q e needs}
    (old : I72.Named409.R1.elected s q e needs) : I72.RepeatedCenters421.R13.elected s q e needs := by
  repeat first | exact old | apply Or.inl

theorem current_R13_local_law_for_mixed_named_traces428 : SelectedLaw428 I72.RepeatedCenters421.R13 :=
  fun rule m fit => I72.RepeatedCenters421.selected_repeated_local_sound421 rule m fit

end Yulang.GeneralDeclarativeI65.StructuralWhere428

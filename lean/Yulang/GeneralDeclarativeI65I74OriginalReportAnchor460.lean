import Yulang.GeneralDeclarativeI65I74CompiledTrailDecomposition460

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
open Yulang.GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Declaration Clause)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open AuthoredInspectQuery456 (AuthoredQuery compileQuery compile_query_exact)
open Checker408 (Problem)
open RetainedFull445 (FullProblem)
open GeneralDeclarativeWhere319 (Capture)
open RoutedReadyMixed457 (ReportAtField)
open RecordTraversal455.MixedQA (MixedPath)
open InlineStructuralPolicy458 (policy)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)

/-- Addresses into the existing, unfiltered visible roster and the actual
written declaration and request. Nothing in the locator edits or supplies
a replacement declaration, capture, where clause, or compilation result. -/
structure AnchorAddress where
  visibleOrdinal : Nat
  headArgument : Nat
  originalClauseOrdinal : Nat
  deriving DecidableEq

/-- A source address receipt, not election, DeclarationReady, or rule
completeness. It intentionally does not decide the remaining local
admissibility gates for the general G04 branch. -/
structure OriginalAnchor (p : Problem) where
  location : AnchorAddress
  declaration : Declaration
  original : Pattern
  clause : Clause
  capture : Capture
  code : Expr
  actualVisible : (visible p.state.core p.root)[location.visibleOrdinal]? = some declaration
  actualHead : declaration.head[location.headArgument]? = some original
  actualArgument : p.root.demand.arguments[location.headArgument]? = some capture
  actualClause : declaration.requirements[location.originalClauseOrdinal]? = some clause
  compiled : AuthoredQuery p.state.core (normalize original) code

def readOriginalAnchor (p : Problem) (a : AnchorAddress) : Option (OriginalAnchor p) :=
  match v : (visible p.state.core p.root)[a.visibleOrdinal]? with
  | none => none
  | some d =>
    match h : d.head[a.headArgument]?, arg : p.root.demand.arguments[a.headArgument]?,
          c : d.requirements[a.originalClauseOrdinal]? with
    | some original, some capture, some clause =>
      match code : compileQuery p.state.core (normalize original) with
      | none => none
      | some e =>
        some ⟨a,d,original,clause,capture,e,v,h,arg,c,(compile_query_exact ..).mp code⟩
    | _,_,_ => none

theorem every_independent_anchor_replays {p : Problem} (a : OriginalAnchor p) :
    readOriginalAnchor p a.location = some a := by
  rcases a with ⟨loc,d,pat,clause,arg,code,h1,h2,h3,h4,compiled⟩
  have eq : compileQuery p.state.core (normalize pat) = some code :=
    (compile_query_exact ..).mpr compiled
  unfold readOriginalAnchor
  split
  · rename_i wrong
    rw [h1] at wrong
    cases wrong
  · rename_i got h
    have same : got = d := Option.some.inj (h.symm.trans h1)
    subst got
    split
    · rename_i original capture c hA hB hC
      have he : original = pat := Option.some.inj (hA.symm.trans h2)
      have be : capture = arg := Option.some.inj (hB.symm.trans h3)
      have ce : c = clause := Option.some.inj (hC.symm.trans h4)
      subst original capture c
      split
      · rename_i fail
        rw [eq] at fail
        cases fail
      · rename_i result run
        have re : result = code := Option.some.inj (run.symm.trans eq)
        subst result
        rfl
    · simp_all

theorem address_from_original_declaration_is_exact {p : Problem} (a : OriginalAnchor p) :
    OriginalAt a.declaration (.head a.location.headArgument) (readTerm a.original) :=
  .head a.actualHead

theorem anchor_original_where_input_is_same_declared_site {p : Problem}
    (a : OriginalAnchor p) {i : Nat} {patt : Pattern} (found : a.clause.arguments[i]? = some patt) :
    OriginalAt a.declaration (.clause a.location.originalClauseOrdinal a.clause.id i) (readTerm patt) :=
  .clause a.actualClause found

theorem anchor_compiles_the_normalized_original {p : Problem} (a : OriginalAnchor p) :
    AuthoredQuery p.state.core (writeTerm (normalized (readTerm a.original))) a.code := by
  simpa only [normalized_reencodes_exactly,write_read_term] using a.compiled

def exactReport {p : Problem} (a : OriginalAnchor p) (path : MixedPath)
    (terminal : Nat) : ReportAtField :=
  ⟨p.root.occurrence,a.declaration.id,a.location.originalClauseOrdinal,a.clause.id,path,terminal⟩

structure AnchoredFieldWire (p : Problem) where
  anchor : AnchorAddress
  spine : CompilerFieldWire p.state.core

def readAnchoredField (p : Problem) (w : AnchoredFieldWire p) : Option ReportAtField := do
  let a ← readOriginalAnchor p w.anchor
  let (path,terminal,_) ← readAlreadyCompiledField p.state.core a.capture.lower
        (normalized (readTerm a.original)) a.code w.spine
  pure (exactReport a path terminal)

def anchored (p : Problem) (r : ReportAtField) : Prop :=
  ∃ (a : OriginalAnchor p) (last : Term),
    CompiledField p.state.core a.capture.lower (normalized (readTerm a.original))
      a.code r.path r.terminal last ∧ exactReport a r.path r.terminal = r

/-- Reification only for source/route identity; it does not install a
G04 checker branch or infer readiness from a locator. -/
theorem attained_exact_report_iff_finite_anchored_read {p : Problem} {r : ReportAtField} :
    (∃ w, readAnchoredField p w = some r) ↔ anchored p r := by
  constructor
  · rintro ⟨w,ok⟩
    cases h : readOriginalAnchor p w.anchor with
    | none => simp [readAnchoredField,h,Option.bind] at ok
    | some a =>
      cases out : readAlreadyCompiledField p.state.core a.capture.lower
          (normalized (readTerm a.original)) a.code w.spine with
      | none => simp [readAnchoredField,h,out,Option.bind] at ok
      | some data =>
        obtain ⟨path,terminal,last⟩ := data
        have eq : exactReport a path terminal = r := by
          simpa [readAnchoredField,h,out,Option.bind] using ok
        subst r
        exact ⟨a,last,(precompiled_field_iff_exact_finite_path
          (anchor_compiles_the_normalized_original a)).mp ⟨w.spine,out⟩,rfl⟩
  · rintro ⟨a,last,joint,report⟩
    obtain ⟨w,read⟩ := (precompiled_field_iff_exact_finite_path
      (anchor_compiles_the_normalized_original a)).mpr joint
    exact ⟨⟨a.location,w⟩,by
      simp [readAnchoredField,every_independent_anchor_replays a,read,report,Option.bind]⟩

theorem read_result_cannot_replace_original_occurrence {p : Problem} {r : ReportAtField}
    {w : AnchoredFieldWire p} (ok : readAnchoredField p w = some r) :
    r.occurrence = p.root.occurrence := by
  obtain ⟨a,_,_,eq⟩ := attained_exact_report_iff_finite_anchored_read.mp ⟨w,ok⟩
  rw [← eq]
  rfl

theorem addressed_field_holds_in_every_same_fit {p : FullProblem} {r : ReportAtField}
    (original : anchored p.old r) (m : I72.Model) (fit : I72.FitsFull p.state m) :
    ∃ (a : OriginalAnchor p.old) (last : Term) (used : Bool),
      exactReport a r.path r.terminal = r ∧
      RoutedInlineStructural458.ModelTrail p.state.base.core m a.capture.lower a.code r.path r.terminal used ∧
      CoordinateWalk (fun _ => queryKeys p.state.base.core) a.capture.lower
        (normalized (readTerm a.original)) r.path r.terminal last ∧
      AliasCycle p.state.base.core.current.ordinary
        (observed p.state.base.core.current.ordinary) r.terminal := by
  obtain ⟨a,last,h,report⟩ := original
  obtain ⟨used,real,written,cycle⟩ := compiled_field_keeps_same_fit (s := p.state) h m fit
  exact ⟨a,last,used,report,real,written,cycle⟩

end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460

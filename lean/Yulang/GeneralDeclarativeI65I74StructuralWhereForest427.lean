import Yulang.GeneralDeclarativeI65I74StructuralWhereVisit427

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere427
open GeneralDeclarations (Declaration)
open CommonRoleOutermostResolver (Dictionary)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralDeclarativeInspect321 (PatternK2)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeEmissionForest322 (Placement)

structure VisiblePointWire427 where
  head : PositiveHeadWire427
  rival : RivalWire427
  raw : ExactRecordVisitWire427

structure VisiblePoint427 (s : State) (q : Request) where
  positive : ReadPositiveHead427 s q
  rival : ReadBoxRival427 s q
  complete : visible s q = [positive.decl,rival.decl] ∨ visible s q = [rival.decl,positive.decl]
  distinct : positive.decl.id ≠ rival.decl.id
  rawWire : ExactRecordVisitWire427
  checkedSites : checkExactRecordVisits427 s.current.ordinary rival.found.root
    rival.found.box rival.found.field rawWire = true
  allSourceHeads :
    (visible s q).all (checkedCandidateVisitBySource427 s rival.found.box) = true

def readVisiblePoint427 (s : State) (q : Request) (w : VisiblePointWire427) :
    Option (VisiblePoint427 s q) := do
  let a ← readPositiveHead427 s q w.head
  let r ← readBoxRival427 s q w.rival
  if whole : visible s q = [a.decl,r.decl] ∨ visible s q = [r.decl,a.decl] then
    if distinct : a.decl.id ≠ r.decl.id then
      if sites : checkExactRecordVisits427 s.current.ordinary r.found.root
          r.found.box r.found.field w.raw = true then
        if all : (visible s q).all (checkedCandidateVisitBySource427 s r.found.box) = true then
          pure ⟨a,r,whole,distinct,w.raw,sites,all⟩
        else none
      else none
    else none
  else none

theorem complete_visible_point_has_no_filtered_K2_assumption427 {s q} (p : VisiblePoint427 s q) :
    ∀ d ∈ visible s q, ∃ source code, d.head = [source] ∧ translateWhere427 s source = some code ∧
      ¬ PatternK2 s.current.ordinary p.rival.found.root code := by
  intro d found
  exact checked_candidate_by_source_visits_exact427 p.checkedSites
    (List.all_eq_true.mp p.allSourceHeads d found)

theorem complete_visible_point_has_independent_rival_mismatch427 {s q} (p : VisiblePoint427 s q)
    (m : Model) (fit : Fits s m) :
    ∀ d ∈ visible s q, Nonempty (SourceHead s q d) → d = p.positive.decl :=
  (positive_box_cannot_be_displaced_by_its_checked_rival427 p.rival p.complete
    ⟨p.positive.head⟩ m fit).2

private def captureSame427 (a b : Capture) : Bool :=
  decide (a.lower = b.lower ∧ a.center = b.center ∧ a.upper = b.upper)

private theorem capture_same427 {a b : Capture} (h : captureSame427 a b = true) : a = b := by
  cases a
  cases b
  obtain ⟨l,c,u⟩ := of_decide_eq_true h
  cases l; cases c; cases u; rfl

structure OriginalPreparedRoot427 {s q} (f : AuthoredBodyFrame393 s q) where
  visiblePoint : VisiblePoint427 s q
  declaration : visiblePoint.positive.decl = f.decl
  lexical : ∀ binder ∈ f.decl.inputNames, f.input binder = visiblePoint.positive.capture binder

/-- Check the already-placed parent against the exact positive source
event before looking at any where witness. Reserve arbitrary placement
provenance for the independent frame producer, not for the witness. -/
def readOriginalPreparedRoot427 {s q} (f : AuthoredBodyFrame393 s q)
    (w : VisiblePointWire427) : Option (OriginalPreparedRoot427 f) := do
  let p ← readVisiblePoint427 s q w
  if declaration : p.positive.decl = f.decl then
    if same : f.decl.inputNames.all
          (fun n => captureSame427 (f.input n) (p.positive.capture n)) = true then
      pure ⟨p,declaration,fun n present => capture_same427 (List.all_eq_true.mp same n present)⟩
    else none
  else none

theorem actual_prepared_root_keeps_original_input_capture427 {s q f w p}
    (_ : readOriginalPreparedRoot427 (s:=s) (q:=q) f w = some p)
    (checked : GeneralDeclarations.DeclarationChecked (authoredRegistry s.current).constructors
      (authoredRegistry s.current).roles f.decl) {k} (cl : OriginalRecordArgument427 f k 0) :
    f.names.input cl.binder = p.visiblePoint.positive.capture cl.binder := by
  unfold AuthoredBodyFrame393.names GeneralDeclarativeFrameReadback325.sourceNames
  exact (GeneralDeclarativeProducedNames325.exact_input checked cl.inHead).trans
    (p.lexical _ cl.inHead)

private def noLeafEmission427 : Placement := ⟨fun _ _ => point 0,fun _ _ => 0⟩

structure ReviewedWhereAt427 {s q} (f : AuthoredBodyFrame393 s q) (ordinal : Nat) where
  original : OriginalRecordArgument427 f ordinal 0
  actual : VisiblePoint427 s original.child
  leaf : actual.positive.decl.requirements = []
  noOutputs : original.child.demand.outputs = []
  header : GeneralDeclarations.DeclarationChecked (authoredRegistry s.current).constructors
    (authoredRegistry s.current).roles actual.positive.decl

def ReviewedWhereAt427.dictionary {s q f k}
    (p : ReviewedWhereAt427 (s:=s) (q:=q) f k) : Dictionary :=
  .node p.actual.positive.decl.id []

theorem reviewed_where_has_exact_same_model_leaf427 {s q f k} (atlas : B6OccurrenceAtlas401 s)
    (p : ReviewedWhereAt427 (s:=s) (q:=q) f k) (m : Model) (fit : Fits s m) :
    I72.DictionaryEvidence ⟨s,atlas⟩ m p.original.child p.dictionary := by
  let a := p.actual.positive
  let f' : AuthoredBodyFrame393 s p.original.child := ⟨a.ordinal,a.decl,a.fromRegistry,a.visibleDecl,
    noLeafEmission427,a.capture⟩
  let e := originalNoOutputEvent427 atlas f' a.head p.noOutputs
  have empty : e.kids = [] := by
    simp [e,originalNoOutputEvent427,I72.Event.kids,frameWhereKids400,children,
      AuthoredBodyFrame393.clauses,f',a,p.leaf]
  have fact : I72.LocalMeaning m e := by
    refine ⟨source_head_sound a.head m fit,?_⟩
    intro i; exact Fin.elim0 (Fin.cast (congrArg List.length p.noOutputs) i)
  have kept : I72.FixedTargets m e := by
    intro i; exact Fin.elim0 (Fin.cast (congrArg List.length p.noOutputs) i)
  exact .node e fact kept (empty.symm ▸ .nil)

structure ReviewedWhereWire427 where
  originalRow : Nat
  leaf : VisiblePointWire427

def readReviewedWhereAt427 {s q} (f : AuthoredBodyFrame393 s q)
    (ordinal : Nat) (w : ReviewedWhereWire427) : Option (ReviewedWhereAt427 f ordinal) := do
  let a ← readOriginalRecordArgument427 f ⟨ordinal,0,w.originalRow⟩
  let leaf ← readVisiblePoint427 s a.child w.leaf
  let d := leaf.positive.decl
  let registry := authoredRegistry s.current
  let orig := s.current.environment.source
  if empty : d.requirements = [] then
    if noOut : a.child.demand.outputs = [] then
      if header : GeneralDeclarativeWitnessHeader349.checksDecl orig d = true then
        if all : GeneralSourceMetadataDeclarations291.explicitCheck
            registry (GeneralSourceMetadataRows291.interpretation orig.snapshot) = true then
          let cov := (GeneralSourceMetadataDeclarations291.explicit_exact _ _).mp all
          pure ⟨a,leaf,empty,noOut,GeneralDeclarativeWitnessHeader349.decl_checked
            (cov d (List.mem_of_getElem? leaf.positive.fromRegistry)) header⟩
        else none
      else none
    else none
  else none

/-- Independent of installer and checker dispatch. The list index is the
actual original source-order list; callers can provide physical witness
data but cannot provide a replacement order or a semantic child answer. -/
inductive ReviewedForest427 {s q} (f : AuthoredBodyFrame393 s q) : List Nat → Type where
  | nil : ReviewedForest427 f []
  | cons : ReviewedWhereAt427 f k → ReviewedForest427 f ks → ReviewedForest427 f (k::ks)

def ReviewedForest427.requests {s q f ks}
    (v : ReviewedForest427 (s:=s) (q:=q) f ks) : List Request :=
  match v with
  | .nil => []
  | .cons a tail => a.original.child :: tail.requests

def ReviewedForest427.dictionaries {s q f ks}
    (v : ReviewedForest427 (s:=s) (q:=q) f ks) : List Dictionary :=
  match v with
  | .nil => []
  | .cons a tail => a.dictionary :: tail.dictionaries

def ReviewedForest427.originalNames {s q f ks}
    (v : ReviewedForest427 (s:=s) (q:=q) f ks) : List Nat :=
  match v with
  | .nil => []
  | .cons a tail => a.original.name :: tail.originalNames

theorem reviewed_source_order_get427 {s q f ks}
    (v : ReviewedForest427 (s:=s) (q:=q) f ks) (n : Nat) :
    v.requests[n]? = (ks[n]?).bind (fun k => (frameWhereKids400 f)[k]?) := by
  induction v generalizing n with
  | nil => simp [ReviewedForest427.requests]
  | cons a tail ih =>
    cases n with
    | zero => simpa [ReviewedForest427.requests] using
        (structural_where_keeps_original_child_at_ordinal427 a.original).symm
    | succ n => exact ih n

theorem reviewed_source_order_is_entire_original_where427 {s q f}
    (v : ReviewedForest427 (s:=s) (q:=q) f (List.range f.decl.requirements.length)) :
    v.requests = frameWhereKids400 f := by
  apply List.ext_getElem?
  intro i; rw [reviewed_source_order_get427]
  by_cases inside : i < f.decl.requirements.length
  · rw [List.getElem?_range inside]; rfl
  · have bigger : f.decl.requirements.length ≤ i := Nat.le_of_not_lt inside
    have sourceAbsent : (List.range f.decl.requirements.length)[i]? = none :=
      List.getElem?_eq_none (by simpa using bigger)
    have callAbsent : (frameWhereKids400 f)[i]? = none :=
      List.getElem?_eq_none (by simpa [frameWhereKids400,children,AuthoredBodyFrame393.clauses] using bigger)
    simp [sourceAbsent,callAbsent]

def readReviewedWhereSuffix427 {s q} (f : AuthoredBodyFrame393 s q) (start : Nat)
    : (w : List ReviewedWhereWire427) → Option (ReviewedForest427 f (List.range' start w.length))
  | [] => some .nil
  | next :: rest => do
    let first ← readReviewedWhereAt427 f start next
    let tail ← readReviewedWhereSuffix427 f (start+1) rest
    pure (by simpa [List.range'_succ] using ReviewedForest427.cons first tail)

def readReviewedWhere427 {s q} (f : AuthoredBodyFrame393 s q) (w : List ReviewedWhereWire427) :
    Option (ReviewedForest427 f (List.range f.decl.requirements.length)) :=
  if exactLength : w.length = f.decl.requirements.length then
    by simpa only [List.range_eq_range',exactLength] using readReviewedWhereSuffix427 f 0 w
  else none

theorem reviewed_source_order_and_same_model_forest427 {s q f ks}
    (v : ReviewedForest427 (s:=s) (q:=q) f ks) (atlas : B6OccurrenceAtlas401 s)
    (m : Model) (fit : Fits s m) :
    I72.DictionaryEvidenceForest ⟨s,atlas⟩ m v.requests v.dictionaries := by
  induction v with
  | nil => exact .nil
  | cons a rest ih => exact .cons (reviewed_where_has_exact_same_model_leaf427 atlas a m fit) ih

theorem reviewed_original_where_forest_has_same_model_parent427 {s q f w atlas v}
    (h : SourceHead s q f.decl) (empty : q.demand.outputs = [])
    (_ : readReviewedWhere427 (s:=s) (q:=q) f w = some v)
    (m : Model) (fit : Fits s m) :
    I72.DictionaryEvidence ⟨s,atlas⟩ m q (.node f.decl.id v.dictionaries) := by
  let e := originalNoOutputEvent427 atlas f h empty
  have semantics : I72.LocalMeaning m e := by
    refine ⟨source_head_sound h m fit,?_⟩
    intro i; exact Fin.elim0 (Fin.cast (congrArg List.length empty) i)
  have targets : I72.FixedTargets m e := by
    intro i; exact Fin.elim0 (Fin.cast (congrArg List.length empty) i)
  refine .node e semantics targets ?_
  change I72.DictionaryEvidenceForest ⟨s,atlas⟩ m (frameWhereKids400 f) v.dictionaries
  rw [← reviewed_source_order_is_entire_original_where427 v]
  exact reviewed_source_order_and_same_model_forest427 v atlas m fit

end Yulang.GeneralDeclarativeI65.StructuralWhere427

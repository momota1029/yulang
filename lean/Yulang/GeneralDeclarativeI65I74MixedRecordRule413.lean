import Yulang.GeneralDeclarativeI65I74RecordConservative412

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.MixedRecord413
open GeneralDeclarativeI65
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Declaration DeclarationChecked)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralDeclarativeWitnessDeclaredState357 (point authoredRegistry)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeGraphRows321 (observed structural literal_head)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeInspect321 (Visit fieldPatterns PatternK2 variable_has_no_visit)
open CommonRoleOutermostResolver (All₂)
open RecordK2412 (closedHead412 closedWhere412 query412 recordInput412 recordRow412)

structure ActualOuterRecord (s : I72.State) (q : I72.Request) where
  root : Nat
  box : Nat
  site : Nat
  args : q.demand.arguments = [point root]
  noOutputs : q.demand.outputs = []
  role : ∃ r ∈ s.core.current.environment.source.roles.rows, r.role = q.demand.role
  roleTable : GeneralSourceMetadataRoles291.Valid s.core.current.environment.source.roles
  origin : Origin
  actualOrigin : origin ∈ s.core.origins
  originalSlot : origin.slot = root
  originalTerm : origin.endpoint = recordInput412 box site
  rawRow : recordRow412 root box site ∈ s.core.current.ordinary.equations

def bindingQuery413 (box binder : Nat) : Expr :=
  .record box (.variable binder) (.primitive .emptyRecord [])

structure PlainCandidate {s q} (outer : ActualOuterRecord s q) (row : Declaration) where
  binder : Nat
  empty : Nat
  head : row.head = [closedWhere412 outer.box empty binder]
  noWhere : row.requirements = []
  covered : DeclarationCovered s.core.current.environment row
  checked : DeclarationChecked (authoredRegistry s.core.current).constructors
    (authoredRegistry s.core.current).roles row
  compiled : translate (authoredRegistry s.core.current).constructors
    (interpretation s.core.current.environment.source.snapshot)
    (closedWhere412 outer.box empty binder) = some (bindingQuery413 outer.box binder)

structure NestedCandidate {s q} (outer : ActualOuterRecord s q) (row : Declaration) where
  nextField : Nat
  binder : Nat
  empty : Nat
  head : row.head = [closedHead412 outer.box nextField empty binder]
  noWhere : row.requirements = []
  covered : DeclarationCovered s.core.current.environment row
  checked : DeclarationChecked (authoredRegistry s.core.current).constructors
    (authoredRegistry s.core.current).roles row
  compiled : translate (authoredRegistry s.core.current).constructors
    (interpretation s.core.current.environment.source.snapshot)
    (normalize (closedHead412 outer.box nextField empty binder)) =
      some (query412 outer.box nextField binder)

def plainCapture413 {s q d} {o : ActualOuterRecord s q} (r : PlainCandidate o d) (n : Nat) :
    GeneralDeclarativeWhere319.Capture :=
  if n = r.binder then point o.site else emptyCapture403

/-- The competing candidate really has a complete, independent head match.
A binder captures the original operand; this proof does not inspect it. -/
def PlainCandidate.matches {s q d} {o : ActualOuterRecord s q} (r : PlainCandidate o d) :
    SourceHead s.core q d := by
  refine .ordered (plainCapture413 r) ?_
  rw [o.args,r.head]
  refine .cons (.ordinary ?_) .nil
  refine ⟨⟨.refl _, .refl _⟩, bindingQuery413 o.box r.binder,r.compiled,.direct (.whole ?_)⟩
  simpa [bindingQuery413,GeneralDeclarativeSubstitution320.logical,
    GeneralDeclarativeSubstitution320.logicals,plainCapture413,point,GeneralDeclarativeHead320.byMode,
    recordRow412] using o.rawRow

theorem plain_record_candidate_does_not_enter_payload413 {view : GeneralDeclarativeK2Graph321.View}
    {root box bind site : Nat} (visited : Visit view root (bindingQuery413 box bind) site) :
    site = root := by
  change Visit view root (.record box (.variable bind) (.primitive .emptyRecord [])) site at visited
  cases visited with
  | here => rfl
  | field _ _ found rest =>
    change _ ∈ [(box, Expr.variable bind)] at found
    rw [(Prod.mk.inj (List.mem_singleton.mp found)).2] at rest
    exact False.elim (variable_has_no_visit rest)

theorem actual_nested_candidate_enters413 {s q d} {o : ActualOuterRecord s q}
    (r : NestedCandidate o d) :
    Visit (structural s.core.current.ordinary) o.root (query412 o.box r.nextField r.binder) o.site := by
  have literal := literal_head o.rawRow
    (show GeneralDeclarativeGraphRows321.shapeOf (recordRow412 o.root o.box o.site).right =
      some (.record [(o.box,o.site)]) from rfl)
  unfold query412
  exact .field (query := .record r.nextField (.variable r.binder) (.primitive .emptyRecord []))
    literal List.mem_cons_self List.mem_cons_self (.here .record)

inductive PlainTape {s q} (o : ActualOuterRecord s q) : List Declaration → Type where
  | nil : PlainTape o []
  | cons : PlainCandidate o d → PlainTape o ds → PlainTape o (d :: ds)

/-- One real nested record and every other visible row checked as a
genuine binding-only match. A picked subset is not a tape. -/
inductive MixedTape {s q} (o : ActualOuterRecord s q) : List Declaration → Type where
  | opens : NestedCandidate o d → PlainTape o ds → MixedTape o (d :: ds)
  | next : PlainCandidate o d → MixedTape o ds → MixedTape o (d :: ds)

structure Opening {s q} (o : ActualOuterRecord s q) (rows : List Declaration) where
  ordinal : Nat
  decl : Declaration
  fromOriginalList : rows[ordinal]? = some decl
  source : NestedCandidate o decl

def MixedTape.opening {s q} {o : ActualOuterRecord s q} {rows} :
    MixedTape o rows → Opening o rows
  | .opens src _ => ⟨0,_,rfl,src⟩
  | .next _ tail =>
    let found := tail.opening
    ⟨found.ordinal+1,found.decl,by simpa using found.fromOriginalList,found.source⟩

theorem PlainTape.each_has_match {s q} {o : ActualOuterRecord s q} {rows}
    (t : PlainTape o rows) (d : Declaration) (here : d ∈ rows) :
    Nonempty (SourceHead s.core q d) := by
  induction t with
  | nil => cases here
  | cons a _ rec =>
    rcases List.mem_cons.mp here with same|later
    · cases same
      exact ⟨a.matches⟩
    · exact rec later

theorem MixedTape.each_unopened_has_match {s q} {o : ActualOuterRecord s q} {rows}
    (t : MixedTape o rows) (i : Nat) {d : Declaration}
    (here : rows[i]? = some d) (other : i ≠ t.opening.ordinal) :
    Nonempty (SourceHead s.core q d) := by
  induction t generalizing i with
  | opens _ rest =>
    cases i with
    | zero => exact (other rfl).elim
    | succ i => exact rest.each_has_match _ (List.mem_of_getElem? (by simpa using here))
  | @next first tail read all ih =>
    cases i with
    | zero =>
      have equal : first = d := Option.some.inj here
      exact ⟨equal ▸ read.matches⟩
    | succ i =>
      apply ih i (by simpa using here)
      intro equal
      apply other
      change i+1 = all.opening.ordinal+1
      rw [equal]

structure MixedRecordRejection (s : I72.State) (q : I72.Request) where
  outer : ActualOuterRecord s q
  tape : MixedTape outer (visible s.core q)
  rivalsExist : 2 ≤ (visible s.core q).length
  distinctIds : ((visible s.core q).map Declaration.id).Nodup
  actualCycle : AliasCycle s.core.current.ordinary (observed s.core.current.ordinary) outer.site

theorem matched_rival_is_real413 {s q} (shape : MixedRecordRejection s q)
    (i : Nat) {row : Declaration} (seen : (visible s.core q)[i]? = some row)
    (competes : i ≠ shape.tape.opening.ordinal) : Nonempty (SourceHead s.core q row) :=
  shape.tape.each_unopened_has_match i seen competes

theorem full_scan_has_actual_K2_413 {s q} (shape : MixedRecordRejection s q) :
    PatternK2 s.core.current.ordinary shape.outer.root
      (query412 shape.outer.box shape.tape.opening.source.nextField shape.tape.opening.source.binder) :=
  ⟨shape.outer.site,actual_nested_candidate_enters413 shape.tape.opening.source,shape.actualCycle⟩

def mixedRecordLocal413 : SourcePrimitives where
  elected := fun _ _ _ _ => False
  other := fun s q v needs => needs = [] ∧ v = .rejected ∧ Nonempty (MixedRecordRejection s q)

def R5 : SourcePrimitives where
  elected := RecordK2412.R4.elected
  other := fun s q v needs => RecordK2412.R4.other s q v needs ∨ mixedRecordLocal413.other s q v needs

theorem dictionary_sound_R5 : DictionarySound R5 := by
  intro s q d chosen m fit
  obtain ⟨t,e,⟨trace⟩,summary⟩ := chosen
  let nodeOf : S10 R5 := fun s q event needs _ localRule _ =>
    (WhereCycle411.R3_local_evidence411 s q event needs localRule).1
  let keep : KeepsFixedOutputs404 R5 := fun s q event needs localRule =>
    (WhereCycle411.R3_local_evidence411 s q event needs localRule).2
  obtain ⟨⟨tree⟩,shape⟩ := (lower_selected_at_exact_trace _ s (nodeOf s)).tree trace summary
  have aligned : CanonicalReplay tree tree.ledger := ⟨rfl,shape,rfl⟩
  have mTree := general_tree_meaning_from_local _ semantic_node_in_signature s q t e d trace tree m fit
  have meaning := typed_replay_keeps_same_event_meaning _ s q t e d trace tree tree.ledger m aligned mTree
  exact exact_ledger_evidence405 tree.ledger m meaning
    (fixed_targets_from_own_elected_events405 keep tree m fit)

end Yulang.GeneralDeclarativeI65.I72.MixedRecord413

import Yulang.GeneralDeclarativeI65I74RawObservationTable471

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471
open RetainedFull445
open PreparedDeclarations463
open LiteralFold471 (SourceGate inputSourceOnly)
open QuotientObservation471 (ConeWire Wire)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open AuthoredInspectQuery456 (AuthoredQuery compileQuery compile_query_exact)
open GeneralDeclarationPatterns (Pattern normalize)
open WrittenPattern460.PhysicalOrigin (Pose exact_original_occurrences)
open GeneralDeclarativeInspect321 (Inspects)
open RecordTraversal455 (termInspects term_inspects_exact455)
open GeneralDeclarativeOrigins321 (restriction from_source)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeNestedIndex332 (ofRows)
open GeneralDeclarativeNestedDecode332 (decode)
open GeneralDeclarativeNestedRun332 (run)
open GeneralDeclarativeNestedSound332 (sound)

structure FieldOriginWire {p : FullProblem} (g : SourceGate p) where
  source : HeadAddress
  originalOrdinal : Nat
  logicalField : Nat
  authoredPath : List Pose
  rawOrdinal : Nat
  token : g.Data

/-- Select a real written field and perform the rooted source read first.
Nothing here assumes either sign of K2 or an equivalent named representative. -/
structure FieldOrigin {p : FullProblem} (g : SourceGate p)
    (gd : CheckedTable p.old.state.core.current) (w : FieldOriginWire g) where
  head : PrecheckedHead gd
  sourceAddress : head.orig.location = w.source
  singleton : visible p.old.state.core p.old.root = [head.orig.declaration]
  exactDeclaration : p.old.state.core.current.environment.source.declarations[w.originalOrdinal]? =
    some head.orig.declaration
  sourcePattern : Pattern
  selectedWritten : WrittenPattern460.PhysicalOrigin.Origin head.orig.original (.field w.logicalField) w.authoredPath sourcePattern
  selectedQuery : Expr
  sourceCompile : AuthoredQuery p.old.state.core (normalize sourcePattern) selectedQuery
  compiledLabel : Label
  compiledChildren : List (Slot × Expr)
  actualHeadQuery : ReadsDescription p.old.state.core head.orig.code compiledLabel compiledChildren
  selectedInQuery : (.field w.logicalField,selectedQuery) ∈ compiledChildren
  sourceNonvariable : Inspects selectedQuery
  row : Equation
  exactRow : p.state.base.core.current.ordinary.equations[w.rawOrdinal]? = some row
  rowAtPoint : row.left = head.orig.capture.lower
  authenticated : g.Authenticates p.root.occurrence w.rawOrdinal row
  rowLabel : Label
  rowChildren : List (Slot × Expr)
  rowObservation : ReadsDescription p.old.state.core row.right rowLabel rowChildren
  actualPayload : Expr
  borrowedAtField : (.field w.logicalField,actualPayload) ∈ rowChildren

def findPayload (cs : List (Slot × Expr)) (l : Nat) : Option (Slot × Expr) :=
  cs.find? fun c => c.1 == .field l

theorem found_payload_is_exact {cs l key e}
    (h : findPayload cs l = some (key,e)) : key = .field l ∧ (key,e) ∈ cs := by
  have test : (key == .field l) = true :=
    List.find?_some (p := fun c : Slot × Expr => c.1 == .field l) h
  exact ⟨beq_iff_eq.mp test,List.mem_of_find?_eq_some h⟩

def readFieldOrigin {p : FullProblem} (g : SourceGate p)
    (gd : CheckedTable p.old.state.core.current) (w : FieldOriginWire g) :
    Option (FieldOrigin g gd w) := do
  let h ← readPrecheckedHead gd w.source
  let keys := p.old.state.core.current.environment.source.declarations
  if hproof : h.orig.location = w.source ∧
      visible p.old.state.core p.old.root = [h.orig.declaration] ∧ keys[w.originalOrdinal]? = some h.orig.declaration then
    let occurrence := (WrittenPattern460.PhysicalOrigin.children h.orig.original (.field w.logicalField)).find? (fun o => o.1 == w.authoredPath)
    match original : occurrence with
    | none => none
    | some (sourcePos,sourcePattern) =>
      match query : readDescription p.old.state.core h.orig.code with
      | none => none
      | some (queryLabel,queryChildren) =>
        match selected : findPayload queryChildren w.logicalField with
        | none => none
        | some (_queryKey,patternCode) =>
          let raw := p.state.base.core.current.ordinary
          match stored : raw.equations[w.rawOrdinal]? with
          | none => none
          | some row =>
            if yes : row.left = h.orig.capture.lower ∧
                g.verify p.root.occurrence w.rawOrdinal row w.token = true ∧ termInspects patternCode = true then
              match own : readDescription p.old.state.core row.right with
              | none => none
              | some (rowLabel,rowChildren) =>
                match field : findPayload rowChildren w.logicalField with
                | none => none
                | some (_rawKey,payload) =>
                  match decoded : compileQuery p.old.state.core (normalize sourcePattern) with
                  | none => none
                  | some code =>
                    if same : eqExpr code patternCode = true then
                      have path : sourcePos = w.authoredPath := beq_iff_eq.mp
                        (List.find?_some (p := fun x : List Pose × Pattern => x.1 == w.authoredPath) original)
                      have real : WrittenPattern460.PhysicalOrigin.Origin h.orig.original (.field w.logicalField) sourcePos sourcePattern :=
                        (exact_original_occurrences ..).mp (List.mem_of_find?_eq_some original)
                      have qp := found_payload_is_exact selected
                      have rp := found_payload_is_exact field
                      some ⟨h,hproof.1,hproof.2.1,hproof.2.2,sourcePattern,path ▸ real,patternCode,
                        (eq_expr ..).mp same ▸ (compile_query_exact ..).mp decoded,queryLabel,queryChildren,
                        description_exact.mp query,qp.1 ▸ qp.2,(term_inspects_exact455 _).mp yes.2.2,row,
                        stored,yes.1,(g.exact ..).mp ⟨_,yes.2.1⟩,rowLabel,rowChildren,description_exact.mp own,
                        payload,rp.1 ▸ rp.2⟩
                    else none
            else none
  else none

def confirmedAddress {p g gd w} (r : @FieldOrigin p g gd w) : Address :=
  childAddress ⟨.named r.row.left,w.rawOrdinal⟩ (.field w.logicalField,r.actualPayload)

structure SourceTyping {p : FullProblem} {g : SourceGate p} {gd : CheckedTable p.old.state.core.current}
    {w : FieldOriginWire g} (r : FieldOrigin g gd w) where
  uses : List Occurrence
  sourceRecognized :
    translate (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry p.old.state.core.current).constructors
      (GeneralSourceMetadataRows291.interpretation p.old.state.core.current.environment.source.snapshot)
      (normalize r.head.orig.original) = some r.head.orig.code
  rooted : Read ⟨p.state.base.core.current.ordinary.normal,[r.row]⟩ .actual
    (.variable r.head.orig.capture.lower) r.head.orig.code uses
  actualOrdinarySource : r.row ∈ (restriction (inputSourceOnly g)).equations

def readTyping {p g gd w} (r : @FieldOrigin p g gd w) : Option (SourceTyping r) := do
  let orig := r.head.orig
  let f := translate (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry
    p.old.state.core.current).constructors
    (GeneralSourceMetadataRows291.interpretation p.old.state.core.current.environment.source.snapshot)
  match legacy : f (normalize orig.original) with
  | none => none
  | some old =>
    if ok : eqExpr old orig.code = true then
      let target ← decode orig.code
      let view : GeneralDeclarativeHead320.State := ⟨p.state.base.core.current.ordinary.normal,[r.row]⟩
      let index := ofRows (s := view) [r.row] (fun _ found => found)
      match out : run index .actual (.variable orig.capture.lower) target.val with
      | none => none
      | some uses =>
        some ⟨uses,legacy.trans (congrArg some ((eq_expr ..).mp ok)),
          target.property ▸ sound index target.val out,from_source _ (g.source _ _ _ r.authenticated)⟩
    else none

structure CheckedFieldBit where
  occurrence : List Nat
  declarationId : Nat
  originalOrdinal : Nat
  authoredPath : List Pose
  logicalField : Nat
  checked : Bool
  deriving DecidableEq

def readFieldBit {p : FullProblem} (g : SourceGate p) (gd : CheckedTable p.old.state.core.current)
    (w : FieldOriginWire g) (table : GraphTicket n) (i : Fin n)
    (scope : ConeWire n m) (q : Wire m k) : Option CheckedFieldBit := do
  let r ← readFieldOrigin g gd w
  let _ ← readTyping r
  if confirmedAddress r = (table.sites.get i).site then
    let b ← replayObservation p.old.state.core table i scope q
    some ⟨p.root.occurrence,r.head.orig.declaration.id,w.originalOrdinal,w.authoredPath,w.logicalField,b⟩
  else none

open QuotientObservation471 (ExactCone ReturnsUpToEquality cone_replay_sound)
open CommonRoleRegularGraph (Graph)

theorem every_same_full_fit_supports_the_local_input_typing_view
    {p g gd w} (h : @FieldOrigin p g gd w) (m : Model) (fit : FitsFull p.state m) :
    GeneralDeclarativeHead320.Models
      ⟨p.state.base.core.current.ordinary.normal,[h.row]⟩ m.assignment := by
  refine ⟨fit.1.1.1.1,?_⟩
  intro row found
  obtain rfl := List.mem_singleton.mp found
  exact fit.1.1.1.2 _ (List.mem_of_getElem? h.exactRow)

theorem read_field_bit_reflects_exact_selected_type_path_and_cycle_or_safety
    {p : FullProblem} {g : SourceGate p} {gd : CheckedTable p.old.state.core.current}
    {w : FieldOriginWire g} {table : GraphTicket n} {i : Fin n}
    {scope : ConeWire n m} {part : Wire m k} {recorded : CheckedFieldBit}
    (ok : readFieldBit g gd w table i scope part = some recorded) :
    ∃ (r : FieldOrigin g gd w) (_t : SourceTyping r) (graph : Graph n),
      readObservationGraph p.old.state.core table = some graph ∧
      ExactCone graph i scope ∧
      confirmedAddress r = (table.sites.get i).site ∧
      recorded.occurrence = p.root.occurrence ∧
      recorded.declarationId = r.head.orig.declaration.id ∧
      recorded.originalOrdinal = w.originalOrdinal ∧
      recorded.authoredPath = w.authoredPath ∧
      recorded.logicalField = w.logicalField ∧
      (recorded.checked = true ↔ ReturnsUpToEquality graph i) ∧
      ∀ m : Model, FitsFull p.state m → GeneralDeclarativeHead320.Models
        ⟨p.state.base.core.current.ordinary.normal,[r.row]⟩ m.assignment := by
  cases origin : readFieldOrigin g gd w with
  | none => simp [readFieldBit,origin,bind,Option.bind] at ok
  | some r =>
    cases typed : readTyping r with
    | none => simp [readFieldBit,origin,typed,bind,Option.bind] at ok
    | some t =>
      by_cases pinned : confirmedAddress r = (table.sites.get i).site
      · cases run : replayObservation p.old.state.core table i scope part with
        | none => simp [readFieldBit,origin,typed,run,bind,Option.bind] at ok
        | some checked =>
          have eq : (⟨p.root.occurrence,r.head.orig.declaration.id,w.originalOrdinal,
            w.authoredPath,w.logicalField,checked⟩ : CheckedFieldBit) = recorded := by
            simpa [readFieldBit,origin,typed,pinned,run,bind,Option.bind] using ok
          subst recorded
          obtain ⟨graph,formed,cone,exacts,_⟩ := observation_solution_has_complete_actual_syntax_cone run
          exact ⟨r,t,graph,formed,cone,pinned,rfl,rfl,rfl,rfl,rfl,exacts,
            every_same_full_fit_supports_the_local_input_typing_view r⟩
      · simp [readFieldBit,origin,typed,pinned,bind,Option.bind] at ok

end Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471
namespace Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarationPatterns (Pattern)
open WrittenPattern460.PhysicalOrigin (Pose atSource literal_occurrence exact_original_occurrences)

theorem no_duplicate_slots_in_a_description {s e label cs}
    (h : ReadsDescription s e label cs) : (cs.map Prod.fst).Nodup := by
  cases h
  case record tail fs l p sem =>
    simp only [RecordEntries,List.map_map]
    change ((sortedFields ((l,p)::fs)).map (Slot.field ∘ Prod.fst)).Nodup
    rw [←List.map_map]
    change ((sortedFields ((l,p)::fs)).map Prod.fst |>.map Slot.field).Pairwise (· ≠ ·)
    rw [List.pairwise_map]
    exact (sorted_labels_are_canonical _).imp (fun gt ne => Nat.ne_of_lt gt (Slot.field.inj ne))
  all_goals simp

theorem unique_payload_lookup {cs : List (Slot × Expr)} {l : Nat} {e : Expr}
    (nd : (cs.map Prod.fst).Nodup) (mem : (.field l,e) ∈ cs) :
    findPayload cs l = some (.field l,e) := by
  induction cs with
  | nil => cases mem
  | cons first rest ih =>
    obtain ⟨key,payload⟩ := first
    rcases List.mem_cons.mp mem with same | later
    · cases same
      simp [findPayload]
    · have nonmatching : key ≠ .field l := by
        intro matchKey
        subst key
        exact (List.nodup_cons.mp nd).1 (List.mem_map.mpr ⟨_,later,rfl⟩)
      simp [findPayload,nonmatching]
      exact ih (List.nodup_cons.mp nd).2 later

theorem source_origin_lookup_is_functional
    {p : Pattern} {label : Nat} {poses : List Pose} {t : Pattern}
    (auth : WrittenPattern460.PhysicalOrigin.Origin p (.field label) poses t) :
    ((WrittenPattern460.PhysicalOrigin.children p (.field label)).find? fun o => o.1 == poses) =
      some (poses,t) := by
  cases got : (WrittenPattern460.PhysicalOrigin.children p (.field label)).find?
      (fun o => o.1 == poses) with
  | none =>
    have found := (exact_original_occurrences ..).mpr auth
    have refuses := (List.find?_eq_none.mp got) (poses,t) found
    exact False.elim (refuses (by simp))
  | some hit =>
    obtain ⟨path,out⟩ := hit
    have same : path = poses := by simpa using List.find?_some got
    subst path
    have aux : WrittenPattern460.PhysicalOrigin.Origin p (.field label) poses out :=
      (exact_original_occurrences ..).mp (List.mem_of_find?_eq_some got)
    have tied : out = t := Option.some.inj ((literal_occurrence aux).symm.trans (literal_occurrence auth))
    subst out
    rfl

end Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471
namespace Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471
open GeneralDeclarativeWitnessLiteral349 (eq_expr)
open PreparedDeclarations463
open RetainedFull445
open LiteralFold471 (SourceGate)
open AuthoredInspectQuery456 (compile_query_exact)
open RecordTraversal455 (term_inspects_exact455)

theorem independent_source_field_origin_replays {p g gd w} (r : @FieldOrigin p g gd w)
    (good : g.verify p.root.occurrence w.rawOrdinal r.row w.token = true) :
    readFieldOrigin g gd w = some r := by
  have anchor := each_prechecked_head_position_replays gd r.head
  rw [r.sourceAddress] at anchor
  have approve : r.head.orig.location = w.source ∧
      visible p.old.state.core p.old.root = [r.head.orig.declaration] ∧
      p.old.state.core.current.environment.source.declarations[w.originalOrdinal]? =
        some r.head.orig.declaration := ⟨r.sourceAddress,r.singleton,r.exactDeclaration⟩
  have origin := source_origin_lookup_is_functional r.selectedWritten
  have lens := description_exact.mpr r.actualHeadQuery
  have fQ := unique_payload_lookup (no_duplicate_slots_in_a_description r.actualHeadQuery) r.selectedInQuery
  have gp := (term_inspects_exact455 _).mpr r.sourceNonvariable
  have rowLens := description_exact.mpr r.rowObservation
  have fR := unique_payload_lookup (no_duplicate_slots_in_a_description r.rowObservation) r.borrowedAtField
  have code := (compile_query_exact ..).mpr r.sourceCompile
  simp only [readFieldOrigin,anchor,bind,Option.bind]
  rw [dite_eq_left approve]
  split
  · rename_i miss
    rw [origin] at miss
    cases miss
  · rename_i sourcePos sourcePattern got
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (got.symm.trans origin))
    split
    · rename_i miss
      rw [lens] at miss
      cases miss
    · rename_i key payloads got
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (got.symm.trans lens))
      split
      · rename_i miss
        rw [fQ] at miss
        cases miss
      · rename_i k e got
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (got.symm.trans fQ))
        split
        · rename_i miss
          rw [r.exactRow] at miss
          cases miss
        · rename_i row got
          have same : row = r.row := Option.some.inj (got.symm.trans r.exactRow)
          subst row
          rw [dite_eq_left ⟨r.rowAtPoint,good,gp⟩]
          split
          · rename_i miss
            rw [rowLens] at miss
            cases miss
          · rename_i key payloads got
            obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (got.symm.trans rowLens))
            split
            · rename_i miss
              rw [fR] at miss
              cases miss
            · rename_i k e got
              obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (got.symm.trans fR))
              split
              · rename_i miss
                rw [code] at miss
                cases miss
              · rename_i e got
                have same : e = r.selectedQuery := Option.some.inj (got.symm.trans code)
                subst e
                rw [dite_eq_left ((eq_expr ..).mpr rfl)]

def FieldOriginWithToken {p g gd w} (r : @FieldOrigin p g gd w) (token : g.Data) :
    FieldOrigin g gd { w with token } :=
  ⟨r.head,r.sourceAddress,r.singleton,r.exactDeclaration,r.sourcePattern,r.selectedWritten,
    r.selectedQuery,r.sourceCompile,r.compiledLabel,r.compiledChildren,r.actualHeadQuery,r.selectedInQuery,
    r.sourceNonvariable,r.row,r.exactRow,r.rowAtPoint,r.authenticated,r.rowLabel,r.rowChildren,
    r.rowObservation,r.actualPayload,r.borrowedAtField⟩

theorem independent_source_authentication_supplies_a_replayable_finite_field_token
    {p g gd w} (r : @FieldOrigin p g gd w) :
    ∃ token, readFieldOrigin g gd {w with token} = some (FieldOriginWithToken r token) := by
  obtain ⟨token,accepted⟩ := (g.exact ..).mpr r.authenticated
  exact ⟨token,independent_source_field_origin_replays _ accepted⟩

end Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471

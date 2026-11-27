import Yulang.GeneralDeclarativeI65I74AliasClassDescription472
import Yulang.GeneralDeclarativeI65I74AttachedInputField472

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ObservationAliasHead472
open ObservationSyntax471
open ObservationRawAlias471 (ClassWire)
open QuotientObservation471 (ConeWire Wire ExactCone ReturnsUpToEquality replayCone cone_replay_sound)
open CommonRoleRegularGraph (Node Graph)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table attach)

structure AliasGraphTicket (n : Nat) where
  positions : GraphTicket n
  classes : Vector ClassWire n
  leafClasses : Catalogue

def logicalOwner (node : NodeTicket) (owner : Nat) : Nat :=
  match node.site with
  | .named n => n
  | .inline _ _ => owner

structure ObservedOldTerm (s : GeneralDeclarativeI65.State) (node : NodeTicket) where
  physical : GeneralDeclarativeHead320.Equation
  chosen : s.current.ordinary.equations[node.rowOrdinal]? = some physical
  exact : ExactOwner s.current.ordinary (logicalOwner node physical.left) node.rowOrdinal
  sameRow : exact.row = physical
  term : Expr
  path : match node.site with
    | .named _ => term = physical.right
    | .inline ordinal steps => ordinal = node.rowOrdinal ∧ steps ≠ [] ∧
        descend s physical.right steps = some term

def readAliasAddress (s : GeneralDeclarativeI65.State) (key : NodeTicket)
    (catalogue : Catalogue) (members : ClassWire) : Option (ObservedOldTerm s key) :=
  match placed : s.current.ordinary.equations[key.rowOrdinal]? with
  | none => none
  | some initial => do
    let exact ← readExactOwner s.current.ordinary catalogue (logicalOwner key initial.left)
      key.rowOrdinal members
    have same : exact.row = initial := Option.some.inj (exact.literal.symm.trans placed)
    match kind : key.site with
    | .named _ => some ⟨initial,placed,exact,same,initial.right,by rw [kind]⟩
    | .inline ordinal steps =>
      if pinned : ordinal = key.rowOrdinal ∧ steps ≠ [] then
        match parsed : descend s initial.right steps with
        | none => none
        | some term => some ⟨initial,placed,exact,same,term,by rw [kind]; exact ⟨pinned.1,pinned.2,parsed⟩⟩
      else none

def readAliasNode (s : GeneralDeclarativeI65.State) (d : AliasGraphTicket n) (i : Fin n) :
    Option (Node n) := do
  let key := d.positions.sites.get i
  let old ← readAliasAddress s key d.leafClasses (d.classes.get i)
  let (label,children) ← readDescription s old.term
  let indices ← children.mapM (fun child => findSite d.positions (childAddress key child))
  codeLabel d.positions.signatures label indices

def allAddressesDistinct (w : GraphTicket n) : Bool :=
  decide (w.signatures.Nodup ∧ (List.ofFn fun i => (w.sites.get i).site).Nodup)

def aliasedObservation (s : GeneralDeclarativeI65.State) (d : AliasGraphTicket n) : Graph n :=
  fun i => (readAliasNode s d i).getD .unresolved

def replayAliasObservation (s : GeneralDeclarativeI65.State) (d : AliasGraphTicket n)
    (i : Fin n) (scope : ConeWire n m) (quotient : Wire m k) : Option Bool :=
  if allAddressesDistinct d.positions then replayCone (aliasedObservation s d) i scope quotient else none

theorem read_alias_node_pins_all_definitions_and_all_actual_children
    {s : GeneralDeclarativeI65.State} {d : AliasGraphTicket n} {i : Fin n} {actual : Node n}
    (ok : readAliasNode s d i = some actual) :
    ∃ (old : ObservedOldTerm s (d.positions.sites.get i)) (label : Label) (inputs : List (Slot × Expr)) (indices : List (Fin n)),
      ReadsDescription s old.term label inputs ∧
      inputs.mapM (fun c => findSite d.positions (childAddress (d.positions.sites.get i) c)) = some indices ∧
      codeLabel d.positions.signatures label indices = some actual := by
  cases recorded : readAliasAddress s (d.positions.sites.get i) d.leafClasses (d.classes.get i) with
  | none => simp [readAliasNode,recorded,bind,Option.bind] at ok
  | some term =>
    cases shape : readDescription s term.term with
    | none => simp [readAliasNode,recorded,shape,bind,Option.bind] at ok
    | some z =>
      obtain ⟨label,inputs⟩ := z
      cases children : inputs.mapM (fun c => findSite d.positions (childAddress (d.positions.sites.get i) c)) with
      | none => simp [readAliasNode,recorded,shape,children,bind,Option.bind] at ok
      | some mapped =>
        exact ⟨term,label,inputs,mapped,description_exact.mp shape,children,
          by simpa [readAliasNode,recorded,shape,children,bind,Option.bind] using ok⟩

theorem aliased_replay_checks_a_complete_actual_cone_without_erasing_owners
    {s : GeneralDeclarativeI65.State} {d : AliasGraphTicket n} {i : Fin n} {scope : ConeWire n m}
    {q : Wire m k} {b : Bool} (result : replayAliasObservation s d i scope q = some b) :
    ExactCone (aliasedObservation s d) i scope ∧
    (b = true ↔ ReturnsUpToEquality (aliasedObservation s d) i) ∧
    ∀ j : Fin m, ∃ (old : ObservedOldTerm s (d.positions.sites.get (QuotientObservation471.embedded scope j)))
      (label : Label) (inputs : List (Slot × Expr)), ReadsDescription s old.term label inputs := by
  unfold replayAliasObservation at result
  split at result
  · obtain ⟨here,replay⟩ := cone_replay_sound result
    refine ⟨here,replay,fun j => ?_⟩
    have defined : aliasedObservation s d (QuotientObservation471.embedded scope j) ≠ .unresolved := by
      rw [here.2.2.2]
      have localKnown := here.2.2.1 j
      cases atNode : QuotientObservation471.cone scope j <;>
        simp_all [QuotientObservation471.projectNode]
    cases emitted : readAliasNode s d (QuotientObservation471.embedded scope j) with
    | none => exact (defined (by simp [aliasedObservation,emitted])).elim
    | some node =>
      obtain ⟨old,label,inputs,_,checked,_,_⟩ := read_alias_node_pins_all_definitions_and_all_actual_children emitted
      exact ⟨old,label,inputs,checked⟩
  · cases result

def readAliasField472 (p : FullProblem) (authored : Table) (gd : CheckedTable p.old.state.core.current)
    (input : AttachedFieldWire472) (d : AliasGraphTicket n) (i : Fin n)
    (scope : ConeWire n m) (q : Wire m k) : Option CheckedFieldBit := do
  let a ← attach p.state.base.core.current.ordinary authored
  let r ← readFieldOrigin (gateFromAttachedAuthor472 (p := p) a) gd (input.atGate a)
  let _ ← readTyping r
  if confirmedAddress r = (d.positions.sites.get i).site then
    let b ← replayAliasObservation p.old.state.core d i scope q
    pure ⟨p.root.occurrence,r.head.orig.declaration.id,input.declarationOrdinal,input.path,input.label,b⟩
  else none

theorem named_observation_reads_the_same_value_in_every_original_fit
    {p : FullProblem} {name ordinal : Nat}
    (actual : ObservedOldTerm p.old.state.core ⟨.named name,ordinal⟩)
    (m : Model) (fit : FitsFull p.state m) :
    CommonNominalFullCarrier.Equivalent (m.assignment name).1
      (GeneralNominalCenteredHeadMatExpressions.value
        (GeneralDeclarativeHead320.environment m.assignment) .actual actual.term) := by
  have exact := every_same_ordinary_fit_interprets_that_actual_owner_at_the_named_point actual.exact
    m.assignment fit.1.1.1
  have atRight : actual.term = actual.physical.right := actual.path
  rw [atRight,←actual.sameRow]
  exact exact

theorem aliased_field_report_keeps_its_original_source_typing_and_scope
    {p : FullProblem} {authored : Table} {gd : CheckedTable p.old.state.core.current}
    {input : AttachedFieldWire472} {d : AliasGraphTicket n} {i : Fin n}
    {scope : ConeWire n m} {q : Wire m k} {report : CheckedFieldBit}
    (read : readAliasField472 p authored gd input d i scope q = some report) :
    ∃ (a : GeneralDeclarativeWitnessOrigins350.Attached p.state.base.core.current.ordinary authored)
      (f : FieldOrigin (gateFromAttachedAuthor472 (p := p) a) gd (input.atGate a))
      (event : SourceTyping f),
      confirmedAddress f = (d.positions.sites.get i).site ∧
      report = ⟨p.root.occurrence,f.head.orig.declaration.id,input.declarationOrdinal,input.path,input.label,
        report.checked⟩ ∧
      (report.checked = true ↔ ReturnsUpToEquality (aliasedObservation p.old.state.core d) i) ∧
      (∃ rebuilt, (∀ m : Model, FitsFull p.state m →
        GeneralDeclarativeRepeatedActual323.eqAt m.assignment (.variable f.head.orig.capture.lower) rebuilt) ∧
        GeneralDeclarativeTermWalk322.Walk .actual rebuilt f.head.orig.code event.uses) := by
  cases attached : attach p.state.base.core.current.ordinary authored with
  | none => simp [readAliasField472,attached,bind,Option.bind] at read
  | some a =>
    cases seen : readFieldOrigin (gateFromAttachedAuthor472 (p := p) a) gd (input.atGate a) with
    | none => simp [readAliasField472,attached,seen,bind,Option.bind] at read
    | some f =>
      cases typed : readTyping f with
      | none => simp [readAliasField472,attached,seen,typed,bind,Option.bind] at read
      | some event =>
        by_cases pinned : confirmedAddress f = (d.positions.sites.get i).site
        · cases run : replayAliasObservation p.old.state.core d i scope q with
          | none => simp [readAliasField472,attached,seen,typed,run,bind,Option.bind] at read
          | some b =>
            have exact : (⟨p.root.occurrence,f.head.orig.declaration.id,input.declarationOrdinal,
              input.path,input.label,b⟩ : CheckedFieldBit) = report := by
              simpa [readAliasField472,attached,seen,typed,run,pinned,bind,Option.bind] using read
            subst report
            exact ⟨a,f,event,pinned,rfl,(aliased_replay_checks_a_complete_actual_cone_without_erasing_owners run).2.1,
              exact_same_source_event_is_meant_by_every_original_fit472 f event⟩
        · simp [readAliasField472,attached,seen,typed,pinned,bind,Option.bind] at read

end Yulang.GeneralDeclarativeI65.I72.ObservationAliasHead472

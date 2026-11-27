import Yulang.GeneralDeclarativeI65I74ObservationSyntax471
import Yulang.GeneralDeclarativeI65I74ObservationCone471
import Yulang.GeneralDeclarativeI65I74LiteralFoldInputTyping471

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeLowerKnown321 (Alias)
open CommonRoleRegularGraph (Graph Node)
open QuotientObservation471

/-- A name is an existing raw slot; an inline point is a lexical location
within an existing row. Inline keys never become ordinary variables. -/
inductive Address where
  | named (slot : Nat)
  | inline (ordinal : Nat) (path : List Slot)
  deriving DecidableEq, Repr

def notFlatAlias (q : Equation) : Bool :=
  match q.right with
  | .variable n => decide (q.left = n)
  | _ => true

def FlatFragment (raw : GeneralDeclarativeHead320.State) : Prop :=
  raw.normal.ordinary = [] ∧ raw.normal.intervals = [] ∧
  (∀ q ∈ raw.equations, notFlatAlias q = true)

def checkFlatFragment (raw : GeneralDeclarativeHead320.State) : Bool :=
  decide (raw.normal.ordinary = [] ∧ raw.normal.intervals = []) &&
    raw.equations.all notFlatAlias

theorem flat_fragment_exact {raw} : checkFlatFragment raw = true ↔ FlatFragment raw := by
  simp [checkFlatFragment,FlatFragment,Bool.and_eq_true,List.all_eq_true,and_assoc]

/-- Current boundary: no nontrivial Alias is discarded by this extraction.
The positive guard is deliberately narrower than the general raw graph. -/
theorem flat_fragment_has_no_alias_between_distinct_names {raw a b}
    (closed : FlatFragment raw) (edge : GeneralDeclarativeLowerKnown321.Alias raw a b) : a = b := by
  have bounds {x y} (bound : Bound raw.normal x y) : x = y := by
    induction bound with
    | interval member => rw [closed.2.1] at member; cases member
    | constraint member => rw [closed.1] at member; cases member
    | refl => rfl
    | trans _ _ l r => exact l.trans r
  induction edge with
  | bounds forward _ => exact bounds forward
  | forward hit => simpa [notFlatAlias] using closed.2.2 _ hit
  | backward hit => exact (of_decide_eq_true (closed.2.2 _ hit)).symm
  | trans _ _ l r => exact l.trans r

def descend (s : GeneralDeclarativeI65.State) (term : Expr) : List Slot → Option Expr
  | [] => some term
  | step::rest => do
    let (_,children) ← readDescription s term
    let child ← children.find? fun child => child.1 == step
    descend s child.2 rest

inductive Descent (s : GeneralDeclarativeI65.State) : Expr → List Slot → Expr → Prop where
  | stop : Descent s e [] e
  | down : ReadsDescription s e label branches → (step,child) ∈ branches →
      Descent s child rest target → Descent s e (step::rest) target

theorem descent_sound (s : GeneralDeclarativeI65.State) (term : Expr) {path target}
    (ran : descend s term path = some target) : Descent s term path target := by
  induction path generalizing term with
  | nil => cases ran; exact .stop
  | cons step rest ih =>
    cases found : readDescription s term with
    | none => simp [descend,found,bind,Option.bind] at ran
    | some data =>
      obtain ⟨label,children⟩ := data
      cases hit : children.find? (fun child => child.1 == step) with
      | none => simp [descend,found,hit,bind,Option.bind] at ran
      | some got =>
        obtain ⟨slot,child⟩ := got
        have name : slot = step := by simpa using List.find?_some hit
        subst slot
        exact .down (description_exact.mp found) (List.mem_of_find?_eq_some hit)
          (ih _ (by simpa [descend,found,hit,bind,Option.bind] using ran))

def isDefinedAt (slot : Nat) (q : Equation) : Bool :=
  (q.left == slot) && match q.right with
  | .variable _ => false
  | _ => true

structure NodeTicket where
  site : Address
  rowOrdinal : Nat
  deriving DecidableEq

/-- An exact existing row for the logical name, or a definite inline
subexpression of the stored row. A name's other constructor definitions
are never ignored by choosing a convenient physical row. -/
def readAddress (s : GeneralDeclarativeI65.State) (node : NodeTicket) : Option Expr := do
  let raw := s.current.ordinary
  let row ← raw.equations[node.rowOrdinal]?
  match node.site with
  | .named n =>
    if isDefinedAt n row && (raw.equations.filter (isDefinedAt n)).length == 1
    then some row.right else none
  | .inline atRow path =>
    if atRow == node.rowOrdinal && !path.isEmpty then descend s row.right path else none

theorem named_address_reads_one_exact_existing_definition
    {s : GeneralDeclarativeI65.State} {n i term}
    (read : readAddress s ⟨.named n,i⟩ = some term) :
    ∃ row, s.current.ordinary.equations[i]? = some row ∧ isDefinedAt n row = true ∧
      (s.current.ordinary.equations.filter (isDefinedAt n)).length = 1 ∧ row.right = term := by
  unfold readAddress at read
  cases find : s.current.ordinary.equations[i]? with
  | none => simp [find,bind,Option.bind] at read
  | some row =>
    have normalized : (if isDefinedAt n row &&
        ((s.current.ordinary.equations.filter (isDefinedAt n)).length == 1) then some row.right else none)
          = some term := by simpa [find,bind,Option.bind] using read
    split at normalized
    · rename_i yes
      obtain ⟨own,one⟩ := Bool.and_eq_true_iff.mp yes
      exact ⟨row,rfl,own,beq_iff_eq.mp one,Option.some.inj normalized⟩
    · cases normalized

theorem inline_address_reads_one_exact_existing_lexical_position
    {s : GeneralDeclarativeI65.State} {atRow i path term}
    (read : readAddress s ⟨.inline atRow path,i⟩ = some term) :
    atRow = i ∧ path ≠ [] ∧ ∃ row, s.current.ordinary.equations[i]? = some row ∧
      Descent s row.right path term := by
  unfold readAddress at read
  cases find : s.current.ordinary.equations[i]? with
  | none => simp [find,bind,Option.bind] at read
  | some row =>
    have normalized : (if (atRow == i) && !path.isEmpty then descend s row.right path else none) =
        some term := by simpa [find,bind,Option.bind] using read
    split at normalized
    · rename_i yes
      obtain ⟨eq,nonempty⟩ := Bool.and_eq_true_iff.mp yes
      exact ⟨beq_iff_eq.mp eq,by simpa using nonempty,row,rfl,descent_sound _ _ normalized⟩
    · cases normalized

def childAddress (node : NodeTicket) (child : Slot × Expr) : Address :=
  match child.2 with
  | .variable existing => .named existing
  | _ =>
    match node.site with
    | .named _ => .inline node.rowOrdinal [child.1]
    | .inline _ prior => .inline node.rowOrdinal (prior ++ [child.1])

structure GraphTicket (n : Nat) where
  sites : Vector NodeTicket n
  signatures : List GeneralNormalizedObservation.Shape

def codeLabel (signature : List GeneralNormalizedObservation.Shape)
    (l : Label) (children : List (Fin n)) : Option (Node n) :=
  match l with
  | .nominal k => some (.nominal k children)
  | .scalar b => some (.scalar (CommonRoleScalarSourceInspection.code b))
  | .structural k => if k ∈ signature then some (.structural (signature.idxOf k) children) else none

def findSite (table : GraphTicket n) (address : Address) : Option (Fin n) :=
  (List.finRange n).find? fun i => (table.sites.get i).site == address

theorem find_site_is_exact {table : GraphTicket n} {addr i} (read : findSite table addr = some i) :
    (table.sites.get i).site = addr := by
  have exact := List.find?_some (p := fun j => (table.sites.get j).site == addr) (a := i) read
  exact beq_iff_eq.mp exact

def readNode (s : GeneralDeclarativeI65.State) (table : GraphTicket n) (i : Fin n) :
    Option (Node n) := do
  let key := table.sites.get i
  let e ← readAddress s key
  let (label,children) ← readDescription s e
  let indices ← children.mapM (fun child => findSite table (childAddress key child))
  codeLabel table.signatures label indices

def readObservationGraph (s : GeneralDeclarativeI65.State) (table : GraphTicket n) :
    Option (Graph n) :=
  if checkFlatFragment s.current.ordinary &&
      decide (table.signatures.Nodup ∧ (List.ofFn fun i => (table.sites.get i).site).Nodup)
  then some (fun i => (readNode s table i).getD .unresolved)
  else none

theorem check_node_is_exact_literal_with_all_successors
    {s : GeneralDeclarativeI65.State} {table : GraphTicket n} {i : Fin n} {actual : Node n} (ok : readNode s table i = some actual) :
    ∃ expr label inputs indices,
      readAddress s (table.sites.get i) = some expr ∧
      ReadsDescription s expr label inputs ∧
      inputs.mapM (fun c => findSite table (childAddress (table.sites.get i) c)) = some indices ∧
      codeLabel table.signatures label indices = some actual := by
  cases resolved : readAddress s (table.sites.get i) with
  | none => simp [readNode,resolved,bind,Option.bind] at ok
  | some e =>
    cases described : readDescription s e with
    | none => simp [readNode,resolved,described,bind,Option.bind] at ok
    | some data =>
      obtain ⟨label,inputs⟩ := data
      cases linked : inputs.mapM (fun c => findSite table (childAddress (table.sites.get i) c)) with
      | none => simp [readNode,resolved,described,linked,bind,Option.bind] at ok
      | some values =>
        exact ⟨e,label,inputs,values,rfl,description_exact.mp described,linked,
          by simpa [readNode,resolved,described,linked,bind,Option.bind] using ok⟩

theorem valid_graph_with_resolved_head_is_pinned_to_actual_input_row
    {s : GeneralDeclarativeI65.State} {table : GraphTicket n} {g : Graph n} {i : Fin n} (issued : readObservationGraph s table = some g)
    (seen : g i ≠ .unresolved) :
    FlatFragment s.current.ordinary ∧
    (List.ofFn fun i => (table.sites.get i).site).Nodup ∧
    ∃ actual, readNode s table i = some actual ∧ g i = actual := by
  unfold readObservationGraph at issued
  split at issued
  · rename_i gates
    obtain ⟨flat,dedup⟩ := Bool.and_eq_true_iff.mp gates
    have uniq := of_decide_eq_true dedup
    obtain rfl : (fun i => (readNode s table i).getD .unresolved) = g := Option.some.inj issued
    cases row : readNode s table i with
    | none => exact (seen (by simp [row])).elim
    | some actual => exact ⟨flat_fragment_exact.mp flat,uniq.2,actual,rfl,by simp [row]⟩
  · cases issued

theorem node_encoding_never_collides_on_distinct_structural_signatures
    {signatures : List GeneralNormalizedObservation.Shape} {a b : GeneralNormalizedObservation.Shape}
    (ha : a ∈ signatures) (hb : b ∈ signatures)
    (same : signatures.idxOf a = signatures.idxOf b) : a = b := by
  have left := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr ha)
  have right := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hb)
  exact left.symm.trans (by simpa only [same] using right)

def replayObservation (s : GeneralDeclarativeI65.State) (table : GraphTicket n)
    (i : Fin n) (scope : ConeWire n m) (partition : QuotientObservation471.Wire m k) : Option Bool := do
  let graph ← readObservationGraph s table
  replayCone graph i scope partition

/-- Any positive or safe answer comes from a scope whose every observed
node really reads its exact syntax and every ordered child. A missing
configured address is unresolved, never converted into a safe answer. -/
theorem observation_solution_has_complete_actual_syntax_cone
    {s : GeneralDeclarativeI65.State} {table : GraphTicket n} {i : Fin n}
    {scope : ConeWire n m} {partition : QuotientObservation471.Wire m k} {b : Bool}
    (read : replayObservation s table i scope partition = some b) :
    ∃ graph, readObservationGraph s table = some graph ∧
      ExactCone graph i scope ∧
      (b = true ↔ ReturnsUpToEquality graph i) ∧
      ∀ q : Fin m, ∃ expr label inputs indices,
        readAddress s (table.sites.get (embedded scope q)) = some expr ∧
        ReadsDescription s expr label inputs ∧
        inputs.mapM (fun c => findSite table (childAddress (table.sites.get (embedded scope q)) c)) =
          some indices ∧
        codeLabel table.signatures label indices = some (graph (embedded scope q)) := by
  cases out : readObservationGraph s table with
  | none => simp [replayObservation,out,bind,Option.bind] at read
  | some graph =>
    have ok : replayCone graph i scope partition = some b := by
      simpa [replayObservation,out,bind,Option.bind] using read
    obtain ⟨checked,truth⟩ := cone_replay_sound ok
    refine ⟨graph,rfl,checked,truth,fun q => ?_⟩
    have notUnknown : graph (embedded scope q) ≠ .unresolved := by
      rw [checked.2.2.2]
      have resolved := checked.2.2.1 q
      cases t : cone scope q <;> simp_all [projectNode]
    obtain ⟨_,_,_,picked,data⟩ := valid_graph_with_resolved_head_is_pinned_to_actual_input_row out notUnknown
    rw [data]
    exact check_node_is_exact_literal_with_all_successors picked

open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open LiteralFold471 (SourceGate SourceWire SourceReceipt SourceReport InputTypingEvent
  readSameInputTyping reportOfSource)

inductive ObservedSite where
  | argument
  | field
  deriving DecidableEq

def receiptSite {p g tab w} (r : @SourceReceipt p g tab w) : ObservedSite → Address
  | .argument => .named r.field.folded.owner.left
  | .field => .inline w.field.physical.ownerOrdinal [.field r.field.folded.field]

structure ClassifiedSite where
  report : SourceReport
  site : ObservedSite
  cyclic : Bool
  deriving DecidableEq

/-- Replay the exact already authorized source event. The actual source
occurrence picks the observed point; the wire cannot substitute another
equal-looking field or a cyclic named child. -/
def readTypedObservation {p : FullProblem} (g : SourceGate p)
    (gd : CheckedTable p.old.state.core.current) (input : SourceWire g)
    (site : ObservedSite) (table : GraphTicket n) (i : Fin n)
    (scope : ConeWire n m) (partition : QuotientObservation471.Wire m k) : Option ClassifiedSite := do
  let ⟨r,_typing⟩ ← readSameInputTyping g gd input
  if receiptSite r site = (table.sites.get i).site then
    let b ← replayObservation p.old.state.core table i scope partition
    pure ⟨reportOfSource r,site,b⟩
  else none

theorem typed_observation_cannot_substitute_the_reported_source_site
    {p : FullProblem} {g : SourceGate p} {gd : CheckedTable p.old.state.core.current}
    {input : SourceWire g} {site : ObservedSite} {table : GraphTicket n} {i : Fin n}
    {scope : ConeWire n m} {partition : QuotientObservation471.Wire m k} {packet : ClassifiedSite}
    (read : readTypedObservation g gd input site table i scope partition = some packet) :
    ∃ (r : SourceReceipt g gd input) (typing : InputTypingEvent r),
      readSameInputTyping g gd input = some ⟨r,typing⟩ ∧
      receiptSite r site = (table.sites.get i).site ∧
      packet.report = reportOfSource r ∧ packet.site = site ∧
      replayObservation p.old.state.core table i scope partition = some packet.cyclic := by
  cases givenTyping : readSameInputTyping g gd input with
  | none => simp [readTypedObservation,givenTyping,bind,Option.bind] at read
  | some res =>
    obtain ⟨r,t⟩ := res
    by_cases same : receiptSite r site = (table.sites.get i).site
    · cases replay : replayObservation p.old.state.core table i scope partition with
      | none => simp [readTypedObservation,givenTyping,replay,bind,Option.bind] at read
      | some bit =>
        have exact : (⟨reportOfSource r,site,bit⟩ : ClassifiedSite) = packet := by
          simpa [readTypedObservation,givenTyping,same,replay,bind,Option.bind] using read
        subst packet
        exact ⟨r,t,rfl,same,rfl,rfl,rfl⟩
    · simp [readTypedObservation,givenTyping,same,bind,Option.bind] at read

end Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471

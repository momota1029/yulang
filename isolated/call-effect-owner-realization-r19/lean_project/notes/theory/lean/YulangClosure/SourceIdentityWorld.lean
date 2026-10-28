import YulangClosure.NativeClosureEnvironment
import YulangClosure.Contracts

/-!
Concrete current-world actions of the identity's post-Force suffix. These are
the native immutable-cell, Name/Observe receipt, and owned invocation-return
equations, not a replacement definition of original ValueMem or JointWF.

The arbitrary `V` and `ViewData` fields retain the value payload and all view
metadata; `Rest` carries additional fields untouched by these represented
actions. This is a world projection, not the whole native machine. A Name
dispatch result is explicit: native dispatch_name may change that field and
its separate dictionary-machine store, which is not represented here. Active order
is represented innermost first (the reverse of the native Vec). Historical
receipts retain their original owner after that owner's invocation exits.

AllInstalled is only the all-installed-binding conjunct of PhiW. Its predicate
may be the original candidate-relative value/carrier certificate at a fixed
live event. It is not complete world validity, and no theorem below assumes or
concludes full P_F, the declared-hole interpretation, or inference soundness.
-/
namespace YulangClosure.SourceIdentityWorld

open NativeClosureEnvironment

inductive Owner where
  | moduleRun
  | invocation (id : Nat)
  deriving DecidableEq

inductive Entry where
  | value
  | computation
  deriving DecidableEq

structure Received (V : Type) where
  value : V
  interface : Entry
  view : Nat
  dispatch : Option Nat

def Received.asValue (p : Received V) : Received V :=
  { p with interface := .value }

def Received.atName (p : Received V) (dispatch : Option Nat) : Received V :=
  { p with dispatch := dispatch }

theorem asValue_eq {p : Received V} (h : p.interface = .value) : p.asValue = p := by
  cases p
  simp_all [Received.asValue]

structure View (V ViewData : Type) where
  value : V
  data : ViewData

structure Receipt (K Site : Type) where
  owner : Owner
  view : Nat
  site : Site
  formal : Option K

structure Receiving (K V ViewData Site : Type) where
  views : Store (View V ViewData)
  receipts : Store (Receipt K Site)
  index : (Owner × Nat × Option K) → Option Nat

/-- The actual receipt insertion: append one full record and update only its
original owner/view/formal key. Views are not rewritten by this operation. -/
def Receiving.record [DecidableEq K] (r : Receiving K V ViewData Site)
    (owner : Owner) (view : Nat) (site : Site) (formal : Option K) :
    Receiving K V ViewData Site :=
  { r with
    receipts := r.receipts.push ⟨owner, view, site, formal⟩
    index := fun key =>
      if key = (owner, view, formal) then some r.receipts.size else r.index key }

def Matches (r : Receiving K V ViewData Site) (p : Received V) : Prop :=
  ∃ view, r.views.cell p.view = some view ∧ view.value = p.value

/-- Every already installed row is covered, including unrelated imported and
retained bindings. Empty/uninitialized native cells assert no certificate. -/
def AllInstalled (P : Nat → V → Prop) (s : Store V) : Prop :=
  ∀ i value, i < s.size → s.cell i = some value → P i value

theorem allInstalled_push {s : Store V} {P : Nat → V → Prop}
    (old : AllInstalled P s) {value : V} (new : P s.size value) :
    AllInstalled P (s.push value) := by
  intro i p hi hp
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | heq
  · exact old i p hlt ((push_old s value i hlt).symm.trans hp)
  · subst i
    have same : value = p := Option.some.inj ((push_current s value).symm.trans hp)
    simpa only [same] using new

/-- Apply the independent hereditary action to every existing cell at one
common event. This does not assert that any arbitrary event is compatible. -/
theorem allInstalled_restrict {s : Store V} {P Q : Nat → V → Prop}
    (old : AllInstalled P s)
    (restriction : ∀ i value, i < s.size → s.cell i = some value →
      P i value → Q i value) : AllInstalled Q s := by
  intro i value hi hv
  exact restriction i value hi hv (old i value hi hv)

theorem receipt_new [DecidableEq K] (r : Receiving K V ViewData Site)
    (owner : Owner) (view : Nat) (site : Site) (formal : Option K) :
    (r.record owner view site formal).receipts.cell r.receipts.size =
      some ⟨owner, view, site, formal⟩ := push_current _ _

theorem receipt_old [DecidableEq K] (r : Receiving K V ViewData Site)
    (owner : Owner) (view : Nat) (site : Site) (formal : Option K)
    (i : Nat) (hi : i < r.receipts.size) :
    (r.record owner view site formal).receipts.cell i = r.receipts.cell i :=
  push_old _ _ _ hi

theorem receipt_index [DecidableEq K] (r : Receiving K V ViewData Site)
    (owner : Owner) (view : Nat) (site : Site) (formal : Option K) :
    (r.record owner view site formal).index (owner, view, formal) =
      some r.receipts.size := by simp [Receiving.record]

theorem receipt_other_index [DecidableEq K] (r : Receiving K V ViewData Site)
    (owner : Owner) (view : Nat) (site : Site) (formal : Option K)
    (key : Owner × Nat × Option K) (hne : key ≠ (owner, view, formal)) :
    (r.record owner view site formal).index key = r.index key := by
  simp [Receiving.record, hne]

theorem receipt_matches [DecidableEq K] (r : Receiving K V ViewData Site)
    (owner : Owner) (view : Nat) (site : Site) (formal : Option K)
    (p : Received V) : Matches (r.record owner view site formal) p ↔ Matches r p :=
  Iff.rfl

structure Invocation (Site : Type) where
  call : Site
  provider : Site
  active : Bool

structure Control (Site : Type) where
  invocations : Store (Invocation Site)
  /-- Reverse of the native outer-to-inner active_receivers vector. -/
  active : List Nat
  current : Owner

def deactivate (s : Store (Invocation Site)) (id : Nat)
    (invocation : Invocation Site) : Store (Invocation Site) :=
  { s with cell := fun i =>
      if i = id then some { invocation with active := false } else s.cell i }

/-- Only the independent raw owned-return checks are performed here. In
particular a historical receipt is not an active-owner certificate. -/
def Control.leave (c : Control Site) (id : Nat) (previous : Owner) :
    Option (Control Site) :=
  if c.current = .invocation id then
    match c.active, c.invocations.cell id with
    | top :: rest, some invocation =>
        if top = id ∧ invocation.active = true then
          some ⟨deactivate c.invocations id invocation, rest, previous⟩
        else none
    | _, _ => none
  else none

theorem leave_success {c : Control Site} {id : Nat} {previous : Owner}
    {rest : List Nat} {invocation : Invocation Site}
    (current : c.current = .invocation id) (stack : c.active = id :: rest)
    (found : c.invocations.cell id = some invocation) (live : invocation.active = true) :
    c.leave id previous =
      some ⟨deactivate c.invocations id invocation, rest, previous⟩ := by
  simp [Control.leave, current, stack, found, live]

theorem deactivate_current (s : Store (Invocation Site)) (id : Nat)
    (invocation : Invocation Site) :
    (deactivate s id invocation).cell id =
      some { invocation with active := false } := by simp [deactivate]

theorem deactivate_other (s : Store (Invocation Site)) (id other : Nat)
    (invocation : Invocation Site) (hne : other ≠ id) :
    (deactivate s id invocation).cell other = s.cell other := by
  simp [deactivate, hne]

def OwnerActive (c : Control Site) : Owner → Prop
  | .moduleRun => True
  | .invocation id => ∃ invocation,
      c.invocations.cell id = some invocation ∧ invocation.active = true

/-- A concrete control invariant, weaker than original JointWF. It mentions
every remaining active frame and never derives activity from a receipt. -/
def ControlValid (c : Control Site) : Prop :=
  c.active.Nodup ∧
  (∀ id, id ∈ c.active → OwnerActive c (.invocation id)) ∧
  OwnerActive c c.current

theorem leave_control_valid {c : Control Site} {id : Nat} {previous : Owner}
    {rest : List Nat} {invocation : Invocation Site}
    (valid : ControlValid c) (stack : c.active = id :: rest)
    (previousLive : previous = .moduleRun ∨
      ∃ other, previous = .invocation other ∧ other ∈ rest) :
    ControlValid ⟨deactivate c.invocations id invocation, rest, previous⟩ := by
  have nodup : (id :: rest).Nodup := by simpa only [stack] using valid.1
  have hnot : id ∉ rest := (List.nodup_cons.mp nodup).1
  have keep : ∀ other, other ∈ rest →
      OwnerActive (⟨deactivate c.invocations id invocation, rest, previous⟩ : Control Site)
        (.invocation other) := by
    intro other member
    have hne : other ≠ id := by intro h; subst other; exact hnot member
    obtain ⟨old, found, live⟩ := valid.2.1 other (by simp [stack, member])
    exact ⟨old, (deactivate_other _ _ _ _ hne).trans found, live⟩
  refine ⟨(List.nodup_cons.mp nodup).2, keep, ?_⟩
  rcases previousLive with h | ⟨other, h, member⟩
  · subst previous; trivial
  · subst previous; exact keep other member

structure World (K D V ViewData Site Rest : Type) where
  environments : Arena K D
  cells : Store (Received V)
  receiving : Receiving K V ViewData Site
  control : Control Site
  rest : Rest

/-- Actual parameter binding appends a cell, then an environment whose dispatch
is copied from the selected lexical parent, including a nonlatest parent. -/
def bindValue (w : World K D V ViewData Site Rest) (parent : Nat) (key : K)
    (p : Received V) (node : Node K D)
    (found : nodeAt w.environments parent = some node) :
    World K D V ViewData Site Rest :=
  { w with
    cells := w.cells.push p.asValue
    environments := extendNode w.environments parent key w.cells.size node found }

theorem bind_valid (w : World K D V ViewData Site Rest) (parent : Nat) (key : K)
    (p : Received V) (node : Node K D)
    (found : nodeAt w.environments parent = some node) (valid : Valid w.environments) :
    Valid (bindValue w parent key p node found).environments :=
  .append valid (node_bound found)

theorem bind_read [DecidableEq K] (w : World K D V ViewData Site Rest)
    (parent : Nat) (key : K) (p : Received V) (node : Node K D)
    (found : nodeAt w.environments parent = some node) :
    observe (fun k => decide (k = key))
      (bindValue w parent key p node found).environments w.environments.size
      (bindValue w parent key p node found).cells.cell = some p.asValue :=
  bind_observes_received w.environments parent key node.dispatch w.cells p.asValue

/-- Old aliases and captures keep both their addresses and their complete
received records; the freshly selected lexical parent need not be latest. -/
theorem bind_old_read [DecidableEq K] (w : World K D V ViewData Site Rest)
    (parent : Nat) (key other : K) (p : Received V) (node : Node K D)
    (found : nodeAt w.environments parent = some node)
    (environment cell : Nat) (henv : environment < w.environments.size)
    (hcell : cell < w.cells.size)
    (address : lookupKey other w.environments environment = some cell) :
    observe (fun k => decide (k = other))
      (bindValue w parent key p node found).environments environment
      (bindValue w parent key p node found).cells.cell = w.cells.cell cell := by
  have same := lookup_old (fun k => decide (k = other)) w.environments parent
    environment (some (key, w.cells.size)) node.dispatch henv
  change (lookup (fun k => decide (k = other))
    (.append w.environments parent (some (key, w.cells.size)) node.dispatch)
    environment).bind (w.cells.push p.asValue).cell = _
  rw [same]
  change (lookupKey other w.environments environment).bind _ = _
  rw [address]
  exact push_old _ _ _ hcell

theorem bind_all_installed (w : World K D V ViewData Site Rest)
    (parent : Nat) (key : K) (p : Received V) (node : Node K D)
    (found : nodeAt w.environments parent = some node)
    (P : Nat → Received V → Prop) (old : AllInstalled P w.cells)
    (new : P w.cells.size p.asValue) :
    AllInstalled P (bindValue w parent key p node found).cells :=
  allInstalled_push old new

/-- Name uses the actual dispatch result and the current execution owner.
It creates a read receipt even when consumption is Observe. -/
def observeName [DecidableEq K] [DecidableEq V]
    (w : World K D V ViewData Site Rest) (environment : Nat) (key : K)
    (site : Site) (dispatch : Option Nat) :
    Option (World K D V ViewData Site Rest × Received V) := do
  let p ← observe (fun k => decide (k = key)) w.environments environment w.cells.cell
  let view ← w.receiving.views.cell p.view
  if view.value = p.value then
    pure ({ w with receiving := w.receiving.record w.control.current p.view site none },
      p.atName dispatch)
  else none

theorem name_success [DecidableEq K] [DecidableEq V]
    {w : World K D V ViewData Site Rest} {environment : Nat} {key : K}
    {site : Site} {dispatch : Option Nat} {p : Received V}
    (read : observe (fun k => decide (k = key)) w.environments environment w.cells.cell =
      some p) (matching : Matches w.receiving p) :
    observeName w environment key site dispatch =
      some ({ w with receiving := w.receiving.record w.control.current p.view site none },
        p.atName dispatch) := by
  obtain ⟨view, found, same⟩ := matching
  simp [observeName, read, found, same]

def returnOwned (w : World K D V ViewData Site Rest) (id : Nat)
    (previous : Owner) (p : Received V) :
    Option (World K D V ViewData Site Rest × Received V) := do
  let control ← w.control.leave id previous
  pure ({ w with control := control }, p.asValue)

/-- Construct all three actual suffix actions from the returned carrier's
packet and independent raw frame/view facts. No identity membership, successful
Name, successful leave, completed world or output certificate is assumed. -/
theorem identity_suffix [DecidableEq K] [DecidableEq V]
    (w : World K D V ViewData Site Rest) (parent : Nat) (key : K)
    (p : Received V) (node : Node K D)
    (found : nodeAt w.environments parent = some node)
    (site : Site) (dispatch : Option Nat) (id : Nat) (previous : Owner)
    (rest : List Nat) (invocation : Invocation Site)
    (matching : Matches w.receiving p)
    (current : w.control.current = .invocation id)
    (stack : w.control.active = id :: rest)
    (registered : w.control.invocations.cell id = some invocation)
    (live : invocation.active = true) :
    let bound := bindValue w parent key p node found
    let read := { bound with receiving := w.receiving.record (.invocation id) p.view site none }
    let final := { read with control := ⟨deactivate w.control.invocations id invocation, rest, previous⟩ }
    observeName bound w.environments.size key site dispatch =
      some (read, p.asValue.atName dispatch) ∧
    returnOwned read id previous (p.asValue.atName dispatch) =
      some (final, p.asValue.atName dispatch) ∧
    final.receiving.receipts.cell w.receiving.receipts.size =
      some ⟨.invocation id, p.view, site, none⟩ ∧
    final.receiving.receipts.size = w.receiving.receipts.size + 1 ∧
    final.receiving.views = w.receiving.views ∧
    final.cells = w.cells.push p.asValue ∧
    final.rest = w.rest ∧
    ¬ OwnerActive final.control (.invocation id) := by
  dsimp only
  refine ⟨?_, ?_, receipt_new _ _ _ _ _, rfl, rfl, rfl, rfl, ?_⟩
  · simpa only [bindValue, Received.asValue, current] using
      (name_success (site := site) (dispatch := dispatch)
        (bind_read w parent key p node found) matching)
  · have leave := leave_success current stack registered live (previous := previous)
    simp only [returnOwned, bindValue, leave]
    rfl
  · rintro ⟨other, h, active⟩
    have hsame : { invocation with active := false } = other :=
      Option.some.inj ((deactivate_current _ _ _).symm.trans h)
    subst other
    cases active

/-- Exact native obstruction to identifying this suffix with an unchanged
world: the Name receipt count grows, also when the argument is a latent value. -/
theorem name_world_changes [DecidableEq K]
    (w : World K D V ViewData Site Rest) (site : Site) (view : Nat) :
    ({ w with receiving := w.receiving.record w.control.current view site none } :
      World K D V ViewData Site Rest) ≠ w := by
  intro same
  have counts := congrArg (fun x : World K D V ViewData Site Rest =>
    x.receiving.receipts.size) same
  exact (Nat.ne_of_gt (Nat.lt_succ_self w.receiving.receipts.size)) counts

/-- The result's value/view are unchanged. The dictionary field equals the
actual Name dispatch result; full received-record identity has exactly these
additional normalization/dispatch requirements. -/
theorem suffix_result_fields (p : Received V) (dispatch : Option Nat) :
    (p.asValue.atName dispatch).value = p.value ∧
    (p.asValue.atName dispatch).view = p.view ∧
    (p.asValue.atName dispatch).dispatch = dispatch ∧
    (p.asValue.atName dispatch).interface = .value := ⟨rfl, rfl, rfl, rfl⟩

theorem suffix_result_identity (p : Received V) (value : p.interface = .value) :
    p.asValue.atName p.dispatch = p := by
  rw [asValue_eq value]
  cases p
  rfl

def OwnerRegistered (c : Control Site) : Owner → Prop
  | .moduleRun => True
  | .invocation id => ∃ invocation, c.invocations.cell id = some invocation

theorem deactivate_registered (c : Control Site) (id : Nat)
    (invocation : Invocation Site) (rest : List Nat) (previous owner : Owner)
    (registered : OwnerRegistered c owner) :
    OwnerRegistered ⟨deactivate c.invocations id invocation, rest, previous⟩ owner := by
  cases owner with
  | moduleRun => trivial
  | invocation other =>
      by_cases same : other = id
      · subst other
        exact ⟨_, deactivate_current _ _ _⟩
      · obtain ⟨old, found⟩ := registered
        exact ⟨old, (deactivate_other _ _ _ _ same).trans found⟩

/-- Historical registration uses the stored owner identity. It does not require
that owner to remain active and does not restore its activity on a later read. -/
def ReceiptHistory (w : World K D V ViewData Site Rest) : Prop :=
  AllInstalled (fun _ receipt =>
    (∃ view, w.receiving.views.cell receipt.view = some view) ∧
      OwnerRegistered w.control receipt.owner) w.receiving.receipts

def BindingsMatch (w : World K D V ViewData Site Rest) : Prop :=
  AllInstalled (fun _ p => Matches w.receiving p) w.cells

/-- Direct construction of the world conjuncts needed after the actual
identity suffix. Every old binding and receipt is retained. The sole new
binding is the actual returned packet; the sole new receipt is its Name use.
Original semantic P may include both value and retained-carrier certificates.
Its old and returned inputs are at the same independently supplied live event.
This conclusion is a strict list of established fields, not full JointWF. -/
theorem identity_world_fields [DecidableEq K]
    (w : World K D V ViewData Site Rest) (parent : Nat) (key : K)
    (p : Received V) (node : Node K D)
    (found : nodeAt w.environments parent = some node)
    (site : Site) (id : Nat) (previous : Owner)
    (rest : List Nat) (invocation : Invocation Site)
    (arena : Valid w.environments) (matching : Matches w.receiving p)
    (bindings : BindingsMatch w) (history : ReceiptHistory w)
    (control : ControlValid w.control) (stack : w.control.active = id :: rest)
    (previousLive : previous = .moduleRun ∨
      ∃ other, previous = .invocation other ∧ other ∈ rest)
    (P : Nat → Received V → Prop) (old : AllInstalled P w.cells)
    (returned : P w.cells.size p.asValue) :
    let bound := bindValue w parent key p node found
    let read := { bound with receiving := w.receiving.record (.invocation id) p.view site none }
    let final := { read with control := ⟨deactivate w.control.invocations id invocation, rest, previous⟩ }
    Valid final.environments ∧ AllInstalled P final.cells ∧
      BindingsMatch final ∧ ReceiptHistory final ∧ ControlValid final.control := by
  dsimp only
  refine ⟨bind_valid w parent key p node found arena,
    allInstalled_push old returned, ?_, ?_, leave_control_valid control stack previousLive⟩
  · exact allInstalled_push bindings matching
  · apply allInstalled_push
    · intro i receipt hi hr
      obtain ⟨view, owner⟩ := history i receipt hi hr
      exact ⟨view, deactivate_registered _ _ _ _ _ _ owner⟩
    · obtain ⟨view, hview, _⟩ := matching
      exact ⟨⟨view, hview⟩, _, deactivate_current _ _ _⟩

/-- The all-binding application at the actual final event is constructed
from hereditary old binding actions and the carrier's actual result field.
The event relation is independent: this theorem creates no compatible event. -/
theorem identity_bindings_at_event
    (w : World K D V ViewData Site Rest) (parent : Nat) (key : K)
    (p : Received V) (node : Node K D)
    (found : nodeAt w.environments parent = some node)
    (Certificate : E → Nat → Received V → Prop) (before now : E)
    (compatible : E → E → Prop) (extension : compatible before now)
    (old : AllInstalled (Certificate before) w.cells)
    (hereditary : ∀ i value, i < w.cells.size → w.cells.cell i = some value →
      Certificate before i value → compatible before now → Certificate now i value)
    (returned : Certificate now w.cells.size p.asValue) :
    AllInstalled (Certificate now) (bindValue w parent key p node found).cells := by
  exact allInstalled_push
    (allInstalled_restrict old (fun i value hi hv hp => hereditary i value hi hv hp extension))
    returned

inductive SuffixState (K D V ViewData Site Rest : Type) where
  | entry (world : World K D V ViewData Site Rest) (argument : Received V)
  | body (world : World K D V ViewData Site Rest) (environment : Nat)
  | returning (world : World K D V ViewData Site Rest) (result : Received V)
  | done (world : World K D V ViewData Site Rest) (result : Received V)

/-- The finite identity suffix after the arbitrary carrier's actual Return.
This executor does not execute or restrict that carrier, receipt entry, or a
future call of the returned value. Name retains its read-receipt action. -/
def suffixStep [DecidableEq K] [DecidableEq V]
    (parent : Nat) (key : K) (site : Site) (dispatch : Option Nat)
    (id : Nat) (previous : Owner) :
    SuffixState K D V ViewData Site Rest → Option (SuffixState K D V ViewData Site Rest)
  | .entry w p =>
      match found : nodeAt w.environments parent with
      | none => none
      | some node => some (.body (bindValue w parent key p node found) w.environments.size)
  | .body w environment =>
      (observeName w environment key site dispatch).map (fun out => .returning out.1 out.2)
  | .returning w p =>
      (returnOwned w id previous p).map (fun out => .done out.1 out.2)
  | .done _ _ => none

/-- Every finite prefix of a fixed four-phase deterministic chain, including
zero steps. This derives a classification, rather than assuming a terminal run. -/
theorem four_phase_prefix {S : Type} (step : S → Option S)
    (a b c d : S) (ab : step a = some b) (bc : step b = some c)
    (cd : step c = some d) (endStep : step d = none)
    {n : Nat} {last : S} (path : Prefix (fun x y => step x = some y) n a last) :
    last = a ∨ last = b ∨ last = c ∨ last = d := by
  induction path with
  | refl => exact .inl rfl
  | @snoc n first middle last prior move ih =>
      rcases ih ab with h | h | h | h
      · subst middle
        exact .inr (.inl (Option.some.inj (ab.symm.trans move)).symm)
      · subst middle
        exact .inr (.inr (.inl (Option.some.inj (bc.symm.trans move)).symm))
      · subst middle
        exact .inr (.inr (.inr (Option.some.inj (cd.symm.trans move)).symm))
      · subst middle
        rw [endStep] at move
        cases move

/-- Full finite-prefix classification for the represented post-Force source
suffix. The returned carrier record, source Name slot, and live frame facts
construct all three steps. No final world, result typing, or successful run
is a premise. Divergent/requesting carrier prefixes remain outside this suffix
and retain their original independent contracts. -/
theorem identity_suffix_prefixes [DecidableEq K] [DecidableEq V]
    (w : World K D V ViewData Site Rest) (parent : Nat) (key : K)
    (p : Received V) (node : Node K D)
    (found : nodeAt w.environments parent = some node)
    (site : Site) (dispatch : Option Nat) (id : Nat) (previous : Owner)
    (rest : List Nat) (invocation : Invocation Site)
    (matching : Matches w.receiving p)
    (current : w.control.current = .invocation id)
    (stack : w.control.active = id :: rest)
    (registered : w.control.invocations.cell id = some invocation)
    (live : invocation.active = true)
    {n : Nat} {last : SuffixState K D V ViewData Site Rest}
    (path : Prefix (fun a b => suffixStep parent key site dispatch id previous a = some b)
      n (.entry w p) last) :
    let bound := bindValue w parent key p node found
    let read := { bound with receiving := w.receiving.record (.invocation id) p.view site none }
    let final := { read with control := ⟨deactivate w.control.invocations id invocation, rest, previous⟩ }
    last = .entry w p ∨
      last = .body bound w.environments.size ∨
      last = .returning read (p.asValue.atName dispatch) ∨
      last = .done final (p.asValue.atName dispatch) := by
  have actions := identity_suffix w parent key p node found site dispatch id previous rest
    invocation matching current stack registered live
  dsimp only at actions ⊢
  apply four_phase_prefix (suffixStep parent key site dispatch id previous) _ _ _ _
    (by
      simp only [suffixStep]
      split
      · rename_i missing
        have impossible := missing.symm.trans found
        cases impossible
      · rename_i other present
        have same : other = node := Option.some.inj (present.symm.trans found)
        subst other
        rfl)
    (by simp only [suffixStep, actions.1, Option.map_some])
    (by simp only [suffixStep, actions.2.1, Option.map_some]) rfl path

end YulangClosure.SourceIdentityWorld

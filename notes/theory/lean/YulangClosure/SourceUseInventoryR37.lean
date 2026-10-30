import YulangClosure.SourceCallbackUseR36

/-!
R37 finite retained-source inventory. Native cells retain the owner on an Apply
callee index, which R36's ordinal projection erases. The occurrence registry is
an explicit owner-indexed finite table, not a supplied simulation law. The first
pass checks the whole vector (including unrelated Apply edges); the second pass
enumerates individual R36 issuers in vector order. Allocation availability is a
separate result channel. This does not formalize Rust/HashMap/Arc internals,
runtime invocation, Grant, Catch, propagation, or the original whole-language
claims. All source forms outside the R36 projection remain opaque.
-/
namespace YulangClosure.SourceUseInventoryR37
open NativeCallbackGrantBridgeR31 NativeCallbackGrantBridgeR32
open NativeCallbackCoordinatesR33 NativeSnapshotOwnerR34
open SourceCallbackPermissionR35
open SourceCallbackUseR36

structure Cell (Artifact Definition Module Parse Green : Type) where
  expression : SourceCallbackUseR36.Expression Artifact Definition Module Parse Green
  /-- Relevant exactly when expression.form is Apply. -/
  calleeOwner : RootId Artifact Definition Module Parse Green

structure NativeRoot (Artifact Definition Module Parse Green : Type) where
  id : RootId Artifact Definition Module Parse Green
  cells : List (Cell Artifact Definition Module Parse Green)

def NativeRoot.project (r : NativeRoot Artifact Definition Module Parse Green) :
    Root Artifact Definition Module Parse Green :=
  ⟨r.id, r.cells.map Cell.expression⟩

structure NativePool (history : AllocationHistory)
    (Artifact Definition Module Parse Green : Type) where
  roots : OwnerId history → List (NativeRoot Artifact Definition Module Parse Green)
  effects : OwnerId history → List (HirEffect Module Parse Green)
  occurrenceSources : OwnerId history → List (Nat × SourceNodeKey Parse Green)

def NativePool.project (p : NativePool history Artifact Definition Module Parse Green) :
    Pool history Artifact Definition Module Parse Green :=
  ⟨fun owner => (p.roots owner).map NativeRoot.project, p.effects⟩

def occurrences (r : NativeRoot Artifact Definition Module Parse Green) : List Nat :=
  r.cells.map fun c => c.expression.occurrence

/-- Full vector-derived occurrence/index table. No caller supplies its entries. -/
def indexTable (r : NativeRoot Artifact Definition Module Parse Green) : List (Nat × Nat) :=
  (occurrences r).zipIdx

def lookupOccurrence (r : NativeRoot Artifact Definition Module Parse Green) (occ : Nat) : Option Nat :=
  (indexTable r).lookup occ

variable {history : AllocationHistory} {Artifact Definition Module Parse Green : Type}
variable [DecidableEq Artifact] [DecidableEq Definition] [DecidableEq Module]
variable [DecidableEq Parse] [DecidableEq Green]

def siteValid (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (c : Cell Artifact Definition Module Parse Green) : Bool :=
  decide ((p.occurrenceSources owner.hirOwner).lookup c.expression.occurrence =
    some c.expression.source)

/-- Owner and bounds are checked for *every* Apply, including a foreign formal
or a non-Name callee. The map target must be exactly this vector entry. -/
def edgeValid (r : NativeRoot Artifact Definition Module Parse Green)
    (c : Cell Artifact Definition Module Parse Green) : Bool :=
  match c.expression.form with
  | .apply callee _ =>
    if c.calleeOwner = r.id then
      match r.cells[callee]? with
      | none => false
      | some target => decide (lookupOccurrence r target.expression.occurrence = some callee)
    else false
  | _ => true

def rootValid (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (r : NativeRoot Artifact Definition Module Parse Green) : Bool :=
  decide (occurrences r).Nodup && r.cells.all (siteValid p owner) && r.cells.all (edgeValid r)

/-- The generic table fact is proved here; it is not a Rust law. -/
theorem lookup_of_mem_unique (table : List (Nat × Nat))
    (unique : (table.map Prod.fst).Nodup) (key value : Nat)
    (member : (key, value) ∈ table) : table.lookup key = some value := by
  induction table with
  | nil => simp at member
  | cons head tail ih =>
    rcases head with ⟨headKey, headValue⟩
    obtain ⟨absent, nodup⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with same | later
    · cases same
      simp
    · have different : key ≠ headKey := by
        intro equal
        apply absent
        rw [← equal]
        exact List.mem_map.mpr ⟨(key, value), later, rfl⟩
      have no : (key == headKey) = false := beq_eq_false_iff_ne.mpr different
      simpa only [List.lookup_cons, no] using ih nodup later

omit [DecidableEq Artifact] [DecidableEq Definition] [DecidableEq Module]
  [DecidableEq Parse] [DecidableEq Green] in
theorem occurrence_lookup_sound
    (r : NativeRoot Artifact Definition Module Parse Green) (occ i : Nat)
    (found : lookupOccurrence r occ = some i) : (occurrences r)[i]? = some occ := by
  obtain ⟨before, after, same, _⟩ := List.lookup_eq_some_iff.mp found
  apply List.mk_mem_zipIdx_iff_getElem?.mp
  change (occ, i) ∈ indexTable r
  rw [same]
  simp

omit [DecidableEq Artifact] [DecidableEq Definition] [DecidableEq Module]
  [DecidableEq Parse] [DecidableEq Green] in
theorem occurrence_lookup_complete
    (r : NativeRoot Artifact Definition Module Parse Green)
    (unique : (occurrences r).Nodup) (occ i : Nat)
    (atIndex : (occurrences r)[i]? = some occ) : lookupOccurrence r occ = some i := by
  apply lookup_of_mem_unique
  · simpa [indexTable, List.zipIdx_map_fst] using unique
  · exact List.mk_mem_zipIdx_iff_getElem?.mpr atIndex

omit [DecidableEq Artifact] [DecidableEq Definition] [DecidableEq Module]
  [DecidableEq Parse] [DecidableEq Green] in
theorem occurrence_indices_unique
    (r : NativeRoot Artifact Definition Module Parse Green)
    (unique : (occurrences r).Nodup) (occ i j : Nat)
    (left : (occurrences r)[i]? = some occ) (right : (occurrences r)[j]? = some occ) : i = j := by
  have l := occurrence_lookup_complete r unique occ i left
  have r := occurrence_lookup_complete r unique occ j right
  exact Option.some.inj (l.symm.trans r)

theorem root_validation_exact
    (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (r : NativeRoot Artifact Definition Module Parse Green)
    (valid : rootValid p owner r = true) :
    (occurrences r).Nodup ∧
    (∀ c ∈ r.cells, (p.occurrenceSources owner.hirOwner).lookup c.expression.occurrence =
      some c.expression.source) ∧
    (∀ c ∈ r.cells, edgeValid r c = true) := by
  simpa [rootValid, siteValid, Bool.and_eq_true, List.all_eq_true, and_assoc] using valid

theorem duplicate_occurrences_rejected
    (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (r : NativeRoot Artifact Definition Module Parse Green)
    (duplicate : ¬ (occurrences r).Nodup) : rootValid p owner r = false := by
  simp [rootValid, duplicate]

theorem all_apply_edges_owned
    (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (r : NativeRoot Artifact Definition Module Parse Green)
    (valid : rootValid p owner r = true)
    (c : Cell Artifact Definition Module Parse Green) (member : c ∈ r.cells)
    (callee argument : Nat) (form : c.expression.form = .apply callee argument) :
    c.calleeOwner = r.id ∧ ∃ target, r.cells[callee]? = some target ∧
      lookupOccurrence r target.expression.occurrence = some callee := by
  have checked := (root_validation_exact p owner r valid).2.2 c member
  simp only [edgeValid, form] at checked
  split at checked
  · rename_i owned
    cases ht : r.cells[callee]? with
    | none => simp [ht] at checked
    | some target =>
      exact ⟨owned, target, rfl, by simpa [ht] using checked⟩
  · simp at checked

theorem invalid_unrelated_apply_rejected
    (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (r : NativeRoot Artifact Definition Module Parse Green)
    (c : Cell Artifact Definition Module Parse Green) (member : c ∈ r.cells)
    (callee argument : Nat) (form : c.expression.form = .apply callee argument)
    (invalid : c.calleeOwner ≠ r.id ∨ r.cells[callee]? = none) : rootValid p owner r = false := by
  cases checked : rootValid p owner r with
  | false => rfl
  | true =>
    obtain ⟨owned, target, atTarget, _⟩ := all_apply_edges_owned p owner r checked c member callee argument form
    rcases invalid with foreign | missing
    · exact False.elim (foreign owned)
    · rw [missing] at atTarget
      contradiction

theorem source_key_mismatch_rejected
    (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (r : NativeRoot Artifact Definition Module Parse Green)
    (c : Cell Artifact Definition Module Parse Green) (member : c ∈ r.cells)
    (mismatch : (p.occurrenceSources owner.hirOwner).lookup c.expression.occurrence ≠ some c.expression.source) :
    rootValid p owner r = false := by
  cases checked : rootValid p owner r with
  | false => rfl
  | true => exact False.elim (mismatch ((root_validation_exact p owner r checked).2.1 c member))

/-- Rust's parent map keys the already checked target occurrence. -/
def occurrenceParents (r : NativeRoot Artifact Definition Module Parse Green) (occ : Nat) : Nat :=
  r.cells.countP fun c => match c.expression.form with
    | .apply callee _ => match r.cells[callee]? with
      | some target => target.expression.occurrence == occ
      | none => false
    | _ => false

theorem parent_count_occurrence_index
    (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (r : NativeRoot Artifact Definition Module Parse Green)
    (valid : rootValid p owner r = true) (ni : Nat)
    (name : Cell Artifact Definition Module Parse Green) (atName : r.cells[ni]? = some name) :
    occurrenceParents r name.expression.occurrence = calleeParents r.project ni := by
  unfold occurrenceParents calleeParents
  simp only [NativeRoot.project, List.countP_map, Function.comp_def]
  apply List.countP_congr
  intro c member
  cases form : c.expression.form with
  | lambda _ _ | name _ | other _ => simp
  | apply callee argument =>
    obtain ⟨_, target, atTarget, _⟩ := all_apply_edges_owned p owner r valid c member callee argument form
    have unique := (root_validation_exact p owner r valid).1
    have ht : (occurrences r)[callee]? = some target.expression.occurrence := by
      simp [occurrences, atTarget]
    have hn : (occurrences r)[ni]? = some name.expression.occurrence := by
      simp [occurrences, atName]
    have same : target.expression.occurrence = name.expression.occurrence ↔ callee = ni := by
      constructor
      · intro equal
        exact occurrence_indices_unique r unique name.expression.occurrence callee ni (equal ▸ ht) hn
      · intro equal
        subst callee
        have eqTarget := Option.some.inj (atTarget.symm.trans atName)
        exact congrArg (fun x => x.expression.occurrence) eqTarget
    simpa [form, atTarget, beq_iff_eq] using same

structure Prepared (history : AllocationHistory)
    (Artifact Definition Module Parse Green : Type) where
  root : NativeRoot Artifact Definition Module Parse Green
  lambdaIndex : Nat
  selected : SelectedLambda Artifact Definition Module Parse Green
  permission : SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green

def prepare (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri lambdaOccurrence : Nat) :
    Option (Prepared history Artifact Definition Module Parse Green) := do
  let root ← (p.roots owner.hirOwner)[ri]?
  if rootValid p owner root then
    let li ← lookupOccurrence root lambdaOccurrence
    let l ← lookupLambda p.project owner ri li
    let permission ← issueSelected owner l.selection [.result]
    pure ⟨root, li, l, permission⟩
  else none

theorem prepare_exact
    (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri lambdaOccurrence : Nat)
    (ready : Prepared history Artifact Definition Module Parse Green)
    (success : prepare p owner ri lambdaOccurrence = some ready) :
    (p.roots owner.hirOwner)[ri]? = some ready.root ∧
    rootValid p owner ready.root = true ∧
    lookupOccurrence ready.root lambdaOccurrence = some ready.lambdaIndex ∧
    lookupLambda p.project owner ri ready.lambdaIndex = some ready.selected ∧
    issueSelected owner ready.selected.selection [.result] = some ready.permission ∧
    ready.selected.root = ready.root.project := by
  unfold prepare at success
  cases hr : (p.roots owner.hirOwner)[ri]? with
  | none => simp [hr] at success
  | some root =>
    simp only [hr] at success
    cases hv : rootValid p owner root <;> simp [hv] at success
    cases hi : lookupOccurrence root lambdaOccurrence with
    | none => simp [hi] at success
    | some li =>
      cases hl : lookupLambda p.project owner ri li with
      | none => simp [hi, hl] at success
      | some l =>
        cases hp : issueSelected owner l.selection [.result] with
        | none => simp [hi, hl, hp] at success
        | some permission =>
          simp [hi, hl, hp] at success
          subst ready
          have origin := (lookupLambda_origin p.project owner ri li l hl).1
          have same : l.root = root.project := by
            simpa [NativePool.project, hr] using origin.symm
          exact ⟨rfl, hv, hi, hl, hp, same⟩

/-- Second pass: one result per successful individual issuer, in ascending
source vector index. This is list enumeration, with no set quotient. -/
def enumerate (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri li length : Nat) :
    List (SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green) :=
  (List.range length).filterMap (SourceCallbackUseR36.issue p.project owner ri li)

def inventory (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri lambdaOccurrence : Nat) :
    Option (List (SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green)) := do
  let ready ← prepare p owner ri lambdaOccurrence
  pure (enumerate p owner ri ready.lambdaIndex ready.root.cells.length)

theorem inventory_exact
    (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri lambdaOccurrence : Nat)
    (out : List (SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green)) :
    inventory p owner ri lambdaOccurrence = some out ↔
    ∃ ready, prepare p owner ri lambdaOccurrence = some ready ∧
      out = enumerate p owner ri ready.lambdaIndex ready.root.cells.length := by
  unfold inventory
  cases hp : prepare p owner ri lambdaOccurrence <;> simp [eq_comm]

theorem enumeration_complete
    (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri li length : Nat)
    (w : SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green) :
    w ∈ enumerate p owner ri li length ↔
      ∃ ai, ai < length ∧ SourceCallbackUseR36.issue p.project owner ri li ai = some w := by
  simp [enumerate]

theorem enumeration_second_pass
    (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri li length : Nat)
    (l : SelectedLambda Artifact Definition Module Parse Green)
    (permission : SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green)
    (hl : lookupLambda p.project owner ri li = some l)
    (hp : issueSelected owner l.selection [.result] = some permission) :
    enumerate p owner ri li length = (List.range length).filterMap (fun ai =>
      (lookupEdge l.root l.formal.id ai).map (fun edge => assemble l edge permission)) := by
  unfold enumerate
  congr 1
  funext ai
  cases he : lookupEdge l.root l.formal.id ai <;>
    simp [SourceCallbackUseR36.issue, hl, hp, he]

theorem enumeration_order
    (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri li length : Nat) :
    (enumerate p owner ri li length).map (fun w => w.applyIndex) =
      (List.range length).filter (fun ai =>
        (SourceCallbackUseR36.issue p.project owner ri li ai).isSome) := by
  unfold enumerate
  rw [List.map_filterMap]
  rw [← List.filterMap_eq_filter]
  congr 1
  funext ai
  cases hi : SourceCallbackUseR36.issue p.project owner ri li ai with
  | none => simp [Option.guard, hi]
  | some w =>
    obtain ⟨l, edge, permission, hl, he, hp, same⟩ :=
      SourceCallbackUseR36.source_origin p.project owner ri li ai w hi
    have index := (lookupEdge_origin l.root l.formal.id ai edge he).2.1
    simp [Option.guard, hi, same, assemble, index]

theorem enumeration_multiplicity
    (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri li length : Nat)
    (predicate : SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green → Bool) :
    (enumerate p owner ri li length).countP predicate =
      (List.range length).countP (fun ai =>
        ((SourceCallbackUseR36.issue p.project owner ri li ai).map predicate).getD false) := by
  exact List.countP_filterMap

theorem empty_enumeration
    (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri li length : Nat) :
    enumerate p owner ri li length = [] ↔
      ∀ ai, ai < length → SourceCallbackUseR36.issue p.project owner ri li ai = none := by
  simp [enumerate]

theorem empty_success
    (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri lambdaOccurrence : Nat)
    (ready : Prepared history Artifact Definition Module Parse Green)
    (prepared : prepare p owner ri lambdaOccurrence = some ready)
    (noUses : ∀ ai, ai < ready.root.cells.length →
      SourceCallbackUseR36.issue p.project owner ri ready.lambdaIndex ai = none) :
    inventory p owner ri lambdaOccurrence = some [] := by
  have empty := (empty_enumeration p owner ri ready.lambdaIndex ready.root.cells.length).mpr noUses
  simp [inventory, prepared, empty]

theorem issued_index_bounded
    (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri lambdaOccurrence : Nat)
    (ready : Prepared history Artifact Definition Module Parse Green)
    (prepared : prepare p owner ri lambdaOccurrence = some ready)
    (ai : Nat) (w : SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green)
    (issued : SourceCallbackUseR36.issue p.project owner ri ready.lambdaIndex ai = some w) :
    ai < ready.root.cells.length := by
  obtain ⟨_, _, _, hl, _, sameRoot⟩ := prepare_exact p owner ri lambdaOccurrence ready prepared
  obtain ⟨l, edge, permission, hl', he, _, _⟩ :=
    SourceCallbackUseR36.source_origin p.project owner ri ready.lambdaIndex ai w issued
  have same : l = ready.selected := Option.some.inj (hl'.symm.trans hl)
  subst l
  have atApply := (lookupEdge_origin ready.selected.root ready.selected.formal.id ai edge he).1
  rw [sameRoot] at atApply
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp atApply
  simpa [NativeRoot.project] using bound

/-- Complete against *all* R36 individual indices, with the bound derived from
the actual edge rather than supplied as a completeness restriction. -/
theorem inventory_complete_individual
    (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri lambdaOccurrence : Nat)
    (ready : Prepared history Artifact Definition Module Parse Green)
    (prepared : prepare p owner ri lambdaOccurrence = some ready)
    (w : SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green) :
    w ∈ enumerate p owner ri ready.lambdaIndex ready.root.cells.length ↔
      ∃ ai, SourceCallbackUseR36.issue p.project owner ri ready.lambdaIndex ai = some w := by
  rw [enumeration_complete]
  constructor
  · rintro ⟨ai, _, issued⟩
    exact ⟨ai, issued⟩
  · rintro ⟨ai, issued⟩
    exact ⟨ai, issued_index_bounded p owner ri lambdaOccurrence ready prepared ai w issued, issued⟩

/-- Apply every enumerated result to R36's original individual issuer and
then to R35 on the same projected source pool. No independent witness is chosen. -/
theorem inventory_applies_to_r36_r35
    (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri lambdaOccurrence : Nat)
    (out : List (SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green))
    (success : inventory p owner ri lambdaOccurrence = some out) :
    ∃ ready, prepare p owner ri lambdaOccurrence = some ready ∧
      rootValid p owner ready.root = true ∧
      (occurrences ready.root)[ready.lambdaIndex]? = some lambdaOccurrence ∧
      out = enumerate p owner ri ready.lambdaIndex ready.root.cells.length ∧
      ∀ w ∈ out, ∃ ai,
        SourceCallbackUseR36.authenticate p.project owner ri ready.lambdaIndex ai w ∧
        SourceCallbackPermissionR35.authenticate p.project.toR35 owner ri ready.lambdaIndex
          [.result] w.permission := by
  obtain ⟨ready, prepared, equal⟩ := (inventory_exact p owner ri lambdaOccurrence out).mp success
  obtain ⟨_, valid, found, _, _, _⟩ := prepare_exact p owner ri lambdaOccurrence ready prepared
  refine ⟨ready, prepared, valid, occurrence_lookup_sound ready.root lambdaOccurrence ready.lambdaIndex found,
    equal, ?_⟩
  intro w member
  rw [equal] at member
  obtain ⟨ai, _, issued⟩ := (enumeration_complete p owner ri ready.lambdaIndex ready.root.cells.length w).mp member
  exact ⟨ai, issued, authenticated_r35 p.project owner ri ready.lambdaIndex ai w issued⟩

omit [DecidableEq Artifact] [DecidableEq Definition] [DecidableEq Module]
  [DecidableEq Parse] [DecidableEq Green] in
theorem projected_cell_origin
    (root : NativeRoot Artifact Definition Module Parse Green) (i : Nat)
    (expression : SourceCallbackUseR36.Expression Artifact Definition Module Parse Green)
    (found : root.project.expressions[i]? = some expression) :
    ∃ cell, root.cells[i]? = some cell ∧ cell.expression = expression := by
  simpa [NativeRoot.project, Option.map_eq_some_iff] using found

theorem inventory_sites_owned
    (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri lambdaOccurrence : Nat)
    (ready : Prepared history Artifact Definition Module Parse Green)
    (prepared : prepare p owner ri lambdaOccurrence = some ready)
    (w : SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green)
    (member : w ∈ enumerate p owner ri ready.lambdaIndex ready.root.cells.length) :
    (p.occurrenceSources owner.hirOwner).lookup w.name.occurrence = some w.name.source ∧
    (p.occurrenceSources owner.hirOwner).lookup w.application.occurrence = some w.application.source := by
  obtain ⟨_, valid, _, hl, _, sameRoot⟩ := prepare_exact p owner ri lambdaOccurrence ready prepared
  obtain ⟨ai, _, issued⟩ := (enumeration_complete p owner ri ready.lambdaIndex ready.root.cells.length w).mp member
  obtain ⟨l, edge, permission, hl', he, _, equal⟩ :=
    SourceCallbackUseR36.source_origin p.project owner ri ready.lambdaIndex ai w issued
  have same : l = ready.selected := Option.some.inj (hl'.symm.trans hl)
  subst l
  obtain ⟨atApply, _, _, atName, _⟩ := lookupEdge_origin ready.selected.root ready.selected.formal.id ai edge he
  rw [sameRoot] at atApply atName
  obtain ⟨appCell, appIndex, appExpression⟩ := projected_cell_origin ready.root ai edge.application atApply
  obtain ⟨nameCell, nameIndex, nameExpression⟩ := projected_cell_origin ready.root edge.nameIndex edge.name atName
  have owned := (root_validation_exact p owner ready.root valid).2.1
  have appOwned := owned appCell (List.mem_of_getElem? appIndex)
  have nameOwned := owned nameCell (List.mem_of_getElem? nameIndex)
  subst w
  simpa [assemble, Expression.site, appExpression, nameExpression] using And.intro nameOwned appOwned

/-- Every actual matching Name has exactly one incoming parent, translating
R36's global ≤1 check to the successful-edge =1 check used by the inventory. -/
theorem issued_one_parent
    (pool : Pool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri li ai : Nat)
    (w : SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green)
    (issued : SourceCallbackUseR36.issue pool owner ri li ai = some w) :
    ∃ l edge, lookupLambda pool owner ri li = some l ∧
      lookupEdge l.root l.formal.id ai = some edge ∧ calleeParents l.root edge.nameIndex = 1 := by
  obtain ⟨l, edge, permission, hl, he, _, _⟩ := SourceCallbackUseR36.source_origin pool owner ri li ai w issued
  obtain ⟨atApply, _, applyForm, atName, nameForm⟩ := lookupEdge_origin l.root l.formal.id ai edge he
  have unamb := (lookupLambda_origin pool owner ri li l hl).2.2.2.2.2
  have checked := (List.all_eq_true.mp unamb) (edge.name, edge.nameIndex)
    (List.mk_mem_zipIdx_iff_getElem?.mpr atName)
  have limit : calleeParents l.root edge.nameIndex ≤ 1 := by
    simpa [nameForm] using checked
  have positive : 0 < calleeParents l.root edge.nameIndex := by
    apply List.countP_pos_iff.mpr
    exact ⟨edge.application, List.mem_of_getElem? atApply, by simp [applyForm]⟩
  exact ⟨l, edge, hl, he, by omega⟩

/-- The global R36 guard and the Rust second-pass guard are equivalent:
unreferenced formal Names have count zero; each selected edge has count one. -/
theorem ambiguity_guard_equivalent
    (root : Root Artifact Definition Module Parse Green)
    (formal : ParameterId Artifact Definition Module Parse Green) :
    unambiguous root formal = true ↔
      ∀ ai edge, lookupEdge root formal ai = some edge → calleeParents root edge.nameIndex = 1 := by
  constructor
  · intro unamb ai edge found
    obtain ⟨atApply, _, applyForm, atName, nameForm⟩ := lookupEdge_origin root formal ai edge found
    have checked := (List.all_eq_true.mp unamb) (edge.name, edge.nameIndex)
      (List.mk_mem_zipIdx_iff_getElem?.mpr atName)
    have limit : calleeParents root edge.nameIndex ≤ 1 := by simpa [nameForm] using checked
    have positive : 0 < calleeParents root edge.nameIndex := by
      apply List.countP_pos_iff.mpr
      exact ⟨edge.application, List.mem_of_getElem? atApply, by simp [applyForm]⟩
    omega
  · intro every
    apply List.all_eq_true.mpr
    intro pair member
    rcases pair with ⟨name, ni⟩
    have atName := List.mk_mem_zipIdx_iff_getElem?.mp member
    cases form : name.form with
    | lambda _ _ | apply _ _ | other _ => simp [form]
    | name resolution =>
      cases resolution with
      | other _ => simp [form]
      | parameter resolved =>
        by_cases same : resolved = formal
        · subst resolved
          simp only [form, ite_true]
          apply decide_eq_true
          by_cases zero : calleeParents root ni = 0
          · omega
          · have positive : 0 < calleeParents root ni := by omega
            obtain ⟨application, appMem, isParent⟩ := List.countP_pos_iff.mp positive
            cases appForm : application.form with
            | lambda _ _ | name _ | other _ => simp [appForm] at isParent
            | apply callee argument =>
              have target : callee = ni := by simpa [appForm] using isParent
              subst callee
              obtain ⟨ai, atApply⟩ := List.getElem?_of_mem appMem
              let edge : Edge Artifact Definition Module Parse Green := ⟨ni, name, ai, application, argument⟩
              have found : lookupEdge root formal ai = some edge := by
                simp [lookupEdge, atApply, appForm, atName, form, edge]
              have count := every ai edge found
              change calleeParents root ni = 1 at count
              omega
        · simp [form, same]

/-- The Bool records success of all fallible allocations on this call. It is
an explicit execution premise, not a semantic negative or a verified allocator. -/
def allocatedInventory (allocationSuccess : Bool)
    (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri lambdaOccurrence : Nat) :
    Except Unit (Option (List (SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green))) :=
  if allocationSuccess then .ok (inventory p owner ri lambdaOccurrence) else .error ()

theorem allocation_success_correspondence
    (allocationSuccess : Bool) (available : allocationSuccess = true)
    (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri lambdaOccurrence : Nat) :
    allocatedInventory allocationSuccess p owner ri lambdaOccurrence =
      .ok (inventory p owner ri lambdaOccurrence) := by
  simp [allocatedInventory, available]

theorem allocation_failure_distinct
    (p : NativePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri lambdaOccurrence : Nat) :
    allocatedInventory false p owner ri lambdaOccurrence = .error () ∧
    allocatedInventory false p owner ri lambdaOccurrence ≠ .ok none := by
  simp [allocatedInventory]

end YulangClosure.SourceUseInventoryR37

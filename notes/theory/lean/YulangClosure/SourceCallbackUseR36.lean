import YulangClosure.SourceCallbackPermissionR35

/-!
R36 candidate source-side projection. The extended arena retains explicit
resolved Name and Apply constructors and projects to R35 from the same arena.
No typing, runtime receipt, Grant, Catch, or Rust simulation is defined here.
An outer effect annotation classifies a parameter Name as Execute; this gate
accepts only outer-effects-free function formals, hence derives Observe.
All other constructors remain opaque and are outside direct-use selection,
not outside the original source-language obligation.
-/
namespace YulangClosure.SourceCallbackUseR36
open NativeCallbackGrantBridgeR31 NativeCallbackGrantBridgeR32
open NativeCallbackCoordinatesR33 NativeSnapshotOwnerR34
open SourceCallbackPermissionR35

inductive Resolution (Artifact Definition Module Parse Green : Type) where
  | parameter (id : ParameterId Artifact Definition Module Parse Green)
  | other (constructor : Nat)

inductive Form (Artifact Definition Module Parse Green : Type) where
  | lambda (formal : Parameter Artifact Definition Module Parse Green) (body : Nat)
  | name (resolution : Resolution Artifact Definition Module Parse Green)
  | apply (callee argument : Nat)
  | other (constructor : Nat)

structure Expression (Artifact Definition Module Parse Green : Type) where
  occurrence : Nat
  source : SourceNodeKey Parse Green
  startByte : Nat
  endByte : Nat
  form : Form Artifact Definition Module Parse Green

structure Root (Artifact Definition Module Parse Green : Type) where
  id : RootId Artifact Definition Module Parse Green
  expressions : List (Expression Artifact Definition Module Parse Green)

structure Pool (history : AllocationHistory)
    (Artifact Definition Module Parse Green : Type) where
  roots : OwnerId history → List (Root Artifact Definition Module Parse Green)
  effects : OwnerId history → List (HirEffect Module Parse Green)

def Expression.toR35 (e : Expression Artifact Definition Module Parse Green) :
    SourceCallbackPermissionR35.Expression Artifact Definition Module Parse Green :=
  ⟨e.occurrence, e.source, e.startByte, e.endByte,
    match e.form with
    | .lambda formal body => .lambda formal body
    | .name _ => .other 0
    | .apply _ _ => .other 1
    | .other tag => .other (tag + 2)⟩

def Root.toR35 (r : Root Artifact Definition Module Parse Green) :
    SourceRoot Artifact Definition Module Parse Green :=
  ⟨r.id, r.expressions.map Expression.toR35⟩

def Pool.toR35 (p : Pool history Artifact Definition Module Parse Green) :
    SourcePool history Artifact Definition Module Parse Green :=
  ⟨fun owner => (p.roots owner).map Root.toR35, p.effects⟩

structure Site (Parse Green : Type) where
  occurrence : Nat
  source : SourceNodeKey Parse Green
  startByte : Nat
  endByte : Nat
  deriving DecidableEq

def Expression.site (e : Expression Artifact Definition Module Parse Green) : Site Parse Green :=
  ⟨e.occurrence, e.source, e.startByte, e.endByte⟩

inductive Consumption where
  | observe | execute
  deriving DecidableEq

def consumption (annotation : SourceAnnotation Artifact Definition Module Parse Green) :
    Consumption :=
  match annotation.ty with
  | .mk none _ => .observe
  | .mk (some _) _ => .execute

structure SelectedLambda (Artifact Definition Module Parse Green : Type) where
  root : Root Artifact Definition Module Parse Green
  expression : Expression Artifact Definition Module Parse Green
  formal : Parameter Artifact Definition Module Parse Green
  body : Nat
  annotation : SourceAnnotation Artifact Definition Module Parse Green

def SelectedLambda.selection (l : SelectedLambda Artifact Definition Module Parse Green) :
    SelectedFormal Artifact Definition Module Parse Green :=
  ⟨l.root.id, l.expression.occurrence, l.expression.source,
    l.expression.startByte, l.expression.endByte, l.formal, l.annotation⟩

structure Edge (Artifact Definition Module Parse Green : Type) where
  nameIndex : Nat
  name : Expression Artifact Definition Module Parse Green
  applyIndex : Nat
  application : Expression Artifact Definition Module Parse Green
  argument : Nat

structure Witness (history : AllocationHistory)
    (Artifact Definition Module Parse Green : Type) where
  permission : SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green
  nameIndex : Nat
  name : Site Parse Green
  applyIndex : Nat
  application : Site Parse Green
  resolvedFormal : ParameterId Artifact Definition Module Parse Green
  consumption : Consumption
  deriving DecidableEq

variable {history : AllocationHistory} {Artifact Definition Module Parse Green : Type}
variable [DecidableEq Artifact] [DecidableEq Definition] [DecidableEq Module]
variable [DecidableEq Parse] [DecidableEq Green]

/-- Count actual incoming direct callee edges, not equal spellings. -/
def calleeParents (root : Root Artifact Definition Module Parse Green) (nameIndex : Nat) : Nat :=
  root.expressions.countP fun expression => match expression.form with
    | .apply callee _ => callee == nameIndex
    | _ => false

/-- Failure at any exact-formal Name withholds the whole direct-use inventory. -/
def unambiguous (root : Root Artifact Definition Module Parse Green)
    (formal : ParameterId Artifact Definition Module Parse Green) : Bool :=
  root.expressions.zipIdx.all fun (expression, index) => match expression.form with
    | .name (.parameter resolved) =>
      if resolved = formal then decide (calleeParents root index ≤ 1) else true
    | _ => true

def lookupLambda (pool : Pool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri li : Nat) :
    Option (SelectedLambda Artifact Definition Module Parse Green) := do
  let root ← (pool.roots owner.hirOwner)[ri]?
  let expression ← root.expressions[li]?
  match expression.form with
  | .lambda formal body => do
    let annotation ← formal.annotation
    match annotation.ty with
    | .mk none (.function _ _) =>
      if unambiguous root formal.id then
        some ⟨root, expression, formal, body, annotation⟩
      else none
    | _ => none
  | _ => none

def lookupEdge (root : Root Artifact Definition Module Parse Green)
    (formal : ParameterId Artifact Definition Module Parse Green) (ai : Nat) :
    Option (Edge Artifact Definition Module Parse Green) := do
  let application ← root.expressions[ai]?
  match application.form with
  | .apply callee argument => do
    let name ← root.expressions[callee]?
    match name.form with
    | .name (.parameter resolved) =>
      if resolved = formal then some ⟨callee, name, ai, application, argument⟩ else none
    | _ => none
  | _ => none

def assemble (l : SelectedLambda Artifact Definition Module Parse Green)
    (edge : Edge Artifact Definition Module Parse Green)
    (permission : SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green) :
    Witness history Artifact Definition Module Parse Green :=
  ⟨permission, edge.nameIndex, edge.name.site, edge.applyIndex, edge.application.site,
    l.formal.id, consumption l.annotation⟩

/-- No caller chooses a path, polarity, row, Name, or resolved formal. -/
def issue (pool : Pool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri li ai : Nat) :
    Option (Witness history Artifact Definition Module Parse Green) := do
  let l ← lookupLambda pool owner ri li
  let edge ← lookupEdge l.root l.formal.id ai
  let permission ← issueSelected owner l.selection [.result]
  pure (assemble l edge permission)

def authenticate (pool : Pool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri li ai : Nat)
    (w : Witness history Artifact Definition Module Parse Green) : Prop :=
  issue pool owner ri li ai = some w

theorem lookupLambda_origin
    (pool : Pool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri li : Nat)
    (l : SelectedLambda Artifact Definition Module Parse Green)
    (found : lookupLambda pool owner ri li = some l) :
    (pool.roots owner.hirOwner)[ri]? = some l.root ∧
    l.root.expressions[li]? = some l.expression ∧
    l.expression.form = .lambda l.formal l.body ∧
    l.formal.annotation = some l.annotation ∧
    (∃ argument result, l.annotation.ty = .mk none (.function argument result)) ∧
    unambiguous l.root l.formal.id = true := by
  unfold lookupLambda at found
  cases hr : (pool.roots owner.hirOwner)[ri]? with
  | none => simp [hr] at found
  | some root =>
    cases he : root.expressions[li]? with
    | none => simp [hr, he] at found
    | some expression =>
      cases hf : expression.form with
      | name _ | apply _ _ | other _ => simp [hr, he, hf] at found
      | lambda formal body =>
        cases ha : formal.annotation with
        | none => simp [hr, he, hf, ha] at found
        | some annotation =>
          cases ht : annotation.ty with
          | mk effects value =>
            cases effects with
            | some row => simp [hr, he, hf, ha, ht] at found
            | none =>
              cases value <;> try simp [hr, he, hf, ha, ht] at found
              case function argument result =>
                cases hu : unambiguous root formal.id <;> simp [hu] at found
                subst l
                exact ⟨rfl, he, hf, ha, ⟨argument, result, ht⟩, hu⟩

theorem lookupLambda_r35
    (pool : Pool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri li : Nat)
    (l : SelectedLambda Artifact Definition Module Parse Green)
    (found : lookupLambda pool owner ri li = some l) :
    selectFormal pool.toR35 owner ri li = some l.selection := by
  obtain ⟨hr, he, hf, ha, _, _⟩ := lookupLambda_origin pool owner ri li l found
  simp [selectFormal, Pool.toR35, Root.toR35, Expression.toR35,
    hr, he, hf, ha, SelectedLambda.selection]

theorem lookupEdge_origin
    (root : Root Artifact Definition Module Parse Green)
    (formal : ParameterId Artifact Definition Module Parse Green) (ai : Nat)
    (edge : Edge Artifact Definition Module Parse Green)
    (found : lookupEdge root formal ai = some edge) :
    root.expressions[ai]? = some edge.application ∧ edge.applyIndex = ai ∧
    edge.application.form = .apply edge.nameIndex edge.argument ∧
    root.expressions[edge.nameIndex]? = some edge.name ∧
    edge.name.form = .name (.parameter formal) := by
  unfold lookupEdge at found
  cases ha : root.expressions[ai]? with
  | none => simp [ha] at found
  | some application =>
    cases hf : application.form with
    | lambda _ _ | name _ | other _ => simp [ha, hf] at found
    | apply callee argument =>
      cases hn : root.expressions[callee]? with
      | none => simp [ha, hf, hn] at found
      | some name =>
        cases hnf : name.form with
        | lambda _ _ | apply _ _ | other _ => simp [ha, hf, hn, hnf] at found
        | name resolution =>
          cases resolution with
          | other _ => simp [ha, hf, hn, hnf] at found
          | parameter resolved =>
            by_cases same : resolved = formal
            · simp [ha, hf, hn, hnf, same] at found
              subst edge
              exact ⟨rfl, rfl, hf, hn, same ▸ hnf⟩
            · simp [ha, hf, hn, hnf, same] at found

/-- A shadowing parameter may have identical spelling and row; its resolved
identity still cannot become the selected formal's direct source use. -/
theorem foreign_parameter_name_rejected
    (root : Root Artifact Definition Module Parse Green)
    (formal foreign : ParameterId Artifact Definition Module Parse Green)
    (ai callee argument : Nat)
    (application name : Expression Artifact Definition Module Parse Green)
    (ha : root.expressions[ai]? = some application)
    (hf : application.form = .apply callee argument)
    (hn : root.expressions[callee]? = some name)
    (hnf : name.form = .name (.parameter foreign))
    (different : foreign ≠ formal) :
    lookupEdge root formal ai = none := by
  simp [lookupEdge, ha, hf, hn, hnf, different]

theorem nonparameter_name_rejected
    (root : Root Artifact Definition Module Parse Green)
    (formal : ParameterId Artifact Definition Module Parse Green)
    (ai callee argument constructor : Nat)
    (application name : Expression Artifact Definition Module Parse Green)
    (ha : root.expressions[ai]? = some application)
    (hf : application.form = .apply callee argument)
    (hn : root.expressions[callee]? = some name)
    (hnf : name.form = .name (.other constructor)) :
    lookupEdge root formal ai = none := by
  simp [lookupEdge, ha, hf, hn, hnf]

theorem ambiguity_withholds
    (pool : Pool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri li : Nat)
    (root : Root Artifact Definition Module Parse Green)
    (expression : Expression Artifact Definition Module Parse Green)
    (formal : Parameter Artifact Definition Module Parse Green) (body : Nat)
    (annotation : SourceAnnotation Artifact Definition Module Parse Green)
    (hr : (pool.roots owner.hirOwner)[ri]? = some root)
    (he : root.expressions[li]? = some expression)
    (hf : expression.form = .lambda formal body)
    (ha : formal.annotation = some annotation)
    (ambiguous : unambiguous root formal.id = false) :
    lookupLambda pool owner ri li = none := by
  cases ht : annotation.ty with
  | mk effects value =>
    cases effects <;> cases value <;>
      simp [lookupLambda, hr, he, hf, ha, ht, ambiguous]

theorem source_origin
    (pool : Pool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri li ai : Nat)
    (w : Witness history Artifact Definition Module Parse Green)
    (authentic : authenticate pool owner ri li ai w) :
    ∃ l edge permission,
      lookupLambda pool owner ri li = some l ∧
      lookupEdge l.root l.formal.id ai = some edge ∧
      issueSelected owner l.selection [.result] = some permission ∧
      w = assemble l edge permission := by
  unfold authenticate issue at authentic
  cases hl : lookupLambda pool owner ri li with
  | none => simp [hl] at authentic
  | some l =>
    cases he : lookupEdge l.root l.formal.id ai with
    | none => simp [hl, he] at authentic
    | some edge =>
      cases hp : issueSelected owner l.selection [.result] with
      | none => simp [hl, he, hp] at authentic
      | some permission =>
        simp [hl, he, hp] at authentic
        exact ⟨l, edge, permission, rfl, he, hp, authentic.symm⟩

theorem authenticated_r35
    (pool : Pool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri li ai : Nat)
    (w : Witness history Artifact Definition Module Parse Green)
    (authentic : authenticate pool owner ri li ai w) :
    SourceCallbackPermissionR35.authenticate pool.toR35 owner ri li [.result] w.permission := by
  obtain ⟨l, edge, permission, hl, _, hp, same⟩ := source_origin pool owner ri li ai w authentic
  subst w
  unfold SourceCallbackPermissionR35.authenticate SourceCallbackPermissionR35.issue
  rw [lookupLambda_r35 pool owner ri li l hl]
  exact hp

theorem authenticated_coordinates
    (pool : Pool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri li ai : Nat)
    (w : Witness history Artifact Definition Module Parse Green)
    (authentic : authenticate pool owner ri li ai w) :
    ∃ (l : SelectedLambda Artifact Definition Module Parse Green)
      (edge : Edge Artifact Definition Module Parse Green),
      (pool.roots owner.hirOwner)[ri]? = some l.root ∧
      l.root.expressions[li]? = some l.expression ∧
      l.expression.form = .lambda l.formal l.body ∧
      l.formal.annotation = some l.annotation ∧
      l.root.expressions[ai]? = some edge.application ∧
      edge.application.form = .apply edge.nameIndex edge.argument ∧
      l.root.expressions[edge.nameIndex]? = some edge.name ∧
      edge.name.form = .name (.parameter l.formal.id) ∧
      unambiguous l.root l.formal.id = true ∧
      w.name = edge.name.site ∧ w.application = edge.application.site ∧
      w.nameIndex = edge.nameIndex ∧ w.applyIndex = ai ∧
      w.resolvedFormal = l.formal.id ∧ w.permission.binding.formal = l.formal.id ∧
      w.permission.binding.root = l.root.id ∧
      w.permission.binding.lambdaOccurrence = l.expression.occurrence ∧
      w.permission.binding.snapshotOwner = owner.hirOwner ∧ w.consumption = .observe := by
  obtain ⟨l, edge, permission, hl, he, hp, same⟩ := source_origin pool owner ri li ai w authentic
  obtain ⟨hr, hx, hf, ha, ⟨argument, result, ht⟩, hu⟩ :=
    lookupLambda_origin pool owner ri li l hl
  obtain ⟨hea, hei, hef, hen, henf⟩ := lookupEdge_origin l.root l.formal.id ai edge he
  obtain ⟨_, _, row, _, hpermission⟩ := (issueSelected_exact owner l.selection [.result] permission).mp hp
  subst w
  subst permission
  refine ⟨l, edge, hr, hx, hf, ha, hea, hef, hen, henf, hu,
    rfl, rfl, rfl, hei, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp [assemble, consumption, ht]

theorem authenticated_result_row
    (pool : Pool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri li ai : Nat)
    (w : Witness history Artifact Definition Module Parse Green)
    (authentic : authenticate pool owner ri li ai w) :
    ∃ l argument result row,
      lookupLambda pool owner ri li = some l ∧
      l.annotation.ty = .mk none (.function argument result) ∧
      selectRow result [] = some row ∧
      w.permission.row = row ∧
      (∀ index : Nat, w.permission.row.concrete[index]? = row.concrete[index]?) ∧
      w.permission.row.variables = row.variables ∧
      w.permission.binding.rowPath = [.result] ∧
      w.permission.binding.rowContravariant = true := by
  obtain ⟨l, edge, permission, hl, _, hp, same⟩ := source_origin pool owner ri li ai w authentic
  obtain ⟨_, _, _, _, ⟨argument, result, ht⟩, _⟩ := lookupLambda_origin pool owner ri li l hl
  obtain ⟨_, _, row, hrow, hpermission⟩ := (issueSelected_exact owner l.selection [.result] permission).mp hp
  have resultRow : selectRow result [] = some row := by
    simpa [SelectedLambda.selection, ht, selectRow] using hrow
  subst w
  subst permission
  exact ⟨l, argument, result, row, hl, ht, resultRow, rfl, fun _ => rfl, rfl, rfl, rfl⟩

theorem reject_changed_projection {α : Type}
    (pool : Pool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri li ai : Nat)
    (issued candidate : Witness history Artifact Definition Module Parse Green)
    (computed : issue pool owner ri li ai = some issued)
    (projection : Witness history Artifact Definition Module Parse Green → α)
    (changed : projection candidate ≠ projection issued) :
    ¬ authenticate pool owner ri li ai candidate := by
  intro accepted
  have same : issued = candidate := Option.some.inj (computed.symm.trans accepted)
  exact changed (congrArg projection same.symm)

/-- These falsifiers are distinct projections of one authenticated witness. -/
theorem falsifier_rejection
    (pool : Pool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri li ai : Nat)
    (issued candidate : Witness history Artifact Definition Module Parse Green)
    (computed : issue pool owner ri li ai = some issued)
    (changed : candidate.permission.binding ≠ issued.permission.binding ∨
      candidate.resolvedFormal ≠ issued.resolvedFormal ∨
      candidate.name ≠ issued.name ∨ candidate.application ≠ issued.application ∨
      candidate.nameIndex ≠ issued.nameIndex ∨ candidate.applyIndex ≠ issued.applyIndex ∨
      candidate.permission.row.concrete ≠ issued.permission.row.concrete ∨
      candidate.permission.row.variables ≠ issued.permission.row.variables ∨
      candidate.permission.row.position ≠ issued.permission.row.position ∨
      candidate.consumption ≠ issued.consumption) :
    ¬ authenticate pool owner ri li ai candidate := by
  intro accepted
  have same : issued = candidate := Option.some.inj (computed.symm.trans accepted)
  subst candidate
  simp at changed

theorem covariant_or_other_path_rejected
    (pool : Pool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri li ai : Nat)
    (candidate : Witness history Artifact Definition Module Parse Green)
    (bad : candidate.permission.binding.rowContravariant = false ∨
      candidate.permission.binding.rowPath ≠ [.result]) :
    ¬ authenticate pool owner ri li ai candidate := by
  intro accepted
  obtain ⟨_, _, _, _, _, _, _, _, _, _, path, polarity⟩ :=
    authenticated_result_row pool owner ri li ai candidate accepted
  cases bad with
  | inl h => simp [polarity] at h
  | inr h => exact h path

end YulangClosure.SourceCallbackUseR36

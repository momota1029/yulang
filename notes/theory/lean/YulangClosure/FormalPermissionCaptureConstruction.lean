import Std

/-!
Constructive finite Function/Tuple capture slice, not whole effect hygiene.
Source: candidate_effect.rs `candidate_formal_value_pair` and
`candidate_formal_effect_port`; candidate_scheme.rs `Capture::intern`,
`expand_node`, and negative-formal-root publication. The input below is the
already allocated structural pair. Establishing that every actual source
construction and live capture yields this finite catalog remains OPEN.

The catalog traverses both sides of the pair and interns equal endpoints.
Its numbering order is not the Rust pending-worklist order. The image result
uses its actual computed indices, never an assumed graph-image equation.
Tuple children are inline lists, the mathematical view of the native slice.
Opaque effect endpoints retain covariant views without pretending they are rows.
-/
namespace YulangClosure.FormalPermissionCaptureConstruction

noncomputable section

inductive Step where
  | argument | result | element (index : Nat)
  deriving DecidableEq, Repr

structure Metadata where
  parameter : Nat
  occurrence : Nat
  owner : Nat
  scope : Nat
  sourceRow : Nat
  concrete : List Nat
  deriving DecidableEq, Repr

inductive Effect where
  | row (key : Nat)
  | opaque (key : Nat)
  deriving DecidableEq, Repr

structure Ports where
  positive : Effect
  negative : Effect
  grant : Option Metadata
  deriving DecidableEq, Repr

/-- Fresh omitted/negative-concrete ports and symbolic ports share the row
between polar sides; the caller supplies the allocation counter or symbol key. -/
def sharedPorts (key : Nat) (grant : Option Metadata := none) : Ports :=
  ⟨.row key, .row key, grant⟩

def allocate (next : Nat) (grant : Option Metadata) : Ports × Nat :=
  (sharedPorts next grant, next + 1)

theorem allocation_shared (next : Nat) (grant : Option Metadata) :
    (allocate next grant).1.positive = .row next ∧
    (allocate next grant).1.negative = .row next ∧
    (allocate next grant).1.grant = grant ∧ (allocate next grant).2 = next + 1 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

inductive Shape where
  | atom (identity : Nat)
  | function (argument : Shape) (argumentEffects : Ports)
      (result : Shape) (resultEffects : Ports)
  | tuple (elements : List Shape)
  deriving Repr

instance : DecidableEq Shape := Classical.typeDecidableEq Shape

inductive Endpoint where
  | value (shape : Shape) (positive : Bool)
  | effect (effect : Effect) (positive : Bool)
  deriving DecidableEq, Repr

def Ports.at (ports : Ports) (positive : Bool) : Effect :=
  if positive then ports.positive else ports.negative

def children : Endpoint → List Endpoint
  | .effect _ _ => []
  | .value (.atom _) _ => []
  | .value (.function a ae r re) p =>
      [.value a (!p), .effect (ae.at (!p)) (!p),
       .effect (re.at p) p, .value r p]
  | .value (.tuple elements) p => elements.map (fun child => .value child p)

/-- Both polar terms are constructed together. Function argument polarity
reverses, result polarity is retained, and Tuple preserves polarity. -/
def pair (shape : Shape) : Endpoint × Endpoint :=
  (.value shape true, .value shape false)

def catalog : Shape → List Endpoint
  | .atom id => [.value (.atom id) true, .value (.atom id) false]
  | .function a ae r re =>
      [.value (.function a ae r re) true, .value (.function a ae r re) false,
       .effect ae.positive true, .effect ae.negative false,
       .effect re.positive true, .effect re.negative false] ++ catalog a ++ catalog r
  | .tuple elements =>
      [.value (.tuple elements) true, .value (.tuple elements) false] ++
        elements.flatMap catalog

/-- First-insertion endpoint interning; an existing endpoint keeps its index. -/
def intern (keys : List Endpoint) (endpoint : Endpoint) : List Endpoint :=
  if endpoint ∈ keys then keys else keys ++ [endpoint]

def internAll : List Endpoint → List Endpoint → List Endpoint
  | keys, [] => keys
  | keys, endpoint :: rest => internAll (intern keys endpoint) rest

theorem mem_intern (keys : List Endpoint) (endpoint key : Endpoint) :
    key ∈ intern keys endpoint ↔ key ∈ keys ∨ key = endpoint := by
  by_cases h : endpoint ∈ keys
  · simp [intern, h]; exact fun hEq => hEq ▸ h
  · simp [intern, h]

theorem mem_internAll (requests keys : List Endpoint) (key : Endpoint) :
    key ∈ internAll keys requests ↔ key ∈ keys ∨ key ∈ requests := by
  induction requests generalizing keys with
  | nil => simp [internAll]
  | cons endpoint rest ih =>
      simp only [internAll, ih, mem_intern, List.mem_cons]
      exact or_assoc

def captureKeys (shape : Shape) : List Endpoint := internAll [] (catalog shape)

theorem mem_captureKeys (shape : Shape) (key : Endpoint) :
    key ∈ captureKeys shape ↔ key ∈ catalog shape := by
  simp [captureKeys, mem_internAll]

def image (shape : Shape) (endpoint : Endpoint) : Nat :=
  (captureKeys shape).idxOf endpoint

inductive Node where
  | function (positive : Bool) (argument argumentEffect resultEffect result : Nat)
  | tuple (positive : Bool) (elements : List Nat)
  | row (positive : Bool) (key : Nat)
  | other
  deriving DecidableEq, Repr

def expand (index : Endpoint → Nat) : Endpoint → Node
  | .effect (.row key) p => .row p key
  | .effect (.opaque _) _ => .other
  | .value (.atom _) _ => .other
  | .value (.function a ae r re) p =>
      .function p (index (.value a (!p))) (index (.effect (ae.at (!p)) (!p)))
        (index (.effect (re.at p) p)) (index (.value r p))
  | .value (.tuple elements) p =>
      .tuple p (elements.map (fun child => index (.value child p)))

def nodes (shape : Shape) (index : Nat) : Option Node :=
  ((captureKeys shape)[index]?).map (expand (image shape))

theorem nodes_image (shape : Shape) (endpoint : Endpoint)
    (member : endpoint ∈ catalog shape) :
    nodes shape (image shape endpoint) = some (expand (image shape) endpoint) := by
  have h := (mem_captureKeys shape endpoint).mpr member
  simp only [nodes, image]
  rw [List.getElem?_eq_getElem (List.idxOf_lt_length_iff.mpr h), List.getElem_idxOf]
  rfl

def walk (shape : Shape) (current : Nat) : List Step → Option Nat
  | [] => none
  | step :: rest =>
      match nodes shape current, step with
      | some (.function _ a ae _re _r), .argument =>
          match rest with | [] => some ae | _ :: _ => walk shape a rest
      | some (.function _ _a _ae re r), .result =>
          match rest with | [] => some re | _ :: _ => walk shape r rest
      | some (.tuple _ elements), .element i =>
          match rest with
          | [] => none
          | _ :: _ => (elements[i]?).bind (fun child => walk shape child rest)
      | _, _ => none

/-- Original allocated endpoint reached by the retained source path.
This is a relation on the constructed source pair, not on a captured graph.
Final grants require composed negative polarity and a shared allocated row. -/
inductive Origin : Shape → Bool → List Step → Nat → Metadata → Prop where
  | argument (a r : Shape) (re : Ports) (key : Nat) (metadata : Metadata) :
      Origin (.function a (sharedPorts key (some metadata)) r re) true
        [.argument] key metadata
  | result (a r : Shape) (ae : Ports) (key : Nat) (metadata : Metadata) :
      Origin (.function a ae r (sharedPorts key (some metadata))) false
        [.result] key metadata
  | inArgument {a r : Shape} {ae re : Ports} {p : Bool} {path : List Step}
      {key : Nat} {metadata : Metadata} : Origin a (!p) path key metadata →
      Origin (.function a ae r re) p (.argument :: path) key metadata
  | inResult {a r : Shape} {ae re : Ports} {p : Bool} {path : List Step}
      {key : Nat} {metadata : Metadata} : Origin r p path key metadata →
      Origin (.function a ae r re) p (.result :: path) key metadata
  | inElement {elements : List Shape} {child : Shape} {i : Nat} {p : Bool}
      {path : List Step} {key : Nat} {metadata : Metadata} :
      elements[i]? = some child → Origin child p path key metadata →
      Origin (.tuple elements) p (.element i :: path) key metadata

theorem origin_nonempty {shape : Shape} {p : Bool} {path : List Step}
    {key : Nat} {metadata : Metadata} (origin : Origin shape p path key metadata) :
    path ≠ [] := by cases origin <;> simp

theorem catalog_root (shape : Shape) (p : Bool) : .value shape p ∈ catalog shape := by
  cases shape <;> cases p <;> simp [catalog]

theorem catalog_argument (a r : Shape) (ae re : Ports) :
    ∀ e ∈ catalog a, e ∈ catalog (.function a ae r re) := by
  intro e h; simp [catalog, h]

theorem catalog_result (a r : Shape) (ae re : Ports) :
    ∀ e ∈ catalog r, e ∈ catalog (.function a ae r re) := by
  intro e h; simp [catalog, h]

theorem catalog_element (elements : List Shape) (i : Nat) (child : Shape)
    (found : elements[i]? = some child) :
    ∀ e ∈ catalog child, e ∈ catalog (.tuple elements) := by
  intro e h
  have childMem : child ∈ elements := List.mem_of_getElem? found
  simp only [catalog, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  exact Or.inr (List.mem_flatMap.mpr ⟨child, childMem, h⟩)

/-- No endpoint-image equation is supplied: lookup follows the constructed
catalog, first-insertion interning, and expansion functions. The ambient root
may contain this source pair at any structural descendant. -/
theorem origin_image {source : Shape} {p : Bool} {path : List Step}
    {key : Nat} {metadata : Metadata} (origin : Origin source p path key metadata)
    (ambient : Shape) (contained : ∀ e ∈ catalog source, e ∈ catalog ambient) :
    walk ambient (image ambient (.value source p)) path =
      some (image ambient (.effect (.row key) false)) ∧
    .effect (.row key) false ∈ catalog ambient := by
  induction origin with
  | argument a r re key metadata =>
      have root := nodes_image ambient _ (contained _ (catalog_root _ true))
      have port : Endpoint.effect (.row key) false ∈ catalog ambient := by
        apply contained; simp [catalog, sharedPorts]
      exact ⟨by simp only [walk, root]; rfl, port⟩
  | result a r ae key metadata =>
      have root := nodes_image ambient _ (contained _ (catalog_root _ false))
      have port : Endpoint.effect (.row key) false ∈ catalog ambient := by
        apply contained; simp [catalog, sharedPorts]
      exact ⟨by simp only [walk, root]; rfl, port⟩
  | @inArgument a r ae re p path key metadata origin ih =>
      have inner := ih (fun e h => contained e (catalog_argument a r ae re e h))
      have root := nodes_image ambient _ (contained _ (catalog_root _ p))
      cases path with
      | nil => exact False.elim (origin_nonempty origin rfl)
      | cons step rest => exact ⟨by simpa [walk, root, expand] using inner.1, inner.2⟩
  | @inResult a r ae re p path key metadata origin ih =>
      have inner := ih (fun e h => contained e (catalog_result a r ae re e h))
      have root := nodes_image ambient _ (contained _ (catalog_root _ p))
      cases path with
      | nil => exact False.elim (origin_nonempty origin rfl)
      | cons step rest => exact ⟨by simpa [walk, root, expand] using inner.1, inner.2⟩
  | @inElement elements child i p path key metadata found origin ih =>
      have inner := ih (fun e h => contained e (catalog_element elements i child found e h))
      have root := nodes_image ambient _ (contained _ (catalog_root _ p))
      cases path with
      | nil => exact False.elim (origin_nonempty origin rfl)
      | cons step rest =>
          exact ⟨by simpa [walk, root, expand, List.getElem?_map, found] using inner.1, inner.2⟩

def publishedRoot (shape : Shape) : Option Nat :=
  match shape with
  | .atom _ => none
  | _ => some (image shape (.value shape false))

structure Exported where
  metadata : Metadata
  path : List Step
  port : Nat
  deriving DecidableEq, Repr

def project (shape : Shape) (metadata : Metadata) (path : List Step) : Option Exported := do
  let root ← publishedRoot shape
  let port ← walk shape root path
  match nodes shape port with
  | some (.row _ _) => pure ⟨metadata, path, port⟩
  | _ => none

theorem constructor_to_export {shape : Shape} {path : List Step} {key : Nat}
    {metadata : Metadata} (origin : Origin shape false path key metadata) :
    project shape metadata path =
      some ⟨metadata, path, image shape (.effect (.row key) false)⟩ := by
  have obtained := origin_image origin shape (fun _ h => h)
  have row := nodes_image shape _ obtained.2
  have root : publishedRoot shape = some (image shape (.value shape false)) := by
    cases shape with
    | atom id => cases origin
    | function => rfl
    | tuple => rfl
  simp [project, root, obtained.1, row, expand]

theorem shared_endpoint_image (shape : Shape) (left right : Nat)
    (same : left = right) (p : Bool) :
    image shape (.effect (.row left) p) = image shape (.effect (.row right) p) := by
  cases same; rfl

theorem export_metadata {shape : Shape} {metadata : Metadata} {path : List Step}
    {out : Exported} (success : project shape metadata path = some out) :
    out.metadata = metadata ∧ out.path = path := by
  unfold project at success
  cases root : publishedRoot shape with
  | none => simp [root] at success
  | some current =>
      cases port : walk shape current path with
      | none => simp [root, port] at success
      | some index =>
          cases node : nodes shape index with
          | none => simp [root, port, node] at success
          | some value =>
              cases value <;> simp [root, port, node] at success
              cases success; exact ⟨rfl, rfl⟩

structure Retained where
  metadata : Metadata
  path : List Step
  allocatedRow : Nat
  deriving DecidableEq, Repr

def projectAll (shape : Shape) : List Retained → Option (List Exported)
  | [] => some []
  | entry :: rest => do
      let exported ← project shape entry.metadata entry.path
      let remaining ← projectAll shape rest
      pure (exported :: remaining)

/-- Each original record and its one allocated-row witness is reused. There
is no distinctness premise: sharing never collapses source records. -/
theorem constructor_list_export (shape : Shape) (entries : List Retained)
    (origins : ∀ entry ∈ entries,
      Origin shape false entry.path entry.allocatedRow entry.metadata) :
    projectAll shape entries = some (entries.map (fun entry =>
      ⟨entry.metadata, entry.path, image shape (.effect (.row entry.allocatedRow) false)⟩)) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      have first := constructor_to_export (origins entry (by simp))
      have remaining := ih (fun entry h => origins entry (by simp [h]))
      simp [projectAll, first, remaining]

theorem constructor_list_metadata (shape : Shape) (entries : List Retained)
    (origins : ∀ entry ∈ entries,
      Origin shape false entry.path entry.allocatedRow entry.metadata) :
    (projectAll shape entries).map (List.map Exported.metadata) =
      some (entries.map Retained.metadata) := by
  rw [constructor_list_export shape entries origins]
  simp [List.map_map, Function.comp_def]

end
end YulangClosure.FormalPermissionCaptureConstruction

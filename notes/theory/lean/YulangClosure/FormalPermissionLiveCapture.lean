import YulangClosure.FormalPermissionCaptureConstruction

/-!
Successful constructor histories and the key-allocation part of live capture.
The successful history constructors follow candidate_effect.rs:1414–1544:
argument value, result value, argument effect, result effect. They preserve
allocation counters, composed polarity, source metadata and each retained path.
The empty Tuple history is an internal list accumulator; a Tuple value requires
nonempty elements. Port covariant payloads are delegated signature results,
not an interpretation of candidate_signature_effect.

Capture pending is the REVERSE of Rust's Vec (head = pending.pop()). Discovery
transitions admit row/bound/evidence/context-produced endpoint requests, but
DO NOT establish that Rust generates exactly those requests. No theorem below
asserts root arrival, canonical representative correctness, concrete Rust
simulation, or the original parent soundness/Effect-hygiene result.
-/
namespace YulangClosure.FormalPermissionLiveCapture

open FormalPermissionCaptureConstruction
noncomputable section

structure Emission where
  metadata : Metadata
  row : Nat
  deriving DecidableEq, Repr

/-- Successful effect-port branch, including its one allocation counter.
The positive explicit branch delegates to the existing signature constructor. -/
inductive PortConstruction : Bool → Nat → Ports → List Emission → Nat → Prop where
  | omitted (p : Bool) (next : Nat) :
      PortConstruction p next (sharedPorts next) [] (next + 1)
  | symbolic (p : Bool) (next key : Nat) :
      PortConstruction p next (sharedPorts key) [] next
  | concrete (next : Nat) (m : Metadata) (nonempty : m.concrete ≠ []) :
      PortConstruction false next (sharedPorts next (some m)) [⟨m, next⟩] (next + 1)
  | covariant (next : Nat) (positive negative : Effect) :
      PortConstruction true next ⟨positive, negative, none⟩ [] next

/-- Any emitted permission recovers the fresh shared row and negative polarity.
No free Origin proof or endpoint-image equation is an input. -/
theorem port_emission {p : Bool} {before after : Nat} {ports : Ports}
    {emissions : List Emission} (built : PortConstruction p before ports emissions after)
    {entry : Emission} (member : entry ∈ emissions) :
    p = false ∧ entry.row = before ∧ after = before + 1 ∧
      ports = sharedPorts entry.row (some entry.metadata) ∧ entry.metadata.concrete ≠ [] := by
  cases built <;> simp_all

def prependPath (step : Step) (entries : List Retained) : List Retained :=
  entries.map (fun e => { e with path := step :: e.path })

def atPort (step : Step) (entries : List Emission) : List Retained :=
  entries.map (fun e => ⟨e.metadata, [step], e.row⟩)

def shiftPath : List Step → List Step
  | .element i :: rest => .element (i + 1) :: rest
  | other => other

def shift (entries : List Retained) : List Retained :=
  entries.map (fun e => {e with path := shiftPath e.path})

mutual
  /-- Successful value-pair construction. Atomic identities cover scalar,
  variable and hole leaves; their source/store authentication is separate. -/
  inductive Construction : Bool → Nat → Shape → List Retained → Nat → Prop where
    | atom (p : Bool) (next identity : Nat) : Construction p next (.atom identity) [] next
    | function {p : Bool} {n n₁ n₂ n₃ n₄ : Nat}
        {a r : Shape} {ae re : Ports} {as rs : List Retained} {aes res : List Emission}
        (argument : Construction (!p) n a as n₁)
        (result : Construction p n₁ r rs n₂)
        (argumentEffect : PortConstruction (!p) n₂ ae aes n₃)
        (resultEffect : PortConstruction p n₃ re res n₄) :
        Construction p n (.function a ae r re)
          (prependPath .argument as ++ prependPath .result rs ++ atPort .argument aes ++ atPort .result res) n₄
    | tuple {p : Bool} {n after : Nat} {elements : List Shape} {entries : List Retained}
        (children : TupleConstruction p n elements entries after) (nonempty : elements ≠ []) :
        Construction p n (.tuple elements) entries after
  /-- Sequential Tuple loop; Element indices are shifted after each head. -/
  inductive TupleConstruction : Bool → Nat → List Shape → List Retained → Nat → Prop where
    | nil (p : Bool) (next : Nat) : TupleConstruction p next [] [] next
    | cons {p : Bool} {n middle after : Nat} {head : Shape} {tail : List Shape}
        {first rest : List Retained}
        (child : Construction p n head first middle)
        (remaining : TupleConstruction p middle tail rest after) :
        TupleConstruction p n (head :: tail) (prependPath (.element 0) first ++ shift rest) after
end

theorem shifted_tuple_origin {elements : List Shape} {head : Shape} {p : Bool}
    {path : List Step} {row : Nat} {m : Metadata}
    (origin : Origin (.tuple elements) p path row m) :
    Origin (.tuple (head :: elements)) p
      (shiftPath path) row m := by
  cases origin with
  | @inElement elements child i p path key metadata found inner =>
      exact .inElement (by simpa using found) inner

mutual
  theorem construction_origins {p : Bool} {before after : Nat} {shape : Shape}
      {entries : List Retained} (built : Construction p before shape entries after) :
      ∀ entry ∈ entries, Origin shape p entry.path entry.allocatedRow entry.metadata := by
    cases built with
    | atom => simp
    | @function p n n₁ n₂ n₃ n₄ a r ae re as rs aes res argument result argumentEffect resultEffect =>
        intro entry member
        simp only [List.mem_append] at member
        rcases member with ((first | second) | third) | fourth
        · obtain ⟨e, mem, rfl⟩ := List.mem_map.mp first
          exact .inArgument (construction_origins argument e mem)
        · obtain ⟨e, mem, rfl⟩ := List.mem_map.mp second
          exact .inResult (construction_origins result e mem)
        · obtain ⟨e, mem, rfl⟩ := List.mem_map.mp third
          obtain ⟨negative, _, _, same, _⟩ := port_emission argumentEffect mem
          cases p with
          | false => simp at negative
          | true => rw [same]; exact .argument a r re e.row e.metadata
        · obtain ⟨e, mem, rfl⟩ := List.mem_map.mp fourth
          obtain ⟨negative, _, _, same, _⟩ := port_emission resultEffect mem
          cases p with
          | true => simp at negative
          | false => rw [same]; exact .result a r ae e.row e.metadata
    | tuple children _ => exact tuple_construction_origins children
  theorem tuple_construction_origins {p : Bool} {before after : Nat}
      {elements : List Shape} {entries : List Retained}
      (built : TupleConstruction p before elements entries after) :
      ∀ entry ∈ entries, Origin (.tuple elements) p entry.path entry.allocatedRow entry.metadata := by
    cases built with
    | nil => simp
    | cons child remaining =>
        intro entry member
        rcases List.mem_append.mp member with first | rest
        · obtain ⟨e, mem, rfl⟩ := List.mem_map.mp first
          exact .inElement rfl (construction_origins child e mem)
        · obtain ⟨e, mem, rfl⟩ := List.mem_map.mp rest
          exact shifted_tuple_origin (tuple_construction_origins remaining e mem)
end

/-- Apply the new constructor result to the previously checked catalog theorem.
All records retain their one source metadata/path/allocated-row witness. -/
theorem constructed_catalog_export {before after : Nat} {shape : Shape}
    {entries : List Retained} (built : Construction false before shape entries after) :
    projectAll shape entries = some (entries.map (fun entry =>
      ⟨entry.metadata, entry.path, image shape (.effect (.row entry.allocatedRow) false)⟩)) :=
  constructor_list_export shape entries (construction_origins built)

structure Capture where
  keys : List Endpoint := []
  pending : List Endpoint := []
  expanded : List Endpoint := []
  deriving Repr

def Capture.index (s : Capture) (endpoint : Endpoint) : Nat := s.keys.idxOf endpoint

/-- canon is an explicit frozen representative function. Its correspondence
with session.canonical_value/effect and intrusion.rep is an OPEN owner. -/
def Capture.intern (canon : Endpoint → Endpoint) (s : Capture) (request : Endpoint) : Capture :=
  let endpoint := canon request
  if endpoint ∈ s.keys then s
  else {s with keys := s.keys ++ [endpoint], pending := endpoint :: s.pending}

def Capture.internAll (canon : Endpoint → Endpoint) : Capture → List Endpoint → Capture
  | s, [] => s
  | s, e :: rest => (s.intern canon e).internAll canon rest

/-- Prefix extension is derived from interning, independent of the schedule. -/
theorem intern_extension (canon : Endpoint → Endpoint) (s : Capture) (e : Endpoint) :
    ∃ suffix, (s.intern canon e).keys = s.keys ++ suffix := by
  by_cases h : canon e ∈ s.keys
  · exact ⟨[], by simp [Capture.intern, h]⟩
  · exact ⟨[canon e], by simp [Capture.intern, h]⟩

theorem internAll_extension (canon : Endpoint → Endpoint) (s : Capture) (requests : List Endpoint) :
    ∃ suffix, (s.internAll canon requests).keys = s.keys ++ suffix := by
  induction requests generalizing s with
  | nil => exact ⟨[], (List.append_nil _).symm⟩
  | cons e rest ih =>
      obtain ⟨first, hf⟩ := intern_extension canon s e
      obtain ⟨later, hl⟩ := ih (s.intern canon e)
      exact ⟨first ++ later, by simp only [Capture.internAll, hl, hf, List.append_assoc]⟩

theorem intern_index_stable (canon : Endpoint → Endpoint) (s : Capture) (e old : Endpoint)
    (member : old ∈ s.keys) : (s.intern canon e).index old = s.index old := by
  obtain ⟨suffix, extension⟩ := intern_extension canon s e
  simp only [Capture.index, extension, List.idxOf_append, member, ↓reduceIte]

theorem internAll_index_stable (canon : Endpoint → Endpoint) (s : Capture)
    (requests : List Endpoint) (old : Endpoint) (member : old ∈ s.keys) :
    (s.internAll canon requests).index old = s.index old := by
  obtain ⟨suffix, extension⟩ := internAll_extension canon s requests
  simp only [Capture.index, extension, List.idxOf_append, member, ↓reduceIte]

theorem mem_intern_keys (canon : Endpoint → Endpoint) (s : Capture) (request key : Endpoint) :
    key ∈ (s.intern canon request).keys ↔ key ∈ s.keys ∨ key = canon request := by
  by_cases present : canon request ∈ s.keys
  · simp [Capture.intern, present]
    exact fun same => same ▸ present
  · simp [Capture.intern, present]

theorem mem_internAll_keys (canon : Endpoint → Endpoint) (s : Capture)
    (requests : List Endpoint) (key : Endpoint) :
    key ∈ (s.internAll canon requests).keys ↔ key ∈ s.keys ∨ key ∈ requests.map canon := by
  induction requests generalizing s with
  | nil => simp [Capture.internAll]
  | cons request rest ih =>
      simp only [Capture.internAll, ih, mem_intern_keys, List.map_cons, List.mem_cons]
      exact or_assoc

/-- A miss pushes exactly once and gives the old node-vector length. -/
theorem intern_miss (canon : Endpoint → Endpoint) (s : Capture) (e : Endpoint)
    (fresh : canon e ∉ s.keys) :
    (s.intern canon e).keys = s.keys ++ [canon e] ∧
    (s.intern canon e).pending = canon e :: s.pending ∧
    (s.intern canon e).index (canon e) = s.keys.length := by
  simp [Capture.intern, fresh, Capture.index, List.idxOf_append]

/-- A hit does not push; it returns the original first-insertion index. -/
theorem intern_hit (canon : Endpoint → Endpoint) (s : Capture) (e : Endpoint)
    (old : canon e ∈ s.keys) : s.intern canon e = s := by
  simp [Capture.intern, old]

/-- Exact LIFO expansion of Function/Tuple structural children. Node writes
and row discovery are not represented by this key-only transition. -/
def Capture.popExpand (canon : Endpoint → Endpoint) (s : Capture) : Option Capture :=
  match s.pending with
  | [] => none
  | endpoint :: rest =>
      let popped := {s with pending := rest, expanded := s.expanded ++ [endpoint]}
      some (popped.internAll canon (children endpoint))

theorem popExpand_lifo (canon : Endpoint → Endpoint) (s : Capture) (endpoint : Endpoint)
    (rest : List Endpoint) (pending : s.pending = endpoint :: rest) :
    s.popExpand canon = some
      (({s with pending := rest, expanded := s.expanded ++ [endpoint]} : Capture).internAll
        canon (children endpoint)) := by
  simp only [Capture.popExpand, pending]

theorem popExpand_discovers_children (canon : Endpoint → Endpoint) {s t : Capture}
    {endpoint : Endpoint} {rest : List Endpoint} (pending : s.pending = endpoint :: rest)
    (success : s.popExpand canon = some t) :
    ∀ child ∈ children endpoint, canon child ∈ t.keys := by
  rw [popExpand_lifo canon s endpoint rest pending] at success
  cases success
  intro child member
  exact (mem_internAll_keys canon _ _ _).mpr
    (Or.inr (List.mem_map.mpr ⟨child, member, rfl⟩))

inductive Discovery where
  | seed | row | bound | evidence | context
  deriving DecidableEq, Repr

/-- The two ways the source loop can add endpoint keys. A Discovery transition
records its provenance category but does not claim it produces arbitrary
requests in Rust. Exact request extraction remains OPEN. -/
inductive Transition (canon : Endpoint → Endpoint) : Capture → Capture → Prop where
  | expand {s t : Capture} (success : s.popExpand canon = some t) : Transition canon s t
  | discover (kind : Discovery) (s : Capture) (requests : List Endpoint) :
      Transition canon s (s.internAll canon requests)

theorem popExpand_extension (canon : Endpoint → Endpoint) {s t : Capture}
    (success : s.popExpand canon = some t) : ∃ suffix, t.keys = s.keys ++ suffix := by
  unfold Capture.popExpand at success
  cases pending : s.pending with
  | nil => simp [pending] at success
  | cons endpoint rest =>
      simp only [pending, Option.some.injEq] at success
      subst t
      exact internAll_extension canon _ _

theorem transition_extension {canon : Endpoint → Endpoint} {s t : Capture}
    (step : Transition canon s t) : ∃ suffix, t.keys = s.keys ++ suffix := by
  cases step with
  | expand success => exact popExpand_extension canon success
  | discover _ s requests => exact internAll_extension canon s requests

inductive Run (canon : Endpoint → Endpoint) : Capture → Capture → Prop where
  | refl (s : Capture) : Run canon s s
  | snoc {s t u : Capture} (history : Run canon s t) (step : Transition canon t u) : Run canon s u

theorem run_extension {canon : Endpoint → Endpoint} {s t : Capture}
    (run : Run canon s t) : ∃ suffix, t.keys = s.keys ++ suffix := by
  induction run with
  | refl => exact ⟨[], (List.append_nil _).symm⟩
  | snoc _ step ih =>
      obtain ⟨before, hb⟩ := ih
      obtain ⟨after, ha⟩ := transition_extension step
      exact ⟨before ++ after, by rw [ha, hb, List.append_assoc]⟩

theorem run_index_stable {canon : Endpoint → Endpoint} {s t : Capture}
    (run : Run canon s t) (endpoint : Endpoint) (member : endpoint ∈ s.keys) :
    t.index endpoint = s.index endpoint := by
  obtain ⟨suffix, extension⟩ := run_extension run
  simp only [Capture.index, extension, List.idxOf_append, member, ↓reduceIte]

/-- Every child discovered by an actual modeled pop remains interned after
all later interleaved row/bound/evidence/context steps. -/
theorem discovered_child_retained {canon : Endpoint → Endpoint} {s expanded final : Capture}
    {endpoint child : Endpoint} {rest : List Endpoint}
    (pending : s.pending = endpoint :: rest) (popped : s.popExpand canon = some expanded)
    (member : child ∈ children endpoint) (later : Run canon expanded final) :
    canon child ∈ final.keys ∧ final.index (canon child) = expanded.index (canon child) := by
  have arrived := popExpand_discovers_children canon pending popped child member
  obtain ⟨suffix, extension⟩ := run_extension later
  exact ⟨by rw [extension]; exact List.mem_append_left _ arrived,
    run_index_stable later _ arrived⟩

/-- Explicit catalog-to-live index renaming. This can be noninjective if the
provided canonical representative identifies endpoints; no injectivity is
smuggled in as a consequence of indexing. -/
def renameIndex (shape : Shape) (canon : Endpoint → Endpoint) (s : Capture) (i : Nat) : Nat :=
  match (captureKeys shape)[i]? with
  | none => s.keys.length
  | some endpoint => s.index (canon endpoint)

theorem rename_catalog_image (shape : Shape) (canon : Endpoint → Endpoint) (s : Capture)
    (endpoint : Endpoint) (member : endpoint ∈ catalog shape) :
    renameIndex shape canon s (image shape endpoint) = s.index (canon endpoint) := by
  have actual := (mem_captureKeys shape endpoint).mpr member
  unfold renameIndex image
  rw [List.getElem?_eq_getElem (List.idxOf_lt_length_iff.mpr actual), List.getElem_idxOf]

/-- Publication tests the exact negative composite endpoint; construction alone
never implies presence. This matches the retained formal_domains iteration,
conditional on its term-view decoding to the represented Shape. -/
def publish (s : Capture) (shape : Shape) : Option Nat :=
  match shape with
  | .atom _ => none
  | _ => if .value shape false ∈ s.keys then some (s.index (.value shape false)) else none

theorem publish_function_iff (s : Capture) (a r : Shape) (ae re : Ports) (i : Nat) :
    publish s (.function a ae r re) = some i ↔
      .value (.function a ae r re) false ∈ s.keys ∧
      s.index (.value (.function a ae r re) false) = i := by
  simp [publish]

theorem publish_tuple_iff (s : Capture) (elements : List Shape) (i : Nat) :
    publish s (.tuple elements) = some i ↔
      .value (.tuple elements) false ∈ s.keys ∧ s.index (.value (.tuple elements) false) = i := by
  simp [publish]

/-- An isolated negative composite that never arrived is not published. -/
theorem absent_root_not_published (s : Capture) (shape : Shape)
    (absent : .value shape false ∉ s.keys) : publish s shape = none := by
  cases shape <;> simp [publish, absent]

/-- Constructor-derived catalog output, transported by the explicit renaming.
This is a port-number correspondence only. Establishing that live stored
nodes/walk return this number requires the open Rust capture simulation. -/
theorem constructed_export_renamed {before after : Nat} {shape : Shape} {entries : List Retained}
    (built : Construction false before shape entries after)
    (canon : Endpoint → Endpoint) (s : Capture) :
    (projectAll shape entries).map (List.map (fun out =>
      (out.metadata, out.path, renameIndex shape canon s out.port))) =
      some (entries.map (fun entry =>
        (entry.metadata, entry.path, s.index (canon (.effect (.row entry.allocatedRow) false))))) := by
  rw [constructed_catalog_export built]
  simp only [Option.map_some, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro entry member
  have origin := construction_origins built entry member
  have port := (origin_image origin shape (fun _ h => h)).2
  simp only [rename_catalog_image shape canon s _ port]

end
end YulangClosure.FormalPermissionLiveCapture

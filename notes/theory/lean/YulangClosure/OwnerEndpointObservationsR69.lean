import YulangClosure.SemanticFactEndpointInterpretationR68

/-!
R69 constructs the R68 decoder owner from primitive ordered observations.
The finite checks establish coverage and table coherence, not authenticity of
Rust observation, arena identity, allocation behavior, or the R66 source Root.
All those source/native obligations remain explicit and OPEN.
-/
namespace YulangClosure.OwnerEndpointObservationsR69
open ProviderNativeContextR57 OccurrenceQualifiedFactReadersR65
open SemanticFactEndpointInterpretationR68

structure Observation (T : Type) where
  term : T
  view : SemanticFactEndpointInterpretationR68.View T
  children : List (Nat × T)

structure ComponentObservation (T : Type) where
  term : T
  component : Component
  live : Coordinate

/-- Primitive records of one owner state. Neither an interpreted Inventory nor
an R68 Owner is accepted. Position associations retain the source table;
component vectors are constructed from the complete ordered primitive rows. -/
structure Tables (T : Type) where
  store : Nat
  observations : List (Observation T)
  componentPositions : List (T × Nat)
  componentRows : List (ComponentObservation T)
  currentValues : List Nat
  currentEffects : List Nat

variable {T S : Type}

/-- Exact recursive enumeration order of inventory_term_children. -/
def children : SemanticFactEndpointInterpretationR68.View T → List T
  | .positiveFunction a ae re r | .negativeFunction a ae re r => [a,ae,re,r]
  | .positiveVariant alternatives | .negativeVariant alternatives =>
      alternatives.flatMap Alternative.payloads
  | .positiveRecord fields | .negativeRecord fields => fields.map Field.value
  | .positiveTuple elements | .negativeTuple elements => elements
  | .leaf _ | .component _ | .liveVariable _ _ _
  | .positiveBottom | .negativeTop | .negativeBottom => []

def viewTable (p : Tables T) : List (T × SemanticFactEndpointInterpretationR68.View T) :=
  p.observations.map (fun row => (row.term,row.view))

def assemble (p : Tables T) : Owner T :=
  { store := p.store
    views := viewTable p
    componentPositions := p.componentPositions
    componentTerms := p.componentRows.map ComponentObservation.term
    components := p.componentRows.map ComponentObservation.component
    liveComponents := p.componentRows.map ComponentObservation.live
    valueRepresentatives := p.currentValues
    effectRepresentatives := p.currentEffects }

def componentTag : SemanticFactEndpointInterpretationR68.View T → Option Component
  | .component c => some c
  | _ => none

def coordinateEndpoint (coordinate : Coordinate) : Endpoint T :=
  match coordinate.kind with
  | .value => .value (.row coordinate.ordinal)
  | .effect => .effect (.row coordinate.ordinal)

def rowBound (p : Tables T) (coordinate : Coordinate) : Prop :=
  coordinate.ordinal < match coordinate.kind with
    | .value => p.currentValues.length
    | .effect => p.currentEffects.length

/-- A finite computable check over every input fact, observation, child,
component row/position, and representative. No supplied interpretation law. -/
def Valid [DecidableEq T] (p : Tables T) (fs : List (PrimitiveFact T)) : Prop :=
  (p.observations.map Observation.term).Nodup ∧
  (∀ f ∈ fs, (lookup (viewTable p) f.lower).isSome = true ∧
    (lookup (viewTable p) f.upper).isSome = true) ∧
  (∀ row ∈ p.observations,
    row.children.map Prod.snd = children row.view ∧
    ∀ child ∈ row.children,
      (p.observations[child.1]?).map Observation.term = some child.2) ∧
  (∀ entry ∈ p.componentRows.zipIdx,
    lookup p.componentPositions entry.1.term = some entry.2 ∧
    entry.1.live.kind = entry.1.component.kind ∧ rowBound p entry.1.live ∧
    (lookup (viewTable p) entry.1.term).bind componentTag = some entry.1.component) ∧
  (∀ entry ∈ p.componentPositions,
    (p.componentRows[entry.2]?).map ComponentObservation.term = some entry.1) ∧
  (∀ representative ∈ p.currentValues, representative < p.currentValues.length) ∧
  (∀ representative ∈ p.currentEffects, representative < p.currentEffects.length)

instance [DecidableEq T] (p : Tables T) (fs : List (PrimitiveFact T)) :
    Decidable (Valid p fs) := by unfold Valid rowBound; infer_instance

def construct [DecidableEq T] (p : Tables T) (fs : List (PrimitiveFact T)) : Option (Owner T) :=
  if Valid p fs then some (assemble p) else none

theorem construction_iff [DecidableEq T] (p : Tables T) (fs : List (PrimitiveFact T)) :
    construct p fs = some (assemble p) ↔ Valid p fs := by simp [construct]

theorem construction_rejects [DecidableEq T] (p : Tables T) (fs : List (PrimitiveFact T))
    (invalid : ¬ Valid p fs) : construct p fs = none := by simp [construct, invalid]

/-- All constructed tables retain the same primitive rows, order, and store. -/
theorem all_tables_exact (p : Tables T) :
    (assemble p).store = p.store ∧ (assemble p).views = viewTable p ∧
    (assemble p).componentPositions = p.componentPositions ∧
    (assemble p).componentTerms = p.componentRows.map ComponentObservation.term ∧
    (assemble p).components = p.componentRows.map ComponentObservation.component ∧
    (assemble p).liveComponents = p.componentRows.map ComponentObservation.live ∧
    (assemble p).valueRepresentatives = p.currentValues ∧
    (assemble p).effectRepresentatives = p.currentEffects := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem lookup_exact_of_unique [DecidableEq T] {A : Type} (table : List (T × A))
    (unique : (table.map Prod.fst).Nodup) (t : T) (v : A) (member : (t,v) ∈ table) :
    lookup table t = some v := by
  induction table with
  | nil => simp at member
  | cons head tail ih =>
    have nd := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with same | rest
    · subst head; simp [lookup]
    · have different : head.1 ≠ t := by
        intro same
        exact nd.1 (List.mem_map.mpr ⟨(t,v), rest, same.symm⟩)
      simpa [lookup, different] using ih nd.2 rest

theorem observation_lookup [DecidableEq T] (p : Tables T) (fs : List (PrimitiveFact T))
    (accepted : construct p fs = some (assemble p)) (row : Observation T)
    (member : row ∈ p.observations) : lookup (assemble p).views row.term = some row.view := by
  apply lookup_exact_of_unique
  · simpa [assemble, viewTable, List.map_map, Function.comp_def] using
      ((construction_iff p fs).mp accepted).1
  · exact List.mem_map.mpr ⟨row,member,rfl⟩

theorem observation_index_lookup [DecidableEq T] (p : Tables T) (fs : List (PrimitiveFact T))
    (accepted : construct p fs = some (assemble p)) (index : Nat) (row : Observation T)
    (read : p.observations[index]? = some row) :
    lookup (assemble p).views row.term = some row.view :=
  observation_lookup p fs accepted row (List.mem_of_getElem? read)

theorem fact_seeds_observed [DecidableEq T] (p : Tables T) (fs : List (PrimitiveFact T))
    (accepted : construct p fs = some (assemble p)) (f : PrimitiveFact T) (member : f ∈ fs) :
    (∃ lower, lookup (assemble p).views f.lower = some lower) ∧
    (∃ upper, lookup (assemble p).views f.upper = some upper) := by
  have seeds := ((construction_iff p fs).mp accepted).2.1 f member
  exact ⟨Option.isSome_iff_exists.mp seeds.1, Option.isSome_iff_exists.mp seeds.2⟩

theorem child_coordinates_exact [DecidableEq T] (p : Tables T) (fs : List (PrimitiveFact T))
    (accepted : construct p fs = some (assemble p)) (row : Observation T)
    (member : row ∈ p.observations) :
    row.children.map Prod.snd = children row.view ∧
    ∀ child ∈ row.children,
      (p.observations[child.1]?).map Observation.term = some child.2 :=
  ((construction_iff p fs).mp accepted).2.2.1 row member

theorem recursive_child_observed [DecidableEq T] (p : Tables T) (fs : List (PrimitiveFact T))
    (accepted : construct p fs = some (assemble p)) (row : Observation T)
    (member : row ∈ p.observations) (child : T) (recursive : child ∈ children row.view) :
    ∃ (index : Nat) (observed : Observation T), p.observations[index]? = some observed ∧ observed.term = child ∧
      lookup (assemble p).views child = some observed.view := by
  have exactChildren := child_coordinates_exact p fs accepted row member
  rw [← exactChildren.1] at recursive
  obtain ⟨coordinate, atChild, same⟩ := List.mem_map.mp recursive
  have atCoordinate := exactChildren.2 coordinate atChild
  cases read : p.observations[coordinate.1]? with
  | none => simp [read] at atCoordinate
  | some observed =>
    have sameTerm : observed.term = coordinate.2 := by simpa [read] using atCoordinate
    have term : observed.term = child := sameTerm.trans same
    exact ⟨coordinate.1,observed,read,term,by
      simpa [term] using observation_index_lookup p fs accepted coordinate.1 observed read⟩

/-- Arbitrarily many recursive steps, including cycles; no depth cutoff or
restriction of accepted source constructors is introduced. -/
inductive Reach (p : Tables T) (fs : List (PrimitiveFact T)) : T → Prop
  | lower (f : PrimitiveFact T) (member : f ∈ fs) : Reach p fs f.lower
  | upper (f : PrimitiveFact T) (member : f ∈ fs) : Reach p fs f.upper
  | child (row : Observation T) (member : row ∈ p.observations)
      (parent : Reach p fs row.term) (t : T) (recursive : t ∈ children row.view) : Reach p fs t

theorem complete_seed_recursive_coverage [DecidableEq T] (p : Tables T)
    (fs : List (PrimitiveFact T)) (accepted : construct p fs = some (assemble p))
    (t : T) (reachable : Reach p fs t) : ∃ v, lookup (assemble p).views t = some v := by
  induction reachable with
  | lower f member => exact (fact_seeds_observed p fs accepted f member).1
  | upper f member => exact (fact_seeds_observed p fs accepted f member).2
  | child row member _ t recursive _ =>
    obtain ⟨_,observed,_,_,read⟩ := recursive_child_observed p fs accepted row member t recursive
    exact ⟨observed.view,read⟩

theorem component_roundtrip [DecidableEq T] (p : Tables T) (fs : List (PrimitiveFact T))
    (accepted : construct p fs = some (assemble p)) (index : Nat) (row : ComponentObservation T)
    (read : p.componentRows[index]? = some row) :
    lookup (assemble p).componentPositions row.term = some index ∧
    (assemble p).componentTerms[index]? = some row.term ∧
    (assemble p).components[index]? = some row.component ∧
    (assemble p).liveComponents[index]? = some row.live ∧
    row.live.kind = row.component.kind ∧ rowBound p row.live := by
  have good := ((construction_iff p fs).mp accepted).2.2.2.1 (row,index)
    (List.mk_mem_zipIdx_iff_getElem?.mpr read)
  exact ⟨good.1,by simp [assemble,read],by simp [assemble,read],by simp [assemble,read],good.2.1,good.2.2.1⟩

theorem component_coordinate_constructed [DecidableEq T] (p : Tables T)
    (fs : List (PrimitiveFact T)) (accepted : construct p fs = some (assemble p))
    (index : Nat) (row : ComponentObservation T) (read : p.componentRows[index]? = some row) :
    componentCoordinate (assemble p) row.term row.component = some row.live := by
  have roundtrip := component_roundtrip p fs accepted index row read
  exact component_coordinate_equation (assemble p) row.term row.component index row.live
    roundtrip.1 roundtrip.2.1 roundtrip.2.2.1 roundtrip.2.2.2.1 roundtrip.2.2.2.2.1

theorem constructed_component_view [DecidableEq T] (p : Tables T)
    (fs : List (PrimitiveFact T)) (accepted : construct p fs = some (assemble p))
    (index : Nat) (row : ComponentObservation T) (read : p.componentRows[index]? = some row) :
    lookup (assemble p).views row.term = some (.component row.component) := by
  have checked := (((construction_iff p fs).mp accepted).2.2.2.1 (row,index)
    (List.mk_mem_zipIdx_iff_getElem?.mpr read)).2.2.2
  obtain ⟨view, observed, tag⟩ := Option.bind_eq_some_iff.mp checked
  cases view <;> simp [componentTag] at tag
  case component c =>
    subst c
    exact observed

theorem constructed_component_raw [DecidableEq T] (p : Tables T)
    (fs : List (PrimitiveFact T)) (accepted : construct p fs = some (assemble p))
    (index : Nat) (row : ComponentObservation T) (read : p.componentRows[index]? = some row)
    (polarity : Polarity) :
    raw (assemble p) row.term polarity = some (coordinateEndpoint row.live) := by
  have observed := constructed_component_view p fs accepted index row read
  have coordinate := component_coordinate_constructed p fs accepted index row read
  have bound := (component_roundtrip p fs accepted index row read).2.2.2.2.2
  rw [branch_equation (assemble p) row.term polarity (.component row.component) observed]
  rw [component_branch_equation (assemble p) row.term polarity row.component row.live coordinate]
  cases kind : row.live.kind <;>
    simp only [rowBound, kind] at bound <;>
    simp [checkedRow, coordinateEndpoint, kind, assemble, bound]

theorem position_roundtrip [DecidableEq T] (p : Tables T) (fs : List (PrimitiveFact T))
    (accepted : construct p fs = some (assemble p)) (entry : T × Nat)
    (member : entry ∈ p.componentPositions) :
    (assemble p).componentTerms[entry.2]? = some entry.1 := by
  simpa [assemble] using ((construction_iff p fs).mp accepted).2.2.2.2.1 entry member

theorem current_representatives_exact (p : Tables T) (index : Nat) :
    (assemble p).valueRepresentatives[index]? = p.currentValues[index]? ∧
    (assemble p).effectRepresentatives[index]? = p.currentEffects[index]? := ⟨rfl,rfl⟩

theorem current_value_canonical [DecidableEq T] (p : Tables T) (fs : List (PrimitiveFact T))
    (accepted : construct p fs = some (assemble p)) (index representative : Nat)
    (read : p.currentValues[index]? = some representative) :
    canonical (assemble p) (.value (.row index)) = some (.value (.row representative)) := by
  apply canonical_value_equation (assemble p) index representative read
  exact ((construction_iff p fs).mp accepted).2.2.2.2.2.1 representative (List.mem_of_getElem? read)

theorem current_effect_canonical [DecidableEq T] (p : Tables T) (fs : List (PrimitiveFact T))
    (accepted : construct p fs = some (assemble p)) (index representative : Nat)
    (read : p.currentEffects[index]? = some representative) :
    canonical (assemble p) (.effect (.row index)) = some (.effect (.row representative)) := by
  apply canonical_effect_equation (assemble p) index representative read
  exact ((construction_iff p fs).mp accepted).2.2.2.2.2.2 representative (List.mem_of_getElem? read)

theorem separate_namespaces (value effect : Nat) :
    (Endpoint.value (.row value) : Endpoint T) ≠ .effect (.row effect) := namespaces_distinct value effect

/-- Decoding remains a successful-read premise; coverage alone does not imply
correct polarity, a valid semantic identity, or a source/native R66 Root. -/
theorem constructed_decoded_read [DecidableEq S] [DecidableEq T]
    (p : Tables T) (fs : List (PrimitiveFact T))
    (accepted : construct p fs = some (assemble p))
    (rows : List (FactRow T)) (edges : List (Edge S))
    (decoded : decodeRows (assemble p) 0 fs = some rows)
    (s : S) (slot : Nat) (out : Read S T)
    (read : readAt (inventory (assemble p) rows edges) s slot = some out) :
    Valid p fs ∧ ∃ index f, fs[index]? = some f ∧
      decodeFact (assemble p) index f = some out.fact ∧
      out.fact.identity = .semantic p.store index ∧ out.fact.lower = f.lower ∧
      out.fact.upper = f.upper ∧ Interpreted (assemble p) out.fact :=
  ⟨(construction_iff p fs).mp accepted,
    decoded_read_interpreted (assemble p) fs rows edges decoded s slot out read⟩

/-- SAME R66 slot-0 route and slot-2 construction, with R67 qualified
reification, now for the Owner constructed from primitive table records. -/
theorem r66_same_selected_constructed_endpoints [DecidableEq S] [DecidableEq T]
    (p : Tables T) (fs : List (PrimitiveFact T))
    (accepted : construct p fs = some (assemble p))
    (rows : List (FactRow T)) (edges : List (Edge S))
    (decoded : decodeRows (assemble p) 0 fs = some rows)
    (source : OccurrenceQualifiedConsumerR66.Source S T) (native : Native S T)
    (q : OccurrenceQualifiedConsumerR66.Request S T)
    (root : OccurrenceQualifiedConsumerR66.Root source (inventory (assemble p) rows edges) native q)
    (use lambda : S) (useCoordinate : q.use.occurrence = .source use)
    (lambdaCoordinate : q.lambda = .source lambda) :
    Valid p fs ∧ ∃ route construction,
      readAt (BorrowedQualifiedReadReificationR67.encoded (inventory (assemble p) rows edges))
        (BorrowedQualifiedReadReificationR67.occurrenceIndex (inventory (assemble p) rows edges) use) 0 =
          some (BorrowedQualifiedReadReificationR67.encodeRead (inventory (assemble p) rows edges) route) ∧
      route.fact.identity = root.incidence.probe.fact ∧
      route.fact.lower = root.incidence.probe.registeredRoot ∧
      route.fact.upper = root.incidence.probe.plan.useValue ∧
      readAt (BorrowedQualifiedReadReificationR67.encoded (inventory (assemble p) rows edges))
        (BorrowedQualifiedReadReificationR67.occurrenceIndex (inventory (assemble p) rows edges) lambda) 2 =
          some (BorrowedQualifiedReadReificationR67.encodeRead (inventory (assemble p) rows edges) construction) ∧
      construction.fact.lower = root.incidence.probe.construction.function ∧
      construction.fact.upper = root.incidence.probe.registeredRoot ∧
      Interpreted (assemble p) route.fact ∧ Interpreted (assemble p) construction.fact :=
  ⟨(construction_iff p fs).mp accepted,
    r66_selected_decoded_endpoints (assemble p) fs rows edges decoded source native q root
      use lambda useCoordinate lambdaCoordinate⟩

end YulangClosure.OwnerEndpointObservationsR69

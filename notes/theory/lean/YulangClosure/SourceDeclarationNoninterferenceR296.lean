import YulangClosure.SourceDeclarationCollisionR295

/-!
R296 candidate repair, NOT adopted source semantics. Actual node occurrence
indexes the local relation. Labels and original graph edges remain unchanged.
All contribution constructors, whole rows, packets and operator contracts are
retained. Reflection needs edge closure in addition to occurrence indexing;
Graph does not currently assert that closure. See the checked obstruction below.
-/
namespace YulangClosure.SourceDeclarationNoninterferenceR296
open OriginalSource SourceSignatureConstruction SourceContributionConstruction
open SourceDeclarationRetentionR295
variable {Joint : Type}

inductive Contribution (graph : Graph Joint) (relations : Nat → Relations graph) (operators : Operators graph) :
    (index : Nat) → (whole : Joint) → (node : Node Joint) → Packet node.catalogue whole → Type 1 where
  | primitive (found : graph.node index = some (.primitive intro))
      (packet : Packet intro.catalogue whole)
      (license : intro.License whole packet.port packet.value) :
      Contribution graph relations operators index whole (.primitive intro) packet
  | alternativeLeft (found : graph.node index = some (.alternative site left right result))
      (child : Contribution graph relations operators left whole childNode childPacket)
      (output : Packet result whole)
      (related : (relations index).alternative site false whole childPacket output) :
      Contribution graph relations operators index whole (.alternative site left right result) output
  | alternativeRight (found : graph.node index = some (.alternative site left right result))
      (child : Contribution graph relations operators right whole childNode childPacket)
      (output : Packet result whole)
      (related : (relations index).alternative site true whole childPacket output) :
      Contribution graph relations operators index whole (.alternative site left right result) output
  | conjunction (found : graph.node index = some (.conjunction site left right result))
      (first : Contribution graph relations operators left whole firstNode firstPacket)
      (second : Contribution graph relations operators right whole secondNode secondPacket)
      (output : Packet result whole)
      (related : (relations index).conjunction site whole firstPacket secondPacket output) :
      Contribution graph relations operators index whole (.conjunction site left right result) output
  | image (found : graph.node index = some (.image site operator operands locals result))
      (output : Packet result whole)
      (evidence : (operators.image site operator operands locals result).Evidence whole output) :
      Contribution graph relations operators index whole (.image site operator operands locals result) output
  | call (found : graph.node index = some (.call context mark callee argument nodes locals result))
      (output : Packet result whole)
      (evidence : (operators.call context mark callee argument nodes locals result).Evidence whole output) :
      Contribution graph relations operators index whole (.call context mark callee argument nodes locals result) output
  | forward (found : graph.node index = some node) (source : Forward node step target)
      (child : Contribution graph relations operators target (step.action graph whole) childNode childPacket)
      (output : Packet node.catalogue whole)
      (related : (relations index).forward step whole childPacket output) :
      Contribution graph relations operators index whole node output


/-- Pointwise inclusion of all independent local witnesses. -/
structure RelationMap {graph : Graph Joint} (a b : Relations graph) where
  alternative : ∀ site side whole {c r} (p : Packet c whole) (q : Packet r whole),
    a.alternative site side whole p q → b.alternative site side whole p q
  conjunction : ∀ site whole {l r o} (p : Packet l whole) (q : Packet r whole)
    (v : Packet o whole), a.conjunction site whole p q v → b.conjunction site whole p q v
  forward : ∀ step whole {c r} (p : Packet c (step.action graph whole)) (q : Packet r whole),
    a.forward step whole p q → b.forward step whole p q

def map {graph : Graph Joint} {a b : Nat → Relations graph} {ops : Operators graph}
    (maps : ∀ i, RelationMap (a i) (b i))
    {i w n p} : Contribution graph a ops i w n p → Contribution graph b ops i w n p
  | .primitive f p l => .primitive f p l
  | .alternativeLeft f c p r => .alternativeLeft f (map maps c) p ((maps _).alternative _ _ _ _ _ r)
  | .alternativeRight f c p r => .alternativeRight f (map maps c) p ((maps _).alternative _ _ _ _ _ r)
  | .conjunction f c d p r => .conjunction f (map maps c) (map maps d) p ((maps _).conjunction _ _ _ _ _ r)
  | .image f p e => .image f p e
  | .call f p e => .call f p e
  | .forward f s c p r => .forward f s (map maps c) p ((maps _).forward _ _ _ _ r)

def embed {graph : Graph Joint} {old : Relations graph} {ops : Operators graph}
    {i w n p} : DeclContribution graph old ops i w n p → Contribution graph (fun _ => old) ops i w n p
  | .primitive f p l => .primitive f p l
  | .alternativeLeft f c p r => .alternativeLeft f (embed c) p r
  | .alternativeRight f c p r => .alternativeRight f (embed c) p r
  | .conjunction f c d p r => .conjunction f (embed c) (embed d) p r
  | .image f p e => .image f p e
  | .call f p e => .call f p e
  | .forward f s c p r => .forward f s (embed c) p r

def erase {graph : Graph Joint} {old : Relations graph} {ops : Operators graph}
    {i w n p} : Contribution graph (fun _ => old) ops i w n p → DeclContribution graph old ops i w n p
  | .primitive f p l => .primitive f p l
  | .alternativeLeft f c p r => .alternativeLeft f (erase c) p r
  | .alternativeRight f c p r => .alternativeRight f (erase c) p r
  | .conjunction f c d p r => .conjunction f (erase c) (erase d) p r
  | .image f p e => .image f p e
  | .call f p e => .call f p e
  | .forward f s c p r => .forward f s (erase c) p r

/-- No label freshness: only the actual appended occurrences receive new rules. -/
def localRelations (g : Graph Joint) (d : DeclarationData Joint)
    (old : Relations (install g d)) (i : Nat) : Relations (install g d) :=
  if i = g.nodes.length + 1 ∨ i = g.nodes.length + 2 then retainedRelations g d old else old

def inclusion (g : Graph Joint) (d : DeclarationData Joint)
    (old : Relations (install g d)) (i : Nat) : RelationMap old (localRelations g d old i) := by
  unfold localRelations
  split
  · exact ⟨fun _ _ _ {_ _} _ _ r => r, fun _ _ {_ _ _} _ _ _ r => r, fun _ _ {_ _} _ _ r => Sum.inl r⟩
  · exact ⟨fun _ _ _ {_ _} _ _ r => r, fun _ _ {_ _ _} _ _ _ r => r, fun _ _ {_ _} _ _ r => r⟩

def preserve (g : Graph Joint) (d : DeclarationData Joint)
    (old : Relations (install g d)) (ops : Operators (install g d))
    {i w n p} (c : DeclContribution (install g d) old ops i w n p) :
    Contribution (install g d) (localRelations g d old) ops i w n p :=
  map (inclusion g d old) (embed c)

theorem old_local_relation_exact (g : Graph Joint) (d : DeclarationData Joint)
    (old : Relations (install g d)) (i : Nat) (bound : i < g.nodes.length) :
    localRelations g d old i = old := by
  simp [localRelations, show ¬ (i = g.nodes.length + 1 ∨ i = g.nodes.length + 2) by omega]

/-- This is an explicit missing graph invariant, not assumed global freshness.
It permits cycles and repeated labels. It forbids unresolved outgoing addresses. -/
def ClosedPrefix (graph : Graph Joint) (bound : Nat) : Prop :=
  ∀ i node step child, i < bound → graph.node i = some node →
    SourceEdge node step child → child < bound

noncomputable def restrict {graph : Graph Joint} {a : Nat → Relations graph} {old : Relations graph}
    {ops : Operators graph} {bound : Nat}
    (closed : ClosedPrefix graph bound) (same : ∀ i, i < bound → a i = old)
    {i w n p} (c : Contribution graph a ops i w n p) (inside : i < bound) :
    DeclContribution graph old ops i w n p := by
  induction c with
  | primitive f p l => exact .primitive f p l
  | alternativeLeft f c p r ih =>
      exact .alternativeLeft f (ih (closed _ _ _ _ inside f .alternativeLeft)) p (same _ inside ▸ r)
  | alternativeRight f c p r ih =>
      exact .alternativeRight f (ih (closed _ _ _ _ inside f .alternativeRight)) p (same _ inside ▸ r)
  | conjunction f c d p r ihc ihd =>
      exact .conjunction f (ihc (closed _ _ _ _ inside f .conjunctionLeft))
        (ihd (closed _ _ _ _ inside f .conjunctionRight)) p (same _ inside ▸ r)
  | image f p e => exact .image f p e
  | call f p e => exact .call f p e
  | forward f s c p r ih =>
      exact .forward f s (ih (closed _ _ _ _ inside f s.edge)) p (same _ inside ▸ r)

theorem old_node_reflection (g : Graph Joint) (d : DeclarationData Joint)
    (old : Relations (install g d)) (ops : Operators (install g d))
    (closed : ClosedPrefix (install g d) g.nodes.length)
    {i w n p} (inside : i < g.nodes.length) :
    Nonempty (Contribution (install g d) (localRelations g d old) ops i w n p) ↔
      Nonempty (DeclContribution (install g d) old ops i w n p) :=
  ⟨fun ⟨c⟩ => ⟨restrict closed (old_local_relation_exact g d old) c inside⟩,
   fun ⟨c⟩ => ⟨preserve g d old ops c⟩⟩

def atUse (g : Graph Joint) (d : DeclarationData Joint)
    (old : Relations (install g d)) (ops : Operators (install g d)) (w : Joint)
    (p : Packet d.clause.catalogue (g.substitution d.substitution w))
    (c : Contribution (install g d) (localRelations g d old) ops g.nodes.length
      (g.substitution d.substitution w) d.clause p) :
    Contribution (install g d) (localRelations g d old) ops (g.nodes.length + 2)
      w (referenceNode g d) (usePacket g d w p) := by
  apply Contribution.forward (reference_lookup g d) Forward.reference
  · apply Contribution.forward (insertion_lookup g d) Forward.insertion c p
    change (localRelations g d old (g.nodes.length + 1)).forward _ _ _ _
    simp only [localRelations, true_or, ite_true]
    exact Sum.inr (RetainedForward.insertion _ p)
  · change (localRelations g d old (g.nodes.length + 2)).forward _ _ _ _
    simp only [localRelations, or_true, ite_true]
    exact Sum.inr (RetainedForward.reference w p)


/-- Old graph lookup is lifted from an actual lookup, not a freshness premise. -/
theorem lift_lookup (g : Graph Joint) (d : DeclarationData Joint) {i n}
    (found : g.node i = some n) : (install g d).node i = some n := by
  rw [original_node_retained g d i (List.getElem?_eq_some_iff.mp found).1]
  exact found

theorem lift_provenance (g : Graph Joint) (d : DeclarationData Joint) {i intro route}
    (p : PortProv g i intro route) : PortProv (install g d) i intro route := by
  induction p with
  | introduction f m => exact .introduction (lift_lookup g d f) m
  | contextual f e p ih => exact .contextual (lift_lookup g d f) e ih

def lift_leaf (g : Graph Joint) (d : DeclarationData Joint) {i w}
    (f : LeafLicensedField g i w) : LeafLicensedField (install g d) i w :=
  ⟨⟨f.occurrence.intro, f.occurrence.route, lift_provenance g d f.occurrence.provenance⟩,
    f.port, f.packet, f.license⟩

def lift_operatorField (g : Graph Joint) (d : DeclarationData Joint) {n w} :
    OperatorField g n w → OperatorField (install g d) n w
  | .localField i m p l => .localField i m p l
  | .antecedent s c e f => .antecedent s c e (lift_leaf g d f)

def lift_contract (g : Graph Joint) (d : DeclarationData Joint) {n}
    (c : OperatorContract g n) : OperatorContract (install g d) n where
  Evidence := c.Evidence
  Field := c.Field
  governed := fun w p e f => lift_operatorField g d (c.governed w p e f)

def lift_operators (g : Graph Joint) (d : DeclarationData Joint)
    (ops : Operators g) : Operators (install g d) where
  image := fun s r o l c => lift_contract g d (ops.image s r o l c)
  call := fun c m f a n l r => lift_contract g d (ops.call c m f a n l r)

def lift_relations (g : Graph Joint) (d : DeclarationData Joint)
    (r : Relations g) : Relations (install g d) :=
  ⟨r.alternative, r.conjunction, r.forward⟩

def lift_contribution (g : Graph Joint) (d : DeclarationData Joint)
    (r : Relations g) (ops : Operators g) {i w n p} :
    DeclContribution g r ops i w n p →
      DeclContribution (install g d) (lift_relations g d r) (lift_operators g d ops) i w n p
  | .primitive f p l => .primitive (lift_lookup g d f) p l
  | .alternativeLeft f c p e => .alternativeLeft (lift_lookup g d f) (lift_contribution g d r ops c) p e
  | .alternativeRight f c p e => .alternativeRight (lift_lookup g d f) (lift_contribution g d r ops c) p e
  | .conjunction f c e p q => .conjunction (lift_lookup g d f)
      (lift_contribution g d r ops c) (lift_contribution g d r ops e) p q
  | .image f p e => .image (lift_lookup g d f) p e
  | .call f p e => .call (lift_lookup g d f) p e
  | .forward f s c p e => .forward (lift_lookup g d f) s (lift_contribution g d r ops c) p e

/-- Actual pre-installation contributions survive with their original Evidence.
This strengthens the R295 theorem that starts with an already installed graph. -/
def preserve_original_graph (g : Graph Joint) (d : DeclarationData Joint)
    (r : Relations g) (ops : Operators g) {i w n p}
    (c : DeclContribution g r ops i w n p) :
    Contribution (install g d) (localRelations g d (lift_relations g d r))
      (lift_operators g d ops) i w n p :=
  preserve g d _ _ (lift_contribution g d r ops c)

theorem original_closed_installed (g : Graph Joint) (d : DeclarationData Joint)
    (closed : ClosedPrefix g g.nodes.length) : ClosedPrefix (install g d) g.nodes.length := by
  intro i n s c bound f e
  rw [original_node_retained g d i bound] at f
  exact closed i n s c bound f e

noncomputable def lower_contribution (g : Graph Joint) (d : DeclarationData Joint)
    (r : Relations g) (ops : Operators g) (closed : ClosedPrefix g g.nodes.length)
    {i w n p} (c : DeclContribution (install g d) (lift_relations g d r)
      (lift_operators g d ops) i w n p) (inside : i < g.nodes.length) :
    DeclContribution g r ops i w n p := by
  induction c with
  | primitive f p l =>
      rw [original_node_retained g d _ inside] at f
      exact .primitive f p l
  | alternativeLeft f c p e ih =>
      rw [original_node_retained g d _ inside] at f
      exact .alternativeLeft f (ih (closed _ _ _ _ inside f .alternativeLeft)) p e
  | alternativeRight f c p e ih =>
      rw [original_node_retained g d _ inside] at f
      exact .alternativeRight f (ih (closed _ _ _ _ inside f .alternativeRight)) p e
  | conjunction f c e p q ihc ihe =>
      rw [original_node_retained g d _ inside] at f
      exact .conjunction f (ihc (closed _ _ _ _ inside f .conjunctionLeft))
        (ihe (closed _ _ _ _ inside f .conjunctionRight)) p q
  | image f p e =>
      rw [original_node_retained g d _ inside] at f
      exact .image f p e
  | call f p e =>
      rw [original_node_retained g d _ inside] at f
      exact .call f p e
  | forward f s c p e ih =>
      rw [original_node_retained g d _ inside] at f
      exact .forward f s (ih (closed _ _ _ _ inside f s.edge)) p e

theorem original_graph_iff (g : Graph Joint) (d : DeclarationData Joint)
    (r : Relations g) (ops : Operators g) (closed : ClosedPrefix g g.nodes.length)
    {i w n p} (inside : i < g.nodes.length) :
    Nonempty (Contribution (install g d) (localRelations g d (lift_relations g d r))
      (lift_operators g d ops) i w n p) ↔ Nonempty (DeclContribution g r ops i w n p) := by
  constructor
  · rintro ⟨c⟩
    exact ⟨lower_contribution g d r ops closed
      (restrict (original_closed_installed g d closed)
        (old_local_relation_exact g d (lift_relations g d r)) c inside) inside⟩
  · rintro ⟨c⟩
    exact ⟨preserve_original_graph g d r ops c⟩

namespace Collision
open SourceDeclarationCollisionR295

theorem closed : ClosedPrefix installed original.nodes.length := by
  intro i n s c bound f e
  have choices : i = 0 ∨ i = 1 := by change i < 2 at bound; omega
  rcases choices with rfl | rfl
  · cases f
    cases e
  · cases f
    cases e
    decide

/-- The exact R295 old-node collision cannot occur in the indexed candidate. -/
theorem blocked : ¬ Nonempty (Contribution installed
    (localRelations original declaration old) operators 1 ()
    (.insertion 7 9 0 catalogue) packet) := by
  intro c
  have prior := (old_node_reflection original declaration old operators closed (by decide)).mp c
  exact prior.elim no_old_contribution

/-- Yet the new declaration/reference is usable with a real primitive license. -/
def usable : Contribution installed (localRelations original declaration old) operators
    4 () (referenceNode original declaration) (usePacket original declaration () packet) :=
  atUse original declaration old operators () packet
    (Contribution.primitive (graph := installed) (index := 2) (intro := introduction)
      (by rfl) packet ())

theorem new_use_exists : Nonempty (Contribution installed (localRelations original declaration old)
    operators 4 () (referenceNode original declaration) (usePacket original declaration () packet)) :=
  ⟨usable⟩
end Collision


/-- Every existing derivation has an actual lookup, independently of relations. -/
theorem contribution_lookup {g : Graph Joint} {r : Relations g} {ops : Operators g}
    {i w n p} (c : DeclContribution g r ops i w n p) : g.node i = some n := by
  cases c <;> assumption

namespace Dangling
open SourceDeclarationCollisionR295 (catalogue introduction packet)

def graph : Graph Unit :=
  ⟨[.insertion 70 90 1 catalogue], fun _ => 0, fun _ w => w⟩
def data : DeclarationData Unit := ⟨7, 9, 0, 0, .primitive introduction⟩
def old : Relations graph where
  alternative := fun _ _ _ {_ _} _ _ => Unit
  conjunction := fun _ _ {_ _ _} _ _ _ => Unit
  forward := fun _ _ {_ _} _ _ => Unit

def emptyContract (n : Node Unit) : OperatorContract graph n where
  Evidence := fun _ _ => Empty
  Field := fun _ _ _ => Empty
  governed := fun _ _ e => nomatch e

def ops : Operators graph where
  image := fun _ _ _ _ _ => emptyContract _
  call := fun _ _ _ _ _ _ _ => emptyContract _

theorem not_closed : ¬ ClosedPrefix graph graph.nodes.length := by
  intro h
  have bad := h 0 (.insertion 70 90 1 catalogue) (.insertion 70 90) 1 (by decide) rfl .insertion
  change 1 < 1 at bad
  omega

theorem no_old (c : DeclContribution graph old ops 0 () (.insertion 70 90 1 catalogue) packet) : False := by
  cases c with
  | forward f s child out rel =>
      cases s
      have lookup := contribution_lookup child
      change none = some _ at lookup
      contradiction

/-- The old edge had a valid local rule already. Appending its missing child
creates an old-node contribution even with perfectly indexed new rules. -/
def newContribution : Contribution (install graph data)
    (localRelations graph data (lift_relations graph data old)) (lift_operators graph data ops)
    0 () (.insertion 70 90 1 catalogue) packet := by
  let child : Contribution (install graph data)
      (localRelations graph data (lift_relations graph data old)) (lift_operators graph data ops)
      1 () (.primitive introduction) packet :=
    Contribution.primitive (graph := install graph data) (index := 1) (intro := introduction)
      (by rfl) packet ()
  apply Contribution.forward (by rfl) Forward.insertion child packet
  exact ()

theorem unconditional_reflection_false :
    ¬ (Nonempty (Contribution (install graph data)
      (localRelations graph data (lift_relations graph data old)) (lift_operators graph data ops)
      0 () (.insertion 70 90 1 catalogue) packet) →
      Nonempty (DeclContribution graph old ops 0 () (.insertion 70 90 1 catalogue) packet)) := by
  intro h
  exact (h ⟨newContribution⟩).elim no_old
end Dangling


namespace Selected
open OriginalSourceInterpretation OriginalSourceEnvironment OriginalSourceChecking
open ComputedCallUnionRealizationR293
variable {s : Sorts} {View : Type}

/-- R293's tagged maps are also occurrence-local in the candidate. -/
def unionRelations (g : Graph (RawObservation s)) (old : Relations g) (atIndex : Nat)
    (inputs : Inputs s) (state : Decoded s View) (scope : List Binder)
    (site : Site) (source : Endpoint) (arms : List Endpoint) (i : Nat) : Relations g :=
  if i = atIndex then relations g old inputs state scope site source arms else old

def unionInclusion (g : Graph (RawObservation s)) (old : Relations g) (atIndex : Nat)
    (inputs : Inputs s) (state : Decoded s View) (scope : List Binder)
    (site : Site) (source : Endpoint) (arms : List Endpoint) (i : Nat) :
    RelationMap old (unionRelations g old atIndex inputs state scope site source arms i) := by
  unfold unionRelations
  split
  · exact ⟨fun _ _ _ {_ _} _ _ e => Sum.inl e,
      fun _ _ {_ _ _} _ _ _ e => e, fun _ _ {_ _} _ _ e => e⟩
  · exact ⟨fun _ _ _ {_ _} _ _ e => e,
      fun _ _ {_ _ _} _ _ _ e => e, fun _ _ {_ _} _ _ e => e⟩

/-- A candidate derivation has an actual legacy R293 consumer derivation.
This one-way erasure is not an equivalence with R293's global rule extension. -/
def consume (g : Graph (RawObservation s)) (old : Relations g) (ops : Operators g)
    (atIndex : Nat) (inputs : Inputs s) (state : Decoded s View) (scope : List Binder)
    (site : Site) (source : Endpoint) (arms : List Endpoint) {i w n p}
    (c : Contribution g (unionRelations g old atIndex inputs state scope site source arms) ops i w n p) :
    DeclContribution g (relations g old inputs state scope site source arms) ops i w n p := by
  apply erase
  apply map (a := unionRelations g old atIndex inputs state scope site source arms) _ c
  intro i
  unfold unionRelations
  split
  · exact ⟨fun _ _ _ {_ _} _ _ e => e,
      fun _ _ {_ _ _} _ _ _ e => e, fun _ _ {_ _} _ _ e => e⟩
  · exact ⟨fun _ _ _ {_ _} _ _ e => Sum.inl e,
      fun _ _ {_ _ _} _ _ _ e => e, fun _ _ {_ _} _ _ e => e⟩

def fromSource (g : Graph (RawObservation s)) (old : Relations g) (ops : Operators g)
    (atIndex left right : Nat) (inputs : Inputs s) (state : Decoded s View) (scope : List Binder)
    (site : Site) (source : Endpoint) (arms : List Endpoint) (raw : RawObservation s)
    (node : Node (RawObservation s)) (readout : node.catalogue = branchCatalogue inputs state scope source)
    (packet : Packet (branchCatalogue inputs state scope source) raw)
    (found : g.node atIndex = some (unionNode inputs state scope site left right source arms))
    (child : Contribution g (unionRelations g old atIndex inputs state scope site source arms)
      ops left raw node (readout ▸ packet)) :
    Contribution g (unionRelations g old atIndex inputs state scope site source arms) ops atIndex raw
      (unionNode inputs state scope site left right source arms) (injectSource inputs state scope source arms packet) := by
  apply Contribution.alternativeLeft found child
  simp only [unionRelations, ite_true]
  exact Sum.inr (sourceRelationCast inputs state scope site source arms raw node.catalogue readout packet)

def fromArm (g : Graph (RawObservation s)) (old : Relations g) (ops : Operators g)
    (atIndex left right : Nat) (inputs : Inputs s) (state : Decoded s View) (scope : List Binder)
    (site : Site) (source : Endpoint) (arms : List Endpoint) (raw : RawObservation s)
    (node : Node (RawObservation s)) (readout : node.catalogue = armsCatalogue inputs state scope arms)
    (packet : Packet (armsCatalogue inputs state scope arms) raw)
    (found : g.node atIndex = some (unionNode inputs state scope site left right source arms))
    (child : Contribution g (unionRelations g old atIndex inputs state scope site source arms)
      ops right raw node (readout ▸ packet)) :
    Contribution g (unionRelations g old atIndex inputs state scope site source arms) ops atIndex raw
      (unionNode inputs state scope site left right source arms) (injectArm inputs state scope source arms packet) := by
  apply Contribution.alternativeRight found child
  simp only [unionRelations, ite_true]
  have castArm (cat : Catalogue (RawObservation s)) (same : cat = armsCatalogue inputs state scope arms) :
      TaggedAlternative inputs state scope site source arms site true raw (same ▸ packet)
        (injectArm inputs state scope source arms packet) := by
    subst cat
    exact .arm raw packet
  exact Sum.inr (castArm node.catalogue readout)

theorem union_old_node_iff (g : Graph (RawObservation s)) (old : Relations g) (ops : Operators g)
    (atIndex bound : Nat) (outside : bound ≤ atIndex) (closed : ClosedPrefix g bound)
    (inputs : Inputs s) (state : Decoded s View) (scope : List Binder)
    (site : Site) (source : Endpoint) (arms : List Endpoint) {i w n p} (inside : i < bound) :
    Nonempty (Contribution g (unionRelations g old atIndex inputs state scope site source arms) ops i w n p) ↔
      Nonempty (DeclContribution g old ops i w n p) := by
  constructor
  · rintro ⟨c⟩
    apply Nonempty.intro
    apply restrict closed _ c inside
    intro j hj
    simp [unionRelations, show j ≠ atIndex by omega]
  · rintro ⟨c⟩
    exact ⟨map (unionInclusion g old atIndex inputs state scope site source arms) (embed c)⟩

/-- Explicit application to the unchanged R159 checking edge, on the same
ViewLogic extension and original synthesis endpoint. Source decoding, the
finite checking derivation, and actual branch catalogue remain required.
No EI-to-target inclusion, source admission, or arm authenticity is inferred. -/
theorem source_consumer_and_original_target
    (inputs : Inputs s) (registry : GuardRegistry inputs)
    (readout : RuntimeReadout s View) (ports : PortReadout s View)
    (declarations : Declarations inputs registry) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (context : Context) (mark : Mark)
    (occurrence : Nat) (data : Logical s View) (state : Decoded s View)
    (decoded : decode readout environment = some state) (arms : List Endpoint)
    (scope : List Binder) (raw : RawObservation s)
    (packet : Packet (branchCatalogue inputs (state.logical data) scope ⟨mark.site, .callableImage⟩) raw)
    (g : Graph (RawObservation s)) (old : Relations g) (ops : Operators g)
    (atIndex left right : Nat) (node : Node (RawObservation s))
    (catalogue : node.catalogue = branchCatalogue inputs (state.logical data) scope ⟨mark.site, .callableImage⟩)
    (found : g.node atIndex = some (unionNode inputs (state.logical data) scope mark.site left right
      ⟨mark.site, .callableImage⟩ arms))
    (child : Contribution g (unionRelations g old atIndex inputs (state.logical data) scope mark.site
      ⟨mark.site, .callableImage⟩ arms) ops left raw node (catalogue ▸ packet))
    (checked : Checking (OriginalSourceChecking.kernel inputs registry declarations
      (environmentReading inputs readout ports) original)
      (environment.extend ⟨mark.site, .viewLogic, 0⟩
        (scopeCandidate environment occurrence (.logical .viewLogic data)))
      ⟨.computation, mark.site, context, ⟨mark.site, .callableImage⟩, ⟨mark.site, .synthesis⟩⟩) :
    Nonempty (DeclContribution g (relations g old inputs (state.logical data) scope mark.site
      ⟨mark.site, .callableImage⟩ arms) ops atIndex raw
      (unionNode inputs (state.logical data) scope mark.site left right ⟨mark.site, .callableImage⟩ arms)
      (injectSource inputs (state.logical data) scope ⟨mark.site, .callableImage⟩ arms packet)) ∧
    (unionBody inputs (state.logical data) ⟨mark.site, .callableImage⟩ arms raw).Holds (Meaning inputs) ∧
    Meaning inputs (.trace (raw.atInterface ((state.logical data).interfaces ⟨mark.site, .synthesis⟩))) := by
  refine ⟨⟨consume g old ops atIndex inputs (state.logical data) scope mark.site
    ⟨mark.site, .callableImage⟩ arms (fromSource g old ops atIndex left right inputs (state.logical data)
      scope mark.site ⟨mark.site, .callableImage⟩ arms raw node catalogue packet found child)⟩, ?_⟩
  exact SourceDeclarationRetentionR295.Selected.original_target_pair inputs registry readout ports
    declarations original environment context mark occurrence data state decoded arms scope raw packet checked

end Selected


/-- Registration of every original edge target suffices; no uniqueness of
source labels, owners, scopes, slots or providers is requested. The source
builder must independently establish this registration premise. -/
theorem closed_of_registered_targets (g : Graph Joint)
    (registered : ∀ i n step child, g.node i = some n → SourceEdge n step child →
      ∃ target, g.node child = some target) : ClosedPrefix g g.nodes.length := by
  intro i n step child _ found edge
  obtain ⟨target, lookup⟩ := registered i n step child found edge
  exact (List.getElem?_eq_some_iff.mp lookup).1

/-- One-way compatibility with the existing contribution/projection consumer.
The reverse implication is intentionally absent (R295 refutes it). -/
def toLegacy (g : Graph Joint) (d : DeclarationData Joint)
    (old : Relations (install g d)) (ops : Operators (install g d)) {i w n p}
    (c : Contribution (install g d) (localRelations g d old) ops i w n p) :
    DeclContribution (install g d) (retainedRelations g d old) ops i w n p := by
  apply erase
  apply map (a := localRelations g d old) _ c
  intro i
  unfold localRelations
  split
  · exact ⟨fun _ _ _ {_ _} _ _ e => e, fun _ _ {_ _ _} _ _ _ e => e, fun _ _ {_ _} _ _ e => e⟩
  · exact ⟨fun _ _ _ {_ _} _ _ e => e, fun _ _ {_ _ _} _ _ _ e => e, fun _ _ {_ _} _ _ e => Sum.inl e⟩

theorem use_preserves_owner (g : Graph Joint) (d : DeclarationData Joint)
    (old : Relations (install g d)) (ops : Operators (install g d)) (w : Joint)
    (p : Packet d.clause.catalogue (g.substitution d.substitution w))
    (c : Contribution (install g d) (localRelations g d old) ops g.nodes.length
      (g.substitution d.substitution w) d.clause p)
    (field : (toLegacy g d old ops c).Projection) :
    ((toLegacy g d old ops (atUse g d old ops w p c)).project field).occurrence.owner =
      ((toLegacy g d old ops c).project field).occurrence.owner := rfl

theorem use_preserves_license (g : Graph Joint) (d : DeclarationData Joint)
    (old : Relations (install g d)) (ops : Operators (install g d)) (w : Joint)
    (p : Packet d.clause.catalogue (g.substitution d.substitution w))
    (c : Contribution (install g d) (localRelations g d old) ops g.nodes.length
      (g.substitution d.substitution w) d.clause p)
    (field : (toLegacy g d old ops c).Projection) :
    ((toLegacy g d old ops (atUse g d old ops w p c)).project field).license =
      ((toLegacy g d old ops c).project field).license := rfl

end YulangClosure.SourceDeclarationNoninterferenceR296

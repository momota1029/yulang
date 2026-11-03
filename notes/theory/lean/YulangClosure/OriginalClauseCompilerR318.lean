import YulangClosure.SourceDeclarationNoninterferenceR296

/-!
R318: a registered, independently typed relational-clause compiler.

IF construction (2026-10-08) §3.2, source-contracts §2.1. This is the
primitive/Union/Conj/Scope/Rename/Ref fragment, including finite cyclic
registration and finite derivations. It is not the full source or Call grammar.
The input is an original typed clause table, not a Graph, placement, or
DeclContribution. Authentic extraction of this table (in particular for R315
io::tick), original substitution legality, constructor images and complete
Call/EI contracts remain independent source-owner obligations.

Each catalogue is the complete original dependent telescope. The shared Joint
can contain distinct branch/result worlds, providers and output-dependent
futures; none is equated by this compiler. Original relations are inputs at
their owning clauses. Empty license fibers never remove static interfaces.
-/
namespace YulangClosure.OriginalClauseCompilerR318

open OriginalSource SourceSignatureConstruction SourceContributionConstruction
open SourceDeclarationRetentionR295
namespace Local

variable {Joint : Type} {n : Nat}

/-- Original ownership is more than an unqualified operation spelling. -/
structure Identity where
  operationOwner : Declaration
  declaration : Declaration
  clause : Nat
  occurrence : Site
  scope : List Binder
  deriving DecidableEq, Repr

/-- Independently typed source clauses, before graph addresses are generated.
References are original registered identities (Fin n), not arbitrary addresses.
Both Union relations refer to their own whole dependent child/result packets.
No relation contains a target contribution or final checking judgment. -/
inductive Clause (interfaces : Fin n → Catalogue Joint) (substitution : Nat → Joint → Joint)
    (result : Catalogue Joint) where
  | primitive (kind : OriginKind)
      (license : (whole : Joint) → (port : result.Port) → result.Packet whole port → Type)
  | union (left right : Fin n)
      (leftRelation : (whole : Joint) → Packet (interfaces left) whole → Packet result whole → Type)
      (rightRelation : (whole : Joint) → Packet (interfaces right) whole → Packet result whole → Type)
  | conjunction (left right : Fin n)
      (relation : (whole : Joint) → Packet (interfaces left) whole →
        Packet (interfaces right) whole → Packet result whole → Type)
  | scope (binder : Binder) (child : Fin n)
      (relation : (whole : Joint) → Packet (interfaces child) whole → Packet result whole → Type)
  | rename (sub : Nat) (child : Fin n)
      (relation : (whole : Joint) → Packet (interfaces child) (substitution sub whole) → Packet result whole → Type)
  | reference (sub : Nat) (target : Fin n)
      (relation : (whole : Joint) → Packet (interfaces target) (substitution sub whole) → Packet result whole → Type)

/-- The declared ordinary parameters and all dependent evidence/result fields
are represented by interfaces.Packet. A single original substitution family
acts on the entire tuple. Its semantic legality is not inferred here. -/
structure Table (Joint : Type) (n : Nat) where
  identity : Fin n → Identity
  interfaces : Fin n → Catalogue Joint
  substitution : Nat → Joint → Joint
  clauses : (key : Fin n) → Clause interfaces substitution (interfaces key)
  scopeAgreement : ∀ key, (interfaces key).scope = (identity key).scope

def introduction (table : Table Joint n) (key : Fin n) (kind : OriginKind)
    (license : (whole : Joint) → (port : (table.interfaces key).Port) →
      (table.interfaces key).Packet whole port → Type) : Introduction Joint :=
  ⟨(table.identity key).operationOwner, (table.identity key).occurrence,
    kind, table.interfaces key, license⟩

def node (table : Table Joint n) (key : Fin n) : Node Joint :=
  match table.clauses key with
  | .primitive kind license => .primitive (introduction table key kind license)
  | .union left right _ _ => .alternative (table.identity key).occurrence left.val right.val (table.interfaces key)
  | .conjunction left right _ => .conjunction (table.identity key).occurrence left.val right.val (table.interfaces key)
  | .scope binder child _ => .scope binder child.val (table.interfaces key)
  | .rename sub child _ => .rename (table.identity key).occurrence sub child.val (table.interfaces key)
  | .reference sub target _ => .reference (table.identity key).occurrence target.val sub (table.interfaces key)

def graph (table : Table Joint n) : Graph Joint where
  nodes := List.ofFn (node table)
  registration := fun index => if h : index < n then (table.identity ⟨index, h⟩).declaration else 0
  substitution := table.substitution

theorem lookup (table : Table Joint n) (key : Fin n) :
    (graph table).node key.val = some (node table key) := by
  simp [graph, Graph.node]

/-- Receiving declaration identity stays separate from the primitive owner. -/
theorem registration_retained (table : Table Joint n) (key : Fin n) :
    (graph table).registration key.val = (table.identity key).declaration := by
  simp [graph, key.isLt]

theorem catalogue_retained (table : Table Joint n) (key : Fin n) :
    (node table key).catalogue = table.interfaces key := by
  unfold node
  split <;> rfl

theorem scope_retained (table : Table Joint n) (key : Fin n) :
    (node table key).catalogue.scope = (table.identity key).scope := by
  rw [catalogue_retained]
  exact table.scopeAgreement key

/-- Static inventory includes BOTH original alternatives, independent of any
selected derivation or primitive license. Positions preserve duplicates. -/
def alternatives (table : Table Joint n) (key : Fin n) : List (Fin n) :=
  match table.clauses key with
  | .union left right _ _ => [left, right]
  | _ => []

theorem union_inventory (table : Table Joint n) (key left right : Fin n) (lr rr)
    (formed : table.clauses key = .union left right lr rr) :
    alternatives table key = [left, right] ∧
      (node table key).edges = [(.alternative (table.identity key).occurrence false, left.val),
        (.alternative (table.identity key).occurrence true, right.val)] := by
  simp [alternatives, node, formed, Node.edges]

/-- A small fiber retaining the actual original relation witness. The two
heterogeneous equalities only align dependent packet types; they impose no
equality between coordinates of a child packet and a result packet. -/
def Related {a b c d : Catalogue Joint} {childWhole resultWhole : Joint}
    (rel : Packet a childWhole → Packet b resultWhole → Type)
    (actual : Packet c childWhole) (output : Packet d resultWhole) : Type :=
  Σ original : Packet a childWhole, Σ result : Packet b resultWhole,
    PLift (HEq actual original ∧ HEq output result) × rel original result

def Paired {a b c d e f : Catalogue Joint} {whole : Joint}
    (rel : Packet a whole → Packet b whole → Packet c whole → Type)
    (first : Packet d whole) (second : Packet e whole) (output : Packet f whole) : Type :=
  Σ l : Packet a whole, Σ r : Packet b whole, Σ result : Packet c whole,
    PLift (HEq first l ∧ HEq second r ∧ HEq output result) × rel l r result

def originalRelations (table : Table Joint n) (key : Fin n) : Relations (graph table) where
  alternative := fun site side whole {_ _} child output =>
    match table.clauses key with
    | .union _ _ lr rr =>
        if site = (table.identity key).occurrence then
          if side then Related (rr whole) child output else Related (lr whole) child output
        else Empty
    | _ => Empty
  conjunction := fun site whole {_ _ _} first second output =>
    match table.clauses key with
    | .conjunction _ _ rel =>
        if site = (table.identity key).occurrence then Paired (rel whole) first second output else Empty
    | _ => Empty
  forward := fun step whole {_ _} child output =>
    match table.clauses key with
    | .scope binder _ rel =>
        if h : step = .scope binder then by subst step; exact Related (rel whole) child output
        else Empty
    | .rename sub _ rel =>
        if h : step = .rename (table.identity key).occurrence sub then by
          subst step; exact Related (rel whole) child output
        else Empty
    | .reference sub target rel =>
        if h : step = .reference (table.identity key).occurrence target.val sub then by
          subst step; exact Related (rel whole) child output
        else Empty
    | _ => Empty

def emptyRelations (g : Graph Joint) : Relations g where
  alternative := fun _ _ _ {_ _} _ _ => Empty
  conjunction := fun _ _ {_ _ _} _ _ _ => Empty
  forward := fun _ _ {_ _} _ _ => Empty

/-- Occurrence indexing prevents equal source labels from licensing another row. -/
def relations (table : Table Joint n) (index : Nat) : Relations (graph table) :=
  if h : index < n then originalRelations table ⟨index, h⟩ else emptyRelations _

theorem relations_at (table : Table Joint n) (key : Fin n) :
    relations table key.val = originalRelations table key := by
  simp [relations, key.isLt]

/-- No image/Call licenses are synthesized for the fragment. -/
def emptyContract (g : Graph Joint) (node : Node Joint) : OperatorContract g node where
  Evidence := fun _ _ => Empty
  Field := fun _ _ evidence => nomatch evidence
  governed := fun _ _ evidence => nomatch evidence

def operators (table : Table Joint n) : Operators (graph table) where
  image := fun _ _ _ _ _ => emptyContract _ _
  call := fun _ _ _ _ _ _ _ => emptyContract _ _

/-- Original finite clause derivations. Recursive references need a finite
child derivation, not acyclicity or a preexisting graph contribution. -/
inductive Derivation (table : Table Joint n) :
    (key : Fin n) → (whole : Joint) → Packet (table.interfaces key) whole → Type 1 where
  | primitive (key : Fin n) (kind license)
      (formed : table.clauses key = .primitive kind license)
      (whole : Joint) (packet : Packet (table.interfaces key) whole)
      (licensed : license whole packet.port packet.value) : Derivation table key whole packet
  | unionLeft (key left right : Fin n) (lr rr)
      (formed : table.clauses key = .union left right lr rr)
      {whole : Joint} {childPacket : Packet (table.interfaces left) whole}
      (child : Derivation table left whole childPacket)
      (output : Packet (table.interfaces key) whole) (related : lr whole childPacket output) :
      Derivation table key whole output
  | unionRight (key left right : Fin n) (lr rr)
      (formed : table.clauses key = .union left right lr rr)
      {whole : Joint} {childPacket : Packet (table.interfaces right) whole}
      (child : Derivation table right whole childPacket)
      (output : Packet (table.interfaces key) whole) (related : rr whole childPacket output) :
      Derivation table key whole output
  | conjunction (key left right : Fin n) (rel)
      (formed : table.clauses key = .conjunction left right rel)
      {whole : Joint} {firstPacket : Packet (table.interfaces left) whole}
      {secondPacket : Packet (table.interfaces right) whole}
      (first : Derivation table left whole firstPacket)
      (second : Derivation table right whole secondPacket)
      (output : Packet (table.interfaces key) whole) (related : rel whole firstPacket secondPacket output) :
      Derivation table key whole output
  | scope (key child : Fin n) (binder rel)
      (formed : table.clauses key = .scope binder child rel)
      {whole : Joint} {childPacket : Packet (table.interfaces child) whole}
      (prior : Derivation table child whole childPacket)
      (output : Packet (table.interfaces key) whole) (related : rel whole childPacket output) :
      Derivation table key whole output
  | rename (key child : Fin n) (sub rel)
      (formed : table.clauses key = .rename sub child rel)
      {whole : Joint} {childPacket : Packet (table.interfaces child) (table.substitution sub whole)}
      (prior : Derivation table child (table.substitution sub whole) childPacket)
      (output : Packet (table.interfaces key) whole) (related : rel whole childPacket output) :
      Derivation table key whole output
  | reference (key child : Fin n) (sub rel)
      (formed : table.clauses key = .reference sub child rel)
      {whole : Joint} {childPacket : Packet (table.interfaces child) (table.substitution sub whole)}
      (prior : Derivation table child (table.substitution sub whole) childPacket)
      (output : Packet (table.interfaces key) whole) (related : rel whole childPacket output) :
      Derivation table key whole output

/-- Only a catalogue-type transport, retaining the complete original packet. -/
def compiledPacket (table : Table Joint n) (key : Fin n) {whole : Joint}
    (packet : Packet (table.interfaces key) whole) : Packet (node table key).catalogue whole :=
  (catalogue_retained table key).symm ▸ packet

theorem transported_packet_heq {a b : Catalogue Joint} {whole : Joint}
    (same : a = b) (packet : Packet a whole) : HEq (same ▸ packet) packet := by
  cases same
  rfl

theorem packet_heq (table : Table Joint n) (key : Fin n) {whole : Joint}
    (packet : Packet (table.interfaces key) whole) : HEq (compiledPacket table key packet) packet :=
  transported_packet_heq _ packet

def alignContribution {g : Graph Joint} {r : Nat → Relations g} {ops : Operators g}
    {index whole} {actual expected : Node Joint}
    {packet : Packet actual.catalogue whole} {expectedPacket : Packet expected.catalogue whole}
    (same : expected = actual) (samePacket : HEq expectedPacket packet)
    (contribution : SourceDeclarationNoninterferenceR296.Contribution g r ops index whole actual packet) :
    SourceDeclarationNoninterferenceR296.Contribution g r ops index whole expected expectedPacket := by
  cases same
  cases eq_of_heq samePacket
  exact contribution

/-- Construct the actual R296 contribution by induction on original finite
derivations. All graph lookups, selected local relation witnesses and complete
packets are outputs; no contribution or placement is supplied as an input. -/
noncomputable def compileDerivation (table : Table Joint n) {key whole packet}
    (derivation : Derivation table key whole packet) :
    SourceDeclarationNoninterferenceR296.Contribution (graph table) (relations table) (operators table)
      key.val whole (node table key) (compiledPacket table key packet) := by
  induction derivation with
  | primitive key kind license formed whole packet licensed =>
      have found := lookup table key
      simp only [node, formed] at found
      exact alignContribution (by simp only [node, formed]) (packet_heq table key packet)
        (SourceDeclarationNoninterferenceR296.Contribution.primitive
          (graph := graph table) (relations := relations table) (operators := operators table)
          found packet licensed)
  | @unionLeft key left right lr rr formed whole childPacket child output related ih =>
      have found := lookup table key
      simp only [node, formed] at found
      have localWitness : (relations table key.val).alternative (table.identity key).occurrence false
          whole (compiledPacket table left childPacket) output := by
        rw [relations_at]
        simp only [originalRelations, formed, ↓reduceIte, Bool.false_eq_true]
        exact ⟨childPacket, output, ⟨⟨packet_heq table left childPacket, HEq.rfl⟩⟩, related⟩
      exact alignContribution (by simp only [node, formed]) (packet_heq table key output)
        (SourceDeclarationNoninterferenceR296.Contribution.alternativeLeft found ih output localWitness)
  | @unionRight key left right lr rr formed whole childPacket child output related ih =>
      have found := lookup table key
      simp only [node, formed] at found
      have localWitness : (relations table key.val).alternative (table.identity key).occurrence true
          whole (compiledPacket table right childPacket) output := by
        rw [relations_at]
        simp only [originalRelations, formed, ↓reduceIte]
        exact ⟨childPacket, output, ⟨⟨packet_heq table right childPacket, HEq.rfl⟩⟩, related⟩
      exact alignContribution (by simp only [node, formed]) (packet_heq table key output)
        (SourceDeclarationNoninterferenceR296.Contribution.alternativeRight found ih output localWitness)
  | @conjunction key left right rel formed whole firstPacket secondPacket first second output related ihl ihr =>
      have found := lookup table key
      simp only [node, formed] at found
      have localWitness : (relations table key.val).conjunction (table.identity key).occurrence whole
          (compiledPacket table left firstPacket) (compiledPacket table right secondPacket) output := by
        rw [relations_at]
        simp only [originalRelations, formed, ↓reduceIte]
        exact ⟨firstPacket, secondPacket, output,
          ⟨⟨packet_heq table left firstPacket, packet_heq table right secondPacket, HEq.rfl⟩⟩, related⟩
      exact alignContribution (by simp only [node, formed]) (packet_heq table key output)
        (SourceDeclarationNoninterferenceR296.Contribution.conjunction found ihl ihr output localWitness)
  | @scope key child binder rel formed whole childPacket prior output related ih =>
      have found := lookup table key
      simp only [node, formed] at found
      have localWitness : (relations table key.val).forward (.scope binder) whole
          (compiledPacket table child childPacket) output := by
        rw [relations_at]
        simp only [originalRelations, formed, ↓reduceDIte]
        exact ⟨childPacket, output, ⟨⟨packet_heq table child childPacket, HEq.rfl⟩⟩, related⟩
      exact alignContribution (by simp only [node, formed]) (packet_heq table key output)
        (SourceDeclarationNoninterferenceR296.Contribution.forward found Forward.scope ih output localWitness)
  | @rename key child sub rel formed whole childPacket prior output related ih =>
      have found := lookup table key
      simp only [node, formed] at found
      have localWitness : (relations table key.val).forward (.rename (table.identity key).occurrence sub)
          whole (compiledPacket table child childPacket) output := by
        rw [relations_at]
        simp only [originalRelations, formed, ↓reduceDIte]
        exact ⟨childPacket, output, ⟨⟨packet_heq table child childPacket, HEq.rfl⟩⟩, related⟩
      exact alignContribution (by simp only [node, formed]) (packet_heq table key output)
        (SourceDeclarationNoninterferenceR296.Contribution.forward found Forward.rename ih output localWitness)
  | @reference key child sub rel formed whole childPacket prior output related ih =>
      have found := lookup table key
      simp only [node, formed] at found
      have localWitness : (relations table key.val).forward
          (.reference (table.identity key).occurrence child.val sub) whole
          (compiledPacket table child childPacket) output := by
        rw [relations_at]
        simp only [originalRelations, formed, ↓reduceDIte]
        exact ⟨childPacket, output, ⟨⟨packet_heq table child childPacket, HEq.rfl⟩⟩, related⟩
      exact alignContribution (by simp only [node, formed]) (packet_heq table key output)
        (SourceDeclarationNoninterferenceR296.Contribution.forward found Forward.reference ih output localWitness)

/-- The legacy interface has one relation family. Keep an explicit source-key
tag when embedding occurrence-local witnesses. Only forward construction is
claimed: arbitrary legacy derivations do not reflect to original derivations. -/
def legacyRelations (table : Table Joint n) : Relations (graph table) where
  alternative := fun site side whole {_ _} p q =>
    Σ key : Fin n, (originalRelations table key).alternative site side whole p q
  conjunction := fun site whole {_ _ _} p q r =>
    Σ key : Fin n, (originalRelations table key).conjunction site whole p q r
  forward := fun step whole {_ _} p q =>
    Σ key : Fin n, (originalRelations table key).forward step whole p q

def legacyMap (table : Table Joint n) (index : Nat) :
    SourceDeclarationNoninterferenceR296.RelationMap (relations table index) (legacyRelations table) := by
  unfold relations
  split
  next bound =>
    exact ⟨fun _ _ _ {_ _} _ _ e => ⟨⟨index, bound⟩, e⟩,
      fun _ _ {_ _ _} _ _ _ e => ⟨⟨index, bound⟩, e⟩,
      fun _ _ {_ _} _ _ e => ⟨⟨index, bound⟩, e⟩⟩
  next outside =>
    exact ⟨fun _ _ _ {_ _} _ _ e => Empty.elim e,
      fun _ _ {_ _ _} _ _ _ e => Empty.elim e,
      fun _ _ {_ _} _ _ e => Empty.elim e⟩

noncomputable def compileLegacy (table : Table Joint n) {key whole packet}
    (derivation : Derivation table key whole packet) :
    DeclContribution (graph table) (legacyRelations table) (operators table)
      key.val whole (node table key) (compiledPacket table key packet) :=
  SourceDeclarationNoninterferenceR296.erase
    (SourceDeclarationNoninterferenceR296.map (legacyMap table) (compileDerivation table derivation))

/-- Internal address change for a duplicated clause root. All recursive child
derivations and original local evidence stay unchanged. -/
def reroot {g : Graph Joint} {r : Relations g} {ops : Operators g}
    {index target whole node packet} (found : g.node target = some node)
    (contribution : DeclContribution g r ops index whole node packet) :
    DeclContribution g r ops target whole node packet := by
  cases contribution with
  | primitive _ p l => exact .primitive found p l
  | alternativeLeft _ c p e => exact .alternativeLeft found c p e
  | alternativeRight _ c p e => exact .alternativeRight found c p e
  | conjunction _ c d p e => exact .conjunction found c d p e
  | image _ p e => exact .image found p e
  | call _ p e => exact .call found p e
  | forward _ source c _ e => exact .forward found source c _ e

/-- Data are computed from the original target and reference identities. The
formed-reference premise below authenticates the reference within this input
table; it does not authenticate extraction of the table from native source. -/
def declaration (table : Table Joint n) (target use : Fin n) (substitution : Nat) :
    DeclarationData Joint :=
  ⟨target.val, (table.identity target).clause, (table.identity use).occurrence,
    substitution, node table target⟩

/-- Opaque after kernel checking to keep downstream field-type normalization
from unfolding the entire source induction. No axiom or extra law is added. -/
noncomputable opaque insertedContribution (table : Table Joint n) (target use : Fin n) (sub : Nat)
    {whole packet} (derivation : Derivation table target whole packet) :
    SourceDeclarationNoninterferenceR296.Contribution
      (install (graph table) (declaration table target use sub))
      (SourceDeclarationNoninterferenceR296.localRelations (graph table) (declaration table target use sub)
        (SourceDeclarationNoninterferenceR296.lift_relations (graph table) (declaration table target use sub)
          (legacyRelations table)))
      (SourceDeclarationNoninterferenceR296.lift_operators (graph table) (declaration table target use sub)
        (operators table))
      (graph table).nodes.length whole (node table target) (compiledPacket table target packet) := by
  apply SourceDeclarationNoninterferenceR296.preserve
    (graph table) (declaration table target use sub)
  exact reroot (clause_lookup (graph table) (declaration table target use sub))
    (SourceDeclarationNoninterferenceR296.lift_contribution
      (graph table) (declaration table target use sub) (legacyRelations table) (operators table)
      (compileLegacy table derivation))

/-- The actual R296 IF-Insert/Use consumer. The occurrence is an original
reference clause; the frame pullback is kept distinct from its result relation. -/
noncomputable def atUse (table : Table Joint n) (target use : Fin n) (sub : Nat)
    (rel) (_formed : table.clauses use = .reference sub target rel)
    (whole : Joint) (packet : Packet (table.interfaces target) (table.substitution sub whole))
    (derivation : Derivation table target (table.substitution sub whole) packet) :=
  SourceDeclarationNoninterferenceR296.atUse (graph table) (declaration table target use sub)
    (SourceDeclarationNoninterferenceR296.lift_relations (graph table) (declaration table target use sub)
      (legacyRelations table))
    (SourceDeclarationNoninterferenceR296.lift_operators (graph table) (declaration table target use sub)
      (operators table)) whole (compiledPacket table target packet)
    (insertedContribution table target use sub derivation)

noncomputable def legacyUse (table : Table Joint n) (target use : Fin n) (sub : Nat)
    (rel) (formed : table.clauses use = .reference sub target rel)
    (whole : Joint) (packet : Packet (table.interfaces target) (table.substitution sub whole))
    (derivation : Derivation table target (table.substitution sub whole) packet) :=
  SourceDeclarationNoninterferenceR296.toLegacy (graph table) (declaration table target use sub)
    (SourceDeclarationNoninterferenceR296.lift_relations (graph table) (declaration table target use sub)
      (legacyRelations table))
    (SourceDeclarationNoninterferenceR296.lift_operators (graph table) (declaration table target use sub)
      (operators table)) (atUse table target use sub rel formed whole packet derivation)

/-- The attachment at IF-Insert consumes the very clause contribution
retained inside legacyUse, as proved by the field-preservation theorems below. The pullback
interface stays distinct from the original reference-result telescope. -/
noncomputable def attachment (table : Table Joint n) (target use : Fin n) (sub : Nat)
    {whole packet} (derivation : Derivation table target whole packet) :
    DeclaredAttachment (install (graph table) (declaration table target use sub))
      (retainedRelations (graph table) (declaration table target use sub)
        (SourceDeclarationNoninterferenceR296.lift_relations (graph table) (declaration table target use sub)
          (legacyRelations table)))
      (SourceDeclarationNoninterferenceR296.lift_operators (graph table) (declaration table target use sub)
        (operators table))
      ⟨(graph table).nodes.length + 1, target.val, (table.identity target).clause,
        (graph table).nodes.length, whole, node table target,
        compiledPacket table target packet⟩ :=
  .declared _ _ (insertion_lookup (graph table) (declaration table target use sub))
    (SourceDeclarationNoninterferenceR296.toLegacy (graph table) (declaration table target use sub)
      (SourceDeclarationNoninterferenceR296.lift_relations (graph table) (declaration table target use sub)
        (legacyRelations table))
      (SourceDeclarationNoninterferenceR296.lift_operators (graph table) (declaration table target use sub)
        (operators table)) (insertedContribution table target use sub derivation))

/-- Actual application chain: compileDerivation -> insertedContribution ->
R296.atUse -> R296.toLegacy. The declared attachment and use retain the SAME
licensed projection and packet; routes gain their genuine contextual steps. -/
theorem used_owner_preserved (table : Table Joint n) (target use : Fin n) (sub : Nat)
    (rel) (formed : table.clauses use = .reference sub target rel)
    (whole : Joint) (packet : Packet (table.interfaces target) (table.substitution sub whole))
    (derivation : Derivation table target (table.substitution sub whole) packet)
    (field : (attachment table target use sub derivation).contribution.Projection) :
    ((legacyUse table target use sub rel formed whole packet derivation).project field).occurrence.owner =
      ((attachment table target use sub derivation).contribution.project field).occurrence.owner := rfl

theorem used_packet_preserved (table : Table Joint n) (target use : Fin n) (sub : Nat)
    (rel) (formed : table.clauses use = .reference sub target rel)
    (whole : Joint) (packet : Packet (table.interfaces target) (table.substitution sub whole))
    (derivation : Derivation table target (table.substitution sub whole) packet)
    (field : (attachment table target use sub derivation).contribution.Projection) :
    HEq ((legacyUse table target use sub rel formed whole packet derivation).project field).packet
      ((attachment table target use sub derivation).contribution.project field).packet := HEq.rfl

theorem used_license_preserved (table : Table Joint n) (target use : Fin n) (sub : Nat)
    (rel) (formed : table.clauses use = .reference sub target rel)
    (whole : Joint) (packet : Packet (table.interfaces target) (table.substitution sub whole))
    (derivation : Derivation table target (table.substitution sub whole) packet)
    (field : (attachment table target use sub derivation).contribution.Projection) :
    HEq ((legacyUse table target use sub rel formed whole packet derivation).project field).license
      ((attachment table target use sub derivation).contribution.project field).license := HEq.rfl

theorem attached_field_preserved (table : Table Joint n) (target use : Fin n) (sub : Nat)
    {whole packet} (derivation : Derivation table target whole packet)
    (field : (attachment table target use sub derivation).contribution.Projection) :
    ((attachment table target use sub derivation).place field).original =
      (attachment table target use sub derivation).contribution.project field := rfl

theorem attached_owner_preserved (table : Table Joint n) (target use : Fin n) (sub : Nat)
    {whole packet} (derivation : Derivation table target whole packet)
    (field : (attachment table target use sub derivation).contribution.Projection) :
    ((attachment table target use sub derivation).place field).placement.owner =
      ((attachment table target use sub derivation).contribution.project field).occurrence.owner := rfl

/-- A theorem-level consumer root for the checker, with no Graph/contribution
input and all original finite derivation evidence explicit. -/
theorem compiled_contribution_exists (table : Table Joint n) {key whole packet}
    (derivation : Derivation table key whole packet) :
    Nonempty (SourceDeclarationNoninterferenceR296.Contribution
      (graph table) (relations table) (operators table) key.val whole
      (node table key) (compiledPacket table key packet)) := ⟨compileDerivation table derivation⟩

theorem compiled_attachment_exists (table : Table Joint n) (target use : Fin n) (sub : Nat)
    {whole packet} (derivation : Derivation table target whole packet) :
    Nonempty (DeclaredAttachment (install (graph table) (declaration table target use sub))
      (retainedRelations (graph table) (declaration table target use sub)
        (SourceDeclarationNoninterferenceR296.lift_relations (graph table) (declaration table target use sub)
          (legacyRelations table)))
      (SourceDeclarationNoninterferenceR296.lift_operators (graph table) (declaration table target use sub)
        (operators table))
      ⟨(graph table).nodes.length + 1, target.val, (table.identity target).clause,
        (graph table).nodes.length, whole, node table target,
        compiledPacket table target packet⟩) := ⟨attachment table target use sub derivation⟩

/-- All source references are registered, including cycles. No acyclicity,
fresh labels or finite unfolding assumption is used. -/
theorem graph_closed (table : Table Joint n) :
    SourceDeclarationNoninterferenceR296.ClosedPrefix (graph table) (graph table).nodes.length := by
  intro index result step child bound found edge
  have inside : index < n := by simpa [graph] using bound
  let key : Fin n := ⟨index, inside⟩
  have same : result = node table key := Option.some.inj (found.symm.trans (lookup table key))
  subst result
  simp only [graph, List.length_ofFn]
  unfold node at edge
  split at edge <;> cases edge <;> omega

/-- The source-identified reference is consumed at its original substituted
whole row. This proves the IF frame contribution, not its independent result
relation or a source Checking/admission judgment. -/
theorem authenticated_use_exists (table : Table Joint n) (target use : Fin n) (sub : Nat)
    (rel) (formed : table.clauses use = .reference sub target rel)
    (whole : Joint) (packet : Packet (table.interfaces target) (table.substitution sub whole))
    (derivation : Derivation table target (table.substitution sub whole) packet) :
    let g := graph table
    let d := declaration table target use sub
    let r := SourceDeclarationNoninterferenceR296.lift_relations g d (legacyRelations table)
    let ops := SourceDeclarationNoninterferenceR296.lift_operators g d (operators table)
    Nonempty (DeclContribution (install g d) (retainedRelations g d r) ops
      (g.nodes.length + 2) whole (referenceNode g d)
      (usePacket g d whole (compiledPacket table target packet))) :=
  ⟨legacyUse table target use sub rel formed whole packet derivation⟩

/-- The full original source identity stays alongside each generated row. -/
def inventory (table : Table Joint n) :=
  List.ofFn fun key => (table.identity key, (node table key).catalogue, alternatives table key)

theorem inventory_retained (table : Table Joint n) (key : Fin n) :
    (inventory table)[key.val]? =
      some (table.identity key, table.interfaces key, alternatives table key) := by
  simp [inventory, catalogue_retained]

theorem primitive_license_required (table : Table Joint n) (key : Fin n) (kind license)
    (formed : table.clauses key = .primitive kind license)
    {whole packet} (derivation : Derivation table key whole packet) :
    Nonempty (license whole packet.port packet.value) := by
  cases derivation with
  | primitive _ _ _ original _ _ licensed =>
      have equality := original.symm.trans formed
      cases equality
      exact ⟨licensed⟩
  | unionLeft _ _ _ _ _ original _ _ _
  | unionRight _ _ _ _ _ original _ _ _
  | conjunction _ _ _ _ original _ _ _ _
  | scope _ _ _ _ original _ _ _
  | rename _ _ _ _ original _ _ _
  | reference _ _ _ _ original _ _ _ =>
      rw [formed] at original
      contradiction

theorem empty_license_no_derivation (table : Table Joint n) (key : Fin n) (kind)
    (formed : table.clauses key = .primitive kind (fun _ _ _ => Empty))
    (whole : Joint) (packet : Packet (table.interfaces key) whole) :
    ¬ Nonempty (Derivation table key whole packet) := by
  rintro ⟨derivation⟩
  exact (primitive_license_required table key kind _ formed derivation).elim Empty.elim

/-! A diagnostic source table, not an authenticated native declaration. Its
child/result worlds differ; futures depend on the actual result provider.
The unselected right clause has no license, but retains its own scope. -/
namespace Diagnostic

structure Returned where
  world : Nat
  provider : Nat
  future : Fin provider → Nat

def childCatalogue (id : Nat) : Catalogue Nat :=
  ⟨Unit, fun _ _ => Nat, [⟨id, .invocation, 0⟩], fun _ => id⟩
def resultCatalogue : Catalogue Nat := ⟨Unit, fun _ _ => Returned, [], fun _ => 90⟩
def interfaces (key : Fin 4) : Catalogue Nat :=
  match key.val with
  | 0 => childCatalogue 0
  | 1 => childCatalogue 1
  | _ => resultCatalogue

def leftRelation (whole : Nat) (child : Packet (interfaces 0) whole)
    (result : Packet (interfaces 2) whole) : Type :=
  PLift (result.value.world = (show Nat from child.value) + 5 ∧
    result.value.provider = (show Nat from child.value) + 1)
def rightRelation (whole : Nat) (_child : Packet (interfaces 1) whole)
    (_result : Packet (interfaces 2) whole) : Type := Empty

def referenceRelation (whole : Nat) (child : Packet (interfaces 2) (whole + 7))
    (result : Packet (interfaces 3) whole) : Type :=
  PLift (result.value.world = child.value.world + 2)

def table : Table Nat 4 where
  identity := fun key => ⟨51, 81, key.val, key.val + 100, (interfaces key).scope⟩
  interfaces := interfaces
  substitution := fun _ whole => whole + 7
  clauses := fun
    | ⟨0, _⟩ => .primitive .primitive (fun whole _ value => PLift (value = whole))
    | ⟨1, _⟩ => .primitive .primitive (fun _ _ _ => Empty)
    | ⟨2, _⟩ => .union 0 1 leftRelation rightRelation
    | ⟨3, _⟩ => .reference 0 2 referenceRelation
    | ⟨_ + 4, bound⟩ => False.elim (by omega)
  scopeAgreement := fun _ => rfl

def returned (whole : Nat) : Returned := ⟨whole + 5, whole + 1, fun i => i.val + 90⟩
def resultPacket (whole : Nat) : Packet (table.interfaces 2) whole := ⟨(), returned whole⟩

def derivation (whole : Nat) : Derivation table 2 whole (resultPacket whole) :=
  .unionLeft 2 0 1 leftRelation rightRelation rfl
    (.primitive 0 .primitive (fun whole _ value => PLift (value = whole)) rfl
      whole ⟨(), whole⟩ ⟨rfl⟩)
    (resultPacket whole) ⟨rfl, rfl⟩

theorem different_worlds_compile (whole : Nat) :
    (returned whole).world ≠ whole ∧
      Nonempty (SourceDeclarationNoninterferenceR296.Contribution
        (graph table) (relations table) (operators table) 2 whole (node table 2)
        (compiledPacket table 2 (resultPacket whole))) := by
  constructor
  · simp only [returned]; omega
  · exact compiled_contribution_exists table (derivation whole)

theorem unselected_empty_retained (whole : Nat) :
    alternatives table 2 = [0, 1] ∧
      (node table 1).catalogue.scope = [⟨1, .invocation, 0⟩] ∧
      ¬ Nonempty (Derivation table 1 whole ⟨(), whole⟩) := by
  refine ⟨rfl, rfl, ?_⟩
  exact empty_license_no_derivation table 1 .primitive rfl whole ⟨(), whole⟩

theorem empty_license_no_compiled_contribution (whole : Nat) :
    ¬ Nonempty (SourceDeclarationNoninterferenceR296.Contribution
      (graph table) (relations table) (operators table) 1 whole (node table 1)
      (compiledPacket table 1 ⟨(), whole⟩)) := by
  rintro ⟨contribution⟩
  change SourceDeclarationNoninterferenceR296.Contribution _ _ _ _ _
    (.primitive (introduction table 1 .primitive (fun _ _ _ => Empty))) _ at contribution
  cases contribution with
  | primitive _ _ licensed => exact Empty.elim licensed
  | forward _ source _ _ _ => cases source

theorem original_substitution_once (whole : Nat) :
    (SourceSignatureConstruction.Step.reference 103 5 0).action
      (install (graph table) (declaration table 2 3 0)) whole = whole + 7 := rfl

end Diagnostic

end Local
end YulangClosure.OriginalClauseCompilerR318

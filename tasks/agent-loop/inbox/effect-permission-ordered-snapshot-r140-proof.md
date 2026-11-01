# R140 ordered snapshot proof handoff

Assignment: /root/r139_proof; session R140; handoff revision 1.
Contract: EFFECT-PERMISSION-ORDERED-SNAPSHOT/20261102-R140 revision 1,
SHA-256 e81ff2ddd7cda47bfb60bc1738e0c5bc3bfce4eb9effc183dd725003b4db06d0.
Source handoff: tasks/agent-loop/inbox/effect-permission-ordered-snapshot-r140-source.md,
28,566 bytes, SHA-256 3335922fa8b259a1f4dea95bbf72e4ee6db8a99d7dd22fce25b3909e91aa8f56.
Both input hashes were recomputed and match the primary's frozen intake.
Baseline: 4c1d58a646a1101c080659ebfed6ae7862d8aded.
Role: bounded Lean leaf; requested lean_prover/bounded; observed model/effort UNKNOWN.
Author: /root/r139_proof; descendants: none. Active-work acknowledgement sent to
/root before writes. Other workers' files and frozen R139 files were not edited.
Outcome: candidate, CONSTRUCTED_BUT_UNCHECKED. Kernel acceptance, printed theorem
types, complete transitive axiom results, independent review, source correspondence
and production authority are not established.

## Governing source and original obligation

Original statement: notes/theory/2026-10-13-intrusion-source-preservation-proof.md §1;
current correction: notes/design/2026-10-24-birth-level-scc-intrusion.md §§2–6;
whole-language scope: docs/yulang-whole-proof-closure-ja.md §§1–3. The all-supported-
source quantifiers, lawful finite histories, original lexical/type/event scopes,
complete Call, correlated evidence and one shared witness remain unchanged.
The source manuscript docs/yulang-source-type-safety-ja.tex sec:owners separates
live execution owner identity from retained historical evidence and does not
promote its candidate machine to Authoritative semantics.

Exact Lean parent: YulangClosure.SourceProblem.InferenceSoundness:
`∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
 ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a`.
This remains a proposition definition with uninstantiated concrete source fields.
No LocalLaws, native equality, assumed injectivity, or circular typing relation
is supplied by this packet.

The exact prior structural schema is
YulangClosure.FormalPermissionConstructorR136.{Row,Value,Elements,ports,inventory,
rowAllowed,emit,inventory_exact,record_identity,constructEntry}.
Its file was checked by computing Git's blob digest directly with hashlib,
without invoking Git: 2265896c38a8febf7fd41d10c9a49f9f4a1bc340, matching the
immutable baseline dependency in the frozen source handoff (10,356 bytes;
SHA-256 3289bccd2b85dd4576adb1c4a870e635985b60e2e87c459d9174c4a0477eab4f).
The new module imports Std only; it does not import the unchecked R139 module
or depend on R136's project proof/import cone.

R139's independent review corrections are retained: SourceNodeKey equality is
not occurrence injectivity; explicit allocation failure coverage does not cover
allocator aborts or all Clone allocations; FormalPosition is distinct from Formal;
R139 remains unchecked. No same-offset/source-occurrence uniqueness claim is made.

## Representation and exact source equations

Namespace: YulangClosure.FormalPermissionOrderedSnapshotR140.
TaggedKey has all eight Rust tag shapes, parameterized by seven separate payload
types: owner(Owner), occurrence(Occurrence), formal(Formal),
formalPosition(Owner, Nat), scope(Scope), node(Node), effect(Effect),
symbol(Scope, Symbol). FormalPosition's source index is represented as Nat;
Rust usize bounds and its relationship to HirParameterId remain separate premises.
Symbol retains both lexical scope and spelling. Derived DecidableEq uses payload
equality and tag discrimination; it carries no Rust-to-Lean correspondence law.

Context retains parameter index, occurrence, owner and annotation scope. Row
retains node position, ordered concrete members and ordered symbolic variables.
record uses ONE supplied table to encode context, formal position, row and members.
Paths are retained directly. This packet does not construct/interleave mutable
Rust registration; a complete frozen table is the projection input. List.idxOf
returns the length sentinel on absent keys: no authentication or injectivity
claim is made for an unregistered table, and table coverage must be supplied by
a separate source-to-table construction before interpreting the codes as IDs.

All accepted leaf families are represented: Unit, Int, Bool, Str, Variable and
Hole. Function has both child values and their optional rows. Tuple elements
retain their own optional rows even when unsupported; empty tuples and annotated
tuple children are explicitly rejected by supported. No accepted branch is
silently deleted to shorten the order proof. Variable/hole registration side
effects are omitted from this frozen-table projection, explicitly below.

ports inventories Function argument subtree, result subtree, immediate argument
row, immediate result row. Argument polarity flips; result polarity is retained.
Each path appends Argument or Result. Tuple traversal appends Element(index) in
source index order. inventory is the corresponding recursive emitted sequence.
inventory_order_filter / element_order_filter target exact list equality with
flatMap emit, preserving row order rather than merely set membership.

emit retains exactly negative/nonempty-concrete/zero-symbol-variable rows.
Positive, omitted, symbolic and empty rows are filtered out. rowAllowed separately
models native rejection: at most one symbolic variable, with negative rows either
one symbol/no concrete or nonempty concrete/no symbols. constructProjection checks
supported before publishing the pure projection; projection_success connects its
success to that gate and the exact flatMap inventory. Total inventory alone is
not claimed to be successful construction for unsupported source shapes.

record_fields retains every context field, formal-position code, path, row code
and ordered concrete map. concrete_position and concrete_length preserve each
member occurrence and sequence length. concrete_duplicates preserves two equal
members at their original adjacent positions plus an arbitrary remaining suffix.
The table itself is shared by every field and every record in all these targets.

The exact source fixture is:
`act io; my bridge (consume: ((int -> [io] ()) -> ()) -> (() -> (int -> [io] ()))) = consume`.
fixtureRows models the argument/result Function tree with effect rows attached
to each inner Function's result child, as in the committed fixture.
exact_aar_rrr_fixture targets the exact sequence
`[record table context AAR row1, record table context RRR row2]`, with row1 and
row2 retaining their separate source node values and the same single io effect.
exact_fixture_admitted targets its source projection admission;
exact_fixture_paths, exact_fixture_rows and exact_fixture_shared_effect retain
respectively `[AAR, RRR]`, the two ordered row codes and two distinct records each
containing the same one-element io-code sequence. Row identity inequality is not
assumed or inferred; distinct paths suffice to keep the two records unmerged.
fixture_order also covers arbitrary nonempty closed member sequences in both
rows, including repeated members.

Root annotation rows are separate: Annotation.rootRow is not traversed by
nestedProjection, and root_row_separate targets invariance when that root row
changes. EntryImage is a different record shape and Snapshot holds a separate
rootEntriesBefore vector. This is a structural separation, not proof that Rust
never mutates that vector or that entry construction itself is implemented here.

appended_suffix is pure list append/drop algebra. It does not identify an actual
Rust pre/post State or prove the observed output is an append. The frozen source
candidate owns those same-call facts. compareAndFinish computes equality of the
supplied expected/actual images and of before/after entry vectors. comparison_success
extracts the facts actually checked by that function; it never identifies the
supplied actual vector with a Rust execution. Failure has no Snapshot payload;
error_excludes_snapshot targets this result-type boundary. No private completion
marker is treated as an independent authenticity theorem.

## Constructed theorem statements and audit status

The following declarations include future inline `#check @<qualified-name>` and
`#print axioms <qualified-name>` commands in the frozen artifact. None was run.
For EVERY declaration below: actual printed type UNAVAILABLE; actual transitive
axiom list UNAVAILABLE; kernel status UNCHECKED. Source text is not printed-type
or axiom-audit evidence. The artifact contains no sorry/admit/project axiom or
kernel-bypass declaration; a static text scan is not a transitive dependency audit.

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.inventory_order_filter (value : Value Node Effect Symbol) (positive : Bool) (path : List Step) :
      inventory table context value positive path = (ports value positive path).flatMap (emit table context)
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.element_order_filter (elements : Elements Node Effect Symbol) (positive : Bool)
      (path : List Step) (index : Nat) :
      elementInventory table context elements positive path index =
        (elementPorts elements positive path index).flatMap (emit table context)
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.record_fields (path : List Step) (row : Row Node Effect Symbol) :
    (record table context path row).parameter = context.parameter ∧
    (record table context path row).formalPosition = table.idxOf (.formalPosition context.owner context.parameter) ∧
    (record table context path row).occurrence = table.idxOf (.occurrence context.occurrence) ∧
    (record table context path row).owner = table.idxOf (.owner context.owner) ∧
    (record table context path row).scope = table.idxOf (.scope context.scope) ∧
    (record table context path row).path = path ∧
    (record table context path row).sourceRow = table.idxOf (.node row.position) ∧
    (record table context path row).concrete = row.concrete.map (fun effect => table.idxOf (.effect effect))
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_length (path : List Step) (row : Row Node Effect Symbol) :
    (record table context path row).concrete.length = row.concrete.length
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_position (path : List Step) (row : Row Node Effect Symbol) (index : Nat) :
    (record table context path row).concrete[index]? =
      row.concrete[index]?.map (fun effect => table.idxOf (.effect effect))
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_duplicates (path : List Step) (position : Node) (effect : Effect)
    (rest : List Effect) :
    (record table context path (⟨position, effect :: effect :: rest, []⟩ : Row Node Effect Symbol)).concrete =
      table.idxOf (.effect effect) :: table.idxOf (.effect effect) ::
        rest.map (fun item => table.idxOf (.effect item))
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.positive_filtered (path : List Step) (row : Row Node Effect Symbol) :
    emit table context ⟨true, path, some row⟩ = []
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.omitted_filtered (positive : Bool) (path : List Step) :
    emit table context (⟨positive, path, none⟩ : Port Node Effect Symbol) = []
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.symbolic_filtered (positive : Bool) (path : List Step) (position : Node)
    (concrete : List Effect) (name : Symbol) (rest : List Symbol) :
    emit table context ⟨positive, path, some ⟨position, concrete, name :: rest⟩⟩ = []
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.empty_filtered (positive : Bool) (path : List Step) (position : Node) (variables : List Symbol) :
    emit table context ⟨positive, path, some ⟨position, [], variables⟩⟩ = []
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_emitted (path : List Step) (row : Row Node Effect Symbol)
    (nonempty : row.concrete ≠ []) (closed : row.variables = []) :
    emit table context ⟨false, path, some row⟩ = [record table context path row]
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.mixed_negative_rejected (position : Node) (effect : Effect) (tail : List Effect) (name : Symbol) :
    rowAllowed false (some (⟨position, effect :: tail, [name]⟩ : Row Node Effect Symbol)) = false
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.tuple_annotated_child_rejected (value : Value Node Effect Symbol) (row : Row Node Effect Symbol)
    (rest : Elements Node Effect Symbol) (positive : Bool) :
    supported (.tuple (.cons value (some row) rest)) positive = false
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.empty_tuple_rejected (positive : Bool) :
    supported (Value.tuple (Elements.nil : Elements Node Effect Symbol)) positive = false
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.projection_success (table : Table (Owner := Owner) (Occurrence := Occurrence) (Formal := Formal)
    (Scope := Scope) (Node := Node) (Effect := Effect) (Symbol := Symbol))
    (context : Context Owner Occurrence Scope) (annotation : Annotation Node Effect Symbol)
    (output : List PermissionImage) :
    constructProjection table context annotation = some output ↔
      supported annotation.value false = true ∧
        output = (ports annotation.value false []).flatMap (emit table context)
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.root_row_separate (table : Table (Owner := Owner) (Occurrence := Occurrence) (Formal := Formal)
    (Scope := Scope) (Node := Node) (Effect := Effect) (Symbol := Symbol))
    (context : Context Owner Occurrence Scope) (value : Value Node Effect Symbol)
    (before after : Option (Row Node Effect Symbol)) :
    nestedProjection table context ⟨value, before⟩ = nestedProjection table context ⟨value, after⟩
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.fixture_order (table : Table (Owner := Owner) (Occurrence := Occurrence) (Formal := Formal)
    (Scope := Scope) (Node := Node) (Effect := Effect) (Symbol := Symbol))
    (context : Context Owner Occurrence Scope) (first second : Row Node Effect Symbol)
    (firstNonempty : first.concrete ≠ []) (firstClosed : first.variables = [])
    (secondNonempty : second.concrete ≠ []) (secondClosed : second.variables = []) :
    inventory table context (fixtureRows first second) false [] =
      [record table context aar first, record table context rrr second]
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.exact_aar_rrr_fixture (table : Table (Owner := Owner) (Occurrence := Occurrence) (Formal := Formal)
    (Scope := Scope) (Node := Node) (Effect := Effect) (Symbol := Symbol))
    (context : Context Owner Occurrence Scope) (first second : Node) (io : Effect) :
    inventory table context (fixtureRows (ioRow first io) (ioRow second io)) false [] =
      [record table context aar (ioRow first io), record table context rrr (ioRow second io)]
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_admitted (first second : Node) (io : Effect) :
    supported (fixtureRows (ioRow first io : Row Node Effect Symbol) (ioRow second io)) false = true
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_paths (table : Table (Owner := Owner) (Occurrence := Occurrence) (Formal := Formal)
    (Scope := Scope) (Node := Node) (Effect := Effect) (Symbol := Symbol))
    (context : Context Owner Occurrence Scope) (first second : Node) (io : Effect) :
    (inventory table context (fixtureRows (ioRow first io) (ioRow second io)) false []).map PermissionImage.path =
      [aar, rrr]
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_rows (table : Table (Owner := Owner) (Occurrence := Occurrence) (Formal := Formal)
    (Scope := Scope) (Node := Node) (Effect := Effect) (Symbol := Symbol))
    (context : Context Owner Occurrence Scope) (first second : Node) (io : Effect) :
    (inventory table context (fixtureRows (ioRow first io) (ioRow second io)) false []).map PermissionImage.sourceRow =
      [table.idxOf (.node first), table.idxOf (.node second)]
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_shared_effect (table : Table (Owner := Owner) (Occurrence := Occurrence) (Formal := Formal)
    (Scope := Scope) (Node := Node) (Effect := Effect) (Symbol := Symbol))
    (context : Context Owner Occurrence Scope) (first second : Node) (io : Effect) :
    (inventory table context (fixtureRows (ioRow first io) (ioRow second io)) false []).map PermissionImage.concrete =
      [[table.idxOf (.effect io)], [table.idxOf (.effect io)]]
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.appended_suffix (prefix suffix : List PermissionImage) :
    (prefix ++ suffix).drop prefix.length = suffix
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.comparison_success {Key : Type} (table : List Key) (expected actual : List PermissionImage)
    (entryBefore entryAfter : List EntryImage) (snapshot : Snapshot Key)
    (success : compareAndFinish table expected actual entryBefore entryAfter = .ok snapshot) :
    actual = expected ∧ entryAfter = entryBefore
```

```lean
YulangClosure.FormalPermissionOrderedSnapshotR140.error_excludes_snapshot {Key : Type} (error : Failure) (snapshot : Snapshot Key) :
    authenticated (.error error) ≠ some snapshot
```

## Parent application, missing premises and ownership

If checked, these table-local targets apply the R136 inventory method to the
source candidate's exact ordered paths/filter/context/member projection. They
would provide an unchanged-quantifier list theorem for arbitrary finite modeled
values, plus the exact two-row fixture. No checked theorem currently follows:
execution and the transitive axiom audit are unavailable by contract.

First remaining local premise: pinned Lean elaboration and full type/axiom audits
for these exact bytes, under a separately authorized verification decision.
Owner: primary Luna/verification owner. No retry was attempted or requested here.

First source/native premise: actual same invocation and State give the pre-call
prefix and post-success append suffix used by the source wrapper, and its supplied
expected/actual images are the concrete Rust projections at every accepted branch.
The Rust-to-Lean representation relation must preserve all eight key payloads,
complete Eq/clone behavior, table coverage and same-table reuse. Owner: R140 source
lane and primary-assigned fresh independent reviewer. SourceNodeKey accepted-source
uniqueness and FormalPosition-to-formal correspondence remain OPEN with their
existing source owners. The code does not add them as assumptions/typeclass laws.

Remaining parent premises: native inventory equality over the accepted domain,
actual consumer/arrival/capture/copy/Catch behavior, full source effect meaning,
A/B, H, the shared source witness and concrete SourceProblem instance. Owner:
primary and the relevant source/proof owners; these targets cannot construct the
InferenceSoundness witness. No production or solver admission authority follows.

Mutual TODO R140-VERIFY-1: primary retains a future verified environment/resource
decision, then elaborates the exact module and inspects EVERY inline audit.
Falsifier: any syntax/elaboration error, changed quantifier, additional unapproved
axiom, sorryAx, or mismatch against the frozen intended statements.
Mutual TODO R140-RUST-LEAN-ORDER-BRIDGE-1: source owner/reviewer matches all port
steps, polarity, row filters, context and repeated members to concrete same-call
Rust fields. Falsifier: any first mismatching constructor branch or row field.
Mutual TODO R140-SOURCE-ACCEPTED-KEY-UNIQUENESS-1 and
R140-FORMAL-INDEX-CORRESPONDENCE-1 remain as in the source handoff. None grants a
new lease or closes a premise. Independent review remains pending primary dispatch.

## Commands, resources and limits

No Lean/Lake/checker execution, version probe, build, tests, environment probe,
installation, dependencies, source edit, Git command/mutation, or scratch output
ran in R140. Only bounded read/search operations, hashlib source-hash checks and
writes to the two exact leased outputs occurred. Actual Lean version in R140 is
UNOBSERVED. The already read project pin is leanprover/lean4:v4.35.0, with -j1/-M1024
and no external packages; this is configuration evidence only.

R139 failure remains material: its only permitted module command and both version
queries exited -6 with `failed to create thread: Resource temporarily unavailable`
under one-CPU affinity and RLIMIT_AS=1073741824; no elaboration or axiom output was
produced. That record was not replaced with a success receipt or retried.

Assignment bound: 600 seconds; no sustained external compute processes were
launched. CPU/RSS for authoring/read operations were not measured. No shared
verification cache ownership, generated outputs, scratch files or descendants.
Represented cases and omissions are enumerated above. Actual Eq, usize/u32 width,
allocation/clone aborts, interning chronology, State ownership, constraints,
propagation and consumers remain outside this pure projection construction.

Frozen artifact revision 1: `notes/theory/lean/YulangClosure/FormalPermissionOrderedSnapshotR140.lean`, 23626 bytes, SHA-256 `da3baeabd61ff8fd30d078a4481f4a6c62ef5801cdb670f634e4d7c827add985`.
Frozen handoff revision 1: this exact path; its final byte size and SHA-256 are returned separately to avoid a self-referential hash.

STOPPED_WRITING: both exact leased paths frozen. No further writes, children, generated outputs, scratch or outstanding cache leases.

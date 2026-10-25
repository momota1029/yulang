# Native closure environments, current cells and represented body realization

Status: source correspondence candidate, pending combined formal/source review.
Authors: primary /root (source/verification) and constructive author
/root/native_closure_environment_astra_r1 (formal candidate).
Baseline657d688fc022261fa1013f7eb4f2b323d6cfd4a6, research/simple-sub-intrusion.
Contract LEAN-NATIVE-CLOSURE-ENVIRONMENT-20261025/r1 SHA
2630ec7db277777bf4e0fb8e99a665cdd65d842471264a736a079c122a1f073f.
All59 pinned inputs match. Requested childAstra/medium, observedUNKNOWN.

## Authority and exact claim

The existing operational specification requires the typing context to retain
captures/shared resources (tex206), distinguishes Value formal A from Computation
formal UA (220-221), and permits a finite environment graph read as closed
substitution (258-261). This note derives the native lexical-address supplier
and uses the companion formal construction to close represented Call bodies.
It adds no language semantics, executable callable constructor or compiler change.

The environment graph, cell store and value/closure graph are distinct objects.
A closure stores an environment index, not a copy of its bound values. Environment
nodes are immutable once appended; a binder resolves to a stable cell address.
Reading that cell observes its CURRENT content, which may be uninitialized or
have been written since closure capture. A recursive local can produce a cycle
cell -> closure -> captured environment -> same cell even though environment
parent edges are acyclic. Parent acyclicity proves neither guarded value-graph
realization nor a typed store. Those original obligations remain OPEN.

For every actually generated finite environment arena and valid saved environment,
lookup terminates and returns the nearest matching full binder identity's cell.
Later arena appends do not change that old address resolution. Dispatch-only
nodes leave lexical resolution unchanged. Parameter binding shadows precisely
its full identity. Native closure entry uses the saved environment, independent
of the caller's environment except for explicitly retained dispatch/value data.
For a finite resolved layout whose current cells already have represented typed
values, the formal realization constructs the exact substitution and applies the
existing body substitution theorem. This last result remains conditional on
source layout and actual value representation/typing; it does not create those
premises from an arbitrary native store.

## All environment constructors and handle validity

Environment at machine175 retains parent Option<usize>, optional (Binder,cell)
and dispatch::State. Machine start447 creates exactly node0 with parent=None,
binder=None and default dispatch. Existing environments are never overwritten,
removed or truncated. The only production pushes are:

| Owner | New node and returned handle |
| --- | --- |
| with_dispatch2596-2599 | id=old length; parent=Some(input), binder=None, supplied dispatch; return id. |
| extend2626-2633 | id=old length; parent=Some(input), binder=Some(exact key,cell), copy parent's dispatch; return id. |
| bind2635-2638 | id=old cell length; append Some(exact ReceivedValue); then extend(input,key,id). |

All non-root environment handles originate from these returned pre-append lengths.
All other uses copy existing handles from active Evaluate state, saved frames,
Closure/Delay payloads, or use literal0 for root evaluation/initialization.
No source integer, arithmetic-derived value or caller-provided raw index becomes
an environment handle. These fields are private. Test-only hand-written machine
states are outside the production constructor induction.

Inductively, input handles are below the old arena length, and every newly
created parent is strictly below its child's new index. Earlier nodes are
unchanged. Reusing any older valid environment as parent is permitted; the graph
is not a single contiguous chain and does not require parent=child-1. Root is
parentless; every source-produced non-root node has an older parent. Thus every
lookup's followed parent chain is finite. Vector reallocation does not invalidate
index handles. Successful returned allocations are modeled; an infallible native
allocation abort is not claimed to return a recoverable error.

This is a source construction induction over the complete handle-producer set,
not an assumed arbitrary well-formed arena. The model's own append theorems
supply that invariant for all histories of such constructors, retaining dispatch
and binder/cell payloads. A malformed self-parent/cyclic arena is not a producer
result and cannot instantiate the builder theorem.

## Actual lookup, identity and module cells

Machine.lookup2585-2594 first checks the selected frame via get. If its binder
exists and the supplied predicate matches, it returns that cell immediately.
Otherwise it follows parent; a missing frame or absent parent returns None.
For generated valid environments, strict parent decrease makes the unbounded
Rust loop coincide with the finite formal lookup, including exact nearest match.
The finite bound counts environment nodes, including binderless dispatch nodes;
it does not bound later user computation or resolving value-graph cycles.

Binder at program207-211 is a tagged union of Parameter(HirParameterId),
Local(HirLocalId), and Catch(LocalSourceCatchBinderId). Name785-811 uses:

| Source resolution | Exact address lookup |
| --- | --- |
| ModuleDef(id) | definition_indices.get(full id), independent of lexical env. |
| Parameter(id) | nearest Binder::Parameter(candidate) with candidate==id. |
| Local(id) | nearest Binder::Local(candidate) with candidate==id. |
| CatchBinder(id) or CaseBinder(id) | nearest Binder::Catch(candidate) with candidate==id. |
| Imported, Unresolved, Ambiguous | no address; MissingBinding. |

HirParameterId compares source-root owner and ordinal (module1377-1408);
HirLocalId likewise retains its owner and ordinal. Catch identity additionally
retains arm_source (local_source463ff). The tags remain distinct; equal spelling,
ordinal alone, source display or hash collision is not equality. The formal key
must denote these complete identities, or an injective encoding already supplied
elsewhere. Its decidable equality is not a new spelling-based resolution policy.

Program994 and1008 set each definition index to definitions.len() immediately
before pushing that definition. Machine452 allocates exactly definitions.len()
initial cells, all None. Each stored module index is therefore in bounds; later
cell appends preserve it. Global resolution is a direct cell reference in a
resolved layout, not a fake lexical binder inserted into environment0. Missing
module ids remain failures. This address fact does not establish source-to-layout
coverage for arbitrary expressions or native cell typing.

After address resolution, Name814 reads self.cells[cell]. Missing lexical
address yields MissingBinding; present lexical cell with None yields
UninitializedBinding. Module cell None starts guarded lazy global initialization,
with a GlobalRead frame and initializer environment derived from0; repeated active
initialization yields RecursiveDefinitionInitialization. No placeholder value is
returned for an absent/uninitialized binding.

On Some(received), dispatch_name may update the copied ReceivedValue.dispatch,
then consume uses NameConsumption and may return or execute a computation.
The current-cell realization denotes the stored carrier before these operations;
address lookup transparency is not dispatch or force semantic transparency.
Neither dispatch_name nor consume writes the stored cell in this path.

## Dispatch-only nodes and error boundaries

initializer_environment2601 returns the same parent when dictionaries are absent;
otherwise it calls dispatch.initializer and appends a binderless node with the
returned state. substitute_environment2606 is a no-op if dictionaries or the
substitution are absent; otherwise it composes dispatch.substitution with the
supplied substitution and appends a binderless node. dispatch_environment2612
appends a dispatch word and likewise creates a binderless node. These wrappers
therefore preserve every lexical address on success, including nested wrappers.
Their dispatch values are retained, not erased as semantically irrelevant.

The called dispatch owner is dispatch.rs: append67, then78, initializer143,
name161. These helpers mutate their own metadata arenas/default map, never the
lexical environment nodes or cell contents. A returned error before with_dispatch
means no lexical node was appended. It does NOT mean global rollback:
initializer inserts into defaults before rejecting an existing entry, and name
can append metadata before a later allocation failure. No proof here asserts
idempotence, commutativity, freshness or observational irrelevance of those
substitutions. Their ordered semantic interpretation is a separate obligation.

## Closure capture and actual entry branches

Instruction::Lambda864-887 copies parameter, pattern flags, role, schemas, body
label and CURRENT environment into ExecutableValue::Closure. Callee1181-1200
creates the delayed argument with the CALLER environment before examining the
callee. The Closure pattern1224-1232 then binds its environment variable to the
SAVED closure environment. At1286 substitute_environment receives that saved
index and the callee ReceivedValue.dispatch; the caller's lexical environment is
not substituted for it. The delay still refers to caller environment, which is
correct argument scope, rather than a change to the closure body scope.

new_invocation runs before substitution; a later dispatch failure can retain
owner/metadata changes while body entry fails. The address theorem neither
reorders these steps nor asserts whole-machine rollback or typed error-freedom.
ReceiverReturn stores activation and previous owner. ValueEntry carries the
resulting saved-derived environment exactly.

| Entry branch | Lexical effect |
| --- | --- |
| Computation1316-1331 | Bind the closure parameter to the same delay handle, Computation interface, selected receiving view, dispatch=None; evaluate body without forcing it here. This branch does not inspect unit/record flags. |
| Value ordinary1440-1490 | Force argument first. After optional callback validation/view construction, bind parameter to exact returned value/view/dispatch with Value interface, then evaluate body. |
| Value unit1471-1476 | Validate actual Unit; retain saved-derived environment without a parameter binder. Failure enters no body. |
| Value record1468 / bind_record_parameter2655 | Process fields in source order; bind each field identity only when its value/default has been obtained. No whole-record parameter binder is added here. |

Optional callback_schema validation may fail before any parameter binding; on
success it changes the copied receiving view while retaining the actual value
and dispatch. The body-closing lemma must use that actual carrier's representation,
not an invented unchanged-view premise. For Computation, a represented argument
is a delay with a typed computation body; it is not an eagerly evaluated result.

bind_record_parameter first validates the argument/view and actual record. A
present field projects its view, composes its dispatch with the argument dispatch,
sets Value interface and creates a fresh parameter cell. If absent with a default,
it saves RecordDefault and evaluates the default under the environment containing
only earlier fields. On return1491, the default value/view is projected, that
field is bound, then processing resumes at index+1. Missing without default,
invalid record/view or projection failure does not silently introduce a binding.
Even empty patterns require an actual record. A default may suspend/fail/diverge;
no theorem here claims finite completion of all defaults. Repeated application
of the append lookup theorem applies to each successful field introduction.

## Cell allocation/writes and all other binder producers

There is no cell removal or index reuse. The complete production cell mutation
set found by searching every self.cells occurrence is:

| Owner | Mutation and environment relation |
| --- | --- |
| Start452 | Allocate None for every global definition. |
| begin_local2523-2526 | Append fresh None; recursive local extends env before initializer, nonrecursive does not yet extend. |
| Frame::Local1543-1560 | Write actual received carrier with Value interface; recursive env already contains the cell, nonrecursive extends now; continue the block. |
| Frame::Root1739 | Write received carrier with Value interface into scheduled definition cell. |
| Frame::GlobalRead1760 | Write received carrier with Value interface into lazily initialized global cell; then dispatch/consume a copy. |
| bind2637 | Append Some(exact supplied carrier), then extend with its fresh cell. |

The structural store theorem intentionally permits current-cell changes; it
does not claim that the runtime rewrites every initialized cell arbitrarily or
that every write preserves a source type. Recursive closure capture can occur
while its own preallocated cell is None; later initialization changes what the
same captured address reads. Before that write the partial realization must
fail; after it the same address can return the new value. The finite Call value
syntax cannot generally represent that cyclic closure graph, which remains OPEN.

All bind callers use the same constructor law: CatchReturn value arm1116;
Computation formal1316; ordinary Value formal1476; RecordDefault1494;
Case binder1699 and structural-case list1717; request payload2194 and continuation
binder2216; record field2671. The only direct extend callers besides bind are
recursive preallocation2526 and nonrecursive local completion1553. Wildcards,
unit catch payload and patterns with no binder retain the input environment.
A forwarded handler's stored environment is copied by template replay; the
reviewed template result does not mutate that environment arena or cell store.

## Formal realization application and residual source owners

The native Vec is projected by the chronological `Arena.root`/`Arena.append`
log of its successful pushes; `nodeAt` selects the corresponding array node.
This records construction history without changing its parent edges. Supply
`Valid.root` initially and `Valid.append` at every append using the old valid
parent handle from the producer induction. `nodeAt_old`, `node_exists` and
`parent_decreases` then give actual node existence and rank; `lookup_node`
is the exact same-arena first-match/parent equation inspected in Rust.

`walkFuel` formalizes that parent loop itself. Its OUTER None denotes exhausted
fuel, distinct from Some None (completed native absence). `walk_complete` and
`bounded_lookup` show that every generated valid index i completes at fuel i+1
with Some(lookup result); fuel exhaustion never masquerades as absence. Thus
nearest lookup and finite completion are applied to the actual loop, rather than
inferred just from a different structurally recursive definition. `lookup_old`
and `lookup_history` preserve old address resolution under arbitrary later
append branches; `dispatch_transparent` discharges binderless wrapper equations.
`extendNode` uses the actual parent's dispatch. `parameter_shadows` and
`parameter_preserves` give exactly the same-key/different-key behavior; the
latter explicitly requires key inequality and is never applied to the new formal.

`closure_entry` gives the saved-index equation. `Store.push`, `push_current`,
`push_old` and `bind_observes_received` supply the fresh-cell allocation/read
facts. At the native projection the store size is cells.len(), an out-of-range
observation is None, and every source-produced lexical/global cell reference is
in range by the constructor/allocation argument above. A represented store is
obtained by reading each CURRENT native cell and projecting its actual carrier
when a separately supplied exact value readback exists; no projection is
invented for an unsupported closure/cyclic value. `observe_current` makes the
current-store dependence explicit. New parameter allocation preserves all old
in-range cells, while `parameter_preserves` preserves different full keys.
The source-layout owner still must show that captured free positions exclude
this bound formal identity; the native law does not assume all keys differ.

`Reference.lexical` denotes the complete Binder key, and `Reference.global`
denotes the already resolved module cell. `address`, `read` and `realize` perform
the actual finite reference/address/current-value reads. Any missing address or
missing represented cell aborts the Option traversal. `realize_captured` supplies
a position-by-position Captured derivation from success. `captured_index` proves
that every type-bearing index in `context layout` reads its actual captured
value; the explicit total-function filler is never substituted for a missing
free-variable read. `CellsTyped` requires the actual represented cell's original
ValueTyped derivation at the exact declared layout type, even for aliases and
duplicates. It does not assert arbitrary stores are typed or infer types from
lexical address equality.

`successful_read_typed` applies that per-cell evidence to the actual read;
`realized_substitution_typed` constructs the existing substitution premise.
`close_body` applies `TypedCall.substituteCallComp_typed` to the open represented
body, retaining its bind/request lifting. For actual ordinary parameter entry,
combine `bind_observes_received` with the source layout's index0/new-formal and
successor/captured-free mapping, then apply `close_parameter_body` with the
returned carrier's typed representation. For Computation use
`delayed_parameter` and `close_computation_body`, retaining the actual closed
argument computation as a delay of type UA. Value-unit bodies use the unchanged
layout; successful record-field/default steps apply the same introduction law
one at a time with their actual field identities and current typed values.
These applications do not assert source-to-layout coverage or typed readback for
all native values: those are the exact remaining original premises below.

Remaining owners, all primary intake:
- ENV-LAYOUT-1: actual source-resolved binder/global references and de Bruijn free
  positions for each represented body, with binder lifting and coverage.
- ENV-CELL-VALUE-1: native ReceivedValue/current cell -> represented TypedCall.Value
  and its original type; primitive literal readback is only one accepted supplier.
- ENV-GRAPH-1: guarded recursive/shared value graph realization and original typing.
- ENV-CALLABLE-1: closure as a value, full code/environment/adapter/native trace
  interpretation; current Function is outside Value and is not silently inserted.
- ENV-DISPATCH-1: source dictionary dispatch and consumption/force meaning,
  including receiving/view metadata and operation errors.

The full source-native / typed callable parent therefore remains OPEN. This
packet supplies the concrete address/current-cell/substitution mechanism and its
conditional typed body application, not arbitrary source typing or Bad exclusion.
NO_SAFE_CODE_SLICE; no confirmed runtime defect. No compiler, diagnostic,
expectation, config, native test or new production semantics change is made.

# Physical Value relation calls and their shared child execution

Date: 2026-10-26. Producer: primary `/root`.
Branch/baseline: `yulang3`, `a9c746f31cc0eabeba9ebf5b673b6f121ed0ca82`.
Status: constructed and checked; fresh independent review required.

## Original obligation and exact seam

The unchanged parent is complete native inference correspondence and the same
original scoped source witness in `SourceProblem.InferenceSoundness`. The
accepted `NativeValuePorts` constructs full child keys in a decoded Arena;
`NativeValueDrain` connects that computation to actual enqueue occurrences in
its shared control projection. The new `NativeRelationInterner` constructs the
materialized native maps and physical RawKey/ScopedFlowId decoding. This packet
joins those particular constructions at their exact relation-call cut.

The implementation owners are `candidate_context.rs` 3511–3669 for the four
port admissions, 2630–2656 for Context interning, 2795–2815 for scope-transformer
interning, and 3062–3094 for the physical relation call. The two-stage native
steppers are `lib.rs` 14955–15054. `candidate_scope.rs` 269–280 computes retained
transformer bytes. Exact source hashes are in the producer's source manifest.

This module changes no Rust implementation, approved inference behavior,
supported syntax, toolchain, expected output or semantic authority. It imports
the accepted complete Value/control construction and the frozen physical
interner; it does not change either dependency.

## One physical store and the same complete key

`Store` contains the physical `Native` interner plus the preparatory Context and
transformer vectors. Its decoded Arena is computed from that store. There is
no independently chosen relation vector or assumed reflection field.

`prepare` performs the existing full child preparation: canonicalize the raw
pair, read the optional closed-weight view, build the child-local Context in
the original order around the actual post-check Context, and consume or retain
the complete deferred demand according to the exact Function/Tuple/Record/
Variant port. It constructs the child key from that pair, actual new Context
ID, original sources and resulting complete Flow. The checked preparatory
constructors preserve the relation vector exactly.

`physical_relation_constructs_admission` takes a constructed physical history,
the successful preparatory computation and the actual `allocate = (after, ok id)`
equation. From those it derives the original `NativeValuePorts.admit` result,
the resulting physical history, physical stored-key decoding at exactly `id`,
and every field of the existing `AdmissionResult`. No semantic child membership,
chosen matching output, selected ID correspondence or finished body appears as
an input. `registered_is_physical_readback` also derives physical RawKey/FlowId
decoding for every retained receipt from the constructor history.

## The preparatory resource cut

A fresh native scope transformer charges `ScopeInventory` before the relation
call; assuming the counter remains unchanged would omit real source behavior.
`Funding.preparationWork` therefore retains the actual successful preparatory
work amount separately from the relation call's own Flow charge. `inventory`
checks native integer/work bounds, updates the same physical counter, and
`inventory_exact` constructs the corresponding `NativeRun.inventory` event.
The allocation then uses the actual prepared Context vector length as
`contextCount`, rather than trusting a caller's larger counter.

The work amount is an independently observed resource input, just like the
interner's reservation flags and platform-width bound. It is not inferred from
semantic safety or guessed from a logical transformer's element count. Its
exact derivation from native retained capacities remains a preparation owner.
Native `ScopeInventory::from_plan` also begins with retained plan work and then
charges other inventories; the initial `NativeHistory` must represent that
real initialization. This packet never identifies every real initial state
with an empty zero-work store.

Preparation failure returns `None` because the complete physical Context/scope
allocation failure trace is outside this successful-table projection. Once the
physical relation call is reached, its failed output is retained explicitly in
`Some (store, Except.error failure)`. A new Flow and all charged work can remain
after a relation-map reservation fails. Such a result cannot produce a successful
port receipt or enter the successful child loop. Invalid Context is the native
assertion boundary reified by the interner model, not ordinary successful
availability. No allocation or work failure is treated as semantic acceptance.

## Shared cursor, enqueue and original outer branch

The new `State` stores one physical relation source and the exact remaining
cursor/control data. `State.decoded` constructs the existing `NativeValueDrain`
state from those fields. Admission changes the physical store and pending
receipt. Enqueue consumes that same receipt, records the full raw task,
constructs its immutable drain occurrence, preserves the arbitrary old queue,
pushes to the front and advances the source cursor. The decoded admission and
enqueue equal the existing checked transitions by construction.

`drive_refines_emit` proves that a successful computed physical-relation loop
both preserves `NativeHistory` and is exactly the existing `emit` computation
on the decoded state. This is a one-way success refinement: physical resource
failure is not assumed impossible merely because a pure decoded interner can
allocate. Each concrete failure is retained in the lower admission result.

`physical_children_pipeline` applies actual drain preflight, the constructed
relation/child loop and the prior shared control history. It derives the middle
control history directly. In every ensuing quiescent continuation, every original
child has a corresponding full admission receipt, physical complete-key readback
at the same raw ID, and a diagnosed `returnReady` occurrence in that same history.

`executeChildrenAfterContext` obtains the actual ordered child list from the
existing Context/Value dispatch, then runs preflight and this physical relation
loop. `context_physical_pipeline` consequently does not take a favorable child
list or independently matching middle state. Its successful structural branch
retains the complete original request and candidate-mode guards. Duplicate,
canonical/retained rewrite, diagnostic, shortcut and fallback branches retain
their distinct existing owners; this adapter does not reduce the supported
language to its structural-child branch.

Work serials, the raw-task naming table, issued/returned occurrence lists and
the interner's origin/birth records are proof annotations of the projections.
They are not asserted to be additional fields allocated by Rust. Physical map
decisions do not read those annotations.

## Checked concrete distinctions

The module includes distinct, kernel-checked boundary cases:

- Relation-map failure leaves one new Flow, no new relation and the work charge,
  while returning an error rather than a receipt.
- A subsequent call can reuse that retained Flow even with new Flow allocation
  disabled, and obtains the same complete relation key at raw ID zero.
- A nonzero preparatory charge of seven followed by a new Flow charge leaves
  work eight after relation reservation failure.
- A caller's supplied Context count of 99 cannot admit an unallocated Context:
  the actual prepared frontier is used and the assertion boundary is retained.
- A complete four-port Function example has four distinct issued occurrences
  and physical relation IDs, one common control history, and both scope
  transformer charges retained. The example's resource observations are explicit
  model inputs, not a measurement or claim about a particular allocator's ABI.

## Verification and evidence preservation

The isolated project pins 11 dependency modules and three configuration files.
The physical interner input is
`1fd7ece6c6a7c6df7159efaebaec585b78a9e8513e9b10e6a3fb4d472b577d3a`.
The exact checker is Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, with native Lake
`5.0.0-src+eb6cafb`. Ordinary checks use one CPU/thread, `-j1 -M1024`, an outer
119-second bound and a 1280-MiB aggregate process ceiling. No global setting or
dependency was changed.

Final check07 builds the exact module and audits all **29 authored roots**;
check08 prints all **180 originating declarations / 63 theorem constants**,
including private/generated declarations, with complete type and axiom pairs.
Both exit zero with no warning or error. The complete census SHA-256 is
`46355122ddd0ff711136197490bfabcba425305b4b452c47f1b40a034cd22d53`.
Theorem axiom sets: 31 none, 19 `propext`, 5 `propext` plus `Quot.sound`, and
8 additionally `Classical.choice`. No project axiom, accepted proof hole or
unchecked native-evaluation axiom appears.

Eight of the packet's twenty focused calls were used. Failed checks01/02 preserve
the original syntax, dependent-elimination and projection-normalization errors.
Check03 verified the initial bridge before the resource and outer-branch
extensions. Check04 preserved an explicit namespace lookup failure; check05
preserved implicit Store argument inference failures; check06 preserved the
missing decidable-equality instance in one concrete assertion probe, repaired
with kernel definitional equality. Every source snapshot, command, full output
and measured receipt remains in `value-relation-r4/**`. Earlier success is not
substituted for the final source's checks07/08.

## Exact remaining parent owners

This is a concrete removal of the decoded-Arena/physical-relation seam. It does
not extract a whole accepted Rust execution. The initial native/control histories,
canonical maps, complete raw table/term lookups, preparatory Context/transformer
allocation traces and actual resource observations need their original source
readback. The post-relation `dependency` calls, lifecycle/source-support
invalidations, incoming-route sampling and native enqueue reservations must
also be represented before interpreting this successful projected loop as a
complete native execution. Its prefix must be joined to genuine rollback and
table lifetimes at their original chronological cuts.

A diagnosed return is not a conflict-free diagnostic vector or semantic
subtyping result. No quiescent continuation or whole-inference termination is
assumed to exist. Full Value/Effect meanings, original source Kernel clauses,
general recursive introduction and one authentic same-scoped source witness
remain separate obligations. `SourceProblem.InferenceSoundness` and complete
native correspondence remain OPEN.

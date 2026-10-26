# Native merge expansion: constructed carriers, Effect steps and Replay origins

Date: 2026-10-26. Status: kernel-checked local construction; native execution
authentication and recursive currentness OPEN; independent review pending.
Author: `/root/native_merge_construction`, bounded generic fallback for
`.codex/agents/lean-prover.toml`. No compiler changes or production authority.
Baseline: `b26e7de1aada0e15ac5147feb8654ec34ac90275`, branch `yulang3`.

## 1. Original obligation and result

The unchanged parent is `YulangClosure.SourceProblem.InferenceSoundness` in
`notes/theory/lean/YulangClosure/Contracts.lean`:

```text
∀ source scope constraints solution,
  supported source → generates source scope constraints → solves constraints solution →
  ∃ witness, sourceJudgment source scope witness ∧ sameScoped source scope witness solution.
```

The source domain, lexical and event scopes, one shared witness, generalization,
complete Function/Call behavior, effects, optional records and method selection
are unchanged. `SourceProblem.NativeCorrespondence` is the separate obligation
connecting actual native success to generated constraints and their solution.
The current occurrence qualification remains the Authoritative birth-level
induced Value graph rule. No arbitrary row equality is declared a qualifying
original source occurrence by this construction.

The immediate frontier is `MERGE-EXPANSION-COVER-1`, section 6 of
[`2026-10-26-native-replay-lifecycle.md`](2026-10-26-native-replay-lifecycle.md).
This packet does **not** finish that frontier. It constructs three components
that were previously source calculations or unconstructed history steps:

1. The actual finite incidence operations retain each installed identity-context
   Allowance fiber at its new representative, with an original-parent dependency
   path. A retained residual bound has its exact post-check carrier, including
   storage at a third owner. Its level-selected storage owner is computed.
2. The entire local Effect operand expansion commutes with representative
   absorption. This includes every indexed Support member, both forms of tail
   continuation, local returns, conflicts and availability failure.
3. An append/Replay transcript, starting empty and executing the actual two
   quadrants and dependency filter, constructs an indexed historical operation
   and child position for every fired product. Both old/old exclusion and an
   exact dependency hit have such an origin.

None of these results identifies a historical origin with a recursively current
or returned expansion. That distinction is the first remaining mathematical
step after authenticating the projection. The module never reads the native
pair-admission `completed` map as a certificate.

The new file is
[`YulangClosure/NativeMergeExpansion.lean`](lean/YulangClosure/NativeMergeExpansion.lean).
Its only project import is `NativeReplayCoverage`; it reuses that module's
`product`, `replayDelta` and quadrant identity. It does not use the abstract
full-product `.merge` action or its `Covered` invariant. `NativeRowModel` and
`NativeRowSaturation` were inspected as later consumers; their syntactic
saturation and accepted-model hypotheses are not supplied by this packet.

## 2. Generation transport of the factored row Effect

### Exact data and immutable payload

`Endpoint` represents all seven native `EffectEndpointKey` constructors:
EffectRow, Allowance, Support, Contribution, AnnotationMember, BottomPositive
and EmptyNegative. Rigid IDs and AnnotationMember positions are preserved.
`Key` keeps lower/upper endpoints, the stored Context ID, source-set ID and
Effect transformer ID. An authenticated Effect relation has no deferred
Function demand: `relation_with_scoped` rejects that combination. The retained
transformer ID refers to the whole immutable transformer, including its
stamp/protection behavior; it is not an identity replacement.

`publish`/`publications` project successful discharge publication after the
filter callbacks. Identity-context and empty-filter executions cannot publish
such an event. Induction proves `identity_postCheck`: every identity-context
key still has post-check context zero after any such publication sequence.
The theorem does not authenticate parsing or completion of the callbacks.
Actual native publication occurs only once per relation; repeated publications
in the more general erased data are immaterial to the identity theorem.

`allowanceFiber owner view sources transformer` computes the exact installed
negative bound `owner <= Allowance(view)` with identity context and the original
source and transformer IDs. `installExpansion` attaches every supplied filter
view and an optional **already retained residual bound**, eliding duplicate
attachments. It models the row-lower branch after its native constructors;
it does not infer an installed bound from the `discharged` marker alone.

### Copy selection and the frozen whole-prefix scan

`copyInputs` is the list of exact physical BoundKeys addressed by the native
two-side copy loop after its pre-merge representative reads. `copiedMoves`
selects attached fibers by those complete keys. This selection is necessary:
historical raw incidences with the same numeric owner can have obsolete endpoint
keys, so selecting every incidence merely by owner would invent ParentCopy
events. Every selected move retains its original fiber, target bound and
`ParentCopy(parentIndex)` reason.

`copyFibers` preserves all old incidence storage. `canonicalMoves` then scans
one frozen input prefix, computes each bound's representative image, and records
an `EqualityCanonicalization` move when the key changes. `canonicalize` attaches
those images with deduplication. Newly appended images are not recursively
scanned in that pass. `renameBound_absorb` and `bound_pair_rename` supply the
normalization algebra needed when the native constructor canonicalizes the
target pair again.

This is an incidence-membership and dependency-path projection. It is not a
claim of literal equality with every runtime vector or its order. The native
physical insertion can retain additional admissions, metadata or fibers;
those must remain in an authenticated full readback. The per-bound linked
Replay order is authenticated separately. Interning repeated identical moves
and attachments preserves the membership claims used here.

For an installed filter `f`, `allowance_carrier_exact` computes

```text
carrier q (postCheck (publications events [])) f
  = allowanceFiber (q owner) view sources transformer.
```

`merged_expansion_filters` places this exact key in the computed merge result.
It has no `Covered`, currentness, semantic Allowance preservation or returned
child premise. `merged_filter_parent_path` constructs the dependency path from
the original full-context parent to the installed filter and then, when needed,
through its equality transport. It does not manufacture a replacement direct
Replay or FunctionPort edge.

### The residual and its owner

`residualBound` is the actual row-lower placement rule. For distinct row
endpoints `x,y`, if `level(y) <= level(x)`, it stores the negative upper at `x`;
otherwise it stores the positive lower at `y`. A rigid upper is stored at `x`.
`residual_bound_constructed` proves that either placement still denotes exactly
the original directed comparison. `merged_computed_residual` constructs the
chosen fiber and its post-merge carrier. Its source application is to the
unconsumed Context branch; consumed Allowance endpoints and reflexive pairs
do not falsely acquire an extra residual bound.

`merged_expansion_residual` and `merged_residual_parent_path` also work for an
already retained bound at any third owner. `carrier_payload` gives its exact
context formula:

```text
if renameBound q oldBound = oldBound
then oldStoredContext
else postCheck oldRelation.
```

Source sets and transformer IDs are unchanged. Equality with the old stored
context is deliberately absent. Replay continues to read attached fibers'
**stored** contexts; this projection does not replace them with post-check
contexts or claim equality between an old and new whole Replay relation key.

## 3. Local Effect expansion, including tails and diagnostics

`Effect.checkOperand` transcribes `candidate_check_effect_operand`. For a
Support view it constructs all AnnotationMember positions in native order,
then the optional canonical row tail. For a Contribution or AnnotationMember
at an Allowance, it reads the exact member token, selects the closed-weight
allowed set when present, and either returns locally, emits the canonical tail
comparison, or retains a conflict. EmptyNegative produces the corresponding
conflict. The other shapes are unavailable. Missing table entries are marked
unavailable in the projection; its native correspondence is for valid retained
table IDs, not a claim about an out-of-range Rust access.

The main exact type, with the namespace shortened, is:

```lean
Effect.operand_expansion_transport
  (old current : Nat → Nat)
  (absorbs : ∀ row, current (old row) = current row)
  (tables : Effect.Tables) (lower upper : Endpoint) :
  Effect.checkOperand current tables
      (renameEndpoint current lower) (renameEndpoint current upper) =
    Effect.renameOutcome current
      (Effect.checkOperand old tables lower upper)
```

This is a proved constructor equation, not an assumed child-transport law.
The absorption premise is the representative-forest equation. It does not
require an injective quotient, acyclic row constraints, empty tails, identity
scope transformers or a semantic solution. `support_member_exact` and
`support_tail_exact` expose the original indexed members and optional tail.

The theorem transports **one-step emitted obligations**. A Support local return
after enqueueing children, or a mismatch function returning Rust `Ok`, remains
distinct from completing those children or accepting the enclosing drain.
Row handling belongs to `candidate_apply_effect`; the row-lower placement
component above addresses that separate owner. Value constructor ports and
context semantics are not silently replaced by the Effect fragment.

## 4. Both Replay skips now have constructed historical origins

`Replay.State` records new/old attached fibers, retained whole dependencies and
an erased append-only list of successful operation-creation batches. For one
exact ordered pair of physical BoundKeys, ordinary replay computes

```text
newLower × (newUpper ++ oldUpper) ++ oldLower × newUpper
```

and filters dependencies already present. Incoming replay enumerates the full
current product and bypasses that filter. Successful generation records the
operation batch and advances the saved heads. Attachment checks membership
before prepending a new fiber. Thus actual distinct per-bound fiber lists give
distinct enumerated pairs; the batch filter has the same successful output as
the native loop's incremental dependency insertion.

`OriginInvariant` is an internal induction invariant: the old/old product is in
the dependency set, and every dependency has a batch origin. `initial_origins`,
`step_origins` and `run_origins` derive it from the empty state. The public roots
take a list of construction events; they do not assume this invariant or a
coverage ledger.

`old_old_indexed_origin`, `dependency_skip_has_origin` and
`fired_product_indexed_origin` return actual operation and child **list indices**
with successful `getElem?` equations. In particular, ordinary dependency
suppression returns an earlier batch witness even though that pair is absent
from the newly generated children. Incoming replay has its own batch even when
the same dependency already existed.

The indices belong to the erased successful creation history. They are not
current runtime `ReplayOperationId` values, cannot be used as acknowledgement
receipts, and do not turn a reclaimed operation into a present runtime object.
An authentication map must retain the operation's creation epoch when rollback
can reuse numeric IDs. The current module has no rollback or retirement step.

The per-input abstraction also requires the exact native child-key constructor
to remain fixed for that input pair and attached relation identities. For
canonical identical BoundKeys, their task endpoints are the same; stored
contexts, source sets and scoped flows of those relation IDs are immutable.
Replay therefore uses the same ordered constructor arguments. This does not
make the descendant row endpoints inside rigid Function/Support structures
current. The separate expansion-transport construction is still necessary.

## 5. Actual source owners and remaining authentication

All source paths in this table are under `crates/yu-solver/src` at the frozen
baseline; the relevant bodies were read, not inferred from the old note.

| Construction | Actual owner | Established projection / remaining source obligation |
| --- | --- | --- |
| Effect keys and immutable scoped payload | `lib.rs:794–807`; `candidate_context.rs:3043–3095` | Seven endpoints and exact Effect fields are represented. Authenticate interning identity and the concrete finite table encoding. |
| Filter publication and residual | `candidate_context.rs:3670–3885,3898–3936,3297–3302` | Identity post-check stability and installed-check construction are proved. Authenticate exact parser output, successful callbacks, processing parent and Derived/attach events. |
| Physical copy selection | `candidate_intrusion.rs:599–690`; `candidate_extrusion.rs:619–635,877–938`; `candidate_effect.rs:685–725` | Copy inputs are whole addressed canonical BoundKeys, not owner-only matches. Read back those inputs and the actual prefix. Metadata with `MissingOriginAssociation` is not substituted for an executable fiber. |
| Whole-prefix canonicalization | `candidate_context.rs:4230–4254,4318–4331` | Every changed fiber has the computed post-check carrier and Transport event; original-parent paths are constructed. Authenticate forest absorption, fixed post-check table during the pass and full incidence readback. |
| Residual bound placement | `candidate_extrusion.rs:1151–1171` | Both level branches and rigid-upper storage normalize to the original directed pair. Authenticate the actual unconsumed Context/Dispatch route. |
| Effect member/tail expansion | `candidate_effect.rs:1237–1305` | Full local outcome commutation is proved. Descendant execution and diagnostic acceptance remain open. |
| Replay product and suppression | `candidate_context.rs:3992–4076` | Empty-origin event induction supplies historical indexed owners for both skips. Authenticate linked heads, exact whole dependency keys, successful operation creation and transaction-erased history. |
| Merge scheduling and returns | `lib.rs:14308–14311,14881–14947` | Merge occurs at its actual empty-worklist Transport boundary. Runtime pending/active/ack/return readback is not constructed here. |

Authentication is not a replacement name for semantic completion. It relates
the actual native constructor data to the explicit computations just proved.
The full application still needs one committed execution history, including
rollback of mutations to earlier owners, not a collection of independently
chosen favorable snapshots. `operations` intentionally retains historical
creation after runtime reclamation; it never asserts that a returned event
exists merely because an operation is absent.

## 6. First remaining parent premise

After those readback obligations, the exact remaining step within
`MERGE-EXPANSION-COVER-1` is:

> For every historical Replay child selected by either skip, connect its
> original factored expansion, the constructed filter/residual carriers and
> all newly combined products to one finite graph of **current** retained,
> queued, active, locally expanded or returned dispositions. Recursively justify
> each child under the current representatives and exact contexts, and relate
> the terminal graph to the actual accepted drain and ordered acknowledgements.

The local Effect constructor equation now supplies the Support/member/tail
step of that induction. The filter theorem supplies concrete check carriers
and original-parent paths; the Replay theorem supplies historical creation
indices. Neither supplies a missing current disposition. Row cycles must keep
active back-references; generation transport must not mark them terminal.
Pending acknowledgements and a later merge after an earlier merge queued work
remain genuine cases. Full Value ports, nonidentity context interpretation,
original record adaptation, source scopes and complete Call remain separate
obligations of the unchanged parent.

This is new generation-change construction, not another claim of R181's
unchanged-representation factorization. R181's section 4 is reused to identify
what was actually installed. No compiler defect, impossibility theorem,
source-qualified counterexample or production promotion is claimed.

## 7. Verification and frozen evidence

Pinned native toolchain:
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.
Lake reports `5.0.0-src+eb6cafb (Lean version 4.35.0)`; Lean reports `4.35.0`,
commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. The primary provisioned and
verified the official release digest
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.

All checks used the isolated project
`/workspace/scratch/f98087c7ac1a/native-merge-r2/project`, its own `.lake`,
`LEAN_NUM_THREADS=1`, `lean -j1 -M1024`, `lake --no-cache`, and a 120-second
whole-check limit. No shared project cache or root imports were changed.
Eight bounded checker calls were used. Final call 08 rebuilt the module and
ran the full originating-module census in 4.14 seconds, all commands exit 0,
with no warnings. It audited **all 270 originating theorem constants among
638 declarations**, including private and generated proofs:

| Full theorem axiom set | Count |
| --- | ---: |
| None | 168 |
| `propext` | 73 |
| `propext`, `Quot.sound` | 29 |

No `Classical.choice`, project axiom, proof hole or native-evaluation assumption
occurs in that complete audit. The major merge, Effect and Replay roots have
`[propext, Quot.sound]`; this is not an axiom-free claim. Full types and exact
per-theorem lists are retained in the log and machine-readable inventory.
The originating-module audit rejects every nonstandard transitive axiom and
every project axiom declaration. A source search of the changed module and
its project dependency found no proof holes or checker bypasses.

Material failures remain in `check01.log`, `check03.log`, `check04.log` and
`check06.log`: reserved `from` binders and missing existential annotations;
over-unfolding an endpoint before a rewrite; an underdetermined existential
child list; and an underdetermined intermediate path key. They were repaired
without changing the theorem goals. Calls 02, 05 and 07 checked the staged roots;
call 08 audits the final corrected physical-input selection and every theorem.
No Cargo call, native executable probe, network request or Git operation ran.

| Frozen object | SHA-256 |
| --- | --- |
| `NativeMergeExpansion.lean` | `f14bd35e8f7a6b9f326dadf003797c63f4a48fd0d0c0c9d68891c579560baf6e` |
| `native-merge-r2/check08-full-audit.log` | `fe3f0a8a1a5203ce396a86be30a04cd6dc2b9735623e11a9e6edafadaf464fdc` |
| `native-merge-r2/theorem-inventory.json` | `148d411e9222031996af0b3c88ed6af9a04f1a5a55c7e828db4e96a0f22c809b` |
| `native-merge-r2/project/AuditNativeMergeExpansion.lean` | `8e5845e10964063a38d493e8a8d2633e6671df9b518951317db90c249219275c` |
| `native-merge-r2/manifest.json` | `b14bfccc97a65fb39854ff208da78e3d3c23b8697dc91cd979eed472f01add9e` |

The manifest records the baseline, 24 governing/source/configuration inputs,
all failed and successful logs, and the audit program. The companion handoff
records this paper's final hash and the exact writer-stop receipt. Independent
review and primary integration remain pending; this author does not certify
its own result. The original inference and complete native lifecycle parents
remain OPEN.

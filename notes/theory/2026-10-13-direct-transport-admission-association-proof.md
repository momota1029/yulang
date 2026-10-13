# Direct transport and frozen source-admission association

Status: independently reviewed local source correspondence; private accessor
and local coverage law implemented; no parent-gate closure.
Baseline: `8d90a83e5aa3c7035c799aa2fbb2b833256525a3`, branch
`research/simple-sub-intrusion`; the four compiler inputs below also have no
diff against `09e1219b`.
Owner: primary-assigned leaf `prove_direct_transport_association`.
Exclusive output: this file only. No delegation, compiler changes or Git mutation.

## 1. Frozen statement, hypotheses and exclusions

This packet derives an inert construction fact, not semantic authorization.
For every successful invocation of
`candidate_context_transport_witness_with_evidence(parent, to, use_origin, w)`
in one live owning candidate `State`, let its actual returned value be `(c,t)`.
Let `T` be that state's transform record at `t`, and `S` its record at
`T.antecedent`. These variables name these exact construction records; they
are not independently selected marginal witnesses. Let `P(S)` be the ordered
list reached from **S's saved admission head**, following only each admission's
`previous_on_group`, in newest-to-oldest order.

The scope is constructor-generated, well-formed current arenas, and a query
borrow in that same State while this particular record remains live. A rollback
may intervene only if it retains the actual transform and its prerequisite
records. A copied numeric ID retired by rollback, a stale captured snapshot,
an ID from another State, or a manually fabricated/mutated snapshot is outside
this lifetime hypothesis. This is the existing private arena lifetime, not a
new source restriction. During an immutable borrowed query the arena cannot
be mutated or rolled back.

Required conclusion:

1. `T.from == w.from`, `T.to == to == w.to`,
   `T.source_relation == parent`, `T.child_relation == c`,
   `S.source_bound == T.from`, and `S.relation == Some(T.source_relation)`.
2. For every admission ID `a` in `P(S)`, its actual record `A` has
   `A.bound == T.from` and `A.relation == T.source_relation`. It yields exactly
   the construction association
   `(t, a, A.bound, A.relation, A.origin, T.to, T.child_relation)`.
   `A.origin` is the non-optional `TypedPairKey` stored in that admission.
3. `P(S)` is finite, contains every admission of that exact source group
   present at the freeze, preserves distinct admission IDs and their
   multiplicity, and is unchanged by later appends that retain its records.
4. The separately frozen emission prefix keeps its existing emission-to-
   admission links. This query asserts no destination admission or physical
   destination emission and requires neither to manufacture a source link.

Empty `P(S)` proves no origin association. Its existence does not authenticate
ordinary seeds, establish original source reachability, activate constraints,
prove complete replay, authenticate parent-copy/extrusion eligibility, or
discharge complete Call, effects, soundness, principality, source admission,
L4, bulk joint-opposite-pair disposition or F5. Original source scopes,
attachment/provider identities, residual constructor lineages and all these
parent obligations remain unchanged and OPEN.

The gap conclusion is a **proposed local change**, distinct from current code:
copy all `S.coverage` bits unchanged; omit only this transform constructor's
new `MissingOriginAssociation` bit when the exact matching source snapshot
has a valid, nonempty source-admission prefix. Otherwise retain/add that bit.
In particular, an inherited `MissingOriginAssociation` bit is never cleared.

No hypothesis says that operational `origins[bound]` identifies fibers. The
proof instead derives the group invariant from `BoundEvidence::admit`, then
uses the direct creator's exact frozen snapshot.

## 2. Authority, input freeze and actual owners

Governing authority is top-level inference principles §§2–4 (cost, proof before
implementation, necessary abnormal-path safety), contextual attachment/
admission §§3–4 (exact identity, bound origins and contextual transport), and
the selected residual-lineage policy (distinct recipes, exact fan-out and
qualifying recorded parent/copy pairs). These do not select new source meaning.
`rules/compiler-engineering.md`, “Natural compiler behavior and proof-obligation
economy,” favors using the evidence already known at construction; this
bounded seam uses existing references instead of reconstructing a fiber from
the separate origin table. Required A/B parent claims are not reclassified.

The leaf follows M1 bounded inert correspondence, with fresh independent
`compiler_referee` assigned by the primary before implementation. Reading
`rules/agent-orchestration.md` (model routing and proof delegation),
`rules/research-lab.md`, `rules/design-authority.md`,
`rules/compiler-engineering.md`, `rules/git-concurrency.md`,
`rules/orchestration-budget.md` and the `yulang-proofs` skill grants no producer
self-certification or shared-record authority.

Exact compiler owners, using baseline line numbers:

| Owner | Responsibility |
| --- | --- |
| `candidate_context.rs:344–376` | Admission, immutable snapshot fences, transform fields |
| `candidate_context.rs:394–439` | Arena/key maps, checkpoint and rollback |
| `candidate_context.rs:508–528` | Exact group snapshot and full-record interning |
| `candidate_context.rs:530–573` | Every successful admission appended to its exact group |
| `candidate_context.rs:580–587` | Physical emission names its existing admission |
| `candidate_context.rs:589–610` | Transform interning, reverse link and latest-child index |
| `candidate_context.rs:1535–1549` | State wrappers around snapshot/import/admit/emit |
| `candidate_context.rs:1619–1657` | State rollback invokes evidence rollback before relation removal |
| `candidate_context.rs:2409–2422` | Attach records a bound fiber; it creates no admission |
| `candidate_context.rs:3182–3196` | Direct snapshot, child/dependency/transform/attach, actual returned transform ID |
| `candidate_effect.rs:420–470` | Operational origins and inert admissions have different multiplicity |
| `candidate_effect.rs:563–601` | Separate fiber transport and relation=None operational origin fallback |
| `candidate_scheme.rs:545–559` | Capture stores the exact snapshot value as evidence |
| `candidate_scheme.rs:1195–1197,1255–1268` | Captured snapshot import and separate FreshUse admission cause |
| `candidate_context.rs:757–1018` | CircuitEvidence/readiness has separate consumers and gaps |

SHA-256 input manifest:

```text
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df  crates/yu-solver/src/candidate_effect.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  notes/design/2026-10-10-contextual-attachment-admission-design.md
d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98  notes/design/2026-10-10-contextual-residual-lineage-selection.md
```

The prior `2026-10-13-native-bulk-bound-coverage.md` distinguishes the unary
transport and unassociated operational origin loops; its missing joint ordered
lower/upper disposition is excluded here. This result supplies only the local
source-admission link already carried by the unary transform.

## 3. Constructive derivation from the owning operations

### Exact grouping, descending links and multiplicity

Initially there are no groups/admissions. `admit(bound,origin,relation,cause,d)`
uses precisely `(bound,relation)` as the `group_keys` key. A new group starts
with empty heads. An existing group is retrieved by exact typed key equality;
there is no representative/canonical-shape comparison at this owner.

On a successful admission all fallible reserves precede the group/admission
pushes. Let `n` be the previous admission arena length. The new ID is `n`, the
record contains the given `bound`, `origin`, `relation`, and group ID, and its
previous link is exactly that group's previous head. Then the group head
becomes `n`. By induction every prior link points to a strictly smaller ID in
that same exact group, and every record in the chain has its group's original
key. Each successful call extends the chain by one distinct admission.

The `duplicate` argument affects only a counter. It never suppresses the new
admission. Therefore equal origins in one group remain distinct admissions;
the same origin admitted to different relations remains in different group
chains. Neither case licenses deduplicating this accessor by origin.

### Frozen prefix and interning

`snapshot(b,Some(r))` looks up exactly `(b,r)`, then copies the group's current
admission and emission heads and ORs its current coverage into a new value.
If absent, both heads are None and the explicit missing-group/antecedent/
physical-emission gaps are recorded. `snapshot(b,None)` additionally records
the missing-relation gap and does not choose any fiber.

`intern_snapshot` keys by the entire `EvidenceSnapshot`, including exact bound,
optional relation, both heads and coverage. Reusing a snapshot ID therefore
reuses that identical frozen value. A changed admission/emission fence cannot
be collapsed merely because endpoint keys match. The value's heads are not
replaced by current group heads afterward.

Repeated predecessor traversal from a saved head strictly decreases the
admission ID, hence terminates in at most `head.0 + 1` visits. Its list is
exactly the group's successful admissions through that head. Later admissions
append new records and replace the mutable group head; they do not mutate old
records or old snapshot values. Thus this saved prefix is append-stable even
when source and destination keys are equal. The immutable query uses no live
group-head reread and no destination recursion.

### Direct transform constructor and actual returned ID

The direct creator first rejects `to != w.to`. It takes
`snapshot(w.from,Some(parent))` from its current State and interns it. It then
constructs `c` from the destination pair and the parent's post-check context,
records `Dependency::Transport {child:c,parent,use_origin,witness:Some(w)}`,
passes precisely that snapshot ID, `w`, `parent`, and `c` to `transform`,
attaches `(to,c)`, and returns exactly `(c,t)` on successful sampling.

`transform` records those exact arguments. Its full-record key includes the
antecedent snapshot ID, both bound keys, both relation IDs, reason and coverage.
An interning hit returns an identical existing record, so it also satisfies
these equalities. The group invariant therefore applies to `P(S)` and every
yielded source record. Its stored `TypedPairKey` origin is already present and
does not need to be joined with the operational origin table.

The association is the actual source admission carried as the transform's
antecedent. It says that this transform references that admission as one member
of its frozen source fiber. It does not say that a destination admission was
emitted, that its processing pair equals this origin, or that this origin is
an authentic source/attachment/provider/handler certificate.

`transform_children[child]` stores the most recently inserted transform for
that child and is not an inverse of transformation. Multiple transforms may
share one child, and an interning hit does not rewrite that index. The actual
returned ID identifies the requested full transform regardless of this map.
Consequently this accessor must never rediscover `t` by child lookup or arena
census.

### Separately frozen emission-to-admission links

`emit(a,slot)` reads the actual admission `a`, appends an emission with exactly
that ID and its bound, and links it into that admission's group's emission
chain. `snapshot` freezes this emission head independently of its admission
head. In a constructor-generated local snapshot each emission in its saved
prefix links to an already admitted member of the saved admission prefix:
the admission existed before emission, and the simultaneous admission head
includes every such prior same-group admission. Later emission appends do not
alter those links or either saved head.

This is a source-side construction property only. No emission-prefix scan is
needed for direct source-admission association. A source admission can exist
without a physical emission; `MissingPhysicalEmission` remains an independent
gap in that snapshot. A newly emitted slot after the freeze cannot retroactively
supply physical evidence to the frozen snapshot.

### Rollback and ID lifetime

`BoundEvidence::rollback` restores reverse and latest-child maps from logs,
removes new transform/snapshot/recipe interning keys, restores prior group
heads/coverage in reverse group-log order, removes new group keys, and truncates
the admission/emission/group arenas. Retained records are not rewritten.
Because their prerequisites were created before them, every retained transform
keeps its retained snapshot, and every retained local snapshot keeps its
recorded prefix. Strict predecessor descent remains true after restoration.

`State::rollback` calls this evidence rollback at line 1619; the effect-algebra
rollback delegates to it (`candidate_effect.rs:248`), and intrusion rollback
delegates to the effect-algebra (`candidate_intrusion.rs:104`). Thus a rollback
to a checkpoint before `t`'s creation retires `t`; one that retains the actual
`t` also retains its prerequisite prefix. An interning hit on a precheckpoint
transform preserves that earlier actual record.

IDs are vector indices, with no epochs. Later appends can reuse a retired
index. Checking an index is in range and its key matches cannot prove that an
old copied handle names the original construction. The query contract must
therefore stay within the actual live State/route lifetime. No epoch/global
registry is proposed. A borrowed view enforces absence of concurrent mutation
during the query, but does not authenticate arbitrary stale numeric input.

Failure before the wrapper returns gives the caller no successful `(c,t)`.
Some earlier relation/dependency/transform writes may already exist if a later
attach/sample fails; this packet does not declare them publishable. The owning
private attempt must discard/roll back invalid dependent work according to its
existing lifecycle. The proof neither requires full capacity restoration nor
derives a global failure-publication theorem from storage truncation.

## 4. Proposed private borrowed interface and validation boundary

The following is a contract for the primary/implementer, not new code or a
selected public API. A State wrapper delegates to a BoundEvidence reader:

```text
transport_admissions(&self, actual_live_transform_id)
    -> checked borrowed transform view + frozen admission cursor

view: exact transform ID, borrowed transform/snapshot metadata
cursor item: transform ID, source admission ID, &BoundAdmission,
             destination BoundKey, destination child RelationId
```

The item exposes source bound/fiber/origin through the borrowed admission and
destination through this exact transform. It exposes no fabricated destination
admission/emission, copied payload collection or authorization verdict.

Reader requirements:

1. Input must name the actual live returned transform in its owning arena.
   Bounds-check transform and antecedent snapshot references; failure produces
   an explicit unavailable/inconsistent result, never an empty success that
   means authenticated association.
2. Check `snapshot.source_bound == transform.from` and
   `snapshot.relation == Some(transform.source_relation)` exactly. Do not
   canonicalize endpoints or search aliases. Key mismatch produces no
   association and keeps/adds the local origin-association gap.
3. A None admission head is a valid absence of source-admission evidence and
   yields zero associations. It cannot justify omitting the new gap.
4. For a nonempty head, get that admission and check its bound and relation
   equal the exact source key. Under the constructor-generated current-arena
   invariant in §3, this O(1) head validation establishes membership of the
   entire prefix. The proposed constructor must own/use this check before it
   claims local direct association in its coverage.
5. Borrow the arena and advance solely through the saved head and then
   `previous_on_group`. Each step may defensively check index validity, exact
   bound/relation/group, and strict descending predecessor. A mismatch must
   be reported as inconsistency and never yielded as an associated record.
   These checks require no allocation. They do not extend the lifetime scope.

There is an explicit difference between the actual direct creator and the
low-level `transform` method. Current `transform` indexes `snapshots[antecedent]`
without checking the source key. `import_evidence` interns a supplied snapshot
value without validating its heads. Although private heads cannot be fabricated
outside the module, public source-bound/relation fields of a copied snapshot
can be changed; imported captured values also require their owning lifecycle.
Thus this note does not prove arbitrary imported snapshots safe merely because
their IDs are in range.

The approved bounded scope is same live State/route and well-formed current
arena. Direct `snapshot` generation establishes the invariant needed for O(1)
head/key validation. If an API is later required to authenticate arbitrary
untrusted imported prefixes, it must first establish that additional owner/
lifetime premise, or validate the whole prefix before making a whole-prefix
claim; numeric/key equality alone cannot solve stale same-key index reuse.
Do not silently broaden this accessor or add persistent metadata to do so.

## 5. Local gap law and unchanged operational meaning

Write `G(S)` for the set of existing coverage bits and `M` for
`MissingOriginAssociation`. Define `D(T,S)` as exact source-key match plus a
valid nonempty current-arena prefix as above. The proposed constructor law is

```text
G_new(T) = G(S) union (if D(T,S) then empty else {M}).
```

Therefore `G(S)` is always a subset of `G_new(T)`. Inherited `M` stays set even
when `D` holds. The empty/mismatched/unavailable-prefix case retains/adds `M`.
Current code instead sets `G_current(T) = G(S) union {M}` unconditionally at
`candidate_context.rs:592–593`; no current implementation claim is made for
the proposed law. Full transform interning must continue to use the resulting
coverage in its key.

Do not subtract `M` from an existing snapshot or old transform; distinguish
an inherited flag from the one the local constructor would newly add. Other
flags remain bit-for-bit inherited, including missing physical emission,
processing antecedents, seed authentication and replay-use antecedents.
OwnerEmission's `MissingAntecedent` flag concerns its unavailable antecedent,
so a nonempty group does not authorize deleting it.

The operational origin loop at `candidate_effect.rs:582–600` explicitly takes
`relation=None`, imports a snapshot with `MissingOriginAssociation`, and
creates a separate destination admission through its original processing-pair
origin route. It remains unchanged and gapped. The fiber loop continues to
construct the same child/dependency/transform and attach it; the existing
`(child,transform_id)` return signature already supplies the required handle.
This reader/gap law never executes replay, changes contexts or filters,
canonicalizes rows, changes FreshUse reconstruction, or grants CircuitEvidence
readiness. Typed drain completion/discharge is not inferred from association.

## 6. Required implementation cases and cost

These are focused case obligations for the later implementer and primary's
verification owner; no tests or probes ran in this packet.

| Case | Required local result |
| --- | --- |
| One origin admitted on two fibers | Query only the exact source relation's prefix; never join by origin |
| Several admissions on one fiber, including duplicate origin | Yield each admission ID once in saved reverse insertion order |
| Source equals destination, later admissions/emissions | Saved prefix remains unchanged; no latest-head reread or recursion |
| No group / transform-only source fiber | Zero direct admission associations; retain/add local M |
| Exact-key aliases after representative changes | Only original exact source key matches; no shape/canonical-key substitution |
| Same child from several transforms / transform interning hit | Actual returned transform ID selects its own snapshot; child map irrelevant |
| Nonempty source prefix without physical source emission | Direct admission association available; physical-emission gap remains |
| Existing source coverage already contains M | M remains set; no blanket clearing |
| Snapshot key/head mismatch or unavailable reference | No mismatched record yielded; explicit missing/inconsistent classification |
| Rollback retains transform / rollback retires it | Retained prefix survives; retired handle must not be reused as old evidence |
| Failure after transform but before wrapper success | No successful returned evidence; existing private lifecycle owns cleanup/publication |
| Capture/FreshUse and relation=None operational fallback | Original behavior/gaps unchanged; no new destination evidence inferred |

No new persistent field, arena, certificate copy, cache or census is needed.
Existing transforms retain O(F) constant-sized references for F distinct
transform records; the reader adds O(1) cursor/view space and zero heap
allocation or payload clones. Header validation is O(1) under the established
local constructor invariant. Traversal is O(Avisited), where Avisited counts
only admissions in the saved prefix actually visited (plus constant work on
each checked edge). Querying q prefixes costs O(q + sum Avisited); repeated
queries can repeat this work. This packet selects no cache or amortization
claim. Hash-map lookup/interning cost remains the existing expected lookup cost,
not a new worst-case guarantee.

## 7. Evidence, omissions and commit packet

Method: direct source induction over admission/group writes, exact snapshot/
transform construction and rollback prefixes. This is a bounded unreviewed
source correspondence derivation; §4 is a proposed accessor contract and §5
a proposed implementation law. It is not an established reviewed theorem,
executable probe or whole-source operational correspondence.

Checks performed: bounded `rg`/`sed`/`cat` owner and rule inspection;
`git rev-parse HEAD` and branch read; `sha256sum` on the seven manifest inputs;
read-only `git diff` of four compiler inputs against both the pinned baseline
and `09e1219b` (empty); exact leased-file whitespace and dependency recheck
reported at handoff. No build, test, runtime probe, benchmark, solver execution,
measurement sample, Git mutation, child launch or source edit. Static process
work only, no heavy process, within the 15-minute allocation; CPU/RAM were
not measured. No second equivalent proof route was attempted.

Requested routing: normal `gpt-6.1-sol` / `high` per primary packet. Observed
effective model/effort: unknown; no runtime metadata was available. The
registered prover role has no model/effort pins and configured subagent defaults
are Sol/high, but those file reads do not prove this session's effective model.
No Astra escalation or delegation occurred.

Unverified scope: stale/cross-State imported-snapshot lifetime, global capture/
FreshUse lifecycle, source eligibility, semantic transport qualification,
activation/discharge/replay completeness, joint opposite-pair context/dependency
disposition, source/Call/effect completeness, soundness, required principality,
L4 and production/F5 cutover. No parent status is changed here.

Next action: primary assigns fresh independent compiler-referee review of this
frozen statement, constructor induction and §4–5 preconditions; after
adjudication assign the bounded accessor/gap-law implementation with the exact
case obligations in §6 and the unchanged origin-loop requirement.

Commit packet:

- Exact leased path: `notes/theory/2026-10-13-direct-transport-admission-association-proof.md`.
- Baseline: `8d90a83e5aa3c7035c799aa2fbb2b833256525a3`.
- Changed dependency hashes: none in the seven-input manifest; recheck before
  independent review/integration. Only this new research note is produced.
- Review status: unreviewed research-only; no self-certification or closure.
- Checks: static owner inspection, hash and baseline diff checks; no executable
  verification. Primary owns any later builds/tests and review.
- Proposed checkpoint message: `research: derive direct frozen transport admission association`.
- Shared-record deltas for primary/curator only: record this bounded direct
  association derivation and pending independent review; keep bulk joint-pair,
  source/Call/L4/F5 parents OPEN; after review, route §4–6 to the existing
  inert-evidence implementation lane. This leaf edits no task, index or theory
  status record.

## 8. Primary independent review and implementation correspondence

A fresh independent `compiler_referee` passed this frozen source derivation at
producer SHA-256 `ff23081506543ccdca099c8ad439f8b2228a20989c405e22418cdc516ae051fb`,
with no findings. Architecture adjudication confirms the existing snapshot
representation suffices without new semantic policy or persistent storage.
The manifest and proposed-code descriptions above refer to the pre-implementation
baseline; they do not claim the current owner still has those bytes.

The primary assigned the bounded constructor/borrowed-reader implementation.
The same independent referee passed its frozen delta with no findings. A
separate mandatory pre-write `spec_auditor` approved the one existing assertion
change for the two truly admitted source fibers: coverage equals frozen source
coverage, preserving every inherited gap. The operational ambiguous-origin
fallback retains its own gap; no source-authentication or circuit completeness
follows from the direct association.

The [integration record](../progress/2026-10-13-direct-transport-admission-integration.md)
identifies the actual code, unchanged operational consumers, private reader
scope, hashes and two compile checks. Runtime cases in §6 remain unexecuted.
This closes the local record correspondence only; all original source/Call,
joint opposite-pair, L4, soundness/principality and F5 obligations remain OPEN.

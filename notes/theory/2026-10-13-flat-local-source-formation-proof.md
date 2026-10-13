# Flat LocalSource formation: source-derived scheduling invariant

Status: independently reviewed research derivation of an internal builder transformation;
dependent entrypoint change BLOCKED by downstream recursive association;
no theorem promotion, implementation certification, or implementation authority
Baseline supplied by primary: `593b81ff5d2c9da39a3ba459e3e3f1671049ea3c`
Branch supplied by primary: `research/simple-sub-intrusion`
Exclusive output lease: this file only; leaf, no delegation
Method: static construction and transition induction; no executable probe
Verification owner: primary; fresh independent `compiler_referee` required

## 1. Frozen obligation and boundary

Let O be the inspected `module/local_source.rs` builder. Let F be precisely O
with the expression-depth integer removed from `Work::Expression`,
`Work::Initializer`, `expression`, `block`, and their call arguments; with the
three tests `depth > 128`, `depth + tails.len() > 128`, and
`depth + parameters.len() + 1 > 128` removed; and, optionally, with only
`block`'s `has_recovery(&statement)` disjunct removed. F retains
`Work::Restore(usize)` and `Work::Publish(u32, usize)`: their integers are
lexical stack lengths. Their behavior and scheduling are unchanged.

Quantify over every finite proper immutable CST rooted at the actual
`RootPlan.node`, with the actual root, artifact, admitted parameters, namespace,
source-key inventory, counters, and next occurrence ordinal supplied by
`lower_plan`. No parameter, local binder, occurrence, source key, range, or
lexical scope is replaced. The proper-tree premise means that child traversal
reaches strict descendant occurrences, different sibling branches have
disjoint descendants, and each occurrence has finite children. It is the
representation contract of the `rowan::SyntaxNode<YulangLanguage>` used here,
not a property of arbitrary user-supplied transition graphs.

Required conclusions:

1. F's formation schedule terminates or stops with an error/resource failure;
   expression nesting does not induce recursive calls in this builder.
2. On O-supported inputs, successful F produces the same ordered arena and
   bindings, exact branded identities, scopes, resolutions, and identity-map
   writes. On runs whose O depth tests never reject, other structural failures
   occur at the same semantic operation. Allocation failure timing is excluded
   from exact trace equality; safe private early stop is sufficient.
3. For larger finite CSTs passing every retained structural, annotation,
   identity and resource check, F completes with every reserved slot written
   exactly once and all constructor-owned identities retained. Root recovery
   exclusion implies recovery exclusion at every scheduled statement.
4. Give explicit formation work/storage bounds, including remaining scans and
   copies. Do not assert universal linear time, bounded RSS, arbitrary source
   parsing, complete allocation recovery, or full restoration on failure.

This is a conditional derivation for the exact proposed F, with its operational
premises established at the inspected O constructor. F is not implemented by
this note. It is a local safety/natural-source-formation obligation (A/B), not a
soundness or principality theorem for inference.

Preserved exclusions: root `parameters.len() >= 128`, the matching caller
`admitted.parameters.len() > 127`, all annotation depth-128 guards, supported
syntax and private local visibility, operation checks, SourceGeneralize scopes,
and all downstream checks. No change to ordinary HIR selection, boxed legacy
lowering, primitives, complete Call, effects, generalization, public schemes,
F5, or `main`. No restriction is added to make this proof work.

## 2. Governing sources and actual ownership

- Top-level principles `notes/design/2026-10-11-yulang-inference-top-level-principles.md`
  §§1–4: natural mathematical inference, computational accounting,
  proof-before-implementation, and necessary abnormal-path safety.
- SourceGeneralize `notes/design/2026-10-08-source-generalize-definition.md`
  §§2–3 selects `notes/theory/2026-10-08-source-generalize-definition-and-proof.md`
  §3.3, “Owning rules, declarations and event telescopes.” The design itself
  has no numbered §3.3. That selected construction requires actual introduction
  owners and original scopes; this note preserves existing HIR facts and does
  not claim that HIR facts alone instantiate its complete semantic records.
- `notes/progress/2026-10-10-generic-local-source-hir.md`, “Costs and boundary,”
  records the historical 128 expression envelope and nested recovery scans.
- `notes/design/2026-10-10-ordinary-hir-successor-carrier.md` §§1–5 is a
  **Reviewed proposal, approval pending**, not authority to enable ordinary
  carrier formation. Its separate ordinary-HIR integration gate stays open.

Actual source bridge (baseline line numbers):

| Owner | Established fact |
| --- | --- |
| `module.rs:911–921` | Opt-in lowerer creates source identity/key inventories and sets `local_source`; ordinary `lower_module` does not. |
| `shadow.rs:352–360` | `source_keys` uses an explicit stack over source-node children to inventory source keys. |
| `module.rs:1270–1319`, `1389–1430` | Plan admission owns root headers; `lower_plan` creates root parameters once in admitted order and passes those exact IDs to formation. Root cap remains. |
| `local_source.rs:257–389` | Root recovery preflight, root Lambda formation, work dispatch, completion inventory, final root annotation, and successful return. |
| `local_source.rs:392–436` | One lexical stack plus latest-spelling map owns push/restore and nearest binding. |
| `local_source.rs:438–475` | `slot` owns fresh ordinal reservation; `set` owns occurrence minting, source identity write, range and scope. |
| `local_source.rs:477–695`, `698–831` | Expression/block cases own all descendant schedules, local IDs, local parameter owners, scopes and block order. |
| `module.rs:2295–2304` | Recovery means descendant node `Missing`/`Invalid` or token `Error`. |
| `source_annotation.rs:349–397`, `399–506` | Annotation recovery/depth preflight precedes actual recursive type parsing. |
| `candidate_source.rs:82–113`, `169–308`, `413–419` | Consumer preflight reads complete arena; emitter uses retained occurrences/parameter/local IDs, child ordinals and scopes. This consumer is not changed or proved complete here. |

The lowerer ultimately publishes `HirModule` only at `module.rs:1040–1058`.
`local_source::form` and carrier insertion errors propagate through `?`,
aborting that owning lowering attempt. Counter writes before a failure are not
rolled back by this builder; no returned `LocalSource` or `HirModule` exposes
that incomplete attempt. This statement concerns these actual callers and
does not authorize retrying a partially mutated counter set.

## 3. Termination from actual source descent

There are only four work variants. `Restore` and `Publish` emit no further
work. `Initializer` emits one `Publish` and one expression, after a finite
iteration over its already retained parameter vector. Its expression node is
`body(statement)`: the sole `OperatorChain` child of that statement's
`BindingBody`, a strict descendant of the initializer statement.

Every expression scheduling case is similarly rooted in source descent:

- OperatorChain: head is its first direct child; each argument is the sole
  child of a distinct tail, with ColonApplicationTail additionally requiring
  that child to be OperatorChain. These argument subtrees are disjoint from
  the head and from one another. An empty CallTail writes Unit immediately;
  an ascription parses its type immediately; an operation PathTail writes
  Operation immediately. None schedules its parent or itself.
- ParenthesizedExpression: its sole child is a strict descendant. Empty
  parentheses write Unit immediately.
- BracedStatementBlockExpression: `block` obtains sole children of direct
  Statement wrappers. The final OperatorChain is scheduled once. Each earlier
  BindingStatement is scheduled as Initializer once. Those subtrees are
  pairwise disjoint and strict descendants of the block.
- Name, Integer, Unit and Operation leaves schedule nothing.

By proper-tree induction each syntax occurrence is visited as an expression
at most once, each retained binding statement is initialized at most once,
and each descendant expansion has finite fanout. The work expansion forest
is finite. Root and local parameter Lambdas deliberately reuse the statement
source key, but they are formed by finite `for` loops and are not syntax-node
work expansions. Thus reuse of that source key supplies no cycle.

The call graph is `form` loop → `expression` → at most `block`, returning
before the next loop iteration. Neither `block` nor a helper calls
`expression` or `form`. There is no recursive expression call. The recursive
`parse_type`/`parse_group` route remains, with unchanged preflight counting one
per parenthesized-inner or arrow-result transition and rejecting depth >128.
Parameter-annotation clones and annotation destruction also remain bounded by
that retained annotation representation. No claim is made about parser,
Rowan/library implementation stacks, or downstream inference stacks.

## 4. Single-write slots and retained identity

Use the invariant: every reserved slot is either (a) written, or (b) owned by
exactly one pending formation responsibility. Root reserves one slot.
Each root/local parameter iteration writes the current slot as Lambda and
transfers responsibility to exactly one fresh body slot. It never revisits
the written slot.

For OperatorChain, reverse tail processing writes the current slot and
transfers the callee/inner responsibility to a fresh slot. An Apply additionally
reserves a fresh argument slot and either writes Unit immediately or transfers
it to one pending argument expression. After all tails, the remaining current
slot is written as Operation or transferred to the one head expression.
Zero tails transfer the original unwritten slot without writing it.

A nonempty Group writes its incoming slot, reserving and scheduling one inner
slot. A Block writes its incoming slot, reserves one final-expression slot and
one initializer slot per binding, and transfers each to its unique work item.
Initializer writes only its own pending slot chain; Publish/Restore write no
expression slots. Leaves write their incoming slot once. No transition copies
or duplicates a pending responsibility. Thus a successful empty work queue
has no pending slot; the completion loop additionally rejects any `None`.

Every structural child expression index is allocated later than its parent
index. Block's initializer links through binding records also point from the
block to later allocated slots. Therefore the completed arena's structural
expression graph is acyclic independently of CST descent. Names retain
resolution IDs and do not create structural expression edges; recursive local
resolution cannot create a work cycle.

Each successful `set` fetches the existing node key, mints one fresh checked
occurrence in the same artifact, records it, and stores the actual range,
scope and form. Occurrence IDs are unique even when Lambda/Unit/Apply records
intentionally share a source node. `block` mints each Local ID once from the
binding vector length. Local parameter IDs advance one checked counter from
the root parameter count and record the actual local owner before retaining
the parameter. No new synthetic source identity or reconstructed scope is
needed for larger depth; the same constructors retain the same evidence.

## 5. Depth erasure and lexical trace preservation

Relate O and F states by removing only expression-depth fields/arguments.
All other vectors, maps, indices, counters, scopes and work order agree.
For an O run not rejected by a removed test, every transition has an identical
F transition after this projection. Depth is read only by those tests and in
the deleted arithmetic arguments. In particular, it never selects a key,
occurrence, namespace entry, lexical entry, scope or form.

`Restore`'s integer is **not** erased: it is the stack length recorded when
entering a block. Initializer's `guard` is also that stack length. Initializer
pushes a temporary self-local only for a parameterized binding, then pushes
parameters in source order. Parameters may shadow the self binder. Its pushed
Publish lies below all initializer body work. Nested block Restore items lie
above that Publish and restore their own saved lengths first. Publish then
restores its saved guard and installs exactly that completed local binder.

Block pushes Restore, final-expression work, then initializers in reverse
source order. LIFO execution forms each initializer then publishes it in
source order; the final expression sees all earlier publications; block exit
removes them. Outer pending argument/head work resumes after nested block
restoration. The `previous` chain maintained by push_binding restores the
latest surviving same-spelling binding exactly. Every guard is a saved prefix
length preserved until its restoration; expression nesting counts play no
part. Consequently nearest-name resolution, recursive self visibility,
nonrecursive self exclusion, captures and all explicit parameter/local/block
scope fields are invariant under erasure.

The same slot/set and parameter/local creation order gives exact occurrence
allocation order, arena order, binding order and sidecar-map writes, not merely
isomorphic identities. Exact structural failure preservation applies whenever
the removed tests would pass; inputs formerly rejected at those tests may now
proceed and are precisely the intended increased formation envelope.
Resource layout/allocation timing can change; no corresponding failure-trace
identity or complete restoration is required.

## 6. Recovery preflight justifies the one scan removal

`form` evaluates `has_recovery(plan.node)` before constructing its Builder.
The predicate searches all descendant nodes/tokens for the three recovery
kinds. Sections 3–4 establish that every scheduled statement/expression and
every synthetic Lambda's source node lies in that same subtree. Descendant
transitivity gives `!has_recovery(statement)` for every statement handed to
`block`'s initializer loop. Removing only that disjunct is therefore logically
silent; the BindingStatement-kind requirement remains.

This does not prove absence of every possible separately recorded recovery
object. It proves redundancy for exactly the owning `has_recovery` predicate.
No plan mutation or foreign subtree insertion occurs between preflight and
scheduling. Annotation, header and operation recovery checks stay as written;
this packet does not remove their independent checks.

## 7. Explicit work and space accounting

Count the actually successful formation of one root:

- N: node/token occurrences in its CST subtree; R: root parameters;
- P: total retained local parameters; I: local bindings; K: blocks;
- A: Apply tails excluding the initial operation PathTail; C: ascription tails;
- G: nonempty Groups; E: popped Expression items; S: reserved expression slots.

Then

```text
S = 1 + R + P + 2A + C + G + K + I
work items popped = E + 2I + K, with E <= N
lexical pushes = R + P + I + J, with J <= I
```

J counts parameterized initializer temporary self bindings. Each lexical
entry is popped at most once. All child inventories, initializer inventories,
parameter loops, slot writes and completion iterations are bounded by these
counts. Work/arena/lexical structural records are O(N+R+P+S+I); peak work is no
larger than the total emitted work. Vector reservation uses the existing
allocation API, not a proved allocator growth or RSS bound.

Let H be the sum of actual header/identifier recovery-scan element visits,
Q the sum of annotation recovery/preflight/type-parser element visits,
and Bcopy the total bytes copied/hashed plus annotation tree records cloned
(including retained parameters duplicated into Lambdas). Keep these actual
costs visible rather than treating all strings/annotations as unit cost.
The root recovery scan costs O(N). Removing the block-statement scan eliminates
its potentially repeated traversal of whole nested initializer bodies.
Remaining header recovery checks inspect target/tail/argument/identifier
subtrees, not initializer bodies; annotation checks traverse actual annotation
subtrees. They remain included in H and Q, as do root header planning and the
source-key inventory when accounting for the whole opt-in lowering route.
Successful admitted header shapes have constant wrapper overlap; annotations
have the unchanged 128 parse-depth bound. This note does not erase these scans
or certify the entire upstream lowering cost.

Under expected HashMap behavior and normal amortized vector growth, formation
work is O(N+R+P+S+I+H+Q+Bcopy). Without those library assumptions, retain map,
allocation and copy costs explicitly; this is not an unconditional linear-time
theorem. Scratch and retained spelling/annotation payload storage add their
actual sizes to structural storage; shared CST/source/identity payloads,
namespace maps, allocator overhead and failed-attempt peaks are not measured.
The final output vector coexists transiently with the Option arena. No RSS or
allocation-failure-restoration claim follows from `retained_arena_bytes`.

Finite larger depth is therefore no scheduling reason to reject. Success still
requires representable checked identities and successful retained allocations.
Existing infallible string, map and annotation allocations remain; the proof
does not make them fallible or guarantee successful formation of arbitrarily
large finite input. On errors the actual caller propagates failure and returns
no partial product. The separate root cap bounds root parameter Lambda
construction; it does not guard recursive body association. Annotation depth
protects real recursive type parsing; both caps remain.

## 8. Downstream obstruction: entrypoint removal is not safe yet

The primary reported a material downstream counterroute before this artifact
froze. Narrow source inspection confirms it. `lower_plan` successfully inserts
the carrier and then calls `lower_body` (`module.rs:1412–1455`). The opt-in
entrypoint sets `local_source=true` but does not set `shadow_applications`
(`module.rs:911–921`). Therefore `lower_body` reaches `lower_simple_chain`
(`module.rs:1641–1674`) without the shadow application's body-depth guard.

`lower_simple_chain` calls `associate_chain_owned` **before** checking whether
the association has a usable atom (`module.rs:2095–2106`). That association's
`ChainParser::value` calls `collect_nested_items`; the latter recursively visits
non-OperatorChain child nodes and recursively calls `associate_chain_owned`
for nested OperatorChain nodes (`lib.rs:505–538`). It constructs recursively
owned `HirExpr` children along this route. An eventual `atom=None` and
Unsupported result arrives only after that construction.

The static family `my result = ` followed by d opening parentheses, `1`,
and d closing parentheses illustrates the seam: assuming its parsed CST is
available and recovery-free, its expression forms are already supported by
the internal builder. F no longer rejects increasing group depth, so the
entrypoint can reach increasingly deep recursive association. The root has
zero parameters and no annotation; the retained root parameter cap and
annotation cap do not protect this call chain. This is a source-call-graph
counterroute, not an executed stack-overflow result, measured threshold,
claim that arbitrary d parses, or refutation of the local work-stack proof.

Thus internal builder termination and preservation do **not** establish safety
of removing the entrypoint's effective expression envelope. Keep the current
cap in production until the primary establishes a remedy at the owning
association/construction responsibility and independent review accepts the
complete route. This note supplies no workaround, source restriction, guessed
new depth limit, or authority to bypass association. The precise additional
premise is: newly admitted source depths must not reach unbounded recursive
association/ownership construction or destruction before rejection/publication.
Its owner is `lib.rs` association and `module.rs`'s unconditional consumer call,
not the flat LocalSource work scheduler.

## 9. Dependency snapshot, checks and handoff

SHA-256 frozen before derivation (rechecked after writing):

| Dependency | SHA-256 |
| --- | --- |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-hir/src/module.rs` | `943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5` |
| `crates/yu-hir/src/module/source_annotation.rs` | `a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb` |
| `crates/yu-hir/src/lib.rs` (added when downstream seam reported) | `51e5fa543cd65ced879a7561e0d602e686a072378cde5ec16a20b4afb875fc0a` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-hir/src/shadow.rs` | `687b49061273974fe874a8479a8db91ba24cc77fe92e6d2b96ae46a3626cf9dc` |
| `crates/yu-syntax/src/syntax_kind.rs` | `f3c7632b8e5c975ed917de56355030d90106b8710fe6cd89020e8394a73a09c0` |
| SourceGeneralize design | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| Selected SourceGeneralize construction | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| Ordinary HIR proposal | `82d98a38208c2cab7788b97deec8f1319734dbaddd41de70a7e56bae00fea689` |
| Top-level principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| Generic local source checkpoint | `39d2f27f7b86152832eb3168df10830112690772a706cabf096f72819e206353` |

Commands: bounded `cat`, `sed -n`, `rg -n`, `rg --files`, and `sha256sum`
reads of the stated dependency cone; `apply_patch` writes to the leased note.
Full local_source and source_annotation files read; caller, key inventory and
consumer ranges read as listed above. No Git calls, builds, tests, probes,
measurements, subprocess search jobs, or delegated jobs. Budget: one static
leaf, at most 15 minutes; zero heavy processes and zero measured samples.
Config inspected: registered `prover`, no role model/effort pins, configured
normal defaults `gpt-6.1-sol`/`high`. Requested leaf routing: normal Sol/high;
observed effective runtime model/effort: unknown. No Astra escalation.

Falsifiers examined: same/ancestor work schedule; synthetic Lambda cycle;
duplicated or abandoned successful slot; expression-depth/lexical-guard
conflation; recovery descendant bypass; recursive builder expression call.
The case analysis above supplies direct constructor reasons against each.
No two failed proof routes or unchanged missing premise occurred. Independent
review must still attack the tree/ownership assumptions and exact proposed
transformation. The separate downstream obstruction in §8 prevents an
entrypoint-safety conclusion. No compiler patch, compiler verification or
independent review has run.

Next action: primary investigates the exact downstream association owner in §8
and establishes a bounded remedy before permitting cap-removal implementation;
fresh `compiler_referee` review may examine this frozen internal derivation in
parallel. The dependent production gate remains BLOCKED on that precise seam.

## Primary review and implementation boundary

Fresh independent `compiler_referee` review passed this bounded internal
formation theorem with no findings at producer SHA-256
`e7824bd3bdf3fb224f8655eabab2d6ba74ced96dff9ba40de0f2860b9d805cd9`.
The reviewer checked the constructor schedule, exact slot/work accounting,
identity/scoping simulation, recovery ancestry and stated cost exclusions.
The primary consumes the theorem only as support for the proposed flat
builder transformation; the downstream entrypoint premise in §8 remains OPEN.

A separate read-only source audit independently confirmed that deep groups
would newly reach recursive association. An architect proposed returning a
private simple-body projection alongside successful binding formation to
avoid building that discarded tree. A conformance audit found no new approval
requirement within this opt-in scope; the ordinary first-slice association
contract and pending ordinary-HIR migration remain separate. Its exact
projection equivalence is being constructed and has not yet been reviewed.
No compiler cap is removed by this checkpoint, and no implementation,
complete source/inference, Call, soundness, principality or F5 gate is closed.

Checks for this checkpoint are static dependency, link/fence/whitespace and
diff-scope inspection only. Zero tests, builds, probes or measurements.

The later [projection proof and F-success bridge](2026-10-13-formed-local-source-simple-projection-proof.md)
received fresh independent review and were consumed by the exact two-file
[implementation](../progress/2026-10-13-flat-local-source-projection-integration.md).
That record separates the completed internal source/code correspondence and
compile checks from unexecuted runtime verification and remaining recursive
consumers. Section 8 and its hashes describe this proof's original baseline;
they are not a current-code claim that the formed-binding consumer still
constructs the discarded tree.

Commit packet: exact path `notes/theory/2026-10-13-flat-local-source-formation-proof.md`;
baseline `593b81ff5d2c9da39a3ba459e3e3f1671049ea3c`; dependency hashes above;
claim/review status unreviewed conditional source derivation with explicit
downstream blocker; static reads and
hash comparison only; proposed checkpoint message
`research: derive flat LocalSource formation invariants`.
Shared-record deltas reserved for primary/curator: record the frozen local
proof candidate and pending independent review; preserve the existing
expression cap pending the downstream remedy, preserve root/annotation caps,
and keep ordinary-carrier, inference, complete-Call and F5 gates separate.

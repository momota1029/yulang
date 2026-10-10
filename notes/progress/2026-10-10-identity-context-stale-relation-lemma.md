# Identity context and stale queued relation endpoints

Date: 2026-10-10. Status: frozen, unreviewed, non-authoritative research.
Producer: `/root/identity_relation_transport_proof`, prover-equivalent generic
leaf; no custom prover ran in this assignment. Baseline:
`3cd40155376d1bfa3418bc6dae6e62081156f258`.
Exclusive lease: this note. Method: constructive control-flow derivation from
actual relation, transport, queue and diagnostic owners. No executable probe.

## Objective, authority and frozen statement

Examine whether a queued work item `(t, Some(r))`, whose retained relation is
`(P, ContextId(0))` with `P = task_pair(t)`, may execute using current canonical
endpoints after qualifying parent/copy equality, while preserving its complete
source, ordered replay, diagnostic and contextual dependencies.

Governing authority: contextual-attachment-admission design §§3.1–5 (distinct
source attachment identity, exact context and ordered shared derivations,
checks before omission, obligation transfer and rollback); parent-copy SCC
intrusion's **Selected operation and compiler responsibility** (actual recorded
parent/copy equality affects solving). These meanings are fixed. This note
does not select new language behavior, self-omission, or an implementation repair.
Rules research-lab, design-authority, git-concurrency, agent-orchestration and
compiler-engineering, plus the yulang-proofs skill, were read.

Quantifiers: for every well-formed private candidate session `S`, valid queued
item `t,r` and current representative map `rho`, let `Q = rho(P)`. Relation
keys are immutable and `r.key = (P,I)`, where `I = ContextId(0)`. Consider the
stale case `Q != P`. Representative forests terminate, are kind preserving,
and satisfy `rho(rho(P)) = rho(P)`; a successful selected merge is the equality
authority. No assertion of arbitrary SCC qualification, row-map soundness or
successful source inference is included. Allocations and resource checks must
succeed for any conclusion about completed transport.

**Claim class:** source-derived local lemmas and a conditional certificate
preservation lemma. The universal full-lifecycle preservation claim remains
open: raw item/relation agreement plus identity context is insufficient evidence
for it. No source-reachable counterexample to every possible repair is claimed.

## Derivation from actual owners

### 1. The baseline rejects the stale identity item

`State::relation`, candidate_context.rs:1422–1442, interns `(pair, context)`;
it neither canonicalizes a supplied pair nor rewrites an existing relation key.
`enqueue_item`, lib.rs:12123–12134, keeps a supplied RelationId and raw task.
The drain, lib.rs:11857–11861, installs that relation as processing and invokes
`candidate_context_execute` with the raw task.

At candidate_context.rs:1846 the assertion is `r.key.pair == rho(task_pair(t))`.
Thus `P != Q` causes an assertion failure before the identity branch at1847.
This is an unconditional control-flow consequence of the frozen stale-case
hypotheses, rather than a run performed here. The prior endpoint-route audit
observed exactly `P = Effect(27,58)`, `Q = Effect(27,44)`, RelationId270 and `I`
after the actual58→44 merge. Its producer chronology and derivation parents
remain unverified; that note is bounded historical execution evidence.

### 2. Identity has no local context-discharge work

If a valid relation `c` instead has key `(Q,I)` and the supplied task has
canonical pair `Q`, the same assertion passes and execution immediately returns
`Ok(false)`. No filter validation, registration, discharge or context traversal
occurs. This lemma follows from candidate_context.rs:1838–1848 alone. It does
not establish that dropping `r`, substituting `c`, or returning before the
assertion preserves their derivations.

Ordinary Effect solving is canonical at its own owner:
`candidate_apply_effect`, candidate_extrusion.rs:726–751, starts by replacing
both endpoints with representatives. From the same session and processing
metadata, invocation on `(l,u)` and on `(rho(l),rho(u))` therefore enters the
same remaining body. This includes equality handling, level-selected bound
orientation and opposite replay; it assumes no interleaved forest mutation
between the two initial canonicalizations. The analogous **kernel** fact holds
for `candidate_apply_value` at695–724. It does not equate the surrounding Value
drain: lib.rs:11888–11894 deliberately retains a raw diagnostic pair and its
edge to canonical work. Nor does it equate complete Effect drain state, which
still memoizes the raw pair at11864–11873.

### 3. Changed attached bounds have an existing certificate bridge

Add these explicit hypotheses: before the successful canonicalization scan,
`r` occurs in the retained bound list at key `from`; `to = rho(from) != from`;
and `r.key.pair = bound_pair(from)`. Hold the forest fixed during that scan.
For a source-generated identity relation, `post_check_context(r) = I`: the
only live discharge insertion follows the nonidentity execution path, while
relation keys remain immutable.

`candidate_context_canonicalize_bounds`, candidate_context.rs:2035–2052,
visits each retained entry in its initial list prefix. For this entry it calls
`candidate_context_transport_witness(r,to,0, EqualityCanonicalization{from,to})`.
The transport owner at2091–2112 interns `c = (bound_pair(to), I)`, records the
exact Transport dependency, and attaches `c` at `to`. The caller additionally
records `Derived { parent:r, child:c }`. Consequently:

- The original immutable relation, original bound incidence and existing
  origins/dependencies remain stored. No old replay input or parent is replaced.
- Diagnostic traversal gains a forward `r→c` edge: `dependency(Derived)` calls
  `edge`, candidate_context.rs:1458 and1483–1516. Transport alone intentionally
  supplies no diagnostic constraint edge at1462.
- Existing source bundles propagate across that edge and authenticated
  equality transport, via `bundle_edge`/`bundle_link` at1318–1372.
- Retained evidence closure includes both `r` and `c` and their connected
  derivations: candidate_context.rs:343–347 and442–460 treats dependency
  incidence bidirectionally; origin iteration at305–306 remains on `r`.
- A later ordered replay still records lower then upper RelationIds and exact
  BoundKeys at1969–2029. Even when both contexts are `I`, the Replay dependency
  is retained at2009–2016; identity context is not empty provenance.

This proves preservation of those **stored certificate incidences** under the
stated successful bound-transport operation. It does not prove that `c` is
installed for the pending work item, that all later replay quadrants actually
execute, or that any inference result can publish. The scan does not enumerate
the queue or all relations. Its existing rollback owner journals relation,
edge, dependency, bound and replay append state at1062–1125; full route
rollback/publication correspondence was not derived here.

## Precise remaining premise and discriminating obstruction

The required premise is an owner-supplied connection from the retained queued
derivation to the canonical relation used for processing, with all applicable
source and replay incidences and the proper diagnostic direction preserved.
For the attached-bound subcase above the existing Derived/Transport bridge
supplies such a connection. It must not be assumed for an arbitrary queued
relation or reconstructed merely from identity context and equal representatives.
An explicit `r→c` edge is a sufficient route, not a proof that every sound
implementation must use precisely that edge: an existing certified alternative
path through replay parents could suffice.

The current owners expose why a general proof stops here:

1. `candidate_context_admit`, candidate_context.rs:1663–1676, compares the
   retained processing relation's **stored** pair with the canonical parent
   pair. For stale `r` the comparison fails. It interns/selects `(Q,I)` as the
   parent and records derivation from that parent; it does not record `r→c`.
   In the Effect drain, the canonical evidence call at lib.rs:11867 is therefore
   not itself a queue transport operation.
2. `candidate_context_bound`, candidate_context.rs:1915–1949, repeats the exact
   stored-pair test against canonical origin. A stale processing relation
   again falls back to the canonical source relation. Its new bound may be
   derived from `c` without a local link to `r`.
3. `merge_candidate_rows`, candidate_intrusion.rs:577–605, changes the forest,
   canonicalizes existing bound fibers and replays merged bounds. It never
   updates pending `TypedWorkItem`s or transports unattached relations.
4. Conflict replay, candidate_effect.rs:518–589, traverses forward
   `context.children(pair)` edges. Merely retaining the old relation and a
   Transport record is not the same as making a new downstream conflict
   reachable from its original source occurrence.
5. Completion is also distinct: `mark_candidate_pair`, candidate_intrusion.rs:
   220–254, marks the processing RelationId only for canonical pair admission;
   `pair_is_current`, lib.rs:11354–11365, consults that relation and generation.
   Pair equality alone does not authenticate completion of the retained fiber.

A smallest **local obstruction**, not a demonstrated source program, consists
of two relation keys `r=(P,I)` and `c=(Q,I)`, `P!=Q=rho(P)`, processing `r`, and
no retained changed-bound incidence or other path connecting `r` to `c`.
Calling the admission owner on the canonical task selects `c` as its own
canonical parent and records `Derived(c,c)`; it supplies no missing `r→c`.
This is an exact branch derivation, with no model checker or oracle assumptions.
Additional original Replay/FunctionPort parents may provide alternate paths in
an actual source state; their presence and adequacy are deliberately unresolved.
The prior audit does not establish them for270. This obstruction refutes only
the inference that the admission call automatically establishes queue transport.

The missing fact is lifecycle evidence already available where raw task,
RelationId and representative change meet. Under the compiler-engineering
proof-economy classification this is required correctness/provenance with a
constructional retention seam, not authority to weaken inference or retire a
semantic theorem. No second equivalent probe was attempted.

## Coverage, checks, resources and omissions

Checks: narrow `sed`/`rg` source reads; `git rev-parse HEAD`; read-only status;
`git diff 3cd401553 --` on the eight direct dependencies below was empty;
SHA-256 dependency checks. No tests, builds, GDB, prover CLI, mutations,
seeds/ranges, source minimization, external Oracle or performance samples.
The source is the operational reference; this is not independent Oracle
validation or independent review. Shared premises are well-formed retained
records, successful selected equality and successful resource checks.

Budget: <=1h, <=1 process, research note only. An initial rules/skill read batch
briefly launched two lightweight read-only shell calls concurrently, exceeding
the one-process reading bound; all subsequent shell calls were serial. Zero
compute probes/heavy processes. CPU, peak RAM and total analysis wall time were
not measured; individual read calls completed in milliseconds. Requested model
and effort were not specified in the received packet; effective runtime settings
were not exposed and remain unknown. Native prover unavailability/attempt is
reported by the primary packet, not authenticated by this leaf.

Omitted: actual creation/replay parents of270, full source reachability of the
local obstruction, nonidentity stale contexts, alias-specific Value diagnostics,
all conflicting/late replay paths, full rollback and certificate invalidation,
runtime handler/Call semantics, publication, soundness and principality.
Failure conditions: missing changed-bound incidence, absent alternative
derivation bridge, unstable forest during transport, incomplete resource checks,
or substituting canonical work without preserving raw diagnostic provenance.

Recommended next action: primary has the repair owner establish and retain the
queue-to-canonical derivation bridge at its owning seam, resolving270's actual
producer/parent certificate before claiming the identity shortcut preserves
complete provenance; obtain fresh independent review of that concrete artifact.

## Frozen dependencies and commit packet

Direct dependencies matched the baseline; none changed:

```text
3b219b51ed8aba6ffc85675fd1d500b901a6f63b31325a85a586d688eee3515a  crates/yu-solver/src/candidate_context.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a  crates/yu-solver/src/candidate_extrusion.rs
2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e  crates/yu-solver/src/candidate_effect.rs
9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1  crates/yu-solver/src/lib.rs
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  notes/design/2026-10-10-contextual-attachment-admission-design.md
8ae4348a93dce6df1852a34b2294ebc5e4e256d8b018c1f6eaad42c502470a8e  notes/design/2026-10-10-parent-copy-scc-intrusion.md
adf324b86cfc11c80c4dc8f40d52884875baf843536d88c9e871c1921199b87f  notes/progress/2026-10-10-endpoint-assertion-route-audit.md
```

Exact leased path:
`notes/progress/2026-10-10-identity-context-stale-relation-lemma.md`.
Baseline SHA: `3cd40155376d1bfa3418bc6dae6e62081156f258`.
Changed dependency hashes: none. Review status: frozen, unreviewed,
research-only; conditional derivation, no full preservation/theorem closure.
Checks already run: static owner derivation, baseline-path diff, dependency
hashes, final lease/status inspection; no executable validation.
Proposed checkpoint message:
`research: derive identity-context transport premise for stale work items`.
Shared-record deltas left for primary/curator: record the local identity/kernel
lemmas and existing attached-bound certificate bridge; keep arbitrary queued
relation transport and270's producer certificate open. Do not promote effect
hygiene, soundness, principality or any production gate. No shared record or
question-board files were edited. Producer writes stop at this frozen handoff.

# Oracle generalized observations: continuation demand and the first lost directed component

Date: 2026-10-11
Status: frozen bounded research derivation; independently reviewed with one minor precision correction; original universal H remains OPEN
Claim class: source-derived local operational derivation and a localized obstruction; no established universal theorem or source-qualified counterexample
Yulang3 primary baseline: `35e88c8113c9c6516e260170503bea753e4ede6`
Branch supplied by primary: `research/simple-sub-intrusion`
Oracle revision supplied by primary/governing record: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Inspected Oracle checkout: `/tmp/yulang2-oracle-read`
Exclusive output lease: this file only; leaf, no delegation

## 1. Frozen objective, quantifiers and authority

Attack **H**, exactly as frozen in
[global effect hygiene](2026-10-11-oracle-global-effect-hygiene-proof.md) §1,
with its original successfully lowered Oracle source domain:

For every source P in that domain, every successfully lowered composed-negative
concrete annotation occurrence a, its original lexical scope sigma and binders,
every actual copy/instantiation u, and every actual function call/output route k
involving a, subtraction authorized by a removes only the contribution attached
to that exact instance on that route. An independent contribution at the same
resolved family survives. Symbolic annotation tails remain connected. Every
current and future concrete lower reaching the relevant receiver encounters
the authentic retained check. Occurrence, attachment, scope, provider/call
binder and correlated residual lineage survive actual copying, generalization,
compaction, pruning, finalization and delayed consumption, up to the actual
consistent fresh-use renaming.

The provider, witness, call output and tail remain those of the same source
derivation. None may be selected independently. Function arguments reverse
composed polarity; results preserve it. Incorrect concrete lowers require
the authentic check/error and safe nonpublication. Successful lowering is
not assumed to imply successful inference. Resource-terminal private attempts
need not restore all tables. No source envelope or ordinary inference rule is
changed. The old retracted callback scheme is unused.

Exact authority: [annotation policy](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5; [concrete implementation gate](../design/2026-10-10-concrete-effect-annotation-implementation.md),
“Annotation checking and publication owner,” “Conflict ownership and replay,”
and “Practical formation and reconstruction envelope”;
[contextual admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§§3–4,6; [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5 and Authority and integration. The policy's withdrawn callback §6 is
not a result oracle. Admission §6 continues to disable general Y3 negative
concrete formals.

Operational assumptions for the local calculations below: the inspected source
bytes, valid arena nodes, normally completed selected constructors, no fresh-ID
exhaustion, and count operations within their actual representable domain.
These assumptions do not supply successful source resolution, all-history
replay, scheme correctness, complete Call, soundness or principality. Cases
outside these local calculations remain in H; they are omitted evidence,
not excluded source.

## 2. New method: derive the demand carried by the authentic consumer

The previous packet used forward annotation and clone inductions. This attempt
starts at the actual fresh-use and call consumer and follows the *directed pair*
of weights backward to the exporter. It then compares the consumer's demand
with the pair that compaction actually reads. This method neither adds a
reconstruction layer to the compiler nor assumes that a stored filter activates.

All Oracle paths below are relative to the inspected checkout.

The real local generalization route is
`crates/infer/src/lowering/expr/tail.rs::generalize_local_binding` (945–1017).
It drains selection/subtype work, may retain a live monomorphic slot when
selection is unresolved, constructs its actual non-generic set, invokes
generalization and finalization, and publishes the resulting local scheme.
Thus an arbitrary compact graph is not an automatically reachable local scheme.

The local use route (tail.rs:854–942) invokes
`instantiate_scheme_with_roles_and_provenance` and emits the returned predicate
to the *actual use's* Value coordinate. In
`instantiate.rs::instantiate_scheme_parts` (621–647), one instantiator
freshens the selected variables and stack IDs, clones recursive bounds and
predicate, then wraps that predicate with POP count
`M = u32::MAX` for each selected stack ID (770–787).
The stack map is reused across the entire clone. This gives a real inserted
operation at the use site, beyond a renaming lemma.

`tail.rs::make_app_with_origins` (535–627) emits the four-port Function demand
from that callee Value, the actual argument Value/Effect, and this call's result
Value/Effect. It forwards the actual invocation Effect and callee evaluation
Effect into the application Effect. These are designated coordinates, not
independent marginal outputs.

Let W=(L,R) be the actual constraint pair and i one genuinely freshened selected
ID. Starting with the root wrapper and an otherwise empty direct demand,
`propagate.rs::step_subtype` (11–36) and
`constraints/mod.rs::with_left_prefix` (3577–3582) give

```text
W0 = (POP_i^M, empty).
ordinary Argument Value/Effect: swapped(W0) = (empty, POP_i^M).
Result Value/Effect: W0.
a second ordinary argument reversal: W0 again.
```

These equations follow from the actual Function decomposition
(propagate.rs:210–269) and `swapped` (constraints/mod.rs:3566–3571).
They are not a universal “all ports get the same POP” statement.
The pure argument Effect branch uses `both_from_right` (3591–3596):
on W0 it emits an empty pair, and on (empty,POP_i^M) it emits
(POP_i^M,POP_i^M). The separate receiver routing in that branch also matters.
Its result must not be replaced by parity alone.

Two exact local consequences follow.

* If an actual output descendant's positive wrapper prefixes PUSH_i before
  the carried POP_i^M, the directed count equation
  `compose_same_id_counts(0,1,M,0)` is (M-1,0).
  No active i-PUSH remains in that left component.
* A wrapper PUSH_j at j != i remains active under that root operation, even
  when j has the same family. A concrete nominal `Con(E, [])` is a different
  constructor; a POP entry does not itself erase it.

The first consequence requires the actual order. POP_i^M followed by a later
PUSH_i has an active PUSH; M is not an unordered infinity. Counts and replay
caps therefore cannot be ignored. Both calculations are source-derived local
weight facts awaiting review, not proofs that every attached contribution
reaches this output descendant or every independent source effect reaches its
concrete observer.

## 3. Nested source discriminator: no invented predicate route

The prior falsification note supplies this constructed annotation discriminator:

```text
Function(Unit, None, None,
  Function(Unit, None, [resolved E], Unit))
```

It corresponds to the previously proposed source body `(cb ()) ()`.
This packet does not parse, resolve or execute that text. Assume only that
the real source owners have supplied that tree at a formal boundary.

From `annotation/constraints.rs::connect_parameter_computation_detailed`
(251–282) and `connect_value_detailed` (124–137), paired annotation bounds
are connected to that actual formal coordinate in both directions.
The inner `lower_ret_effect_bounds` (424–470) chooses q, allocates i, and
constructs its positive effect PUSH_i(q), negative effect FILTER_E(q),
and matching POP/filter on the *inner returned Unit Value*.
The outer Function has omitted immediate result Effect and therefore returns
no call predicate. Function construction (363–389) does not hoist the inner
predicate.

Consequently, in the decomposition demanded by the second application, the
inner PUSH is on its Effect result and the inner POP is on its Unit Value
result. The POP is **not** a wrapper on the Function returned by the first
application. Nor does the second application recover cb's local predicate:
its callee is an `Expr::App`, while the local lookup accepts `Expr::Var`.
This corrects the tempting but invalid cancellation trace at the first call.

The two actual four-port demands identify the delayed owner. Connecting their
generated constraints through all live bounds, extrusion and replay still needs
the machine's source/replay correspondence. If the delayed body's q/PUSH_i
reaches a positive generic compact occurrence, stack selection can retain i
and the fresh root operation in §2 can act on a later use. Whether it does
reach that occurrence is the next question; neither stored provenance nor
the nested tree establishes it. No resulting scheme or source-qualified
hygiene failure is claimed.

## 4. First lost component: positive scheme projection reads only L

This continuation method exposes a more local obstruction than the whole
generalization pipeline.

`compact/collect/mod.rs::compact_scheme_lower_bounds` (848–877) first asks
`scheme_projectable_lowers_in_scope`. The actual query
(`constraints/structural_kernel/access.rs:862–892`) omits a record when
`ProofOccurrenceStore::project_lower` returns Excluded. Its owning evaluator
(`constraints/proof/mod.rs:9975–10130,11632–11765`) follows current live
claim/support/formula records; its inclusion decision is not a theorem
about every future higher-order use.

For each included weighted lower bound B, however,
`compact_lower_bounds_from` (898–920) reads

```text
compact_pos_bound_id(B.pos, B.weights.left.to_stack_weight() union outer_weight)
```

**B.weights.right is not passed.** A directed right POP that reached this
positive lower through an authentic argument reversal is thus absent from
this recursive projection. In addition, positive Function compaction sends
its carried weight only to result ports and resets argument ports
(`compact/collect/type_nodes.rs:17–23`).
Negative Function compaction carries it into arguments and resets results
(124–135).

Here is a static discriminator for the proposed proof step “compact every
weighted bound, then reuse the same port cancellation.” It is not a source
counterexample. Consider a valid typed bound with

```text
B.pos = Fun(..., ret_eff = Stack(q, PUSH_i(E)), ...)
B.weights = (empty, POP_i^M).
```

When that actual bound is replayed against a Function demand, result
decomposition keeps its directed pair. Normalizing its result Stack prefixes
PUSH_i on the left while retaining POP_i^M on the right. A genuine subsequent
`compose_for_replay` applies W-Mix:
`directed_weight.rs::mix` (13–43) removes the active i-PUSH and leaves the
appropriate remaining right POP. By contrast, compacting B through the
positive lower owner above sees no right POP; its recursive q occurrence
receives PUSH_i. The two constructors do not commute syntactically or preserve
active i-counts by a simple structural induction.

This rejects that proof shortcut. It does not show incompatible published
observations: upper projections, other joint ports, recursive bounds or
subsequent root POP can represent the lost component. Moreover, although
§2 shows how right POPs are actually emitted, this packet has **not** shown
that this particular same-i B is source-reachable with the same authentic
provider/call/output incidence. Freshness rules out an independently fabricated
caller PUSH_i; correlated same-use flows and recursive bounds must be traced.
Choosing such a provider independently would invalidate the argument.

The smallest unproved premise exposed by this route is therefore at this
specific record projection:

> For every original source-reachable included positive lower B whose right
> component is forgotten at `compact_lower_bounds_from`, and each authentic
> later linked call/output demand, the omitted right component's checking and
> cancellation consequences are already discharged or are represented by the
> exported **joint** ports/bounds under the same fresh-use map. In particular,
> for a same-i latent PUSH that can meet that forgotten POP, identify the
> actual surviving coupled representation or prove from its construction
> that this incidence cannot arise.

This is a necessary source/operational premise for the attempted direct
simulation, not an added hypothesis to H, an adopted exclusion or a claim of
absolute minimality among all proofs. One can prove H by another argument,
but this induction cannot cross this owner without that evidence. The required
evidence is narrower than a general declaration that compact schemes are
principal: one weighted record, its correlated ports, and its later demand.
All other original H cases remain OPEN.

## 5. Why selection, death and finalization do not repair the proof automatically

Type quantifier selection uses actual levels above the boundary and excludes
the actual non-generic set (generalize/mod.rs:900–921).
Stack selection scans nonempty PUSH entries at covariant compact occurrences
of those selected coordinates
(`generalize/core/stack_ids.rs:23–49,72–180`).
After `sorted_stack_quantifiers`,
`extend_declared_all_stack_quantifiers` also includes enumerated IDs whose
machine fact has subtractability `All` (`generalize/mod.rs:867–888`).
Thus the selection happens *after* the right component in §4 has been
forgotten. One cannot use the selection criterion as proof that its input
preserved the consumer's demand.

The early death pass has declared-ID, live-covariant-PUSH, declared-All and
non-generic exemptions (core/prune.rs:39–77).
The later generalization pass removes every enumerated ID outside the selected
set (generalize/mod.rs:177–238), and ancestor finalization repeats selection
and pruning (837–864). `without_ids` drops entries, not their global filter.
These are real implementation decisions, not discharge certificates for
future demand.

Concrete negative Stack projection may convert filter/PUSH families into an
ordinary row and recurse on the inner tail with only the outer weight
(type_nodes.rs:545–582). It supplies a possible structural replacement,
but does not prove that a shared symbolic tail has the same future checks or
that provider/output correlation survives the replacement.
Principal variable finalization then sets the global filter to All
(compact/finalize.rs:586–603,837–839).
The exported Scheme has no machine filter table
(`generalize/finalize.rs:3–27`; `poly/src/types.rs:17–23`).
The earlier local filter-registration induction therefore stops at precisely
this lifetime boundary.

Finally, the census/pruner does not traverse neutral family-argument handles
inside weights, while scheme finalization and instantiation clone them.
The parameterized-effect closure question from global hygiene §5 persists.
No nullary calculation here excludes it. Residual merging/source-coordinate
feedback, alias count subsumption, recursive/role bounds, ancestor substitution,
imports, extrusion and qualifying parent/copy intrusion also remain evidence
dependencies. Literal retained-ID cloning does not settle any discarded record.

## 6. Economy audit, separate Y3 gate and next action

The prior forward proof and nested falsification left source-owned generalized
discharge untouched. Before this attempt the economy audit was applied:
the original safe subtraction, future-check and natural-generalization claims
remain A/B. Reconstructing authentic provider/output incidence from a
post-projection row or equal family would be D; the owning constraint record
already has the actual directed pair and derivations. This new method traces
that pair directly and locates the exact projection that stops reading it.
It neither reclassifies H as optional C nor licenses retaining new metadata
or changing Oracle/Y3 semantics.

The obstruction now calls for evidence at that owner rather than another
equivalent abstract attachment lemma. No proposed representation is adopted.
A canonical certificate could be assessed only if the primary establishes
what source-known fact is discarded and obtains any required design authority.
A claim/support record by itself is not a certificate of all future-use
observation.

The [Y3 owner crosswalk](../progress/2026-10-11-effect-hygiene-y3-owner-crosswalk.md)
remains a separate gate: negative concrete formal preflight and the paired
constructor reject the row; no live coupled annotation PUSH, same-call
activation or output POP is emitted. Complete Call is separately unresolved.
No Oracle-local lemma enables that missing branch.

**One next action:** primary assign a source-owner packet at
`compact_lower_bounds_from` and the production replay/instantiation owners:
produce or rule out a source-generated B with the forgotten right POP and
same-instance latent PUSH, preserving its full source occurrence, provider,
call, output and tail incidence; if reachable, derive its actual exported
replacement observation. Keep H and the independent Y3 construction gate OPEN.
A fresh independent referee, appointed by the primary, is required before
consuming any local lemma or promoting a status.

## 7. Independent review

An independent `prover` review found no blocking or major issue in the local
weight derivations or the claim that positive lower compaction omits the
right-weight component. The reviewer confirmed the ordinary argument
reversal, the distinct pure-Effect transformation, same-ID count ordering, and
that the nested annotation's matching POP wraps the returned Unit Value rather
than the returned Function. The reviewer recommended one precision correction,
now incorporated in §5: after `sorted_stack_quantifiers`,
`extend_declared_all_stack_quantifiers` also adds enumerated IDs whose machine
fact has subtractability `All`.

An independent `spec_auditor` found no conformance issue in either this proof
or the bounded three-run Oracle observation note. These reviews certify only
the stated local derivation and observation limits. They did not establish
same-instance B reachability, a published hygiene failure, universal H,
complete Call, soundness, principality or Y3 production conformance.

## 8. Checks, resources and runtime

Changed path: this exact leased note only. No compiler, test, design, task,
index, configuration, question-board or other worker file was edited.
No Git command, Oracle invocation, build/test, executable probe, network query,
child delegation or external communication ran. Internal messages went only
to the delegating primary. No jobs were launched by this leaf.

Commands/results: bounded `cat`, `sed`, `rg` owner/rule reads and Python
standard-library SHA-256/document inspection. Initial large captures truncated;
decisive sections were reread in bounded ranges. Two guessed owner paths
(`machine/projection.rs` and `core/quantifiers.rs`) were absent; subsequent
symbol lookup found the real query and quantifier owners. These failures do
not supply evidence. Final document whitespace/local-link check and dependency
snapshot recheck passed. No executable source-reachability evidence was acquired.

One bounded constructive Sol attempt; no equivalent retry or escalation.
At most five lightweight read commands were requested concurrently in the early
read batch; subsequent reads/checks were sequential. Heavy processes,
measurement samples, executable search seeds/ranges and test runs: zero.
Aggregate CPU/RSS and total reasoning wall time were not instrumented; the
packet supplied no numerical quota. No shared verification capacity was used.

Requested model/effort: `gpt-6.1-sol` / `high`.
The inspected configuration registers an unpinned prover with Sol/high defaults.
Observed effective model/effort: unknown, because runtime metadata was not
available. The actual parent-assigned leaf identity ran; no Astra/override
success or hot-reload claim is made.

## 9. Dependency snapshot and commit packet

SHA-256 pins inspected bytes, not Git blob identity. Oracle revision identity
and Y3 baseline are primary-supplied. No Git comparison was performed; baseline
equality remains primary-owned. Direct dependencies were rechecked at freeze.

| Dependency | SHA-256 |
| --- | --- |
| `AGENTS.md` | `89403c6fca2e3c351d7194340e627c3dfd092c8e623ec5e8532ce6e1d5ff3f4d` |
| `rules/orchestration-budget.md` | `a0a114b589e8920af8e8fd871d15f63d68b735fc1a553f5a89952b1eab8489e5` |
| `rules/agent-orchestration.md` | `3b1e9c5a083ae4257d3d8ad4bacadf55adf07997d0b02c10bcbec4ccda3258be` |
| `rules/research-lab.md` | `3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69` |
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` |
| `rules/compiler-engineering.md` | `4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9` |
| `rules/git-concurrency.md` | `2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6` |
| `.codex/config.toml` | `dae388e4e811c346727ec6688472c7fcf6341ddc5466168cfaa03fdcc0b8e17a` |
| `.codex/agents/prover.toml` | `485a26c7409e16c692ad10095031ab0e7084726ec5da5666082b3bbc4a5daf98` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-10-concrete-effect-annotation-implementation.md` | `3a3186723cd93edd2f767a7e4a481cb6dbed701fc749502e640071f65a4d89ae` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/theory/2026-10-11-oracle-global-effect-hygiene-proof.md` | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| `notes/progress/2026-10-11-effect-hygiene-y3-owner-crosswalk.md` | `c686583391997552abd1d69d0dc4167784c498f67c22fdc6e127b378d442e37a` |
| `notes/progress/2026-10-11-oracle-effect-nested-scheme-falsification.md` | `fd6cb9ea14adb8bbe873d118dae3e52bf498696d9caf37be2155c346e6b86ecb` |
| `/tmp/yulang2-oracle-read/crates/infer/src/annotation/constraints.rs` | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
| `/tmp/yulang2-oracle-read/crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `/tmp/yulang2-oracle-read/crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `/tmp/yulang2-oracle-read/crates/infer/src/instantiate.rs` | `876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c` |
| `/tmp/yulang2-oracle-read/crates/infer/src/generalize/mod.rs` | `03bfda4e4997347b59483de96eca652b67477639fc363e0890d546d2cf36fcef` |
| `/tmp/yulang2-oracle-read/crates/infer/src/generalize/finalize.rs` | `a8e5a1c8e6ad57d1fac7e25a1ab6a329093e5c76e6d84c0625c124c349f07492` |
| `/tmp/yulang2-oracle-read/crates/infer/src/generalize/core/prune.rs` | `05e6d343c90f1bbc77def8e50f9acb746451ceb3889bb50dd17342621afba26d` |
| `/tmp/yulang2-oracle-read/crates/infer/src/generalize/core/stack_ids.rs` | `adb9cd35d483af62ea0c3ebc572b9a0535761f3bfb99aedad49b371833b95f8f` |
| `/tmp/yulang2-oracle-read/crates/infer/src/compact/collect/mod.rs` | `828fa02521e2426297a9369df2fd9ef1560b7403a668ddfe881063ef16bdfd40` |
| `/tmp/yulang2-oracle-read/crates/infer/src/compact/collect/type_nodes.rs` | `96dc38a9a05c447f019bb0421e0b37057d283026ba87bce121bb33959b0d8ab2` |
| `/tmp/yulang2-oracle-read/crates/infer/src/compact/finalize.rs` | `53a2452b109ddb461d98f6124d410fa2e771e700e272084f3b83ed87b4f3d272` |
| `/tmp/yulang2-oracle-read/crates/infer/src/constraints/mod.rs` | `ad3cf5fd60462cb1a08ef1a5d6fc57c4fd640148597bc3b331d09729616d8392` |
| `/tmp/yulang2-oracle-read/crates/infer/src/constraints/directed_weight.rs` | `de71ae7ed5a5aed22f3e5d35ca0ebcd52872ff965fcc22523a662cffdd6f28db` |
| `/tmp/yulang2-oracle-read/crates/infer/src/constraints/machine/propagate.rs` | `8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086` |
| `/tmp/yulang2-oracle-read/crates/infer/src/constraints/machine/bounds.rs` | `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7` |
| `/tmp/yulang2-oracle-read/crates/infer/src/constraints/structural_kernel/access.rs` | `ad90bc1444be22df6080c7131ef49fedace884178c375af84ecb09416b38740f` |
| `/tmp/yulang2-oracle-read/crates/infer/src/constraints/proof/mod.rs` | `bc0f3fbcf8f5ed01245e74283d3fd9cb13aa1713aff252a1847fde76b11b8e03` |
| `/tmp/yulang2-oracle-read/crates/poly/src/types.rs` | `9211e62291b82e71e1b78763b83fe9f1d81e0fe4396d9e12d42e9a4a9b13b47c` |

Commit packet:

- Exact leased/change path: `notes/theory/2026-10-11-oracle-generalized-observation-proof.md`; frozen, writes stop at handoff.
- Baseline SHA: `35e88c8113c9c6516e260170503bea753e4ede6`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1` supplied by primary.
- Changed dependency hashes: none observed between inventory and final recheck; none edited by this leaf. Baseline equality remains primary-owned.
- Review status: independently reviewed bounded derivation with the minor §5 precision correction incorporated; no H closure, source-qualified counterexample, source reachability certification, implementation conformance or production authority.
- Checks already run: static owner/rule/authority reads, SHA-256 inventory/recheck and leased-document whitespace/local links. Zero builds/tests/Oracle executions/probes/measurements.
- Proposed research-checkpoint message: `research: isolate Oracle generalized directed-demand projection premise`.
- Shared-record deltas left for primary/curator: link the root-POP four-port derivation; record right-component forgetting at positive lower compaction and its same-instance source-reachability/replacement premise. Keep original H, complete Call, soundness/principality, general admission, Y3 negative constructor/call/output and F5 gates OPEN. No shared record was edited.

# Oracle direct callback return: projection inclusion and the simplification boundary

Date: 2026-10-12
Status: frozen research checkpoint; independent review pending; H remains OPEN
Claim class: bounded source-construction derivation, with an explicit unresolved simplification premise
Primary baseline: `016cca26609ccd17364c31ba2b5a9e91f80dd87f`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle checkout: `/tmp/yulang2-oracle-read`
Exclusive lease: this file; leaf, no delegation or Git mutations

## Objective and frozen statements

The assigned seam is the annotation-positive callback Function in
`my direct(cb: (() -> [tick] ())) = cb`: determine whether its actual
returned-value projection admits that Function, then locate the exact owner
needed to retain its positive result-Effect view through simplification.
The [source use-chain audit](../progress/2026-10-12-oracle-direct-return-use-chain.md)
and the primary's accepted constructor evidence are inputs. The earlier printed
scheme and pure final-call output supply neither raw records nor a proof.

Authority is [annotation effect hygiene](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§1, subject to [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. The original H is fixed by
[the global hygiene note](2026-10-11-oracle-global-effect-hygiene-proof.md) §1:
for every successfully lowered Oracle source program, every successfully
lowered composed-negative concrete annotation occurrence, its original lexical
scope and binders, every actual copy/instantiation, and every actual call/output
route involving that occurrence, its authorized subtraction removes only the
contribution attached to that exact instance on that route; independent
same-family contributions survive. Symbolic tails stay connected, current and
future lowers encounter the retained check, and occurrence, attachment, scope,
provider/call binder and correlated residual lineage survive copying and
generalization up to the actual consistent fresh-use renaming. Successful
lowering does not imply successful inference/publication. Incorrect lowers
require an authentic check/error and safe nonpublication. H's original source
domain, quantifiers and exclusions are unchanged.

The bounded statement derived here is **P**. Select the named-lambda constructor
slice for the displayed direct-return definition, with its annotation connection,
initial fresh skeleton and bare local-Name body. Let c be its fresh formal Value
coordinate, Y its distinct fresh skeleton body Value, A the annotation-positive
Function, x its result-Effect coordinate and α the annotation's fresh SubtractId.
Assume these native operations drain normally, without a terminal proof/resource
failure, and the query/record admission completes. On the fresh direct c→Y
route established below, the annotation lower A at c is considered by replay;
the resulting A lower at Y is projectable, and collecting that lower visits A's
positive result-Effect stack. This is a statement about that bounded source
construction and its native consumer, not every context sharing x or every
subsequent transformation of the complete scheme.

No actual record dump for the earlier execution was recovered. P does not assert
its numeric IDs, record counts, full stored scheme, actual simplifier substitution
list, instantiated provider, final-call Effect, complete Call, soundness,
principality or H. It does not assume that subtype emission alone entails a live
bound, or that an admitted bound alone entails scheme export.

## 1. The source return root is Y

Oracle paths in this note are relative to the pinned checkout. All citations
refer to inspected source owners, not inferred behavior from their names.

`lowering/expr/lambda.rs:665–688` allocates `param_value` with
`fresh_type_var`, then connects its annotation. This is c. At 745–748, a named
definition with `self_value` allocates its skeleton. The owner at 1127–1143
allocates distinct layer outputs and `body_value`; the latter is Y.
`arena.rs:34–38` registers each new coordinate at the current level, and
`poly/src/types.rs:113–117` advances the type-variable counter. Thus c and Y
are distinct in this allocation slice, assuming no ID exhaustion. The skeleton's
initial links connect its own body/layer coordinates; they do not identify c
with Y.

Returning the resolved local Name initially yields c, as established by the
accepted source audit. However, `lambda.rs:797–808` then emits
`subtype_var_to_var_with_origin(c, Y, skeleton_value_origin)` and replaces the
body's Value coordinate with Y. With no body annotation,
`skeleton_value_origin` is `unknown_internal`. This is a real native subtype
operation: `lowering/expr/constraints.rs:99–106` allocates the two variable
endpoints and calls `InferArena::subtype`.

`lambda_parameter_output_predicate_constraints` at `lambda.rs:1571–1578`
returns an empty enclosing-output predicate for a Function parameter. The bare
Name performs no callback application. `wrap_lambda_param` at 954–968 therefore
constructs the direct Function with the replaced body Value Y as its positive
return endpoint, through the empty-predicate output constructor. The initial
skeleton also contains a distinct layer output Value and links it with Y;
neither root can be replaced by c in a proof merely because the Name resolved
to c.

## 2. Admission and replay, rather than a raw bound scan

The accepted annotation construction is independently visible at
`annotation/constraints.rs:134–144,363–389,424–470`: it emits A→c with an
Annotation origin, where A is `Pos::Fun` and its result Effect is the positive
stack of x carrying PUSH α. The paired negative Function connects c's upper
ports. This pair does not emit an enclosing direct-call predicate.

`arena.rs:90–92` forwards subtyping to the machine. At
`constraints/machine/entry.rs:493–499`, native subtyping enqueues the root and
drains the queue. The canonicalizer at 1092–1116 discards Bot, Top and equal
variable endpoints; a Function→variable root is none of those. The root
admission at 1349–1428 records its origin and queues semantic work. The fresh
annotation target c and fresh source slice provide the first admission, rather
than an assumed duplicate whose old execution might be unknown. The drain at
970–996 steps queued work until empty or proof-terminal failure.

`machine/propagate.rs:151–163` sends a non-variable lower with a variable upper
to `add_lower_bound`. That owner at `bounds.rs:630–715` extrudes, checks the
incoming filter, inserts the semantic bound, admits the projection index and
registers provenance/projection clauses. Extrusion at 4523–4533,4547–4592
walks A's children and adjusts levels; it returns the same positive endpoint,
and does not replace A or its stack ID. Alias-cycle subsumption requires a
positive variable endpoint; it cannot subsume A. `TypeBounds::add_bound` at
`constraints/mod.rs:2510–2618` stores an ordinary lower with its record ID.
Thus normal completion admits the A-at-c record, not just its emitted
constraint.

For the subsequent fresh c→Y root, `propagate.rs:106–132` admits the alias
lower at Y and the upper at c. In the selected fresh slice, c previously has
the annotation's Function upper, while Y is a skeleton coordinate newly
allocated after c's annotation; no earlier c→Y variable upper in that slice
supplies a subsumption or canonical-duplicate shortcut. This qualification is
essential: the derivation is not a theorem about arbitrary externally supplied
preconstraints or an already existing covered duplicate.

`bounds.rs:964–1033` gives the newly admitted c→Y upper an original Direct
upper-replay claim when its producer has no qualified parents. The fresh root
admission has none. This claim is uncovered: the production insertion of a
live coverage state is the unweighted effect-Row reduction owner at
`constraints/row_effect.rs:490–525`, originating in the Row-specific reduction
at 237–330. c→Y has a `Neg::Var` endpoint. It does not enter the `Neg::Row`
branch at `propagate.rs:132–140`, so this source route supplies no such
coverage state. Claim presence and live coverage are distinct facts.

The upper replay at `bounds.rs:3582–3644` enumerates both ordinary and evidence
lower records at c, including A. `proof/mod.rs:9270–9359` prepares its pair.
Composition at 9439–9525 requires generic replay when an upper claim is
uncovered; the Direct c→Y claim establishes that condition. A→Y is neither a
trivial equal-variable constraint nor the evidence-only variable-to-variable
case at `bounds.rs:3814–3830`. Native replay therefore submits its real
Function→Y consequence; the same normal drain/admission argument admits it.
The index and claim-parent owner at 3832–3890 registers its exact replay
parents before the queued consequence is consumed. No complete replay theorem
for arbitrary rows or aliases is imported by this specific pair argument.

## 3. Why this Function lower is projectable

The actual projection enumerator is
`constraints/structural_kernel/access/legacy_read_view.rs:214–223`, then
`VarBounds::projection_lower_records` at `constraints/mod.rs:2664–2672`.
It includes both evidence and ordinary lower IDs. It does not scan only live
ordinary lowers and it does not search all source constraints.

The A-at-c root is unclaimed unless later projection claims establish a ledger.
It is returned as `Unclaimed` by `proof/mod.rs:10014–10020`. If a ledger is
established, `bounds.rs:2600–2640,2692–2717` bootstraps the root's independent
`ConstraintOrigin`; a claim whose producer is the A→c root would defeat that
independence check, but that root is Function→variable and takes only the
lower-bound branch. It emits no upper bound/upper claim with that producer.
`bounds.rs:2476–2565` retains a Standalone independent clause. Such a clause
evaluates `IncludedExact` at `proof/mod.rs:11735–11742,11906–11914`.

For the A-at-Y consequence, the registered qualified replay incidence has
`ReplayConjunction { lower_premise: A-at-c, upper_premise: c→Y-upper }`.
Its actual constructor is `bounds.rs:1188–1207`; its evaluator at
`proof/mod.rs:11742–11765` evaluates both premises. The first is included as
above. For the second, upper-record evaluation at 11648–11666 reaches its
Direct claim, whose uncovered root evaluates IncludedExact at
11883–11902. The conjunction is therefore included. Extra excluded arms do
not defeat an included arm; the formula walk at 11705–11725 returns on an
included exact arm. Subject to successful preflight, `project_lower` at
9975–10129 returns `Included`, rather than `Excluded`.

`structural_kernel/access.rs:862–898` consequently keeps this lower.
`compact/collect/mod.rs:848–877` clones its bound and passes it to
`compact_lower_bounds_from` at 898–918. The alias-only lower c at Y is
insufficient by itself: `compact_pos_bound_id` at 1104–1109 emits a secondary
variable occurrence and does not collect c's Function bounds recursively.
Positive alias expansion at `generalize/mod.rs:662–699` likewise adds eligible
variables, not Function bounds. The admitted, included A-at-Y consequence is
the actual bridge that avoids that omission in this bounded route.

## 4. Exact α retention boundary

Collection of A visits its positive result-Effect port at
`compact/collect/type_nodes.rs:13–24`. The stack branch at 84–95 composes its
PUSH α with the incoming weight and visits x positively. The fresh c→Y
replay contributes an empty outer weight. The negative annotation Function
in the direct argument separately visits x negatively; its filter can become
a concrete Row prefix with x as tail at 543–566. Those are real collector
constructors. They establish a weighted positive x view and a negative x
view in the local inputs; they do not by themselves prove what the fully
merged scheme retains.

The complete collector merges all lower Functions and all x views. Function
merging at `compact/merge/entries.rs:288–307` merges the result-Effect port
positively; same-variable merging combines weights by parallel union.
`poly/src/types.rs:565–599` intersects incoming floors before retaining stack
entries. Thus seeing one PUSH in one visited view is not already a theorem
that the merged return port retains that entry with the same family.

The next simplification owner is
`generalize/mod.rs:110–132`, before `prepare_stack_cleaned_compact_root`
at 805–834. `compact/analysis/mod.rs:164–201` runs pinned-interval collapse,
polar/co-occurrence fixed points, sandwiches, then another fixed point.
`occurrence/mod.rs:120–133` flips Function arguments and preserves results,
so a surviving positive x and negative x protect x against polar elimination.
That observation is insufficient for the full simplifier:

- `occurrence/mod.rs:356–397::register_sandwich_flattening` can remove a
  bipolar variable if its positive and negative co-occurrence sets share an
  `AlongItem::Exact` other than itself.
- `occurrence/substitution.rs:109–125::rewrite_type_vars` deletes the entire
  weighted occurrence when the rewrite target is `None`; its α entry is
  deleted with it. A `Some` target instead retains the weight until any
  same-target weight union.
- The closed-row effect-coordinate owner at
  `annotation/constraints.rs:602–620` can reuse an incoming closed-row
  coordinate. Coordinate freshness or absence of other x bounds therefore
  cannot be inferred from α freshness.

The smallest unresolved premise is **S**: in the complete, source-reachable
compact root supplied to this simplifier, the positive returned-callback
Effect occurrence reached above retains a nonempty α PUSH through weight
merging, and its successive substitution/co-occurrence/sandwich images either
retain that occurrence (with the actual representative and weight), or have a
proved equivalent positive Effect observation preserving the same α lineage.
For direct physical retention the decisive data are that occurrence's merged
weight, x's positive/negative co-occurrence sets, and its actual rewrite image
at each fixed point. Bipolarity alone does not establish S. A sufficient
nonremoval test would exclude a shared Exact sandwich and a later `None`
image, but that test is not assumed or proved for the complete source root here.

No simplifier exclusion of this source occurrence has been established either.
The code's deletion branch is a falsifier target, not a source-qualified loss
witness. No equivalent-view theorem is supplied by calling the deletion an
optimization. Quantification, stack cleanup at 805–834, ancestor
simplification, binder census and instantiation/root POP follow S and remain
outside this packet.

## Economy audit, checks and handoff

The previous constructor and use-chain methods left the complete generalized
observation unproved. This packet changes method to native source-root
admission, actual replay incidence and the projection formula consumer. P is
the resulting bounded advance; S is not H closure. Under
`rules/compiler-engineering.md::Natural compiler behavior and proof-obligation
economy`, the required hygiene/generalization premise remains A/B. Treating
the same-bound record as a contribution identity would create reconstruction
debt D; no such relation or new source restriction is introduced. Another
assumed-transition model or a renamed gate would leave S untouched.

Only static `cat`, bounded `sed`/`rg`, dependency hashes and leased-note
integrity checks were used. No Oracle invocation, instrumentation, probe,
build, test, measurement, external contact, Git mutation or child launch ran.
The first broad captures were truncated; decisive owners were subsequently
read in bounded slices. Some guessed source globs were absent and were
replaced by exact owner searches. No heavy verification resource was consumed.
Reads were lightweight shell processes, with one batch of four independent
reads; CPU/RAM and elapsed time were not instrumented. The invocation budget
was zero and remains zero.

Requested routing: normal `gpt-6.1-sol` / `high` proof leaf. Inspected
`.codex/config.toml` supplies those defaults; `.codex/agents/prover.toml`
has no model/effort pin. Observed effective model/effort: unknown, because no
runtime metadata was supplied. No Astra or hot-reload claim. The primary owns
review, classification/promotion and shared-record integration.

One next action: independently review this frozen P derivation, then assign
the exact merged compact-root/co-occurrence image in S to its source and
simplification owners under the existing execution budget. Keep H OPEN.

## Commit packet

- Exact leased path: `notes/theory/2026-10-12-oracle-direct-return-projection-proof.md`.
- Primary baseline: `016cca26609ccd17364c31ba2b5a9e91f80dd87f`;
  Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Dependency hashes: listed in the snapshot below; no dependency was edited.
  Baseline identities are primary-supplied. Equality to the primary Git
  revision remains an integration check; hashes pin inspected bytes.
- Review status: producer derivation, independent review pending; P bounded,
  S unresolved, H OPEN. No production or complete-scheme certification.
- Checks: static source reads/searches, dependency snapshot, note whitespace
  and relative-link integrity. No execution/build/test or measurement sample.
- Proposed message: `research: derive Oracle direct-return projection inclusion`.
- Shared-record deltas for the primary/curator: record c→Y as the actual return
  ownership seam and the included A-at-Y replay-conjunction route; replace the
  generic projection uncertainty with S's merged-weight/co-occurrence/rewrite
  premise. Keep full scheme/instantiation observation, H, complete Call,
  soundness, principality and F5 gates OPEN. No shared record was written.

SHA-256 snapshot at freeze; Oracle paths are relative to
`/tmp/yulang2-oracle-read`. This snapshot was collected after derivation; it
is not a before/after stability check of the entire reading interval.

| Dependency | SHA-256 |
| --- | --- |
| Global H note | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| Direct-return use-chain note | `bafbfe7e08c0a6ce80529b6d78f8be698496b824dec0cc2d5a96b4150c34a3a8` |
| Annotation effect hygiene design | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| Oracle `crates/infer/src/arena.rs` | `e407480ee4984e24ce214543bfe23ed83e34883129487878df034090688bd9db` |
| Oracle `crates/infer/src/annotation/constraints.rs` | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
| Oracle `crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| Oracle `crates/infer/src/lowering/expr/constraints.rs` | `2800250aa516c519d91aa11b0d46455f0a86f14a009be3588c7e039d2c5cbe20` |
| Oracle `crates/infer/src/constraints/machine/entry.rs` | `00c70ca0938b24d4d2dd38de6598fe54217aebd28150ac279b52839046b340b8` |
| Oracle `crates/infer/src/constraints/machine/propagate.rs` | `8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086` |
| Oracle `crates/infer/src/constraints/machine/bounds.rs` | `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7` |
| Oracle `crates/infer/src/constraints/mod.rs` | `ad3cf5fd60462cb1a08ef1a5d6fc57c4fd640148597bc3b331d09729616d8392` |
| Oracle `crates/infer/src/constraints/proof/mod.rs` | `bc0f3fbcf8f5ed01245e74283d3fd9cb13aa1713aff252a1847fde76b11b8e03` |
| Oracle `crates/infer/src/constraints/row_effect.rs` | `080472bb5dcb3f724e808ff745c6fba304cc7ea2574b8f8eb3e3466964e937c2` |
| Oracle `crates/infer/src/constraints/structural_kernel/access.rs` | `ad90bc1444be22df6080c7131ef49fedace884178c375af84ecb09416b38740f` |
| Oracle `crates/infer/src/constraints/structural_kernel/access/legacy_read_view.rs` | `d51ab100c247f34ccf94cd75af2c28e1bf845a9b1a8719780843b02ba2bd35a6` |
| Oracle `crates/infer/src/compact/collect/mod.rs` | `828fa02521e2426297a9369df2fd9ef1560b7403a668ddfe881063ef16bdfd40` |
| Oracle `crates/infer/src/compact/collect/type_nodes.rs` | `96dc38a9a05c447f019bb0421e0b37057d283026ba87bce121bb33959b0d8ab2` |
| Oracle `crates/infer/src/compact/merge/mod.rs` | `272b2ad1609a2e5fe8e17ca9f7924cd2211cb1196a72f94d6118f70d1d886569` |
| Oracle `crates/infer/src/compact/merge/entries.rs` | `d848f4034fa57cb7581e58116aba5e825b3f78c79d48bbd08800352dcfc3b10f` |
| Oracle `crates/infer/src/compact/analysis/mod.rs` | `9c5e7a863f25ad94b10b7c7865af523e30c6ac361847f20f58307f1025432463` |
| Oracle `crates/infer/src/compact/analysis/occurrence/mod.rs` | `7bf082236f7c90a33fe9d0084dc3d993d3528bb5a272a44265df8f27728e46a2` |
| Oracle `crates/infer/src/compact/analysis/occurrence/substitution.rs` | `b6d04c187a870892239db84a16360f700f7efaef4c0ba7b731d1389db31f9bf2` |
| Oracle `crates/infer/src/compact/analysis/sandwich.rs` | `8935b5f295e6c6bda2838385ac1fca8298fe964061a7c6d800f612b2bbcd16f2` |
| Oracle `crates/infer/src/generalize/mod.rs` | `03bfda4e4997347b59483de96eca652b67477639fc363e0890d546d2cf36fcef` |
| Oracle `crates/poly/src/types.rs` | `9211e62291b82e71e1b78763b83fe9f1d81e0fe4396d9e12d42e9a4a9b13b47c` |

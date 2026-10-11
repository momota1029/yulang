# Oracle global effect hygiene: constructive premises and the remaining source bridge

Date: 2026-10-11
Status: frozen research derivation awaiting independent review; original A/B gate remains OPEN
Claim class: source-derived local lemmas and a bounded obstruction, not an established universal theorem
Primary baseline: `b37bfab842dd3f0a39d15c358399a068ff8e3194`, branch `research/simple-sub-intrusion`
Oracle revision supplied by governing notes: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle inspected checkout: `/tmp/yulang2-oracle-read`
Exclusive lease: this file only; leaf, no delegation

## 1. Objective, authority and frozen original statement

Construct or refute the original universal source hygiene claim using the
actual Oracle constructors and consumers. The authority is
[annotation-effect-hygiene-integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§1, [concrete-effect-annotation-implementation](../design/2026-10-10-concrete-effect-annotation-implementation.md),
and [contextual-attachment-admission-design](../design/2026-10-10-contextual-attachment-admission-design.md)
§§3,6, subject to the [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. The reviewed singleton in
[negative-formal-effect-source-proof](2026-10-11-negative-formal-effect-source-proof.md)
§3 is an input, not the universal conclusion. No withdrawn callback result
is an expected scheme here. No new admission rule or representation is adopted.

The statement fixed by the assignment is **H**:

For every Oracle source program P in the original successfully lowered source
domain, every successfully lowered composed-negative concrete annotation
occurrence a, its original lexical scope sigma and binders, every actual
copy/instantiation u of that occurrence, and every actual function call/output
route k involving that occurrence, subtraction authorized by a removes only
the contribution attached to that exact instance on that route. An independent
contribution at the same resolved family survives that subtraction. Symbolic
annotation tails remain connected; every current and future concrete lower
reaching the relevant receiver encounters the actual retained check. The
occurrence, attachment, scope, provider/call binder and correlated residual
lineage remain appropriately identified through actual copying and
generalization, up to the actual consistent renaming of a fresh use.

"Actual" cannot be replaced by an independently selected provider, witness,
output or tail. Nested Function arguments reverse composed polarity; nested
Function results preserve it. Successful lowering alone is not a claim of
successful inference or publication: for an incorrect concrete lower, the
required conclusion is an authentic check/error and safe nonpublication, not
an accepted typing. Aborted/resource-terminal attempts need not restore every
internal table. The no-wrong-typing and no-inconsistent-publication obligations
remain. Successful suspension retains its accepted dependencies.

The only shared operational premises used below are the inspected source bytes,
normal completed method calls, and fresh arena allocation without ID exhaustion.
They are not hypotheses supplying attachment-to-call maps, complete replay,
generalization correctness or provider compatibility. Fresh allocation is
arena-local: IDs from different arenas are not equal merely because their
numeric fields agree. The universal original domain is not narrowed to the
local lemmas' domain. Runtime operation elimination, complete Call, global
soundness and principality are additional parent obligations; H is not their
proof. No execution or exhaustive search is evidence in this lane.

## 2. Actual constructors and the first structural induction boundary

Oracle paths below are relative to the inspected checkout. The owning paired
annotation constructor is `crates/infer/src/annotation/constraints.rs::lower_value_bounds`
(approximately 299–389). Each recursive Function constructs all four ports:
the positive Function uses negative argument ports and positive result ports;
the negative companion reverses those choices. This is a source-emitted paired
constraint construction, not an assumed diagram.

For each concrete non-wildcard result-effect row reaching
`lower_ret_effect_bounds` (424–470), `effect_row_stack` (657–690) allocates one
fresh `SubtractId` for the concrete atom set. `effect_atom_con` (741–748)
excludes symbolic variables from that set. `function_boundary_effect_stack_inner`
(602–620) uses the named tail when present, otherwise may share a closed-row
coordinate through the lowerer's closed-row table. **Shared coordinates do not
share the newly allocated stack ID.** The constructor registers its declared
stack fact and emits the positive PUSH view, negative filtered view and returned
predicate weight. `connect_effect_tail_exact` (639–654), when required, emits
both real variable constraints rather than erasing the tail.

Thus distinct executions of this set constructor in one live arena have
distinct IDs even when they resolve to the same E and same row coordinate.
This follows from `crates/infer/src/arena.rs:47–50` and
`crates/poly/src/types.rs::TypeIds::fresh_subtract_id` (123–126), whose counter advances.
It is a constructive source-allocation lemma, conditional on no counter
exhaustion. It does not establish how every independent source effect emission
is represented; a nominal row item need not have any stack ID.

The Function case returns **only its immediate `ret_eff.subtracts`**. It
retains nested `param` and `ret` port graphs, but does not return their
`output_subtracts` as this Function's call predicate. Tuple construction
concatenates its children's returned predicates. In particular, descending
into a returned Function with an E row constructs the nested stack graph but
does not by itself make that E predicate an immediate predicate of the outer
Function. An induction that equates all descendant negative occurrences with
the outer binder's call predicate has already failed here.

The separate signature owner is `crates/infer/src/lowering/mod.rs::lower_pos/lower_neg`
(571–663), with effect constructors in `lowering/signature_effect.rs`.
It reverses arguments and preserves results. Concrete positive rows retain
their actual tail (78–107); the result-effect negative owner (162–178)
constructs a boundary coordinate and filtered view. Ordinary argument-effect
negative construction (19–37) instead connects a concrete lower. These branches
are different actual constructors. A generic sentence about "all negative
rows allocate the singleton PUSH/POP pair" is false as a source description.
This is not a source-qualified counterexample to H: H's routes and authorized
subtractions still require their actual operational meanings.

The direct formal call owner remains the previously reviewed singleton spine:
`lambda.rs::connect_lambda_pattern_annotation` (1244–1341) retains the returned
predicate; `mark_lambda_param_call_predicate` (919–936) stores it on the newly
introduced local binders. `tail.rs::local_callee_def` (844–850) recognizes an
actual `Expr::Var` and resolved DefId. `make_app_with_origins` (535–624)
uses that exact callee's local record, extends the current latent predicate,
constructs the four-port demand, and forwards this call's return Effect and
callee evaluation Effect to the actual application Effect. The defined lambda
output owner (lambda.rs:1232–1237) wraps both result Value and Effect with the
frame predicate. A source alias or returned callee cannot be assigned this
route by guessing an equivalent row or a plausible provider.

## 3. Local retained-check induction discharged from production owners

The following is a derived **machine-local check-invocation lemma**, awaiting
review. Its conclusion is narrower than replay, acceptance, or H.

Fix one live Oracle machine and a completed successful mutation sequence.
Whenever a non-All filter F has been registered on v, every live semantic
lower bound of v admitted by the production lower-bound owner has had the
actual weighted filter routine invoked with F, either at registration or
insertion. Recursive variable encounters install the same obligation on the
encountered variable. A later live semantic lower is covered in the same way.
The statement is about invoked constraints/checks; any generated invariant
argument constraints still require their ordinary drain and error consumer.

Proof by induction on the two actual mutation events:

1. **Registration.** `bounds.rs::constrain_type_var_lowers_by_filter`
   (3213–3255) inserts F before traversing current lower records. For a new
   registration it invokes `constrain_weighted_pos_lower_by_filter` on every
   current lower with the genuine filter and bound provenance. An existing
   registration needs no second scan; those bounds were covered by its first
   scan or by subsequent insertions. Inserting before traversal terminates a
   repeated variable registration and retains the obligation for future bounds.
2. **New lower.** `add_lower_bound` (630–730) extrudes the actual incoming
   positive endpoint, checks its own left filter before erasing it, inserts
   the semantic lower, and on semantic change invokes
   `constrain_lower_bound_by_registered_filters` (3285–3301). That routine
   visits all filters retained on the actual target. The unchanged semantic
   lower case reuses the already covered endpoint/weight.

The early alias-cycle subsumption at 647–660 is not silently omitted.
`lower_var_alias_replay_cycle_subsumed` (4274–4295) requires an existing lower
with the **same positive variable endpoint** and equal alias keys. The key at
7190–7244 retains every ID, active PUSH presence and its family, POP presence,
and right ID set, while discarding multiplicities. The checker at 3303–3360
reads active stack families and the exact positive endpoint, not POP counts or
PUSH multiplicity. Equal keys therefore give equal concrete checking inputs.
The retained existing lower supplies the check for that omitted alias. This
argument justifies filter coverage only; it does **not** justify count
subsumption for future cancellation or every downstream output.

A search of `.add_lower(` in the constraints source located one production
semantic insertion owner, the call at `bounds.rs:676`; the additional direct
writes inspected at 230,2183 and in the later fixture section are test-only.
This is static owner coverage, not an executable census of all callbacks.
Proof-terminal exits before the registered-filter call do not supply a
successful completed mutation/publication premise.

`check_and_erase_upper_left_filter` (3193–3210) registers on the source receiver
after checking active stack families. `check_and_erase_lower_left_filter`
(3174–3191) checks the actual weighted incoming lower before erasure. Negative
Stack normalization (`propagate.rs:38–56`) checks before consuming the wrapper.
The recursive checking owner traverses Row, Union, Stack and NonSubtract,
registers on variables, and checks concrete effect heads and payloads. It
deliberately does not descend through a Value Function. This prevents a
Value-bound check from acquiring authority over latent Function ports.

This induction discharges a real activation premise absent from a model that
only stores filters. It stops at the live machine boundary. It does not show
that all source routes reach that receiver, that a queued payload comparison
is drained, or that generalized copies reconstitute the same check.

## 4. Actual propagation, residual feedback and per-use identity

`propagate.rs:11–38` prefixes source-emitted positive Stack/NonSubtract
operations. The Function case (210–263) swaps Argument Value/Effect directions
and preserves Result Value/Effect, with the separate pure-argument passthrough
using `both_from_right`. It does not equate those flows. `ConstraintWeights`
in `constraints/mod.rs:3566–3607` emits those transformations and ordered
lower/upper replay composition. `directed_weight.rs:145–170,399–419` composes
only the entry selected by its exact ID. For i != j, a POP of i leaves the j
entry unchanged, regardless of family equality. This is the established local
algebraic step, not a newly asserted global contribution-preservation theorem.

Actual weighted row residual construction is
`constraints/row_effect.rs::add_effect_row_upper_bound` (approximately 87–230).
It checks the incoming allowed filter, computes retained concrete heads and
residual weight, and keys its gamma by source coordinate, sorted retained
families and residual weight. It then **enqueues both** the source-to-head/gamma
feedback and the exact gamma-to-this-tail relation; a reused gamma retains the
new derivation and each projection. Thus gamma is not just a stored name with
no consumer, and distinct source coordinates are in the actual cache key.

Conversely this Oracle key is not an independent source-attachment, provider
or constructor-lineage tuple. Several derivations may share one key/gamma.
The code retaining derivations proves their storage and feedback generation;
it does not prove that merging those routes preserves every original
contribution correlation. No marginal output witness is chosen here.

There is also a derived **per-use stack renaming lemma** for the graph actually
passed to `SchemeInstantiator`, not for the source graph before generalization.
`instantiate.rs:621–647` allocates all scheme variables, recursive variables
and quantified stack IDs through one instantiator before cloning. The map at
741–768 allocates once for each freshened ID, then reuses it. `clone_pos`,
`clone_neg` (849 onward), and `clone_stack_weight` (983–1001) use that same map
through all four Function ports, filters, floors, POPs, PUSHs, and cloned
neutral family arguments. Node maps preserve already cloned shared children.
Induction on these structural clones therefore preserves equality of retained
IDs and sharing within this use; distinct freshly allocated quantified IDs
remain distinct, including when their families agree. Separate instantiators
give independent quantified IDs in the target arena. `clone_subtractability`
(946–981) preserves family paths and clones their actual type arguments.

Unquantified IDs are reused in ordinary instantiation (`freshen_unmapped=false`),
so the lemma cannot say that every ID is independent between uses. Valid scheme
construction must establish which source authority is quantified versus
shared. Imported free type variables additionally use the actual boundary map;
they cannot be assigned arbitrary fresh provider witnesses. Recursive bounds
are restored as actual constraints (`clone_recursive_bounds`, 1004 onward).
This is a genuine copying-constructor lemma with explicit limits.

## 5. Decisive unfinished Oracle premise: generalized observations

Direct source induction and direct clone induction meet at a specific
transformation that neither lemma proves correct. The Oracle does not export
the live constraint machine unchanged:

- `generalize/core/stack_ids.rs:23–49,76–179` chooses quantified IDs using
  **covariant live PUSH occurrences at quantified coordinates**, following
  Function polarity. The selection is not "all IDs introduced by negative
  annotations".
- `generalize/mod.rs:177–238` prunes IDs outside that selected set, with the
  separately declared-All extension at 867–888. `core/prune.rs:504–557`
  removes selected ID entries recursively through all Function ports and
  other structures. Its dead/liveness argument is essential for H.
- `compact/collect/type_nodes.rs:1–115` distributes carried weight only to
  result ports of a positive Function; its negative Function case at 117–135
  carries it into argument ports instead. `compact_neg_stack_effect`
  (545–562) can turn concrete filter/stack families into a row prefix and
  traverse its inner tail with the outer weight. This is a structural
  projection, not a literal persistence of every source filter registration.
- `compact/finalize.rs:586–603,837–839` explicitly resets a compact variable
  weight's filter to All before creating principal Stack nodes. The exported
  `Scheme` (`crates/poly/src/types.rs:17–23`) contains predicate, type/stack
  quantifiers, role predicates and recursive bounds; it has no live machine
  lower-filter table.
- `instantiate.rs:770–787` adds POP count `u32::MAX` for every quantified
  stack ID to the cloned root predicate. This is an actual new transition,
  beyond renaming; singleton one-PUSH/one-POP arithmetic does not justify it.

The precise remaining necessary premise is:

> For every original source-reachable generalized boundary and actual use,
> the Oracle's compaction, polarity-dependent pruning/quantification,
> principal finalization and quantified-root POP construction preserve the
> complete coupled observation of that boundary's actual provider/call,
> current/future lower checks, independent contributions and latent output
> routes. Any discarded ID/filter obligation must be discharged or
> represented by the actual exported structural contract for all future uses;
> any merged residual must preserve its shared-source correlations.

This is not assumed in H or the local lemmas. The observed removal of a filter
or ID is not itself a counterexample: a discharged obligation or equivalent
exported row may justify it. Conversely, syntactic cloning of the resulting
scheme is not that justification. The predicate stored on direct local
binders does not cover every nested/returned route by structural induction.
No source-qualified counterexample was established in this static packet.
The universal H is neither proved nor refuted here.

A further direct pass through the projection owners gives a smaller separation
than treating the whole compact pipeline as opaque. For a concrete nullary
positive `Con(E, [])` that actually reaches `compact_pos_row_item`
(`compact/collect/type_nodes.rs:260–286`), the returned row item is E with empty
arguments for every carried weight. POPs affect neither its family nor its
existence. `compact_pos_row` (404–450) includes that item in the positive row.
This proves preservation at that concrete constructor; it does not establish
that each independent source contribution reaches it. The scheme collector
first queries `scheme_projectable_lowers_in_scope`
(`compact/collect/mod.rs:848–877`), then compacts only the returned lower bounds.
An all-source proof therefore requires coverage at that projection owner,
before the row-item lemma can be applied. A raw bound-table scan is not the
actual scheme construction.

There is also an exact binder-closure audit target for the original domain's
parameterized effect operands. `collect_all_stack_ids_in_type`
(`generalize/core/stack_ids.rs:182–234`) enumerates IDs in each compact
variable's weight and then traverses ordinary compact children; it does not
descend into neutral type-argument handles inside that weight's
Subtractability. Pruning at `core/prune.rs:504–557` has the same visible
structural boundary. However, `generalize/finalize.rs:275–350` clones those
family arguments between arenas, and `instantiate.rs::clone_subtractability`
clones them through the per-use variable/ID maps. `annotation/constraints.rs`
752–768,799–816 permits invariant constructor arguments by paired recursive
lowering, including Function-shaped arguments. Thus the remaining precise
question is whether source-reachable surviving family arguments can contain
an ID outside the scheme's census, or whether an actual earlier owner always
discharges/exposes such IDs. The code above does not supply that closure law.
An AnnType constructor shape alone does not prove a successfully lowered
source witness or an incorrect published result; neither is claimed here.
This question is narrower than another abstract attachment theorem and keeps
all original parameterized cases in H.

The permanent ordinary Simple-sub reference is
`/home/momota1029/rust/simple-sub-reference` at the primary-recorded
`9bae772624c23b52a93c1b226157e16898b4d9db`. Its actual `Typer.scala`
`typeLetRhs`, `Let` and `freshenAbove` owners establish the native operational
level/generalization baseline. They contain no Oracle stack-ID/filter
extension and therefore cannot discharge the seams above. The reviewed
singleton note's qualification remains: the published paper proof excludes
let-polymorphism and omits its full proofs. No stronger theorem is imported.

Complete live replay is another explicit dependency: native bound insertion
generates opposite work, but omission by alias-count subsumption, self-endpoint
handling, row reduction, projection/pruning and memo paths requires its own
observation argument. The local registered-filter lemma does not license any
of those omissions for subtraction/output observations. No complete replay,
extrusion or source-generalization theorem is imported merely from a function
name or stored provenance record.

## 6. Separate current-Yulang3 bridge and economy audit

HIR already retains the relevant original facts: `local_source.rs:289–300`
stores a parameter's annotation and scope; `source_annotation.rs:399–480`
retains its exact nested Function/effect position, and row parsing separately
retains resolved concrete members and variables. These facts are available at
formation rather than reconstructed from effect-family equality.

The current candidate has no corresponding negative concrete constructor:
`candidate_source.rs::preflight_formal` (117–121) starts a formal negative,
reverses Function arguments and preserves results, and requires each negative
effect row to have no concrete member and exactly one variable. The separate
paired guard and `candidate_formal_effect_port` in `candidate_effect.rs`
(1034–1070) also reject that branch. Positive Support/negative Allowance
constructors and actual operand checks remain real implemented mechanisms;
they do not constitute subtraction authority or emitted contributions.

`candidate_context.rs::source_weight` (2174–2195) records empty executable
words. Its SourceUnitPush preparation and `materialize_unit_push` (2200–2222)
are explicitly detached from live relations/bounds/recipes. The reached
`candidate_zero_word_filters` (2615 onward) verifies actual boundary identity
and empty source words before consuming a live closed check. Neither owner
emits the missing negative formal PUSH/matching output POP. Removing preflight
would not supply the absent constructor or its consumer.

`candidate_call.rs:390–442` retains the actual lexical formal registration and
application linkage. `shadow_apply.rs:12–48` explicitly leaves application
typing, invocation image, whole-argument provider compatibility and original
Gen-Call-0 unresolved. Those complete Call premises cannot be inferred from
an accepted negative Function comparison or independently selected outputs.
Current Y3 cannot instantiate even the Oracle direct negative-formal singleton
without the coupled constructor/call/output premise. That is a separate
implementation dependency from the Oracle generalized-observation theorem.

The prior conditional model and singleton route left the current Y3 coupled
negative source constructor/consumer open. This lane changes method by tracing
actual production registrations, scheme constructors and projection owners.
It does not repeat the same assumed transition model a third time. Economy
audit under `rules/compiler-engineering.md`: the original subtraction,
future-check and required natural generalization claims are A/B. Recovering
attachment/binder incidence from an equal row after formation would be D;
HIR/source formation already knows it. The Oracle compaction/generalization
equivalence is a genuine semantic premise, not solved by inventing another
relation or retaining a guessed witness. Calling it C or changing its name
would not close the original gate. No authority or source restriction changes.

One next action: primary assign the exact Oracle generalized-observation seam
above, or a source-qualified falsifier for it, with compaction/pruning and the
actual higher-order call/output owners as frozen inputs; use fresh independent
review of this note before consuming its local lemmas. Preserve the approved
Y3 admission gate and keep its absent negative constructor/consumer explicit.

## 7. Checks, resources and runtime

Only this exact leased note was written. Static commands: bounded `cat`,
`sed`, `rg` owner searches, SHA-256 snapshot/recheck, and a local whitespace/link
check. No Oracle invocation, Y3 invocation, Cargo/build/test, executable probe,
measurement sample, network query, subprocess inference, Git mutation,
configuration change, shared-record write or delegation occurred. These
derivations are producer evidence awaiting independent review.

Read processes were lightweight; the initial batch requested six independent
shell reads concurrently and no CPU-intensive job ran. Later source reads
were sequential. Aggregate CPU/RSS and wall time
were not instrumented. No primary heavy-verification resource was consumed.
The task supplied no numerical wall/CPU/RAM quota; this lane stopped at the
bounded genuine semantic obstruction instead of expanding into all Oracle
metatheory. Initial broad tool captures were truncated; decisive owner sections
were subsequently read narrowly. An initial read-only Git orientation ran;
its transient SHA was explicitly rejected by the primary, and the primary's
pinned baseline above controls. No later Git command or any Git mutation ran.
A `row*.rs` search returned a missing-glob error; the actual owner was located
under `constraints/row_effect.rs` and inspected directly.

Requested routing: normal `gpt-6.1-sol` / `high` proof leaf. Project config
registers the unpinned `prover` and Sol/high defaults. Observed effective
runtime model/effort: unknown; no runtime metadata was supplied. No Astra,
reload or successful-override claim. Parent assigned this actual leaf identity;
no jobs were launched by this leaf. Independent review and gate promotion
remain primary-owned.

## 8. Dependency snapshot and commit packet

SHA-256 values below pin the inspected bytes. They are not Git blob IDs or
proof that every current byte equals the primary baseline. Primary integration
must compare that exact dependency cone against its pinned revision. Oracle
revision identity is inherited from the governing notes, not independently
revalidated by Git in this lane. Dependency stability is checked at freeze.

| Inspected dependency | SHA-256 |
| --- | --- |
| `AGENTS.md` | `89403c6fca2e3c351d7194340e627c3dfd092c8e623ec5e8532ce6e1d5ff3f4d` |
| `rules/agent-orchestration.md` | `3b1e9c5a083ae4257d3d8ad4bacadf55adf07997d0b02c10bcbec4ccda3258be` |
| `rules/research-lab.md` | `3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69` |
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` |
| `rules/compiler-engineering.md` | `4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9` |
| `rules/git-concurrency.md` | `2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6` |
| `.codex/config.toml` | `dae388e4e811c346727ec6688472c7fcf6341ddc5466168cfaa03fdcc0b8e17a` |
| `.codex/agents/prover.toml` | `485a26c7409e16c692ad10095031ab0e7084726ec5da5666082b3bbc4a5daf98` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-10-concrete-effect-annotation-implementation.md` | `3a3186723cd93edd2f767a7e4a481cb6dbed701fc749502e640071f65a4d89ae` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/theory/2026-10-11-negative-formal-effect-source-proof.md` | `262c2569935c30a369846f50fede295d7f024677dca203b5d11e56ed6484f856` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-hir/src/module/source_annotation.rs` | `a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `crates/yu-solver/src/candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `crates/yu-solver/src/candidate_call.rs` | `79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35` |
| `crates/yu-solver/src/shadow_apply.rs` | `230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6` |
| `/tmp/yulang2-oracle-read/crates/infer/src/arena.rs` | `e407480ee4984e24ce214543bfe23ed83e34883129487878df034090688bd9db` |
| `/tmp/yulang2-oracle-read/crates/infer/src/annotation/constraints.rs` | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
| `/tmp/yulang2-oracle-read/crates/infer/src/lowering/mod.rs` | `244e5f8ea339d2e24aa1f8456e99072e4a491b97da58348a4e79eed188ce61a1` |
| `/tmp/yulang2-oracle-read/crates/infer/src/lowering/signature_effect.rs` | `9eec35dcbe721cec20b8cab302c409ec0bc014781a36d5287a781a6cb9fe50ce` |
| `/tmp/yulang2-oracle-read/crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `/tmp/yulang2-oracle-read/crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `/tmp/yulang2-oracle-read/crates/infer/src/constraints/mod.rs` | `ad3cf5fd60462cb1a08ef1a5d6fc57c4fd640148597bc3b331d09729616d8392` |
| `/tmp/yulang2-oracle-read/crates/infer/src/constraints/directed_weight.rs` | `de71ae7ed5a5aed22f3e5d35ca0ebcd52872ff965fcc22523a662cffdd6f28db` |
| `/tmp/yulang2-oracle-read/crates/infer/src/constraints/row_effect.rs` | `080472bb5dcb3f724e808ff745c6fba304cc7ea2574b8f8eb3e3466964e937c2` |
| `/tmp/yulang2-oracle-read/crates/infer/src/constraints/machine/propagate.rs` | `8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086` |
| `/tmp/yulang2-oracle-read/crates/infer/src/constraints/machine/bounds.rs` | `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7` |
| `/tmp/yulang2-oracle-read/crates/infer/src/instantiate.rs` | `876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c` |
| `/tmp/yulang2-oracle-read/crates/infer/src/generalize/mod.rs` | `03bfda4e4997347b59483de96eca652b67477639fc363e0890d546d2cf36fcef` |
| `/tmp/yulang2-oracle-read/crates/infer/src/generalize/finalize.rs` | `a8e5a1c8e6ad57d1fac7e25a1ab6a329093e5c76e6d84c0625c124c349f07492` |
| `/tmp/yulang2-oracle-read/crates/infer/src/generalize/core/stack_ids.rs` | `adb9cd35d483af62ea0c3ebc572b9a0535761f3bfb99aedad49b371833b95f8f` |
| `/tmp/yulang2-oracle-read/crates/infer/src/generalize/core/prune.rs` | `05e6d343c90f1bbc77def8e50f9acb746451ceb3889bb50dd17342621afba26d` |
| `/tmp/yulang2-oracle-read/crates/infer/src/compact/collect/mod.rs` | `828fa02521e2426297a9369df2fd9ef1560b7403a668ddfe881063ef16bdfd40` |
| `/tmp/yulang2-oracle-read/crates/infer/src/compact/collect/type_nodes.rs` | `96dc38a9a05c447f019bb0421e0b37057d283026ba87bce121bb33959b0d8ab2` |
| `/tmp/yulang2-oracle-read/crates/infer/src/compact/finalize.rs` | `53a2452b109ddb461d98f6124d410fa2e771e700e272084f3b83ed87b4f3d272` |
| `/tmp/yulang2-oracle-read/crates/poly/src/types.rs` | `9211e62291b82e71e1b78763b83fe9f1d81e0fe4396d9e12d42e9a4a9b13b47c` |
| `/tmp/yulang2-oracle-read/crates/infer/src/compact/mod.rs` | `122b349ce5adcc273738828736a8f4a7701aa60a57922b286e9fc96965f2ddc4` |
| `/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |

Commit packet:

- Exact leased/change path: `notes/theory/2026-10-11-oracle-global-effect-hygiene-proof.md`; writes stop at handoff.
- Baseline: `b37bfab842dd3f0a39d15c358399a068ff8e3194`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none for the original snapshot dependencies at final recheck; the newly inspected compact-module header and native reference file are included above. No dependency is edited by this leaf. Equality to baseline remains primary-owned.
- Claim/review: unreviewed source-derived local registration/allocation/renaming lemmas plus precise generalized-observation obstruction; no H, source counterexample, soundness/principality or parent-gate closure.
- Checks already run: exact static owner reads/searches, SHA-256 snapshot/recheck and leased-document whitespace/local links; zero executions/builds/tests/measurement samples.
- Proposed checkpoint: `research: derive Oracle hygiene premises and generalization obstruction`.
- Shared-record deltas left for primary/curator: link the discharged local filter-invocation premise and per-use quantified-ID map; record the exact Oracle compaction/pruning/finalization/root-POP observational dependency separately from the absent Y3 negative formal constructor/call/output bridge. Keep original A/B H, complete Call, principality/soundness, admission, production and F5 gates OPEN. No shared task/index/theory-status path edited.

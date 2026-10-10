# Concrete negative formal annotations and the live closed-filter seam

Date: 2026-10-10
Status: unreviewed research derivation; bounded source reachability characterization
Baseline: `7f8c7aed4cfa057c04c3b9eee943152ced610fa0`
Additional frozen input: zero-word consumer delta, SHA-256 `6e098142b589a71d753376d54555b3d76c067840a51dde8ec8af217244e65222`
Lease: this note only; leaf producer, no delegation or semantic authority
Review: compiler-referee found no blocking/major findings; one minor handoff
wording repair is incorporated; no proof-status promotion

## 1. Frozen objective, statement and exclusions

Determine whether a source-authentic concrete annotation at a composed negative
formal Effect position reaches the live zero-word closed-filter consumer and
instantiates the existing conditional local subtraction result.

The governing authority is [annotation integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5 and [contextual attachment admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§§3–4, with the latter's §§5–6 admission boundary retained. Contravariant `[E]`
permits local subtraction; covariant `[E]` permits concrete E there. Root formal
variance is negative, whole-binding variance positive; Function arguments flip
and results preserve it. Ignoring symbolic variables when collecting concrete
atoms does not sever their connections. Different annotations, contribution
lineages, providers and residual recipes remain distinct. The withdrawn callback
scheme is not an oracle.

Freeze the reachability statement as follows. For every actually formed finite
`LocalSource` S, every Lambda formal annotation a in S, and every finite path p
in a's retained Function tree, let C(a,p) be the resolved concrete members of the
Effect row at p and let n(p) count argument descents. Let

```text
sigma(a,p) = -(-1)^n(p).
```

Reach(a,p) means the private `CandidateInference::solve` route admits S,
schedules and executes a's `FormalAnnotation`, constructs an executable view
from that exact row occurrence, and delivers a relation using that view to
`candidate_context_execute`. It is not reachability of an unrelated allowance
or a directly fabricated private fixture.

**Bounded characterization derived below:** at the frozen inputs,

```text
sigma(a,p) = Negative and C(a,p) nonempty imply not Reach(a,p).
```

Consequently this route supplies no nonvacuous source instance of negative
concrete local subtraction. This is a property of candidate guards and
constructors. `CandidateError::Unsupported` is private candidate unavailability;
it is not a proof of language-semantic rejection or a restriction on the
selected policy. Behavior of another inference/fallback route is outside this
statement.

When mapping the [conditional derivation](2026-10-10-contravariant-effect-conditional-proof.md)
§2, preserve all of its binders: any finite decorated monomorphic descriptor
graph Ω, one shared assignment ν, finite execution prefix t, source occurrence
a, actual owner f, exact path p, and actual dynamic boundary instance b when
introduced; its concrete set C_a, symbolic coordinates T_a, contribution
witness c, projected support point πν(c), exact attachment A_a(c), and jointly
scoped typed correspondences M_i. The required result still concerns exact
O minus selected R and its support, with any runtime output requiring the
separate complete-image premise `(O minus R) union N`. This note does not
replace those quantifiers with independent witnesses or endpoint membership.

Excluded: raw-source soundness/principality, complete Call, runtime Handler
selection/receipts/expiry, a callback output, parameterized effect comparison,
general mixed recursion or termination, and certification of nonempty context
lifecycle. No implementation or semantic change is made.

## 2. Source sign and the admission obstruction

Source annotation identity is already retained: `yu-hir/src/module/source_annotation.rs`
32–35, 68–93 defines resolved `SourceEffectId` as module plus declaration key,
`SourceAnnotation` owner/position, and the recursive type/row tree with exact row
position, concrete operands and variables. The argument below starts with an
actually formed `LocalSource`; it does not prove parser/HIR adequacy afresh.

`shadow_apply.rs::CandidateInference::solve` 88–93 calls
`candidate_source::preflight(source)` before collection and session execution.
`candidate_source.rs` 72–75 rejects a Lambda formal if its root has an Effect
row or `preflight_formal(&a.ty, false)` fails. `preflight_formal` 92–96 requires:

```text
at Positive: variables.len() <= 1
at Negative: concrete.is_empty() and variables.len() == 1
Function argument: recurse with !positive
Function result: recurse with positive
```

These requirements apply whenever that node has an explicit row. Omitted rows
are admitted; negative singleton symbolic rows are admitted; a written negative
empty closed row is not admitted by this formal predicate. Root Effect rows
are independently refused by the enclosing formal check.

Induction on p proves that the boolean passed to every visited node is exactly
the selected composed sign. The root receives false. An argument step flips
both that boolean and sigma; a result step preserves both. Thus if preflight
succeeds, every explicit row at negative sigma has an empty concrete vector.
The hypothesized nonempty C contradicts that necessary condition. Because the
solve call uses `?`, it returns before collection: no action for a is executed,
and no view or consumer relation can be formed by this route from p. This
proves the displayed bounded characterization for all finite retained paths.

If collection is considered separately, its scheduling owner is
`candidate_source.rs::emit_candidate_source`: Lambda Visit 246–260 retains
level/scope and schedules `Action::FormalAnnotation` with the actual annotation,
parameter position and Lambda occurrence. `execute_candidate_actions` 549–554
dispatches it to `candidate_formal_annotation`. The scheduler's ability to
carry an annotation does not bypass either the preflight above or the builder
guards below.

## 3. Constructor obstruction and endpoint/sign separation

`candidate_effect.rs::candidate_formal_annotation` 938–955 refuses a root row
and calls `candidate_formal_pair(..., Polarity::Negative, ...)`. The paired
constructor 899–916 has the same necessary row guard: negative variance with
nonempty concrete or anything except one symbolic variable returns unavailable.
Its argument recursion flips variance and its result recursion preserves it.
It constructs the ordinary four-port pair:

```text
F+ = Function(an, qan, qrp, rp)
F- = Function(ap, qap, qrn, rn).
```

`candidate_formal_effect_port` 919–935 admits omitted ports as fresh shared rows
and singleton symbolic ports as scoped rows. The concrete/empty view branch
requires `variance == Positive`. It calls `candidate_signature_effect` twice,
with endpoint polarity Positive then Negative, sharing the occurrence-to-view
map. `candidate_signature_effect` 1364–1366 independently refuses a nonempty
concrete row when source variance is Negative. Therefore bypassing the source
preflight alone does not create a negative concrete interface.

In the permitted concrete branch 1397–1434, the same exact row occurrence
supplies owner, row position, resolved members, optional tail and
`AttachmentSource { composed_polarity: variance, lexical_scope }`. Here variance
is Positive. Endpoint polarity controls the bound operand:

```text
endpoint Positive: Support(view) <= fresh port
endpoint Negative: fresh port <= Allowance(view).
```

This negative `Allowance` endpoint denotes checking of a composed positive
source row. It provides no negative source-position license. For example the
result row in a formal `cb: int -> [E] ()` preserves its negative root sign
and is refused; the inner result row in a formal
`consume: (int -> [E] ()) -> ()` is positive after one argument reversal and
can take the paired Support/Allowance branch. These are sign examples, not
newly executed fixtures or asserted schemes.

`candidate_formal_annotation` 965–971 connects the pair to the raw parameter
with positive-interface <= parameter-negative and parameter-positive <=
negative-interface, retaining the latter in `formal_domains`. Endpoint
orientation and provider flow do not change the source sign already selected
by construction.

## 4. The actual live zero-word chain and what it consumes

For an admitted closed composed positive row, the chain is constructive:

1. `candidate_signature_view` 598–636 allocates the view. Annotation provenance
   with no tail gets `source_weight`; `closed_weight` is that weight exactly
   when the tail is absent. A symbolic tail keeps source identity when supplied
   but exposes no closed weight. Operation provenance receives no source weight.
2. `candidate_context.rs::source_weight` 1360–1383 retains one weight identity,
   exact owner/position, resolved member vector, member ordinals and source
   polarity/scope when supplied. Its live `left_word` and `right_pops` are
   zero-length arrays. The positive `unit_push` marker and
   `materialize_unit_push` 1385–1402 are detached preparation; they emit no live
   relation or executable word.
3. `candidate_context_source` 1606–1614 reads an upper `Allowance(view)`'s
   `closed_weight` and constructs `PrefixLeft { weight, input: IDENTITY }`.
   Otherwise it returns identity. It does not inspect source polarity and
   cannot turn an endpoint sign into a subtraction license.
4. Actual enqueue wiring is `lib.rs::enqueue_item` 12123–12127 ->
   `candidate_effect::candidate_enqueue_evidence` 321–325 ->
   `candidate_context_admit` 1652 onward. The latter supplies a RelationId with
   exact canonical pair/context and dependencies. Initial constraints also
   run `candidate_context_seed` at `lib.rs` 11834. Function decomposition
   reverses argument Value/Effect endpoints and preserves result endpoints at
   `lib.rs` 12023–12052. Its actual caller is
   `candidate_function_port_admit`, `lib.rs` 12074, before enqueueing that child.
   This records Swap/Preserve incidence at `candidate_context.rs` 1675–1704;
   the record is inert and the child still receives its own source context.
   It is not execution of the full §4 contextual Function-port contract.
5. `lib.rs::constrain_live_item_with_inferred_entry` calls
   `candidate_context_execute(item.task, item.relation)` at 11861, after
   selecting the relation's processing scope and before `pair_is_current`
   and ordinary Effect application. Hence this consumer is activated by an
   actual worklist pop, rather than merely retained in a bound table.
6. `candidate_zero_word_filters` 1707–1780 validates the complete context DAG
   before publication. Its admitted forms are identity, a PrefixLeft leaf
   whose input is identity and whose payload matches a closed boundary with
   empty left/right words, and ordered acyclic Replay nodes over those forms.
   Payload IDs are deduplicated without identifying distinct boundary IDs.
   Swap, BothFromRight, WithoutLeftFilter, SuffixRightPops, and nested
   nonidentity PrefixLeft fail this consumer.
7. `candidate_context_execute` 1783–1845 applies each validated boundary's
   Allowance to the true lower endpoint. A new allowance calls
   `candidate_apply_effect`; an already registered one retains the new origin
   and replays that exact bound. Only after this does it mark the relation
   discharged. The boolean says whether the task's exact upper Allowance
   was handled, allowing the caller to skip duplicate ordinary application.
   Other endpoint pairs continue ordinary propagation after filter checking.

`candidate_extrusion.rs::candidate_apply_effect` 726–757 canonicalizes endpoints,
uses the existing level-selected bound direction, inserts the bound and invokes
opposite replay. `candidate_effect.rs::candidate_check_effect_operand` 752–816
expands Support as AnnotationMember/tail tasks; a concrete Contribution or
AnnotationMember is accepted by Allowance on resolved membership, otherwise
forwarded intact to its tail or recorded as a mismatch. These are concrete
checks, not contribution removal. In the closed case the retained upper bound
is the executable registration for subsequent opposite lowers; this local
wiring does not by itself prove complete source replay across every lifecycle.

The delta also makes checked Allowance bound children use identity context only
when the active validated scope matches the parent, canonical receiving owner,
weight and boundary (`candidate_context_bound` 1852–1886), while retaining the
Derived edge to the original parent. `post_check_context` uses identity only
for a discharged relation. This is discharge of retained filter obligations,
not discharge of an emitted effect event.

No branch in this live fragment constructs an exact A_a(c), chooses R, creates
the source-local subtraction residual, or accounts for new output contributions
N. Empty live words cannot implement the negative source PUSH/POP transition
by themselves, and unsupported context operators do not become executable
because their detached evaluator or provenance record exists.

## 5. Hypotheses of the existing conditional result

The classifications concern supply by this frozen source-to-consumer route;
“false” below means the asserted implementation bridge is false here, not that
the reviewed conditional hypothesis or selected language policy is false.

| Conditional premise | Supplied portion | Missing portion and classification |
| --- | --- | --- |
| §2.1 Source formation | Actual annotation owner/tree/row position, resolved nullary identities, symbols and composed sign are retained and used in guards. | Executable negative concrete profile/license construction is absent and guarded out: **false as a claim about this source route**. Any Handler-role profile remains **open**. A static source annotation is not a dynamic receiver. |
| §2.2 Exact attachment A_a(c) | Positive source sets retain identity, member ordinal and lexical scope; Contribution retains resolved identity, source origin and instance (`candidate_effect.rs` 724–751). | Neither supplies the source-derived event/path attachment judgment for a negative local view: **open and not realized here**. Equal support, a membership success or canonical equality supplies no witness. |
| §2.3 Typed transport and owners | Real Function endpoint reversals/preservation, RelationId dependencies, and distinct annotation/contribution records exist locally. | Valid M_i for the decorated realization, common-ν predicate/dependency/lineage preservation, executing/saved owner correspondence and fresh dynamic receiver/expiry premises remain **conditional supplied assumptions** of the earlier theorem, **open** as a whole-source operational bridge. Inert FunctionPort records do not establish executed Swap. This note performs no full lifecycle certification. |
| §2.4 Executable local check | The admitted closed positive fragment has an actual pre-memo consumer, registration, current-bound replay and an upper-bound route for future lower checks. Symbolic tails are retained by the constructor, outside this zero-word closed fragment. | Negative exact attached subtraction, correlated residual target checks and all source negative current/future cases are **false as implemented by this consumer**, with their required implementation correspondence **open**. The admitted positive check is not an instance of this negative premise. |
| §5 Handler/runtime output additions | None established by this chain. | Actual Handler profile, Path/receipt/event observation, active configuration, ordered selection, source discharge and complete `(O minus R) union N` image remain **conditional/open**. Allowance acceptance proves none of them. |

The §3 polarity equation is supplied for the finite retained source tree by
the direct induction in §2. The §4 elementary exact-set subtraction equations
remain the prior conditional algebraic result; this note provides no actual O,
R or runtime output image that instantiates them. Calling a universal theorem
over the presently admitted negative-concrete action set would be vacuous.

## 6. Adjacent routes, falsifiers and the minimum missing transition

Adjacent owners do not invalidate the obstruction. Whole-binding, local-binding
and expression-ascription annotation paths start at positive variance;
`preflight_annotation` 98–105 and `candidate_signature_effect` 1364 guard their
negative concrete descendants too. Whole/root computation checks explicitly
request negative endpoint polarity with positive source variance
(`candidate_annotation_computation_effect` 1193–1201). Operation interfaces
start positive and are distinguished as Operation provenance, so do not create
closed annotation weights. Written negative empty bundles at
`candidate_negative_empty_bundle` 1137–1168 retain inert source construction
only; they are not concrete negative weights or executable relations.

The strongest tempting falsifier is the permitted formal's negative Allowance:
it demonstrably constructs a closed filter and has an activated consumer. Its
source sign remains positive, so it falsifies “every negative endpoint is
unreachable” but not this note's composed-negative statement. Direct private
`candidate_effect_view` fixtures can create closed weights with no source
formation witness; they cannot falsify a source-authentic claim. Source signs,
owners and dynamic attachment evidence cannot be recovered from equal rows.

The minimum missing bridge is an owner-local transition at
`candidate_formal_pair` / `candidate_formal_effect_port` /
`candidate_signature_effect`: from an actual resolved negative row occurrence,
form its source-owned paired executable attachment/subtraction interface,
retaining composed sign, scope, exact members and symbolic coordinates, and
deliver genuine contribution/typed-route evidence to a local residual consumer
that performs the selected licensed operation and retains current/future checks.
Its check/exposure and outgoing residual lineage must remain correlated.
Clearing only preflight is insufficient; the paired and signature guards still
refuse it. Clearing all guards and using today's Allowance consumer would still
provide membership checking without exact local subtraction. Complete Call
meaning remains its separate genuine requirement, not a registry prerequisite
for this formation rule.

The selected contextual admission design explicitly keeps arbitrary concrete
formal enabling behind its later admission/lifecycle gate. This obstruction is
therefore an unfinished owning seam, not a reason to adopt a new restriction.
No new semantic decision or authority is proposed.

Proof-obligation economy: the missing transition is A (licensed effect
correctness) and B (selected ordinary inference behavior); losing source
occurrence/scope/lineage would create D reconstruction debt. HIR and signature
formation already possess occurrence, resolved members and composed sign and
should retain those facts by construction. Actual dynamic attachment/path facts
must come from their owning operation. Existing exact residual lineage,
level/extrusion, qualifying parent/copy equality and generalization duties
cannot be replaced by support cancellation. This is one complete constructor
derivation, not two equivalent proof attempts; no further support-only lemma
is useful evidence for the missing transition.

## 7. Provenance, checks, resources and frozen packet

The leaf producer ran read-only `git rev-parse HEAD` and
`git diff -- crates/yu-solver/src/candidate_context.rs crates/yu-solver/src/candidate_context_tests.rs | sha256sum`;
the observed baseline and combined delta hash matched the supplied inputs.
The assignment prohibited Git commands, so these reads were workflow
nonconformance and are not counted as compliant verification. No Git mutation
occurred. Source inspection used bounded `rg`, `sed` and `cat` reads;
file SHA-256 values below identify the inspected dependency snapshot. Comparison
of every remaining live file to its baseline blob was not performed here and
remains the primary's integration responsibility. No test was read as evidence
that it ran, and no test/build/checker/Oracle execution occurred.

| Direct dependency | Inspected SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0` |
| `crates/yu-solver/src/candidate_effect.rs` | `2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e` |
| `crates/yu-solver/src/candidate_context.rs` | `470a5d45b6a7d6d2faf55de388908fc6b724dac7a14af87a3ff67a227b975ac5` |
| `crates/yu-solver/src/candidate_context_tests.rs` (delta provenance only) | `290f25d1a5a12c6911623bbf9b267983b8ed3ff2a290b678ca115e448ef907fe` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a` |
| `crates/yu-solver/src/shadow_apply.rs` | `6bea8808153b8b71a57e4a8583284e49284ec9aa35118a61f44a3a387a8a32f6` |
| `crates/yu-solver/src/lib.rs` | `9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1` |
| `crates/yu-hir/src/module/source_annotation.rs` | `a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/progress/2026-10-10-contravariant-effect-conditional-proof.md` | `3ef7fd4b45dc55b7e2d7ffb32f28ae2a9912176570d96756658a1f6896033c02` |
| `notes/progress/2026-10-10-selected-formal-contextual-integration.md` | `0a07713df99571d19705333e73c195c3ad29b6165af92cb6821c02cd407da507` |
| `notes/design/2026-10-10-concrete-effect-annotation-implementation.md` | `3a3186723cd93edd2f767a7e4a481cb6dbed701fc749502e640071f65a4d89ae` |

Rules read: orchestration budget; agent orchestration (Model routing and Astra
escalation; Proof delegation and decomposition); research laboratory; design
authority; compiler engineering (proof-obligation economy); Git concurrency.
The `yulang-proofs` skill and registered `.codex/agents/prover.toml` were read.
The role omits model/effort pins and `.codex/config.toml` sets ordinary proof
defaults to `gpt-6.1-sol` / `high`. Requested routing: normal Sol/high proof leaf;
the CLI JSONL confirms an actual child at `/root/bridge_proof` with
`agent_role=prover`, `model=gpt-6.1-sol`, and `effort=high`. This is an observed
real custom-role launch, not a generic fallback. No Astra
assignment, child or independent review was launched here.

Checks: read-only provenance/hash inspection and a note-local whitespace scan
only. One-CPU allowance; lightweight short-lived commands, no heavy process or
measurement samples. Actual CPU/RAM/wall time were not instrumented. This note
is frozen when handed back; further changes require a primary-issued repair.

Next action: primary completes fresh independent review of this bounded bridge.
Any preparatory negative paired-formation work must preserve the current
negative-concrete admission guards. Enabling such rows remains behind the later
contextual-admission §§5–6 gate and any required approval; this note grants no
implementation authority to enable them.

Commit packet: exact leased path
`notes/progress/2026-10-10-contravariant-effect-live-bridge-proof.md`; baseline
`7f8c7aed4cfa057c04c3b9eee943152ced610fa0`; known changed dependencies are the
two zero-word delta files with hashes above and combined delta hash in the
header; no dependency was edited by this producer. Review status unreviewed,
research-only source characterization, no conformance/soundness/principality
promotion. Checks already run are the provenance/hash reads; final note-local
whitespace/hash scan is reported in the leaf handoff. Proposed checkpoint
message: `research: trace negative formal annotation live bridge`.
Shared-record deltas left for primary/curator: record candidate negative-concrete
unreachability and endpoint/source-sign distinction, retain the authentic
negative formation/residual/lifecycle bridge as open, and credit zero-word
execution only for its admitted closed allowance fragment. No shared record
was changed by this leaf.

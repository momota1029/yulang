# Negative formal source, Call and residual formation boundary

Date: 2026-10-13
Status: independently reviewed bounded source-owner characterization; parent gates OPEN
Method: complementary source-construction audit, no constructive theorem certification
Y3 baseline: `fd94dedee30c06f83a3a867ea8da413d3b688eab`
Oracle source pin: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this file only; leaf, no delegation or Git mutation

Independent reviews: `spec_auditor` and `compiler_referee` PASS for the bounded
source-owner characterization and conditional Oracle emission lemma. Both
confirm that the note does not establish source acceptance, residual-demand
reachability, full hygiene, implementation authority, or parent-gate closure.

## Objective, authority and precise claim

Identify the earliest actual source constructor that can join a composed-negative
concrete formal occurrence to its resolved call and owning output, and determine
whether that construction supplies the same attachment lineage to residual
feedback and the exact outgoing tail. This packet follows the existing
[coupled-generation audit](../theory/2026-10-13-negative-formal-coupled-generation.md)
and [consumer discriminator](2026-10-13-negative-formal-consumer-discriminator.md).
Their non-generation and exact-tail findings are dependencies, not new attacks
or independent reviews here. The additional question is where source incidence
ends and the actual joint operational judgment must begin.

Governing sections, with their existing accepted meanings:

- [Top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
  §§1–5 and Authority and integration: ordinary constraint generation and
  necessary abnormal safety; successful suspension/publication remains required.
- [Annotation hygiene integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
  §§1–4 and §6: composed-negative concrete subtraction is function local,
  composed-positive concrete atoms are allowed, and symbolic connections/later
  checks remain. The withdrawn callback scheme specifies no output.
- [Concrete annotation gate](../design/2026-10-10-concrete-effect-annotation-implementation.md),
  Annotation checking and publication owner: paired checking/exposed targets
  share the actual variable/view environment. Pending Call metadata supplies
  no subtraction authority; no full registry prerequisite is imposed on basic
  annotation generation.
- [Attachment/admission](../design/2026-10-10-contextual-attachment-admission-design.md)
  §§3–4 and §6: one identity per exact annotation atom set; concrete residual
  construction retains live feedback and each exact tail projection; general
  concrete-formal enabling remains outside the completed internal gate.
- [Residual identity](../design/2026-10-10-contextual-residual-lineage-selection.md),
  Selected policy: separate constructor lineages survive source/key equality,
  and applicable current/future lowers reach each retained recipe.
- [Complete Call definition](../design/2026-10-07-complete-call-contribution-definition.md)
  §§2–5; [source interfaces](../design/2026-10-08-call-source-interface-definition.md)
  §§2–4; [Function membership](../design/2026-10-08-contextual-function-membership-definition.md)
  §§2–4: actual provider/whole-carrier/complete output and future interfaces are
  correlated. Static placement retains independently supplied contracts and
  does not create original operator typing or primitive admission.

**Claim class:** bounded source-owner characterization plus a conditional
Oracle emission lemma. The original universal hygiene H is unchanged. No
source rejection, H counterexample, semantic impossibility, new meaning,
implementation permission, or theorem closure follows.

Hypotheses for inspected constructor paths: the pinned bytes, successful HIR
formation when specified, successful arena allocation/constructor completion,
and actual binder resolution. The Oracle direct predicate characterization
additionally requires a nonempty concrete immediate result row, a callable
annotation passing the whole-callable wildcard guard, and its actual direct
local call in the corresponding defined frame. No provider implementation is
chosen. Aliases and wildcard forms remain in the original parent domain.

## 1. Earliest Y3 source owners know the join's static inputs

`yu-hir/src/module/local_source.rs:104–175` has the authentic expression
occurrence, `SourceNodeKey`, scope, Lambda parameter, Apply children and resolved
Parameter/Local identities. The parameter itself retains its annotation.
`source_annotation.rs:349–374` constructs the original annotation owner and
position; its type/row constructors retain Function structure, concrete members
and symbolic variables. These are source facts, not a live executable instance.

The first inference constructor positioned to use those facts is
`ConstraintBatch::emit_candidate_source` in `candidate_source.rs`, at the
Lambda visit, before visiting its body (`269–287`):

```rust
Action::FormalAnnotation {
    annotation: Arc::new(annotation.clone()), parameter: position,
    occurrence: expr.occurrence.clone(), scope: /* actual scoped owner */,
}
```

The omitted expression is the actual `parameter_scopes` lookup with its
definition fallback, not a synthesized source judgment. The dispatch at
`candidate_source.rs:660–663` calls `candidate_formal_annotation` with these
same operands. Formal registration is constructed earlier at `180–202`,
using the same `HirParameterId` and parameter recipe position. Parameter name
uses retain its exact registration at `235–245`.

Apply formation (`394–408`) then records an `ApplySourceInput` with its source
expression/owner, exact callee and argument, level, recipe, result,
application-effect coordinate, checking occurrence/cause, and optional formal
name registration. `admit_candidate_fact` (`shadow_apply.rs:1308–1400`) validates
those shared operands before retaining the generated native interface. Thus
the direct static binder-to-call association need not be reconstructed from
equal type rows or nominal support.

This provides a natural *construction position*, not the missing effect law.
The public solve path preflights first (`shadow_apply.rs:92–115`). The negative
formal test is exactly (`candidate_source.rs:116–121`):

```rust
row.concrete.is_empty() && row.variables.len() == 1
```

Consequently the specified negative concrete row is never accepted by this
preflight. Earlier unsupported checks may stop first. Independently,
`candidate_effect.rs:1034–1070` rejects the row in the paired constructor;
`1073–1111` installs its links/domain only after that paired construction
succeeds. No downstream effect conclusion is obtained by bypassing the first
guard. These boundaries were already identified by the dependency notes.

## 2. Call and output records retain incidence, not the operational join

`candidate_call.rs:9–65` retains source registration, names, Apply inputs and
the actual native callee/argument/result/demand/invocation/application ports.
Its source validator (`390–442`) follows the actual wrapped source callee back
to the Parameter name, checks the Lambda registration and scopes, and retains
the native root. This validates static source correspondence on admitted
paths. It does not introduce complete source typing.

The decisive boundary is explicit in `OriginalGenCall0Input` (`90–128`):

```rust
ImmediateOutputPosition,
CompleteOutputPosition,
ElimOrigin,
```

They are returned as still-required original formation inputs by
`PendingCallConstruction::original_formation_inputs` (`221–223`). Its suppliers
also include `OriginalGenCall0` and
`ReceiverDispatchAndCompleteResultFutureInterfaces` (`224–245`). A native
invocation row is therefore not already the original scoped complete output
or evidence that this negative annotation licenses its removal.

`admit_candidate_fact` forwards the callee-evaluation and fresh invocation rows
to the actual application-effect row (`1420–1442`). `admit_lambda_fact`
(`lib.rs:11233–11369`) combines inferred entry and actual body effects at its
fresh returned row and constructs the Function. Its inferred-entry certificate
is retained at that Lambda's real entry-flow constructor (`11295–11307`). It
does not introduce a negative-formal call predicate or output cancellation.
The output is a row endpoint, not a source-certified residual recipe.

Aliases are genuine source routes. `LocalSourceResolution::Local` executes
the actual local scheme route, or its active-initializer link
(`candidate_source.rs:380–390,660–681`). The Apply still owns its exact native
endpoints. The optional *direct Parameter-name* registration is absent for a
plain Local callee; absence of that optional field is no source rejection and
does not show absent type-level alias transport. A proof for an alias must
follow its actual capture/freshening incidence rather than identify its binder
with the original formal through row equality.

The selected complete Call constructors do not fill this cut. C-Call/CallMem
retain an authentic complete `Q_e` under independent C0; J-Owned uses a complete
diagram and real attribution. IF-Insert/IF-Use place the actual declarations
and scoped references. A-UpperCallRef/LC-OwnCall retain those same inputs and
grant no removal permission. None supplies a negative annotation's original
executable local operation merely from the existence of its lexical source
and native four-port demand. This conclusion is confined to the named selected
constructor route; it is not an exhaustive theorem about every historical
source or license constructor.

## 3. Oracle distinguishes direct predicate attachment from residual activation

All locators below are immutable blobs at the Oracle pin. Oracle is comparative
source evidence; its residual-key coalescing is not the selected Y3 identity.

The first actual Oracle coupled constructor is
`annotation/constraints.rs::lower_ret_effect_bounds:424–470`, invoked by the
paired Function constructor (`363–390`). `effect_row_stack:657–690` allocates
one fresh i for the concrete set. That same returned stack supplies:

```text
positive result Effect: Stack(q, PUSH_i(S))
negative result Effect: Stack(q, FILTER(S))
returned call predicate: POP_i.with_filter(S)
```

The last expression is computed by `predicate_weights:921–924` from the actual
stack IDs. Lambda's `mark_lambda_param_call_predicate:919–942` stores that
returned predicate on its actual introduced local. The direct resolved
`Expr::Var` lookup (`tail.rs:690–705,844–852`) retrieves it; the actual App
extends the current latent frame at `551` and `719–725`. The owning output
then wraps the actual body Value and Effect with that frame's predicate
(`tail.rs:1058–1109`; `lambda.rs:1232–1237`). This derives same-i direct
constructor lineage, conditional on the specified owners completing.
`lambda.rs:1585–1586` suppresses this predicate for a Function annotation with
any effect wildcard; the characterization does not override that guard.

**This output construction does not yet imply a residual event.** The output
wrapper is formed from `Pos::Var(body_effect)`/`Pos::Var(body_value)` and is
forwarded to actual output coordinates. A POP-bearing forward to a variable
does not by itself construct an upper `Neg::Row(I,t)`. Residual activation
requires the separate authentic task whose dispatch is
`constraints/machine/propagate.rs:130–137`:

```rust
Neg::Row(items, tail) => self.add_effect_row_upper_bound(
    source, items, tail, constraint.weights, Some(parent),
)
```

Positive Stack/NonSubtract normalization (`11–36`) transports actual weights;
negative Stack normalization (`38–56`) performs receiver checks before
forwarding to the existing inner endpoint. Neither creates an arbitrary
concrete Row demand or selects a convenient tail. The source consumer that
actually formed `I,t` and its correlated incoming weights remains necessary.
No handler, enclosing output annotation or provider body is invented here.

## 4. Conditional same-operation feedback/projection derivation

Suppose an authentic dispatch above reaches the nonempty-retained weighted
branch of `row_effect.rs::add_effect_row_upper_bound:153–234`. This is a
conditional operational lemma, not assumed source reachability. Let its actual
inputs be source u, heads I, tail t, weights (L,R), and producer p. The owner
computes retained J and residual left weight K from those inputs, obtains g,
then constructs one WeightedResidual derivation d carrying its real parents.
Both enqueues occur after the cache fresh/reuse branch:

```text
u <: Row(J,g) @ identity                    [216–221, derivation d]
g <: t        @ normalize_directed_mix(K,R) [223–233, derivation d]
```

The same local g and d appear in both calls; the second call uses this
invocation's exact `tail`, including a cache hit. Their pairing is established
by the reached source statements, not a checker with supplied rules. The
operation preserves the supplied stack IDs while transforming every active
left payload (`1190–1216`). This proves neither that every transformed entry is
an eligible fiber of the original negative formal nor that the complete queue
drains. Identity feedback contains no literal stack operation; its retained
shared derivation supplies the pairing evidence. Oracle g reuse also does not
prove distinct Y3 recipe lineages may be merged.

Y3's named current filter discharge stores
`RelationId -> ContextId` (`candidate_context.rs:699,2800–2809`), while live
source weights have zero-length operation words (`114–133,2174–2195`). Its
detached PUSH adapter creates no live relation or recipe (`2200–2222`). Thus
neither that discharge map nor the retained static Call record is the
authenticated joint operation above. This matches the consumer discriminator's
boundary; it adds no alternative residual arithmetic.

## 5. Exact unprovided original judgment and next action

The first missing original application is at **negative paired-formal
formation**, before body inference: elaborate the actual annotated formal into
an executable, scoped attachment instance and its genuine callable/checking
interface. Its incidence inputs are already known to FormalAnnotation. A
completed constructor must then supply the original resolved-call/output
operation using that same instance (or its genuine coupled alias freshening).
For a residual route, that original operation must account for the actual
Row-upper demand, eligible lower-fiber parents, retained heads, exact tail and
live context, and produce feedback and projection jointly.

These are the required *outputs of the missing application*, not an adopted
new inference rule or hypotheses declared true. The available sources establish
neither this negative introduction nor its residual route. Policy permits the
local subtraction; complete Call placement preserves independently valid
operations; Oracle identifies a bounded implementation owner that does perform
the direct predicate pairing. None of those three statements derives the
missing original source judgment for Y3. In particular, supplying only balanced
PUSH/POP, a native invocation row, or independent output witnesses leaves the
same premise untouched.

Recommended next action: primary/prover expand this single negative
FormalAnnotation introduction with its original operational premises, then
apply it at its authentic direct or aliased Call/output event and identify the
source constructor of the required Row demand. If the current source rules
provide no such clause, return that exact local formation gap to the existing
authority process before an implementation lease. Keep the original H,
negative admission, complete Call, source correspondence and cutover gates OPEN.

## Evidence, resources, limitations and frozen dependencies

Checks: bounded `cat`, `rg`, `sed -n`, Python SHA-256 and immutable read-only
`git show` of the pinned Y3/Oracle blobs. All 18 semantic/source dependency
files below matched the Y3 baseline byte-for-byte at inspection and final
recheck. Aggregate startup captures truncated; decisive governing sections and
source owners were subsequently read in bounded ranges. No broad source search
or exhaustive source-constructor inventory was completed.

No tests, builds, executable probes, runtime Oracle invocation, mutations,
random seeds/ranges, timing samples, Git mutations, child launches or shared
record changes. At most three independent lightweight shell reads ran in a
batch; heavyweight process count zero. CPU/RSS/wall time were not instrumented;
no numeric worker quota was supplied. This leaf used the yulang-proofs skill
for source-bridge discipline; constructive proving and review remain separate
primary-owned lanes. Actual model/effort metadata is unknown.

Oracle independence: source blobs were independently pinned, with no dirty
Oracle checkout or execution oracle used. Y3 and Oracle characterizations
share successful constructor/arena and source-resolution assumptions. No
checker assumes the open transition. Changed governing/source bytes, failed
constructors, an absent Row demand, wildcard suppression, or alias transport
outside the direct route invalidate the affected conditional claim rather than
establish a counterexample.

Unverified scope: complete source acceptance/provider compatibility, original
joint operation and Row-demand reachability, fiber eligibility, future replay,
alias/generalization/extrusion/intrusion preservation, all mutation paths,
parameterized effects, mixed-cycle admission/termination, runtime handlers,
soundness, principality and F5. This audit establishes no full hygiene theorem
and provides no minimized accepted source counterexample.

SHA-256 dependency snapshot; no dependency bytes changed during this packet:

| Y3 path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-10-concrete-effect-annotation-implementation.md` | `3a3186723cd93edd2f767a7e4a481cb6dbed701fc749502e640071f65a4d89ae` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/design/2026-10-10-contextual-residual-lineage-selection.md` | `d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98` |
| `notes/design/2026-10-07-complete-call-contribution-definition.md` | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| `notes/theory/2026-10-13-negative-formal-coupled-generation.md` | `aae5bb8e7410a33d08793e714825270e02c3437d66077d2dd375924cb021cc2c` |
| `notes/progress/2026-10-13-negative-formal-consumer-discriminator.md` | `be2e289628a97f047c786499bc406b108673ce217358d5dd4841ca1f23c14eaf` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-hir/src/module/source_annotation.rs` | `a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_call.rs` | `79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35` |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `crates/yu-solver/src/candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `crates/yu-solver/src/shadow_apply.rs` | `cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |

| Oracle pinned path | SHA-256 |
| --- | --- |
| `crates/infer/src/annotation/constraints.rs` | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
| `crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `crates/infer/src/constraints/machine/propagate.rs` | `8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086` |
| `crates/infer/src/constraints/row_effect.rs` | `080472bb5dcb3f724e808ff745c6fba304cc7ea2574b8f8eb3e3466964e937c2` |

## Commit packet

- Exact leased/changed path:
  `notes/progress/2026-10-13-negative-formal-source-call-output-bridge.md`.
- Baseline SHA: Y3 `fd94dedee30c06f83a3a867ea8da413d3b688eab`;
  Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; all 18 Y3 dependencies match the baseline;
  pinned Oracle hashes above. Primary owns any later integration revalidation.
- Review status: frozen, unreviewed source characterization and conditional
  emission lemma. No independent review, authority or parent closure claimed.
  Writes stop before submitting this artifact for frozen review.
- Checks already run: static source/authority correspondence, immutable blob
  and SHA-256 comparison, leased-note whitespace/newline/local-link integrity;
  zero tests/builds/probes/measurements.
- Proposed message: `research: locate negative formal Call and residual formation bridge`.
- Shared-record deltas intentionally left for primary/curator: record the
  FormalAnnotation formation cut; distinguish original output-position
  formation from native invocation ports and actual Row-upper activation;
  retain H/negative admission/complete Call and source correspondence OPEN.
  No shared task, index, authority, theory-map or question-board edit.

# R225 source-owner trace — callback boundary acquisition and delivery

Sprint/contract revision: R225 / 1, SHA-256
`4d5cea5c80080f4fbe196ca7cba7312bfb88986b8736673388ddfa143ab913a8`.
Assignment/handoff revision: `r225-source-owner-trace` / 1.
Worker: `/root/r225_source_owner_trace`, registered `researcher`; session
`01a1873a-a93b-7dc3-a8ce-028a7b543a80`. Requested model/effort:
`gpt-6.1-sol` / medium; runtime model/effort observation: UNKNOWN.
Baseline: `579df249d52fb57a0ec38e00881036c409dc722c` plus admitted R224
closeout/R225 records. Read-time HEAD was
`c4e263b923368c4c20fdaba95ddbe960f502b967`; all eleven supplementary Rust inputs
below were compared byte-for-byte with the pinned baseline and matched.

Outcome class: **source-native-evidence**, bounded static characterization;
**NO_SAFE_CODE_SLICE**. No theorem, executable counterexample, impossibility
result, semantic decision, or parent-premise discharge is claimed. Roots remain
0/4; packages remain 0/5; parent-premise delta is 0.

## Finding and first owner

The current source carriers preserve substantially more information than the
historical design inventory suggests. They retain application/literal syntax,
formal Function annotations, lexical and import identities, annotation source
positions, and some nested formal-permission paths. Nevertheless, the inspected
source traversal does not acquire a resolved callback boundary and deliver it
to an argument literal before generating that literal's body facts.

The first missing equation belongs to **source application checking**:

```text
original App(context, callee, argument)
  -> acquire the callee formal's instantiated Function contract for this use
     together with its original static callback template/profile
  -> check argument with expected-callback(F_cb, beta, Slots(beta))
     before generating an argument literal's body constraints
  -> consume that same formal/interface at the original App check
```

The output must be constructed from the original declaration/name/annotation
and inference inputs. Supplying `F_cb` or the desired source judgment as a
premise would leave acquisition open. Existing source identities and term
constraints are useful inputs, but no inspected owner composes them into this
operation. `App.descriptorFormation` and the generated callee-to-descriptor
check are downstream consumers. No new API or data carrier is selected here.

For unknown/inferred callees, this finding does not authorize requiring a final
solved type before ordinary constraint generation. The authoritative top-level
inference principles §1.1 retain symbolic types constrained by uses. The bounded
callback-delivery decision §§2–2.1 supplies an already known formal and excludes
unknown callees and annotation/callback overlap (§2, lines 73–78). Extending its
acquisition rule to those cases needs an exact source rule; this lane does not
choose one.

## Actual declaration and source path

| Owner/location | Retained input or construction | Limit for this gate |
|---|---|---|
| `crates/yu-hir/src/module.rs:119` | `SemanticImports` retains caller correspondence and `SourceImportEnvironment`. | It is no longer empty. The retained imports do not themselves assert a callable type. |
| `crates/yu-hir/src/module.rs:1552` | `ResolvedExpr::Apply` retains callee/argument and authentic occurrence; `Lambda` retains parameter/body. | The structural node explicitly supplies neither callability nor a Call typing rule. |
| `crates/yu-hir/src/module/local_source.rs:62,348,572,602` | `LocalSource` retains root/local annotations, named groups, and parameters; `LocalSourceForm` has `Apply`, `Ascription`, `Lambda`; `LocalSourceParameter` retains its annotation. | These are source inputs, not an instantiated expected callback interface. |
| `crates/yu-hir/src/module/source_annotation.rs:125–160` | `SourceAnnotation` retains owner/position; its recursive type has separate effects and `Function { argument, result }`. | A Function source annotation is available; a universal claim that source interfaces are absent would be false. |
| `crates/yu-hir/src/module/local_source.rs:1142–1182` | Named-header formal annotations are parsed into each `LocalSourceParameter`, then retained in the Lambda form. | No contextual callback boundary is acquired here. |
| `crates/yu-hir/src/module/local_source.rs:2092–2122` | Inline `\x -> body` retains a distinct formal identity, lexical scope and body, with `annotation: None`. | No expected-context input enters this literal construction. This source carrier formation alone is not a typing phase. |
| `crates/yu-hir/src/module/source_exports.rs:1–59` | Source export/import declarations preserve routes, visibility and syntax; an operator-owner receipt explicitly carries no inferred scheme. | Source route resolution is not Function contract acquisition. |
| `crates/yu-solver/src/candidate_source.rs:1043–1073` | `emit_candidate_source` authenticates the exact HIR-owned `LocalSource`, owner, occurrences and source ownership. | Authenticity does not establish the missing contextual typing rule. |

Thus the old statements that current `ResolvedExpr` lacks App, all formal
annotation inputs are absent, or `SemanticImports` is empty must not be reused
as current evidence. They occur in callback delivery §6 and compatibility
boundary's candidate-owner inventory. Their approved role/order requirements
remain applicable; their dated implementation inventory is not current.

## Discriminating static derivation: body facts precede App construction

This is a source-code derivation, not a run of the solver. The finite worklist
is a LIFO `Vec` consumed by `pop()` (`candidate_source.rs:1208–1211`). Its
`Work::Visit` payload is only `(index, level, SourceRegionId)`
(`:1016–1025`); it carries no expected callback interface.

For the smallest relevant shape `App(callee, Lambda(x, body))`:

1. Visiting any node pushes `Work::Finish(index, level)` (`:1228`). App then
   pushes argument Visit followed by callee Visit (`:1270–1273`). Pop order is
   therefore complete callee traversal, complete argument traversal, App Finish.
2. Visiting the Lambda emits `Action::BeginLambda` (`:1280–1281`), uses its
   own source parameter annotation, and schedules its body (`:1339–1350`).
   Formal registration had already selected **parameter entry** from the
   presence of the outer computation annotation (`:1104–1116`). This is the
   Value/Computation axis, not Pure/Handler receiver-role selection.
3. The body Visit/Finish actions complete before the Lambda Finish. Lambda
   Finish forms its `LambdaRecipe` and emits `Action::Lambda`, then EndLambda
   (`:2092–2113`). No App-derived expected context has intervened.
4. Only at the enclosing App Finish does the code form
   `CandidateRelation::Apply` (`:1867–1872`), register `ApplySourceInput`
   (`:1912–1923`), and append the corresponding Candidate action. That input
   retains authentic callee/argument endpoints, entry-use registration and
   optional receiver attachment, but no `(F_cb, beta, Slots(beta))`
   (`candidate_call.rs:38–62`).
5. The action interpreter executes the resulting sequence by increasing
   `frame.next` (`candidate_source.rs:2422–2466`). Its native App demand is
   constructed later from the already generated argument/result endpoints
   (`shadow_apply.rs:4302–4341`). The observed `NativeInterface` is consequently
   downstream of the literal-body generation. It is not evidence that the
   expected source callback boundary arrived before that generation.

The finite constructor shape is sufficient to discriminate the missing order:
the argument body can be arbitrarily small, including the single Name `x`.
An existing source-retention fixture contains `my value f = f \x -> x` and
its CallTail equivalent (`crates/yu-hir/tests/inline_lambda_local_source.rs:177`).
No fixture was executed here; this is not an assertion that the example has a
known Function-valued formal, passes type checking, or refutes soundness.
Existing annotated-formal fixtures (`candidate_annotated_function_formals.rs:93`)
use already constructed callback values; their checks do not prove contextual
introduction of inline literals.

## Existing partial evidence does not fill the seam

`candidate_formal_annotation` (`candidate_effect.rs:2125`) recursively creates
positive/negative annotated Function terms. The Function recursion
(`:1851–1878`) preserves nested structural paths and effect-port source data;
`FormalPermission` (`:422–438`) retains source owner, scope, formal, occurrence,
path and source row. The constructor publishes permissions and
`formal_domains[parameter]` (`:2194–2204`). This is real retained source
evidence and must not be discarded. It still lacks a source App operation that
selects the declared formal for this use, performs its instantiation, and
delivers the original callback profile to the argument before its body facts.

Likewise, `FormalRegistrationInput.role` is explicitly `Value | Computation`
(`candidate_call.rs:19–31`). Its `receiver_body`, source scope, optional native
root and App receiver attachment are retained inputs to pending Call
construction. The module header labels them inputs, never certificates.
Conflating their entry role with Handler/Pure would violate the governing
callback rule. No claim here assigns effect-row support a receiver role or
proves a complete invocation from a Function term's shape.

## Connection to the original Lean parent

The original roots are `Contracts.lean:128–154`. The relevant original generator
accepts only `Context` and raw `Source` (`OriginalSourceGeneration.lean:84`).
App creates its original atoms/checks, then recurses on callee and argument
with the same context (`:111–123`). Lambda creates a formal context containing
its annotation ID and independently determined entry, then generates its body
(`:132–168`). `Binding` has annotation/entry identifiers but no constructed
callback contract (`OriginalSourceSyntax.lean:188–198`); Annotation itself is
an identifier (`:23`).

`generated_application_ports` (`OriginalSourceChecking.lean:941`) exposes this
unchanged generator equation. `generated_application_checking` (`:957`) obtains
the callee-to-App-descriptor checking judgment **from supplied satisfaction**.
`PortReadout.application` (`:1255`) selects the callee's returned-value port;
it does not acquire a callback formal or contextualize Lambda generation.
`Kernel.atom`/`admitted` (`OriginalSourceGeneration.lean:670`) are independent
semantic inputs, not constructors for the required fact.
`OriginalSourceCallerSchema.lean:3–8,86` explicitly supplies provenance and
table consistency, without constructing an OriginalSource Binding or typing
judgment. These existing equations therefore do not remove the first missing
source-owner premise. This lane neither alters them nor substitutes a supplied
interface/Kernel predicate for the desired conclusion.

The required eventual construction must preserve the same source scope,
assignment, provider, receipt/world and correlated `nu,K,D`; joint Function
compatibility, complete Call/effect/readout obligations and Value-entry
`receipt; Force(D) >>= B` remain intact. Retained Computation entry remains
distinct. Nothing here composes independent concrete successes or strengthens
the final `F_lit <: F_cb` to endpoint equality. The selected mixed-row receipt
remains limited to its approved deep-handler fragment.

## Authentication, checks and scope

All thirteen contract-pinned semantic/source/R224 inputs matched their stated
SHA-256 on intake. The R224 outcome read was
`a71cf89037bd805b7709747d7a8a1966d18bdb87fb73e96aed7d7abe1ed2db5e`.
The R225 contract and all direct semantic inputs were rechecked before freeze.
The supplementary Rust files above matched these SHA-256 values and the pinned
baseline bytes:

```text
6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646  crates/yu-hir/src/module.rs
7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1  crates/yu-hir/src/module/local_source.rs
409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f  crates/yu-hir/src/module/source_annotation.rs
03727fd3918738a48afde7f7a875de60b63b43ac2cc620896a4ed73d8b0a9179  crates/yu-hir/src/module/source_exports.rs
429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be  crates/yu-solver/src/lib.rs
bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49  crates/yu-solver/src/candidate_source.rs
fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f  crates/yu-solver/src/candidate_call.rs
4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15  crates/yu-solver/src/candidate_effect.rs
99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5  crates/yu-solver/src/shadow_apply.rs
ced364cdbca6c19752e0aa2e36b1516f9337484a8c10323fd632fb81a04163d0  crates/yu-solver/tests/candidate_annotated_function_formals.rs
1fe9cc2e03ffb4d633dab22d2d9c8f6a9682d8013feded572fb2251a77442899  crates/yu-hir/tests/inline_lambda_local_source.rs
```

Commands were bounded read-only `rg`, `sed`/`nl`, Python SHA-256 and byte
comparisons, and read-only `git rev-parse`/`git show`. No Lean/Lake, builds,
tests, compiler execution, Cargo, cache writes, Git mutation, temporary file,
new directory, or descendant was used. No oracle, shared transition simulator,
random seed, finite enumeration or mutation experiment was used. The schedule
argument follows the actual producer and consumer code, independently of its
existing tests; it is not a machine-checked theorem. CPU/RAM peaks and exact
wall time were not instrumented; work remained within the 1,200-second lane
budget, with no heavyweight process. General unknown-callee elaboration,
annotation/callback overlap, imported typed interfaces, runtime acceptance,
full effect interpretation and whole-source adequacy remain unverified.

## Frozen handoff and commit packet

Writes are stopped. Sole leased/new/changed path:
`tasks/agent-loop/inbox/source-contextual-elaboration-r225-owner.md`.
No other author or descendant contributed. Independent review is pending;
this author supplies no self-review receipt. The primary owns checks,
adjudication, shared state and Git.

Recommended next action: review this exact source-owner stop alongside the
constructive lane; require the next source-rule proposal to construct both
formal acquisition and pre-body delivery from the original source inputs while
preserving symbolic inference. Do not start another downstream Function-port
probe with the same acquisition premise supplied.

Commit packet: baseline `579df249d52fb57a0ec38e00881036c409dc722c`; exact path
as above; pinned dependency changes: none. Checks already run: source/hash
authentication and eleven baseline byte comparisons; executable/Lean checks:
not run by this lane. Proposed checkpoint message:
`research: trace R225 callback boundary source owner`.
Shared-record delta left to Luna: record the incomplete source-owner result,
parent delta 0, current Rust inventory correction, exact acquisition/delivery
owner, frozen hash, review disposition and stopped worker state.

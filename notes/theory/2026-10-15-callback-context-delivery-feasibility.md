# Callback context delivery: native source seam and remaining premise

Status: research-only source characterization and conditional local derivation;
original callback-context parent OPEN; independent local source review complete
Baseline: `266da3dd6cf73b4b6267919384cce9389d653f46`
Branch: `research/simple-sub-intrusion`
Lease: this file only; leaf, no delegation; verification/integration owner: primary
Method: bounded static constructor/consumer tracing, with separate generation
and admission orders; no executable model, tests, builds or source changes

Primary adjudication: a fresh compiler referee accepted the local obstruction,
source action-order and shared-map results, with one minor wording correction.
Formal-entry/annotation actions are emitted during Visit, so the whole schedule
is not postorder; the corrected argument below uses only the actual relative
orders it needs. No parent B theorem or production change is certified.

## 1. Frozen original statement

For every source application in the bounded domain of
`2026-10-03-callback-context-delivery.md` §§1–6, fix its original callee use u,
direct unannotated inline literal L = `λ x -> e`, lexical environment Γ, actual
source occurrences and binders, and the known ordinary `Value(F_cb)` callback
formal. Fix the already instantiated interface `F_cb` for u and the original
static template β and `Slots(β)`. The interface may contain open variables:
already instantiated does not mean solved or ground. Fix one joint source
assignment/fiber, its original witness scopes and quantifier order, all live
residual constraints/dependencies, occurrence/incidence, `K,D`, `Rel_C`,
`Flow`/`Observe`, directed-weight/subtraction and attachment evidence. Shared
witnesses remain bound once around their original joint formula; rigid
operation binders do not exchange scopes with dependent existentials.

The required B conclusion is that authentic expected callback boundary delivery
precedes the first body constraint generation, selects L's Handler receiver
role/boundary, and independently generates L's parameter, syntax-directed entry,
body and `Result(I_body)` endpoints. It then forms completed `F_lit` and generates
exactly the ordinary completed-interface obligation `F_lit <: F_cb`. This must
preserve the same u, β/profile, assignment and residual lineage without copying
or equating expected value endpoints with synthesized endpoints. It does not
require that every generated inequality succeeds. Parameter entry is independent
of receiver role. Static β is not a dynamically activated receiver boundary.

Existing exclusions remain: explicitly annotated literal and annotation/callback
overlap, unknown callee, retained Computation formal, import/member resolution,
and general source acceptance. The anchor

```text
my apply (f:int -> int) = f 1
my answer = apply (\x -> x)
```

names the ownership path; identity/integer bodies are not restrictions on the
parent statement. This packet does not claim executable acceptance of that text.
Natural supported bodies and original binder scopes remain quantified.

This note does not establish complete Call, effect hygiene, soundness,
principality, normal progress, generalization or production conformance. It
constructs no replacement endpoint denotation, registry gate or early solver
search policy. The original parent retains its owner and OPEN status.

## 2. Authority and retained results

The governing clauses are callback delivery §§2/2.1 (B reference generation,
one completed inequality; A requires equivalence), §3 (entry/runtime order and
static/dynamic boundary distinction), §4 (new literal versus prebuilt Pure
value), and §6 (source/interface supplier plus contextual traversal; no selected
API or implementation authority). The source-indexed realization §§2, 3, 6–7
preserves original joint coordinates and distinguishes conditional B generation
totality from production correspondence. Its reference constructor theorem
does not prove this compiler's missing source consumer.

`2026-10-11-yulang-inference-top-level-principles.md` §§1/1.1, 3–5 requires
native generation/propagation and construction-first evidence, without early
typing search or general rollback requirements. Its hygiene clarification
reuses `2026-10-10-annotation-effect-hygiene-integration.md` §3: typed transport,
owner/view and exact-interface results keep their supplied typed-path,
owner/profile and source-envelope hypotheses. None provides a raw callback
boundary supplier. Receiver-local eligibility remains conditional; equal rows
cannot create an annotation grant. No existing theorem is reopened here.

The independently reviewed local theorem
`2026-10-15-inline-lambda-hir-formation.md` §§1–6 supplies authentic L, its
distinct parameter identity, body index, lexical capture and source positions.
Its explicit callback/solver exclusions remain. No additional parse or binder
reconstruction is needed for this packet.

Rules read: design authority, orchestration budget, agent orchestration
(particularly model routing and proof delegation), compiler engineering,
research lab and Git concurrency; the yulang-proofs skill and prover/config
declarations. Shared task/lab/index records were consulted as locators, not
additional semantics. No unvalidated question bundle was used as authority.

## 3. Actual owners and two distinct orders

Paths in this section are under `crates/yu-solver/src/`; symbols govern if
line numbers move.

| Owner at the pinned baseline | Relevant construction or consumption |
| --- | --- |
| `shadow_apply.rs::solve_mode`, 302–310 | Completes `collect_candidate_mode_scoped` before constructing `InferenceSession` and calling `run_candidate`. |
| `lib.rs::ConstraintBatch::collect_candidate_mode_scoped`, 1143–1155 | Invokes `emit_candidate_source` while collecting a LocalSource definition. |
| `candidate_source.rs::emit_candidate_source`, 539–743 | Allocates component/parameter recipes, original formal registrations, entry mode and source scopes; the work stack traverses source children. |
| `candidate_source.rs`, 680–683 | On Apply, pushes argument then callee on the LIFO work stack, after its Finish continuation. |
| `candidate_source.rs`, 685–728 | On Lambda, retains omission/source identity, emits annotation actions when present, creates body region and visits body. No expected callback input is accepted. |
| `candidate_source.rs`, 913–948 | Finishes Name; even a Value-entry identity-body Name emits its bottom/empty effect constraints during collection. A module Name separately appends `Action::Module`. |
| `candidate_source.rs`, 950–1020, 1069–1085 | Finishes Apply after its children; retains Apply relation/input and appends its action. Finishes Lambda after body; appends its LambdaRecipe/action. Neither recipe carries `F_cb`, β or `Slots(β)`. |
| `candidate_source.rs::step_candidate_source`, 1250–1329 | Executes one immutable scheduled action, advancing only after successful action execution; Module routes incoming/open uses, Candidate and Lambda call their native admission owners. |
| `candidate_scheme.rs::freshen_candidate_graph`, 1040–1054 | Prepares one FreshUse, drives captured bound restoration, returns root term and rows. |
| `candidate_scheme.rs::prepare_candidate_fresh_use`, 1057–1331 | Reconstructs actual structural Function children through one per-use term/row map, alongside context/scope/evidence remaps. |
| `lib.rs::admit_lambda_fact`, 11271–11443 | Independently obtains parameter/body endpoints, entry/body effects and completed positive Function; records and actively constrains its lower into the literal root. |
| `shadow_apply.rs::admit_candidate_fact`, 1521–1642 | Validates source recipe join, constructs ordinary negative application demand and actively constrains callee into it. Its native inputs are retained here after the body actions. |
| `lib.rs` Function decomposition, 12586–12626; `candidate_step_function_dispatch`, 12736–12763 | Constructs contravariant Argument child, retains FunctionPort relation and enqueues that actual child. |

**Generation order.** The collector actually calls `emit` for body constraints
and constructs body recipes. It is not only inventorying raw syntax. For the
anchor's `x` body, the Name Finish arm emits two effect constraints before
collector return. Session creation and the module Name's FreshUse occur only
after collector return. Thus the existing module FreshUse cannot supply an
already instantiated boundary before that body generation on this path.
Even if these two constraints happen to be role independent, they do not prove
that the required boundary was supplied first. Pure identity behavior cannot
erase the parent ordering obligation for arbitrary supported bodies.

**Admission order.** LIFO traversal completes the callee subtree before visiting
the argument subtree, and completes each body before its enclosing Lambda and
Apply Finish. Visit may append formal-entry/annotation actions before a nested
Lambda's body; the whole schedule is not postorder. The relevant relative order
is callee actions before argument actions, and body actions before enclosing
Lambda and Apply admission actions. Consequently a successful
module/local callee routing action executes before the inline argument's body
actions; those execute before Lambda admission, which precedes enclosing Apply
admission. This is a local source-derived scheduling lemma, not an assumed
matching map. Suspension cannot skip an action: `next` advances only after
success; unavailable/failed execution establishes no successful completion.
The lemma does not give callee instantiation before collection-time generation.

The source types make the missing input visible: `FormalRole::{Value,
Computation}` is entry mode, not Pure/Handler receiver role. OmittedFormal
retains omission provenance and explicitly has no semantic consumer.
ApplySourceInput and LambdaRecipe carry no original expected descriptor/profile.
DirectionalIntroduction and ReceiverBoundaryAttachment concern later call/source
associations; neither is the before-body callback-literal context supplier.

## 4. Native subresults that can be reused

### 4.1 Same-use structural child reconstruction

Quantify over each successful call of `prepare_candidate_fresh_use` on a graph
admitted by its existing structural invariants. For every stored node
`i = Function(p,[a,ae,re,r])`, the returned FreshUse term at i is exactly
`mkFunction_p(terms[a],terms[ae],terms[re],terms[r])` from that one FreshUse.
Repeated references to a child index select the same term entry. Older/shared
rows use the existing row allocation decisions; this claim changes none.

Proof: the loop at 1189–1243 skips already assigned terms. An unfinished
Function first pushes its Finish and each unassigned child; its Finish reads
those same four indices and calls the polarity-specific native constructor.
Row nodes read that FreshUse's `rows[row]`. Row preallocation breaks graph
cycles; structural Function dependencies are the captured DAG. A term is
assigned once and subsequently skipped. Induction over this actual work stack
proves the statement and preservation of shared child references. It does not
infer a callback declaration from an arbitrary Function's shape.

This supplies an existing transport mechanism for a source-retained descriptor
locator if its source owner supplies one. It does not supply that locator,
β/profile identity, receiver role, before-body availability or complete replay.
`freshen_candidate_graph` returns root+rows, not the full descriptor join; its
bound loop actually calls restoration consumers, but this local inspection
does not prove universal restoration completion or Call semantics.

### 4.2 Ordinary final comparison direction

Conditional local derivation: suppose the native solver reaches a structural
pair between the actual known callee Function with original callback argument
interface `F_cb` and this source Apply's ordinary negative demand; suppose the
typed Function dispatcher completes successfully. Apply admission constructs
the demand with this actual argument's independently synthesized endpoint q.
The Argument child at `lib.rs:12586` is `upper.argument <: lower.argument`,
therefore exactly `q <: F_cb`, with contravariant Function orientation. The
dispatcher first calls `candidate_function_port_admit(task, Argument)` then
enqueues that same task; it does not assign q to `F_cb` or equate their children.

Lambda admission independently constructs completed `F_lit` and actively admits
`F_lit <: q_L` at the original literal root. For an unwrapped literal q is q_L;
ordinary Group recipes connect q_L to the enclosing argument component when
parentheses retain a Group. These ordinary constraints represent the
completed-interface obligation through the existing source components.
No extra endpoint equality is needed. This is an exact branch-level bridge,
conditional on authentic callee/formal identity and actual pair reachability;
it does not prove those premises from stored constraints, or prove global
bound activation, eventual success, principality or uniqueness of all replay
events. Adding a second special comparison is not justified by this result.

In particular the application demand is a use-generated upper. It cannot itself
supply the declaration's `F_cb`, β or profile. Choosing an arbitrary solved
Function lower, or independently selecting argument/effect marginals, would
replace the frozen source premise.

## 5. Minimized obstruction and decisive next evidence

There is no semantic counterexample to B in this packet. There is an actual
operational obstruction to claiming that the current consumer implements B:

```text
collect body facts/recipes
  < collection returns
  < create inference session
  < execute callee Module/FreshUse
  < execute body actions
  < execute Lambda action
  < execute outer Apply action
```

Current body-generation input has no expected callback role/boundary. Current
FreshUse can reconstruct the right structural children later, but retains no
source descriptor join delivered to a before-generation continuation. An action
marker between Module and body admission fixes neither defect. Calling the
already emitted constraints a deferred syntax skeleton would require evidence
from a changed generator; this note does not reinterpret the existing phase.

The precise remaining source/operational premise belongs jointly to the
declaration/interface constructor and source generator: retain the original
callback descriptor/template/profile and expose its exact same-u instantiated
image to L's generation owner before that owner emits any body constraints.
The literal owner must consume it to select Handler without changing parameter
entry or borrowing expected value endpoints. The final ordinary comparison
must retain that same image and original witness scopes. This is the needed
input/output relationship, not selection of a Rust API or a new semantic layer.

Two tempting routes leave this premise untouched: callee-before-body admission
and structural FreshUse child reconstruction. The proof-obligation-economy
audit classifies before-body introduction as required A/B conformance/natural
inference; source descriptor recovery after discarding its locator is D debt.
The original source application/registration knows the identities; freshening
knows their actual images. Retain their natural join at those owners rather
than inventing another semantic relation or recovering it from solver success.
This classification neither closes nor weakens the parent.

**Smallest useful provisional evidence packet for primary dispatch.** Instrument
only one known declaration/use and its actual inline argument, at the existing
declaration constructor, exact FreshUse Function reconstruction and body
generation owner. Retain the original descriptor locator and β/profile, and
record actual before/after events from those owners. A reversible generation
continuation/prototype may defer this literal's *actual body generation* until
the supplied same-use boundary exists; it must still use ordinary body forms
and native constraints. A synthetic context map or event emitted after body
collection is insufficient. First use the anchor to minimize the seam, then
the parent coverage proof must handle every original supported body, not just
identity. Primary obtains authority for any production/API choice separately.

Falsifiers: any body fact/recipe generated before authentic context delivery;
descriptor image coming from another use; loss of original β/profile or shared
scope; literal parameter/result copied/equated to expected endpoints; body
generation restarted with another typing; special rejection of an originally
supported body; final comparison fed by an arbitrary Apply demand instead of
the same expected contract. Resource failure must terminate the private attempt
without publishing a fabricated successful contextual literal. No generalized
rollback requirement is introduced.

One next action: primary dispatches this bounded owner-level generation/FreshUse
prototype and its falsifiers after authority adjudication, before a dependent
production implementation. Keep the original parent OPEN meanwhile.

## 6. Frozen dependencies, checks and commit packet

SHA-256 at this pass:

| Dependency | Hash |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `90db34173d366ed826b34492da0fb2f1c5422b1b41e43fcda14892ec8415e7ab` |
| `crates/yu-solver/src/candidate_scheme.rs` | `436687cbc8c4ea372d0066f3f8a8e46cfc28223ade163f49864cd3c5039c60e6` |
| `crates/yu-solver/src/candidate_call.rs` | `4689e2ee34c69c9492ecc1a58af15d7c802f44dca82d69f76e3e1520d8d5f3dd` |
| `crates/yu-solver/src/shadow_apply.rs` | `270ee70b331e4095f404fafafdf0731b57dd451c130cdf251aea2b5944d7cc6c` |
| `crates/yu-solver/src/lib.rs` | `b0f7778934a37ec9c642f7e6232cb61e37a1b0768f6af92556cf873f6b2a69f7` |
| Callback delivery design | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| Source-indexed realization | `76874a219ac86068027b1f08a5bc27a12d93a0169a52cebd896a6ff6f2c6b671` |
| Retained hygiene integration | `4a98b5136a9d0d1bdddf135727c5e8779b579bf3c0b76d0524d01c951df34fd4` |
| Top-level principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| Inline HIR proof | `11b3e531cd42f4326a8a2c80902310926a295c24d9c2996e5844e0e085243dde` |

Commands: bounded `cat`, `sed`, `rg`, `sha256sum`, read-only Git baseline/status,
and apply_patch on this lease. No tests/builds/probes, Oracle runs, measurements,
Git mutations, source edits or children. Static checks and final hash are in the
leaf handoff. Budget: one static pass at most 15 minutes, lightweight shell
reads only, no heavyweight process, zero samples; RSS not measured.

Requested runtime: normal `gpt-6.1-sol` / `high` from the primary packet/role
contract. Config registers prover with absent model/effort pins and Sol/high
subagent defaults. Observed effective runtime model/effort: unknown; no Astra
assignment, reload or override claim. Independent review belongs to primary;
the producer does not certify the subresults or parent.

Commit packet: exact path
`notes/theory/2026-10-15-callback-context-delivery-feasibility.md`; baseline
`266da3dd6cf73b4b6267919384cce9389d653f46`; dependency changes by this leaf:
none; dependency hashes above. Research-only, independently reviewed within the
local scope recorded above; parent OPEN. Checks:
static owner inspection only; no executable verification. Proposed checkpoint:
`research: locate callback context generation and FreshUse boundary`.
Shared-record deltas left for primary/curator: retain original callback parent
OPEN; record generation-before-instantiation obstruction separately from the
reusable admission-order and structural-map subresults; assign exact coupled
descriptor retention/before-body generation evidence owner. No task/index/theory
status records were edited by this leaf.

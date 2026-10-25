# Higher-order operational safety candidate

Status: primary Lean checks passed for the candidate; fresh independent review pending. No production authority.
Author: `/root/higher_order_safety_astra_r1`; requested Astra/medium,
observed model/effort UNKNOWN. Contract PARALLEL-THEORY-20261025/r1,
SHA-256 `0751276e8eedf50d113475a0ef1c41b27b7ffd77cc4ccc28761e3cc9e792ff76`.

## Parent and exact domain

The parent is operational safety for every constructor of the accepted finite
`HigherOrderSyntax.lean` research grammar. The stronger full-language/native
safety and original Simple-sub A/B obligations remain OPEN. This candidate
introduces an independent, explicitly defined research transition relation;
it does not infer operational adequacy from the structural embedding or from
successful typing of entry plans. The operational paper remains a proposal.

`Safety.preservation` quantifies over every context, computation, type, event and
raw `Step` derivation. No transition premise contains typing, preservation,
progress or body safety. `closed_progress` quantifies over every closed typing
derivation. `finite_prefix_safety` quantifies over every finite labelled trace,
including the empty trace; its endpoint retains the original type and is a
return, a concrete suspended request/failure, or has another transition.
Explicit failure is an admitted terminal outcome, not an excluded runtime error.
The theorem proves safety, not termination, successful completion, or absence
of explicit failures.

## Operational construction and parent application

Thunks, callable lambdas/wrappers, unions and intersections have recursive
canonical forms through any finite nest of views. A closed bottom value is
impossible. These lemmas are applied directly in closed progress. In particular,
a typed dynamic call cannot reach a literal/noncallable head, and a viewed thunk
has a specific Force transition rather than being omitted from the theorem.

The raw transition relation evaluates only the first computation of bind and
the bodies of scope/expose. It substitutes at bind/union selection, projects
single-child intersections, and enters callable lambda/wrap plans. Scope and
expose remain syntactically active around the executing computation, including
around a suspended operation. A return exits them with an event carrying their
exact annotations. No rules execute inside delay, lambda body, adapter body,
request continuation or the delayed wrap input before the appropriate entry.

Value-mode entry first forces the carrier and binds the returned value into the
body. Computation-mode entry substitutes the original carrier without forcing.
Both then bind the body result into the separate result consumer. A wrap delays
input adaptation inside the carrier passed to the inner call; its output adapter
runs only after the inner result. Definitional equations expose these orders.
Existing checked entry-plan typing and simultaneous substitution supply the
one-step typing proof. Preservation is then applied along each actual finite
trace, and progress is applied to the preserved endpoint. Neither arbitrary
body safety nor an assumed safe-transition supplier appears in these proofs.

`Suspended` is restricted to an explicit failure/request under the three actual
evaluation contexts. `suspended_decomposition` extracts the concrete terminal
node and finite context. Requests retain their operation instance, payload,
continuation and response binder; arbitrary stuck computations cannot become
terminal by definition. `returned_no_step` and `suspended_no_step` establish that
these states really lack an internal transition.

`context_inversion` and `plug_typed` supply the missing context argument for
resumption. `resume_in_context_typed` quantifies independently over every
retained context and every response value typed at the operation response type.
It substitutes the response into the actual request continuation and reinstalls
the entire context. Internal traces exclude external responses; this separate
lemma supplies typed resumption, not authenticity of externally received data.
It does not discharge F1/FK1 or arbitrary foreign native continuation claims.

## Metadata boundary: retention is not adequacy

Each observed view emits its exact `ViewOccurrence`. Lambda entry emits the
complete `LambdaEntryPlan`, including receipt, annotated types, body, consumer
and carrier. Wrap entry emits both complete adapters and the carrier. These
objects retain paths, views and proof-valued path correspondence. `Steps` keeps
all events in execution order. Original annotations are thus available in the
trace even when a computation projection uses `adapterBody`.

This is **syntactic historical retention only**. View observation advances to
the underlying eliminand and records the occurrence; it does not establish the
view's live propagation, licensing, receipt emission, provider ownership,
path mapping or owner discharge. The ledger model is an explicit candidate
semantics, not evidence that discarding those obligations in the real language
is valid. In particular the permissive `PathRule.adapterMap` and absent runtime
map identity remain untouched. Safety of this model cannot prove the paper's
full view/receipt semantics, source authenticity or compiler correctness.

The exact remaining adequacy premise is a relation between actual source/native
states and this annotated transition system that preserves active view/receipt/
owner behavior and covers every actual successor, request instance and response.
If ledger observations cannot represent that behavior, this operational model
needs a separately authorized semantic refinement before application. The full
parent must not be marked closed by the candidate's internal progress theorem.

## Coverage and falsifiers

Every Value/Comp/Adapter constructor of the accepted finite grammar is covered
by typing plus the progress proof. Literal payloads, top/injection/intersection
wrappers and nested callables are retained. Adapters enter through their actual
bodies using the frozen substitution/entry constructions. There is no recursion
primitive or immutable graph representation here; the independent graph lane
owns that separate extension, which is not imported.

The primary should check every declaration and its axiom list, then distinguish:
viewed Force; nested viewed callables; rejected literal application typing;
value versus computation entry; wrap input/output order and inert argument;
request response binder; consumer-after-body order; scope/expose around request;
and arbitrary typed response under an outer bind. Any missing typed constructor,
typing premise in `Step`, prematurely executed carrier/input adapter, missing
request/context field or unsupported metadata-adequacy claim falsifies the
corresponding result. No checker, build or test was run by this author.

## Dependencies, reuse and next owners

Frozen direct imports/reuse:

| Artifact | SHA-256 |
| --- | --- |
| HigherOrderSyntax.lean | ea727d33692bdcbe6b40245b960d01225b556b5334ffab649eea2699930d5972 |
| HigherOrderSubstitution.lean | 19910452c45b20761ec06dc7e15f94c94b95014ff00f3f5296af005b9adf6f30 |
| HigherOrderEnvironment.lean | 84a461fdff85e7321cf090ba2bb72a7d90415515a2da1eb15e1287ef0361ab83 |
| HigherOrderEntry.lean | c9cb839ff6b34ed97c5d72f9e020437d32175cf517a5841a3a024764747c213b |
| Higher-order core design | 50eb7ebd2ed2d155dfeca2e3ce99f3f5b990cc4f1bf101663949a04d8d4b748f |
| Substitution/entry primary verification receipt | 8e5c0f3b8be37879f9009b8e5ed57a2911b6d130e3ae690fc66a3e43554a5a25 |

The three new dependencies were explicitly frozen and supplied by the primary
as Lean PASS with independent review pending. Their producer and primary repair
provenance remains in the substitution-entry assignment/outcome; this author is
not their independent reviewer. Historical first-order safety is not extended
by analogy; no old failure or assumed-transition test is used as adequacy proof.

TODO HO-SAFETY-CHECK-1: primary checks this exact candidate, repairs only after
acknowledged writer STOP, and appoints fresh independent review. Falsifier:
failed elaboration, prohibited axiom, uncovered typed constructor or circular
operational premise. No production edit is requested.

TODO HO-METADATA-ADEQUACY-1: primary owns the separate source/native and semantic
intake. Required evidence relates the source Lambda/Name/Apply and native
`Instruction::Lambda`, `Frame::ValueEntry`, `Machine::lookup`, `Machine::extend`,
Callee/Computation entry, request capture/replay and consumer owners to the
retained operational annotations and actual successor relation. These owners
are inherited locators, not a fresh audit by this author. Falsifier: an actual
accepted step whose view/receipt/owner effect or response binding has no matching
annotated transition. Missing evidence requires an explicit new packet; no code,
source-domain restriction or Simple-sub inference change is authorized here.

Only the three assigned research/handoff paths were written. No scratch files,
Git operations, background processes, checker calls, descendants or compiler
edits were created. The frozen handoff records exact artifact hashes and STOP.

## Primary verification intake

Both authors stopped before primary takeover. Primary is a coauthor of elaboration repairs; all failed checker rows and original author handoffs remain intact. Safety repairs apply context induction hypotheses to the supplied typing derivation, type existential contexts explicitly, and use trace induction with generalized typing indices. Graph repairs rename a reserved binder, eliminate Empty dependently, expose the observed successor and give explicit joined reference types. No theorem premise or operational rule was weakened. Primary records final module/query hashes and axiom reports in `tasks/agent-loop/inbox/20261025-parallel-theory-r1-verification.jsonl`; fresh nonauthor review remains required. No compiler/native tests ran.

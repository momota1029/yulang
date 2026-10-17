# Sprint accepted-call-hir-admission-contract-20261017

Status: ACTIVE, Luna-admitted at baseline `577172e30`.
Branch: `research/simple-sub-intrusion`; baseline commit: `577172e30c7b...`.
Contract revision: 1. Original source and dependency pins are frozen below.

## Original outcome and success evidence

Parent: the original Yulang inference/execution goal with unchanged A/B claims,
quantifiers, source/native correspondence, F1/FK1, N-Transport, complete Call,
soundness, principality and termination. All remain OPEN. This sprint does not
close or narrow a parent theorem.

Fixed outcome: determine whether the already-authoritative source association
and current HIR contracts imply an error-free HIR admission for the exact source
that failed at the prior HIR error gate. Freeze a reviewed structural projection
contract if one follows; otherwise freeze the smallest exact admission/API
decision required before a compiler edit. Structural HIR retention and lexical
identity are distinct from semantic Call typing and solver acceptance.

Exact source: `my id x = x; my apply f = f 1; my answer = apply id`.
Prior evidence: structural parser recovery was empty; the only authorized test
failed `hir.errors().is_empty()` at line 36, before `CandidateInference::solve`.
No retry. Solver, propagation, export, FreshUse and call-record behavior remain
unestablished. Previous sprint closeout is
`tasks/agent-loop/sprints/20261017-accepted-call-vertical-closeout.md`.

Success requires a reviewed artifact that (a) instantiates the current
association rule for each actual source application and identifies what
current HIR lowering retains/emits, (b) preserves callee/argument order,
source occurrence identity, lexical resolution, nesting and recovery/resource
boundaries, and (c) states exactly whether error-free admission is already
authorized. If not, name the exact observable admission/diagnostic or
representation decision. Another inventory alone is not success.

No language-semantic selection, ordinary HIR diagnostic removal, compiler edit,
example/test edit, execution, solver acceptance, source T, SV-CONSUMER-1,
original Call, soundness, principality, or production promotion is authorized.
The user's permission to change workflow and draft bridge rules authorizes this
proposal and review path, not adoption of a new language/API/architecture rule.

## Governing authority and frozen inputs

Authoritative association: `notes/design/2026-09-18-hir-operator-association-first-slice-draft.md`;
`MlArgument` and Call are structural postfix, and nested ML application is
associated left-to-right. Nested-chain ownership amendment:
`notes/design/2026-09-19-hir-associated-chains-ownership-amendment.md`.
Current simple-module admission excludes application syntax and requires
unsupported bodies to retain ordered errors:
`notes/design/2026-09-19-hir-simple-module-resolution-first-slice-draft.md`.
Direct-root complex expression behavior is separately fixed by
`notes/design/2026-09-20-hir-direct-root-expression-slice.md`.
The ordinary source-carrier decision expressly leaves existing HIR admission,
items, errors, diagnostics and occurrence identities unchanged:
`notes/design/2026-10-10-ordinary-hir-successor-carrier.md`.
Inference priority and user-visible natural behavior are governed by
`notes/design/2026-10-11-yulang-inference-top-level-principles.md`.

Exact direct dependency pins at baseline:

```text
crates/yu-hir/src/module.rs                                      2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e
crates/yu-hir/src/shadow.rs                                      2dffd7fd6542eed9fd3346e0672e76197c248be9c84334f341c4d612234b7ee9
notes/design/2026-09-18-hir-operator-association-first-slice-draft.md ff113c3641f791788bea97e22b4f5dfcb91037be523e8198d3add8e6e89e17ed
notes/design/2026-09-19-hir-associated-chains-ownership-amendment.md e78d2d9865e35828e38c353ee77c359850d8be1884828f75aa931be2bf1556f3
notes/design/2026-09-19-hir-simple-module-resolution-first-slice-draft.md 494a6973ced88a031688213990ea380e64cb74fea3bb1396236a8d1bb911f11a
notes/design/2026-09-20-hir-direct-root-expression-slice.md       e2ca3943817e70de5b51bf432d696e3b3fdf90d85539e92ba429c6102691237b
notes/design/2026-10-10-ordinary-hir-successor-carrier.md        c5fb75bdeb302a1f490398589b823f26d296d4cff3889cd0fddd5be4f801dad1
notes/design/2026-10-11-yulang-inference-top-level-principles.md 7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81
crates/yu-solver/tests/research_accepted_call_vertical.rs        78fd0d4c38df86def4cd4aefb37e164f71269eb58cd9a53b370bc42e42f9a963
tasks/agent-loop/inbox/20261017-accepted-call-vertical.md        e4fa2d76284f6713fef74fb34467f9b29e5c91d3c2b9e52ee10f6874f496362a
tasks/agent-loop/sprints/20261017-accepted-call-vertical-closeout.md 58d78ad936498e0484299d5611e81b4126ea7e24bc2a30e64ada6ab7509bdcd3
```

Base/authority also includes `rules/goal-driven-sprints.md`,
`rules/design-authority.md`, `rules/testing.md`, the sprint decision
`notes/design/2026-10-16-goal-driven-sprints.md`, and
`tasks/agent-loop/README.md`. These govern process and are not semantic
premises. Mutable current state is not an author dependency. If a pinned input
changes, stop dependent writing and return to Luna for a versioned contract.

## Continuing lanes and sequence

Proof lane: `/root/astra_accepted_call_hir_projection`, `astra_prover`,
requested gpt-6-astra / medium, <=480s, max six substantive stages. Construct a
source-directed association/projection account for the exact three bindings.
Show the actual left-associated `MlArgument` structure, exact callee and
argument occurrences, binding/formal resolution, and how the existing module
lowerer treats each node. Identify malformed/recovered/unsupported shapes and
resource bounds. Apply the result to the zero-HIR-error gate. Do not infer
semantic call typing, solver acceptance, or any original parent closure.
Exact outputs:
`notes/theory/2026-10-17-accepted-call-hir-projection.md` and
`tasks/agent-loop/inbox/20261017-accepted-call-hir-projection.md`.

After proof stop/freeze, assign `compiler_referee` <=100s for owner/recovery
and representation review. Then Luna/high <=420s drafts the smallest
owner-local HIR admission contract (not code), including observable diagnostics,
identity preservation, source order, nested application, recovery, unsupported
input, depth/resource limits, and required regression cases. Exact outputs:
`notes/design/2026-10-17-accepted-call-hir-admission-contract.md` and
`tasks/agent-loop/inbox/20261017-accepted-call-hir-admission-contract.md`.
After Luna freezes the design, sequential fresh `spec_auditor` <=100s and
`architect` <=100s review. No author/reviewer overlap. Authors do not alter
pinned dependencies or each other's files.

While a lane waits, Luna may inspect only the already-pinned owners and prepare
the original-parent application; no additional write or execution lane starts.

## Resources, boundaries and stop

Fresh cap 1500s: Astra 480, Luna 420, reviews 300, coordination 120, reserve
180. The selector consultation consumes from coordination. No rollover. Preserve
three inherited UNKNOWN writer/lease reservations; at most one author and one
reviewer active at a time; no child descendants. No Cargo/build/test/runtime
command. No library/source/test write lease. No temporary output outside the
four exact artifact/handoff paths.

Stop and report when a reviewed structural rule is established or the exact
missing admission decision is explicit; on a contradictory authoritative rule;
on budget exhaustion; or if source scope/authority must change. New semantics
return as concise options with compatibility and language-spec impact for the
user. Never silently adopt them.

At closeout report only: (1) original premises genuinely discharged, expected
0 unless direct reviewed parent application says otherwise; (2) new compiler
behavior established, expected none because execution is outside scope; (3) the
remaining unproved item and next single cut. A reviewed proposal is not theorem
closure or production authority. Luna alone adjudicates, updates compact state,
stages explicit paths, commits and pushes.

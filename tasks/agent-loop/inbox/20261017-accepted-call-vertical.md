# Frozen implementation handoff — accepted-call-vertical

Sprint / contract: `minimal-cut-and-accepted-source-vertical-20261017`, rev2,
`95f0f1a3751ffa276c89bedd48d969b430b34771db3f528dbf7473c92a036acf`.
Assignment / handoff revision: accepted-call-vertical-20261017 / 3 (post-run correction).
Parent and scope: original inference/execution goal; independent accepted-source
verification contribution only. Original A/B, Call, FIRST-RESULT-ADEQUACY,
N-Transport, soundness, principality and termination remain OPEN.
Owner: `/root` (Luna primary). No coauthors or descendants.

## Selected source and result

Exact source in both leased files:

```yu
my id x = x; my apply f = f 1; my answer = apply id
```

Source UTF-8 SHA-256:
`bdf41b8059d37dea354a6b6e45a4e0a9f5a0dc412bcee40efb44a0a8bff10ba1`.

The regression was designed to require no structural parser recovery and no HIR
errors before ordinary `CandidateInference::solve`, then check candidate
ownership, conflicts, all three exports, the two module-definition FreshUses,
and source-owned call records. The sole authorized run had no parser recovery,
but failed the zero-HIR-error assertion at line 36 before `solve`; none of the
subsequent solver, propagation, export, FreshUse, or call-record assertions ran.
The only established implementation fact is that this exact source is not
zero-HIR-error under the selected lowering path. No accepted-source vertical
was established, and the run proves no source T, original Call soundness,
native same-witness theorem, or OPRESP semantics.

## Frozen leased outputs

- `crates/yu-solver/examples/research_accepted_call_vertical.rs`
  SHA-256: `79936fb0de85fbe49509623a6fb325d76517254f7adea45439cfbc995e95b8f7`
- `crates/yu-solver/tests/research_accepted_call_vertical.rs`
  SHA-256: `78fd0d4c38df86def4cd4aefb37e164f71269eb58cd9a53b370bc42e42f9a963`
- `tasks/agent-loop/inbox/20261017-accepted-call-vertical.md`
  SHA-256: recorded by the post-run correction receipt.

Direct owners and pins are those in the rev2 contract: HIR diagnostics and
local-source accessors, parser recovery, CandidateInference, source/call and
effect owners, and the existing lifecycle test used only as an API/fixture
reference. No library, existing fixture, expected-output or semantic file was
changed.

## Verification and remaining boundary

Formatting performed only on the two new Rust files with `rustfmt --edition
2024`; no formatter/CI command has been run. The sole planned verification,
after pre-run regression review, is:

```text
cargo test -p yu-solver --features shadow-apply-candidate --test research_accepted_call_vertical
```

One invocation, at most 120 seconds, no retry. It does not imply that the
companion example was executed. Review must check that each expected relation
comes from the selected source and authenticated candidate observations, with
no duplicated candidate-side calculation. Record the exact executed target
and distinguish known repository formatter failures from new-code results.

Proof disposition remains separate: frozen Astra artifact `0a174a481728eb97e381bfe5fb6e04fa090751606b44fd8fd4ee13b467f888d2`; compiler review CLEAN and spec review CLEAN. FIRST-RESULT-ADEQUACY is OPEN at complete same-provider challenge inclusion, correlated Result/Effect/future observation action, and nonidentity residual discharge. OPRESP-DEFAULT-1, ENTRY-1 and C-OMIT remain unresolved/unadopted. No original theorem premise is discharged by this implementation.

Worker state: Luna authoring STOPPED; source files remain frozen after the sole test run.
No example execution or other Cargo/runtime command was performed.

## Sole test receipt — revision 2

The pre-run regression review was CLEAN, but the one authorized command was
executed once and failed at the required zero-HIR-error assertion:

```text
cargo test -p yu-solver --features shadow-apply-candidate --test research_accepted_call_vertical
```

Observed: `yu-solver` test target compiled in 7.73s; one test started, zero
passed, and `accepted source must produce no HIR errors` failed at test line 36.
Exit code 101; total command duration 7.8s. The failure occurs before
`CandidateInference::solve`, so this run establishes neither source acceptance
through the solver nor the later export/FreshUse assertions. It does establish
that this exact fixture is not a zero-HIR-error source under this lowering path.
No retry was made or authorized. No unrelated formatter/CI check ran; formatter
status is therefore separate and unknown. The companion example was neither
compiled as an example target nor executed.


## Independent post-run review

A fresh read-only regression review confirmed all supplied source and output
hashes, the one-run transcript, and the failure boundary above. It found one
low-severity reporting issue in revision 2: the intended downstream assertions
were described as established behavior. This revision corrects that wording.
No code, test, example, diagnostic expectation, or execution transcript changed.
The review author was `/root/accepted_call_vertical_regression_postrun`; requested
regression_auditor / gpt-6.1-sol / low, observed model and effort UNKNOWN; charged
90 seconds; STOPPED with no edits, reruns, or descendants.

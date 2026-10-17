# Frozen implementation handoff — accepted-call-vertical

Sprint / contract: `minimal-cut-and-accepted-source-vertical-20261017`, rev2,
`95f0f1a3751ffa276c89bedd48d969b430b34771db3f528dbf7473c92a036acf`.
Assignment / handoff revision: accepted-call-vertical-20261017 / 1.
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

The regression asserts no structural parser recovery and no HIR errors, then
runs ordinary `CandidateInference::solve`. It checks that the candidate owns
that HIR, has no candidate conflicts, exports all three source definitions,
authenticates both module-definition uses in `answer` as FreshUses, and retains
the source-owned formal and module call records expected from the two actual
source applications. These checks exercise the accepted source → local HIR →
candidate source/call records → solve → export/FreshUse path. They establish
bounded implementation behavior only; they do not prove source T, original
Call soundness, any native same-witness theorem, or OPRESP semantics.

## Frozen leased outputs

- `crates/yu-solver/examples/research_accepted_call_vertical.rs`
  SHA-256: `79936fb0de85fbe49509623a6fb325d76517254f7adea45439cfbc995e95b8f7`
- `crates/yu-solver/tests/research_accepted_call_vertical.rs`
  SHA-256: `78fd0d4c38df86def4cd4aefb37e164f71269eb58cd9a53b370bc42e42f9a963`
- `tasks/agent-loop/inbox/20261017-accepted-call-vertical.md`
  SHA-256: `TO_FILL_HANDOFF_HASH`

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

Worker state: Luna authoring STOPPED; outputs frozen for pre-run review. No
tests, builds or runtime executions have run in this assignment.

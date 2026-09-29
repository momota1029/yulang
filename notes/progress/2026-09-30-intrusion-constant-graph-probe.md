# Intrusion constant-function prepared-graph probe

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Reference: frozen Yulang2 Oracle `a58eefc3`
Classification: focused source-path characterization; no semantic theorem proved

## Observation

A temporary Rust unit test ran the actual Oracle source path on
`pub k x = 1`. Instrumentation at the first
`compact_root_for_generalize` result observed a Function argument containing
`TypeVar(2)`, with
`constraints().bounds().of(TypeVar(2)) == None`. The generalized compact root
saved for the member contains an empty argument node, consistent with the
rendered `any -> int` scheme and zero binders.

This establishes that the constant-function witness's negative-only argument
is unconstrained in the observed prepared compact view. It supplies the
missing premise for applying the conditional greatest-Top/contravariance
erasure lemma to this one fixture. It does not prove the general projection
rule, the denotation assumptions, or erasure when the argument has bounds,
another occurrence, or an enclosing identity.

## Method and scope

The probe used the disposable worktree
`/tmp/yulang-intrusion-constant-graph-probe`, detached from frozen Oracle
revision `a58eefc3`. Command:

```text
cargo test -p infer scratch_oracle_constant_function_prepared_graph -- --nocapture
```

Result: one focused test passed. The instrumentation and temporary test were
removed with the scratch worktree afterward. The frozen Oracle worktree was
not modified. No primary-branch compiler source changed; the design draft,
Oracle ledger, task state, and denotation audit record the observation.

## Next proof obligation

Prove the member root projection/erasure rule for the selected finite graph
class, including negative variables with bounds, shared occurrences, and
environment anchors. The single `k` fixture is characterization evidence
only. Intrusion principality, ordered root-transition simulation, publication,
and incoming-use simulation remain open.

# Visible local StateSlot restart playground

Date: 2026-10-05
Status: bounded executable characterization; candidate transition model only
Review: one independent compiler_referee found no blocking or major issue;
two minor scope/coverage findings were repaired and the focused checker rerun.
Governing sources: [Yulang3 architecture](../../docs/yulang3-architecture.md)
§§6.9, 8.3; [source-state realization boundary](2026-10-03-concrete-compatibility-boundary.md#source-state-realization-boundary-2026-10-03);
[research-playground direction](../design/2026-10-04-inference-research-playgrounds.md).

[`tools/research_local_state_restart.py`](../../tools/research_local_state_restart.py)
enumerates 512 combinations of four `(static slot, runtime activation)` keys,
binary initial values, captured aliases, update targets, and replacement values.
The candidate store model copies the finite environment, replaces only the
target activation, and keeps captured aliases as references to their complete
key. Every modeled alias read observes the replacement exactly when it names
the updated key; another activation of the same static slot is unchanged.

Two deliberately incorrect models have small distinguishing traces:

- Capture-by-value returns the old `0` after a slot replacement with `1`.
- Using only `StateSlotId` as a runtime key changes a sibling activation from
  `0` to `1` when the other activation is updated.

These are counterexamples to the mutants under the candidate model, not
counterexamples to Yulang. §6.9 specifies declaration-origin identity and says
that it is not runtime cell identity; §8.3 selects pure continuation restart.
The source-state audit does not yet give transition equations for declaration,
read, update replacement, capture, or re-entry after resumption. The model
therefore does not establish that this store abstraction or candidate
activation key is the source semantics.

No handler, request/response, raw resumption, general first-class reference,
typed `Rel_C`/`K,D,ν` relation, HIR lowering, or source-wide `EnvStore/JointWF`
is modeled. The broader source-state bridge remains open. This experiment adds
no compiler behavior, semantic rule, or production authority.

Verification: `python3 tools/research_local_state_restart.py` passed
(512 cases, both mutants distinguished); source compilation via Python's
`compile()` passed; `git diff --check` passed. No workspace tests or production
checks were run.

# Captured local State across multi-shot resume: finite probe

Date: 2026-10-05
Status: bounded research characterization; candidate transition assumptions only
Review: one independent compiler_referee found no blocking or major issue; a
minor missing delayed-branch read assertion was repaired and rerun
Governing sources: [ordinary computation semantics](../design/2026-10-02-ordinary-computation-semantics-package.md),
[State bridge boundary](2026-10-04-local-state-capture-observation.md),
[single-restart probe](2026-10-05-local-state-restart-playground.md), and
[executable playground direction](../design/2026-10-04-inference-research-playgrounds.md)
Implementation authority: none

[`research_local_state_multishot.py`](../../tools/research_local_state_multishot.py)
exhausts 324 small configurations of two declaration-origin slots, two
runtime activations, three values, and two resumed replacement branches. Under
the candidate rule that a resumed branch receives its own live store and local
replacement creates that branch's successor store, a captured slot read after
the replacement observes that branch's value. Reusing one immutable incoming
store across branches leaves sibling activations unchanged.

Two executable mutants have minimal witnesses:

- Snapshot capture reads initial `0` after the branch replaces the captured
  slot with `1`.
- A shared mutable store lets the second multi-shot branch's replacement `1`
  change a later read from the first branch, whose replacement was `0`.

This probe is intentionally conditional. It supplies the state passed to each
resume and the successor-store equation; the current source design does not
yet define either the local replacement/read transition or multi-shot store
branching equations. The examples therefore distinguish implementation
mutants under the candidate model, not Yulang semantics. No State rule,
carrier, handler policy, or inference behavior is selected. The result does
not close the source-state blocker and does not alter the stable-core `start!`
fixture's established same-invocation observation.

Verification after the review repair: `python3
tools/research_local_state_multishot.py` passed (324 cases and both mutants);
Python compilation passed; `git diff --check` passed.
No workspace tests, builds, or production changes were made.

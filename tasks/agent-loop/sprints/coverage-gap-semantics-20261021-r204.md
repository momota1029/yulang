# Sprint R204 — Interpret Capture coverage and source-set gaps

Status: CLOSED, solo read-only source audit.

## Goal and authority

Apply R203's successful R187-fixture readback to the original open R183 source-to-Capture frontier question without changing the fixture, source domain, inference behavior, or frozen R183 proof note. This is a source interpretation step under the user's ongoing proof goal. No subagents and no compiler invocation.

Parent remains `notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1, 6–7. R183 remains open. R203 readback note: `notes/theory/2026-10-21-r203-capture-fiber-lineage.md`.

## Exact scope

Read `candidate_context.rs` coverage definitions and constructors, the R203 result, and the R183 §6 gap. Write only this contract, `notes/theory/2026-10-21-r204-coverage-gap-semantics.md`, and `tasks/agent-loop/current.json`. Do not edit solver source or frozen R183 artifacts. No compiler invocation. Run the required agent-sprint unit test after updating current state. Record whether nonzero coverage is evidence of a source-law counterexample or a limitation of the passive observer.

## Outcome

Decode the observed masks and trace their constructor origin. Preserve the distinction between absent source events on a relation and absence of an original constraint path. Return the next exact source/native premise for R183 without promoting fixture observations to a theorem.

## Closeout

The observed masks are generated as explicit unavailable-evidence flags by the observer. This readback therefore identifies a passive evidence limitation, not a source-qualified counterexample. OwnerEmission and ExtrusionLink admissions unconditionally carry gaps for unavailable processing antecedents, ordinary seed authentication and missing antecedent; FreshUse inherits its antecedent snapshot mask and adds the Replay-use antecedent gap. The three relations without source events do not by themselves prove the original provider constraint was lost. R183's universal source-generated frontier law stays open.

# Scoped omitted-formal Replay vertical

Sprint `npair-original-c-elimination-and-replay-cause-20261018`, contract rev2
SHA-256 `a8f31edcdcb568e26fe49464811a241e07513cea25e39118950db4481351cd33`.
Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN; original
conditions closed: 0.

## Implementation

Added a small accepted source to the research example and one focused
`candidate_graph_call` regression:

```yu
my invoke f = f 1; my id x = x; my received = invoke id
```

The example authenticates parser ownership, exact HIR binding owners and the
source keys for both `invoke`'s Apply and `received`'s Apply. It runs
`CandidateInference::solve_scoped_experiment`, requires the candidate to observe
that HIR with no conflicts, and joins the exact omitted-formal directional
introduction to its Call/Apply/native demand and registered formal. The
`received` call is also joined to its source owner, Apply and source key. With
`YU_CALL_REPLAY_OBSERVER=1`, the existing typed observer streams Replay rows to
stderr; command evidence must contain a row for the authenticated `received`
call index with `native_root_matches=true` and both ordered endpoint checks
true. This source-level capture and observer output are structural evidence.

The added regression checks the omitted formal's exact HIR-owned Apply,
directional-introduction owner/formal/checking occurrence, native-demand
identity, scoped solve success and conflict absence. The old annotated
`receive` fixture was not edited.

## Evidence and boundary

Reused the already-reviewed private typed observer in `shadow_apply.rs` and its
provenance note `notes/progress/2026-10-18-npair-ordered-replay-observer.md`.
Its join streams typed `Dependency::Replay` child/ordered endpoints through a
scoped demand to the matching source-call index and native root; it does not
retain new state or alter solver semantics. Reused the previous complete
negative capture (80 Replay dependencies, 186 relation flows, zero
`demand: Some`) only to identify the former run's missing demand-bearing path.
That capture is not a semantic failure and proves neither this new source's
acceptance nor its Replay row.

No `candidate_context.rs` or `shadow_apply.rs` change was made. The new behavior
remains provisional until the exact focused test and example command each run
once after a fresh independent CLEAN review, a primary-owned release receipt,
and a capacity measurement of at least 120 seconds. A failed command or missing
matching typed Replay row stops this packet; no retry is authorized. This is not
the original fixed-c proof, source-domain approval, parent closure, or
production cutover. F1/FK1, N-Transport, soundness, principality, termination
and full correspondence remain separate/open.

## Checks and runtime

`git diff --check` passed. No Cargo command, build, test or example run was
started. Rev1 omitted the `shadow-apply-candidate` feature required by the
focused test module and example; Luna corrected both commands in frozen rev2.
The corrected exact commands remain pending independent CLEAN review and a
fresh Luna release/capacity receipt:

```sh
timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo test --offline -p yu-solver --features shadow-apply-candidate candidate_graph_call --lib
timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo run --offline -p yu-solver --features shadow-apply-candidate --example research_scoped_formal_replay
```

Requested model/effort: Luna/high; observed model/effort: UNKNOWN/UNKNOWN. No
descendants or scratch outputs.

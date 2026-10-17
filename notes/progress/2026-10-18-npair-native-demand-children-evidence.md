# N-pair native-demand children evidence

Sprint `npair-operation-field-and-demand-children-20261018`, contract
revision 1, SHA-256 `c5aabeb141d4f9df33aaa18e60e2dd158f35d7605fce5a74d1310424f6ec0da8`.

## Outcome

The one permitted harness command did not reach execution. The exact query
reviewed CLEAN before the run had SHA-256
`93eafb6c9a90de9ca44d75d82c16ce0b5ac7802926e5891358ab4235e0c8f03c`; its
temporary fixture had SHA-256
`5a6627896bb5817b5e665fa531223755a3951bdb8fe3018ac09eb8d7691e1f52`. All
direct compiler dependency pins matched the contract. The reviewed query
required exactly one Apply in `received`'s exact HIR owner and checked owner,
occurrences, pointers, source keys, scopes, checking occurrence and cause. It
used `CandidateInference::source_call` and the four typed native accessors; it
did not export `received`'s result root for demand children. Aggregate replay
and relation-flow APIs were marked `UNOBSERVED` for same-call linkage.

At 2026-10-17 20:32:42 UTC, with 180 seconds measured remaining, the sole
authorized command was run with a 120-second timeout:

```sh
timeout 120s cargo run --offline --manifest-path crates/yu-solver/Cargo.toml --example research_source_registration --features shadow-apply-candidate
```

It exited 101 during compilation of the example. The first diagnostic was
E0308 at `research_source_registration.rs:162:33`: comparing the value
`expression.source` with `&SourceNodeKey` `key` expected `SourceNodeKey` but
found `&SourceNodeKey`; rustc suggested dereferencing `key`. Equivalent key
reference errors occurred at lines 163–164 and 218–232. E0369 also reported
that `LocalSourceScope` has no `PartialEq` at lines 227, 234 and 235. There
were 12 example compilation errors total. No source/HIR/candidate runtime
output was produced.

The example was then repaired only at those compiler-diagnostic sites: source
keys are dereferenced for comparisons, and scope equality is checked by
matching each `LocalSourceScope` variant and comparing its contained identities.
This post-run example is SHA-256
`25bcd770ed40e10f0f2b621dfe63d26d71178430ae8f787deb346c6a087985ca`. It was
not rerun or independently reviewed; compilation and runtime behavior remain
unverified. The fixture was restored byte-for-byte to its baseline hash
`969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`.

The original parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains
OPEN, with original conditions closed `0 -> 0`. No native-demand observation,
same-call Replay linkage, source theorem, or production result follows from a
compile failure. The source proof's Operation field projection and authentic
Call returned-provider/result action are a separate lane and remain open here.

## Checks, resources, and stop

Only the single authorized Cargo command ran; it failed as above. No tests,
second build, second Cargo invocation, probe, Git operation, or scratch output
was used. Lane clock start was 20:29:42 UTC. The command began at 20:32:42 UTC
with 180 seconds remaining. Writer work stopped after query repair and receipt
preparation; no remaining-cap estimate is used to authorize more work. Requested
model/effort: Luna/high. Observed model/effort: UNKNOWN/UNKNOWN. Fixture bytes
are restored; no process or descendant remains active.

## Revision 2 continuation outcome

Under contract revision 2, SHA-256
`b5ed6d202ed87465e07ef7ea97516fc79a6ef2bd5385e86785709f4397b8f366`, the
query-only compiler fixes received independent CLEAN review at exact example
SHA `25bcd770ed40e10f0f2b621dfe63d26d71178430ae8f787deb346c6a087985ca`.
The temporary fixture SHA was
`5a6627896bb5817b5e665fa531223755a3951bdb8fe3018ac09eb8d7691e1f52`; all five
direct compiler dependency pins matched.

At 20:36:41 UTC, with 329 seconds measured remaining, the same sole authorized
Cargo command ran with a 120-second timeout and exited 0. Cargo reported a
1.82-second build. The harness reached `CandidateInference::solve` with
`candidate.observes_hir=true` and no candidate conflicts. It matched
`source_call[1]` to the `received` definition. Exact owner, Apply pointer,
callee pointer, argument pointer, occurrences, source keys, scopes, checking
occurrence and cause all matched (`true`). The validated native demand was
`TermArenaBrand(1), index 379`; four demand children printed through existing
typed accessors were native argument index 375, argument evaluation effect
377, invocation effect 378, and result 376. The `source_call` observer
validates that these are the NegativeFunction demand's actual four children.
No `received` export/result root was used to obtain them.

The run printed aggregate scoped dependencies, including Replay records, and
relation flows. Those aggregate APIs do not link a record directly to this
call, so `candidate.received_call_replay_flow_linkage=UNOBSERVED` remains the
result. The fixture was restored to baseline SHA
`969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`.

This establishes a bounded candidate source-to-native-demand observation for
the exact HIR Apply, not the original theorem or execution-level Replay
correspondence. HIR still reports UnsupportedItem and UnsupportedExpression
diagnostics in the fixture. Parent closure remains `0 -> 0`; same-w
contribution eta, `T_rho`, N-Transport, H0, and the original Operation
projection plus Call returned-provider/result action remain open. No tests or
other commands ran.

The fresh lane began at 20:36:10 UTC. The command started at 20:36:41 UTC
with 329 seconds remaining. At closeout at 20:36:58 UTC, 48 seconds had
elapsed and 312 seconds remained; the lane stops at this material result.

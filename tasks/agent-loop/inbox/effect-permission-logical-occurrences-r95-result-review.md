# R95 independent execution-result review

Verdict: **FAIL / BLOCKING for R93 candidate acceptance.** The authorized
flattened input was executed and returned exit 1 with elaboration errors.
Two declarations have acceptable printed transitive axiom lists; eight depend
on `sorryAx`. Printed types after an error are not successful proof evidence.
This review accepts the receipt as evidence of a failed bounded check, not as
candidate/kernel acceptance or parent closure.

## Frozen inputs, authorization and resources

Reviewed contract r1 (SHA-256
`787d97362f3ca2d7a6a8e742009408513b0ca73a729228ec430db334727e7a1f`),
manifest r1 (`0cc19b0cc76cd5b9a456d62bb3a7d48d656698afefd22c1bc3eccfbd4ed4142c`),
input review (`9b694c2c29ab4c3b88cfd456862ce101f5249d72cfa5cbee83d477ae1aa890a0`),
and frozen verification receipt (`6a2aca0dfac25074b7b05e0a70a6fa2eedbd877ed92644df0349be6b64d76e45`).
Hashes were independently recomputed. Verification receipt: 261,582 bytes.

The authorization specifies exactly one invocation of
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --stdin -j1 -M1024`,
with one process, 120 seconds, 1,024 MiB, no output files or retry. Its recorded
executable hash matches the manifest:
`bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.
I did not execute that executable. I independently reconstructed stdin in
memory with only the two specified leading inter-module imports removed:
106,897 bytes, SHA-256
`8bd62910afba8530f2140bd5b150db0d5fb5281c4651b87a88f78c51dc53d0d7`.
This matches the authorization, manifest, input review and execution receipt.

The receipt attests that authorization commit
`64200c8997e55938670c9dccaac1351f0e4e558e` and state commit
`abc8309c9bc01f6e1382d934b5116374c3f3ad95` were pushed before execution.
The parent supplies frozen result HEAD/remote `9adf2070e`. No Git operation was
permitted or performed; pushed provenance is therefore primary-supplied
attestation, not an independently queried remote fact.

Recorded execution: 2026-10-31T16:56:35.571454+00:00 to
2026-10-31T16:56:48.146995+00:00, 12.576 seconds, one Lean process, one job,
peak child RSS 928,752 KiB, no timeout, exit **1**. These recorded values fit
the call envelope. Stderr is empty; the errors are in stdout. The retained
pre-execution `NOT RUN` line is historical authorization state; the later
execution section explicitly records the completed failed call.

## All ten printed types and complete axiom census

Prefix: `YulangClosure.OriginalSource.LogicalOccurrencesR93.`
All ten printed types retain the candidate's expected quantifiers and
conclusions: arbitrary index/routes for the first theorem; arbitrary
scope/cursor/route for the two traversal lemmas; arbitrary source category,
Context, source, scope and route for membership/provenance/uniqueness; and
arbitrary App/Lambda operands, Mark, Formal and incoming scope for their
exact equations and inventory results. No printed type rescues an invalid
proof term.

| Declaration | Complete reported axioms | Classification in this input |
| --- | --- | --- |
| `inventory_iff_lookup` | `propext, Quot.sound` | Accepted local declaration; no `sorryAx` dependency |
| `encode_lookup` | `propext, sorryAx` | Failed proof elaboration; recovery hole |
| `observe_eq_follow` | `propext` | Accepted local declaration; no `sorryAx` dependency |
| `source_membership_iff` | `propext, sorryAx, Classical.choice, Quot.sound` | Transitively contaminated through `encode_lookup` |
| `full_route_unique` | `propext, sorryAx, Classical.choice, Quot.sound` | Transitively contaminated through membership |
| `source_provenance` | `propext, sorryAx, Classical.choice, Quot.sound` | Direct elaboration failure plus contaminated dependencies |
| `app_exact` | `propext, sorryAx, Classical.choice, Quot.sound` | Direct elaboration failure; App helper also has errors |
| `lambda_body_exact` | `propext, sorryAx, Classical.choice, Quot.sound` | Direct elaboration failure in all four cases |
| `app_inventory` | `propext, sorryAx, Classical.choice, Quot.sound` | Transitively contaminated |
| `lambda_body_inventory` | `propext, sorryAx, Classical.choice, Quot.sound` | Transitively contaminated |

The complete printed census is at verification receipt lines 3501–3639.
The two clean local declarations do not establish standalone-module acceptance,
the complete candidate, occurrence provenance, or source-to-native equivalence.

## Findings and minimum closure evidence

**BLOCKING — traversal bridge proof fails.** Candidate lines 167–173,
assembled lines 1808/1812; verification receipt lines 61–274. `apply ih` fails
to unify `encode scope cursor` with the reduced `encodeTree`/`encodeForest`
goals in thirteen tree/forest branches. `encode_lookup` consequently has
`sorryAx`; membership and uniqueness inherit it. This violates R95's fixed
success condition requiring all declarations to elaborate with acceptable
axioms. Close by repairing the induction-hypothesis application at its owning
proof and obtaining a separately authorized successful check and complete
clean axiom census; no conclusion weakening or source restriction.

**BLOCKING — provenance witness does not elaborate.** Candidate line 244,
assembled 1883; receipt lines 275–286. After the case split/equality transport,
`hfollow` has the original follow equality while the goal expects the reduced
`some ... = some ...` equality. The supplied conjunction witness is ill-typed.
Close by supplying a correctly transported/reflexive witness in that branch,
then independently review and check the unchanged quantified provenance claim.

**BLOCKING — App construction/equation fails.** Candidate `appRule` lines
264–267 and `app_exact` line 280; assembled 1902–1904 and 1918;
receipt lines 287–408. Six `AtomKind` dotted identifiers lack sufficient type
context, and `rfl` fails in both annotation cases. The printed `app_exact`
type exists only with `sorryAx` dependency. Close the local type inference and
equation proof failures, then check both annotation branches and clean axioms
without changing the generated App rule or its premises.

**BLOCKING — Lambda equation remains unproved.** Candidate lines 321–330,
assembled 1961; receipt lines 409–3500. The output contains unsolved
`none.false`, `none.true`, `some.false` and `some.true` cases: both formal entry
modes and both annotation alternatives fail. It retains unreduced generated
helper structure; this diagnostic alone does not refute the intended equation.
Close with an elaborating proof for all four original branches and a clean
transitive audit, preserving the full telescope and body subtree.

The unused `Prod.exists` simp argument at assembled line 1790 is a warning,
not the acceptance blocker. No semantic counterexample follows from these
elaboration failures. All parent semantic admission/readout, original A/B,
source/native correspondence and production gates remain OPEN. No repair or
second execution belongs to R95.

## Independent resource and writes-stopped receipt

I did not author the candidate or the R95 input review. This is a fresh result
review allocation, independent of the closed R93 review budget. One reviewer,
no descendants; zero Lean/Lake/checker/build/test invocations or retries. Only
read-only inspection, in-memory reconstruction/hashing, UTC clock reads and
this exact leased output were used. No scratch/cache/environment/project copy,
worktree, Git, compiler/source edit or background work.

UTC start: 2026-10-31 16:57:42 UTC.
UTC stop: 2026-10-31 16:59:03 UTC.
Charged elapsed: 81 seconds / 120 seconds.
Only written path: `tasks/agent-loop/inbox/effect-permission-logical-occurrences-r95-result-review.md`.
Writes stopped after this receipt; no execution or background work remains active.

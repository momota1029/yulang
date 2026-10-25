# LEAN-CALL-CONTEXT-TYPING-20261025/r2 — verification-only recovery

Status: FROZEN ACTIVE CONTRACT
Branch / baseline: `research/simple-sub-intrusion` / `227d5d02677aaa2330d1b4da6cb95c1f527fc042`
Primary: Luna

## Purpose and authority

This is a verification-only successor to r1. The unchanged formal proposition is `plugEvaluationContext_typed` as stated in r1. The frozen source candidate and author handoff are reused byte-for-byte; no author, proof edits, implementation edits or semantic changes are authorized.

r1 closed `FAILED_VERIFICATION / UNACCEPTED`: its source-level reviewer was CLEAN, but the preflight pass was not established and the target Lean invocation failed against stale imported outputs. This contract exists only to establish the earliest reproducible dependency result or kernel acceptance of that exact candidate. The proposition, r9 result `SOURCE_INPUT_BLOCKED/UNACCEPTED`, Call A/B, execution adequacy, source/native correspondence, original inference A/B and production gates remain OPEN.

## Frozen inputs

Recheck every hash before compilation. Stop on any mismatch.

| Input | SHA-256 |
|---|---|
| Candidate `notes/theory/lean/YulangClosure/CallContextTyping.lean` | `09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125` |
| Author handoff `tasks/agent-loop/inbox/20261025-call-context-typing.md` | `66164283bf0195aa9c9c072378e174d8dd3cbba4b645afd0fafb7ce192b35907` |
| r1 contract | `ec637a96ccfc766cf586b89fec740ec9480e50580601516ed588591720e43878` |
| r1 outcome | `9ed056210b80b78b944407d122c39b8f2175c4c5f82f583c22b5156f871880c7` |
| `CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `CoreSubstitution.lean` | `fc73d6d60d28f2abb54049a5715751d27df47ad93dbeb8f52966cf98a747bd2f` |
| `CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| `YulangClosure.lean` | `04a209f4aa4a9e8c2848aee11eb16befb6fe4e0b566d4683dd0705f96ccf3b2f` |

Lean is pinned to 4.35.0. Verify the ten explicitly enumerated ignored outputs are under `.lake/` and confirm the candidate/handoff are unchanged. No other path may be written.

## Serialized verification protocol

One Lean process at a time, `-j1 -M1024`. For each command, Luna must record the exact argument vector, working directory, start/end or elapsed time, exit code, stdout, stderr, and SHA-256 of each expected `.olean/.ilean` output. Capture that receipt immediately before starting the next compiler command. A quiet command, file mtime, existing cache, or chained command without per-process exit capture is never PASS evidence.

Compile the four dependencies in this exact order, with `-o` and `-i` pointed to the listed ignored output paths:

1. `CoreSyntax`
2. `Contracts`
3. `CoreSubstitution`
4. `CoreExecution`

Verify each module's pinned source immediately before compiling it. After each command, require exit code zero and both outputs present/hash-recorded before continuing. Stop at the first nonzero exit, timeout, changed input, missing output, or receipt gap. Never launch the candidate after a dependency failure.

Only after all four dependency receipts pass, compile the unchanged candidate to `CallContextTyping.olean/.ilean`. Capture that command and both output hashes. In a subsequent serialized invocation, import the generated candidate, issue `#check YulangClosure.TypedCall.plugEvaluationContext_typed` and `#print axioms YulangClosure.TypedCall.plugEvaluationContext_typed`, and capture its exact exit/stdout/stderr. The entire target compile plus signature/axiom query has a 120-second wall cap. Required axioms are limited to Lean's standard `[propext, Quot.sound]`; no `sorry`, `admit`, custom axioms, unsafe declarations or extra theorem premises are accepted.

All outputs are exactly these ignored files and no others:

- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreSyntax.olean` and `.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/Contracts.olean` and `.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreSubstitution.olean` and `.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreExecution.olean` and `.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallContextTyping.olean` and `.ilean`

## Independent receipt review and resources

After Luna freezes all compiler receipts, assign one fresh nonauthor `compiler_referee` for a read-only audit of input hashes, exact invocation order, exit codes, captured outputs, output hashes, target signature and axiom result. Reviewer cap: 180 seconds. Reviewer runs no compiler, tests or Git. Luna adjudicates; no self-certification.

Fresh total cap **900 seconds**: serialized dependency checks 480 + target compile and query 120 + receipt review 180 + integration/outcome 120. Astra 0. No carryover. The prior r1 grants are closed and cannot be reused. Three unrelated UNKNOWN reservations remain quarantined; maximum new assignment is one reviewer after compiler STOP. No source author is launched.

## Outcomes and stop rule

Success means all dependency and target compiler receipts pass, the exact candidate signature is accepted, the axiom query meets the contract, and the independent receipt review is CLEAN. Only then may Luna mark this bounded formal proposition Lean-checked. This still establishes no source representation, Call operational preservation, execution adequacy, Force/View realization, original inference, source/native correspondence or production theorem.

Any hash mismatch, first dependency failure, stale/missing import, target error, timeout, missing receipt, unexpected axiom or reviewer blocker closes r2 with the exact earliest obstruction. No repair, author, semantic premise, promotion or automatic renewal follows. A repair requires a new separately frozen contract and grant.

Only Luna updates current/outcome, stages the explicit contract/outcome/current and the already-frozen candidate/handoff paths when needed, inspects the outbound range, and commits/pushes non-forced. Outcome path: `tasks/agent-loop/sprints/call-context-typing-20261025-r2-outcome.md`.

# R76 independent review — rejected

Reviewer: `/root/r76_review`, fresh read-only review after both authors STOPPED.

**Verdict: REJECT for R76 closure. Two BLOCKING findings.**

## BLOCKING — Rust source-use occurrence mismatch

`crates/yu-solver/src/candidate_receiver.rs:2360` compares the application checking occurrence with the `DefinitionUse` occurrence; line 2369 repeats the equality. The source collector records the `DefinitionUse` at the callee `Name` (`candidate_source.rs:1786,1791`), while `ApplySourceInput.checking` uses the enclosing `Apply` occurrence (`candidate_source.rs:1911–1918`). In the admitted `answer = relay (provider ())` fixture (`candidate_receiver.rs:2909–2934`), those are distinct HIR nodes. The constructor skips every candidate call, leaves `selected_use` empty and returns `None` before owner selection.

Minimum repair: authenticate the call callee through owner-local HIR and the supported peeling path; match its module-use occurrence and target to the exact `DefinitionUse`, retain the application occurrence separately, and establish a successful constructor witness while preserving duplicate/foreign-owner rejection. Similarity to the older R63 capture mismatch does not justify the new constructor repeating it.

## BLOCKING — Lean proof declarations fail

The exact retained R76 slice failed in audit 2. `SourceInternalChoiceR76.lean:72` leaves an `Except.toOption` goal; lines 87–106 fail to reduce `Except` binds; line 126 uses reserved token `matches`; lines 143 and 149 leave failure-order goals; lines 279 and 291 lack synthesized decision procedures; line 284 has a structure-update syntax error. The axiom output contains `sorryAx` for 10 of 14 declarations, including `ordered_selection_agrees`, `choice_three_premises`, `choice_applies_r66`, and `construction_certifies`. These do not pass the proof gate. Both R76 audit invocations are consumed; no third invocation is allowed by this packet.

The second audit was run with the exact R3 source slice: 35,050 bytes, SHA-256 `bbe5b3a4f36dfc81c9ac40d696b447cbdb4c4b7170af4a00f92258baf3ecd033`; exit 1; stdout SHA-256 `d0f9f8126f850cb373488abd6a49c0fc590f66c42c9d4350fff63a9fa50d32aa`. Full output is retained in the proof handoff.

## Bounded positive observation

The Rust owner-origin loop preserves the examined native order: it skips invalid registrations, checks every eligible recipe cardinality before component comparison, stops at a second match, and does not filter by Function/row. Parameter native root remains distinct from registered Lambda root. These do not overcome the unreachable source-call selection or failed Lean declarations. Compiler behavior is unaffected because this private method has no consumer.

## Independently checked hashes and limits

- Rust source: `a5e9f3cd641f40415a6f2aa1f92fdd2cff9c031c5e64c066f8fde1f792770968`
- Lean module: `28f5c2fc3679e3af4ef2f14bb984307fe036b4c979a3cb91f39ba0c9ebf565c3`
- Rust handoff: `d01be83fd35e9f43acaab981ccbb88522fcdc8ba71e40353313ecd44461135d`
- Proof handoff before the review-header correction: `754610f3bccd83333fcc0412ce5d4e064a53e4c6498b16df893fc20af9e2d79d`
- All 13 source-slice and full-source hashes match R3. Audit 1 stdout is 61,639 bytes, SHA-256 `e7030cc3d9b801fa2d7f7e0f3be6693523243c402da6cd9d5319b8596a831fe3`.

No compiler, Cargo, tests, checker, formatter, Lake, Lean rerun, file writes, scratch, environment, cache, worktree, author contact or descendants. Rust remains uncompiled. Genuine R66 Root, source/native extraction, original A/B and production remain OPEN. Reviewer STOPPED / WRITES STOPPED.

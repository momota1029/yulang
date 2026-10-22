# R325 — runtime member FieldTail source bridge

## Parent claim and current evidence

The active parent is Authoritative R149, adopted within the user's unchanged-Yulang2-samples goal. Types is the exact 142-byte source and requires both inferred entries (`id`, `answer: int`, `name: str`, `pair: (int, str)`) and one captured host write `(42, Yulang)\n`. Console remains the exact 92-byte source and requires ordered writes `hello from Yulang\n`, then `3\n`.

At `d1603fc5d`, candidate inference accepts unchanged Types with no candidate conflicts. The candidate path records exact source-owned member bodies, preserves ordinary member arguments, and dispatches source FieldTails through FreshUse. R325 transports those selected uses into runtime. Exact imported public exports and their local `DefId` dependencies are also compiled from the same observed HIR world; no spelling-based lookup is used.

## Required operational bridge

The runtime must consume a member choice produced by the same successful candidate result. For each runtime FieldTail code site, the candidate supplies authenticated owner/source-owner, occurrence, and selected member identity. The runtime resolves that exact member source from the candidate's HIR world and compiles the ordinary source carrier. Invocation applies the receiver as the first method argument; explicit source method arguments remain subsequent curried parameters.

This construction must not guess from spelling, choose by runtime value shape, or consume a deferred candidate result. If a source code site has two distinct selected members and no source-authorized route distinguishes their uses, runtime construction must reject the mapping. Source identity and the selected member must remain connected across projected member HIR artifacts.

## Proof obligations kept open

1. Candidate selected-use records cover every runtime FieldTail that can execute, including member and operator-provider nested uses.
2. Every record joins to exactly one source HIR artifact, owner, occurrence, member root, and supported carrier.
3. Receiver-first compilation agrees with the source construction for role and implementation members, including explicit method parameters.
4. Runtime continuation, source schedule, laziness, and host-operation order are preserved.
5. The implemented code enforces the above for all accepted paths, including missing, duplicate, ambiguous, and resource-exhausted construction.

A focused test can falsify these joins but cannot prove the universal claim. The no-subagent user instruction means no independent prover or reviewer runs in this sprint; theorem and R149 remain OPEN.

## Result and remaining parent work

Unchanged Types now passes candidate inference, compiles selected member and infix provider roots, follows `std::int::to_string` and other exact imports, and enters the machine. The host-write adapter is derived from the exact `std::io::out::write` operation-path import and its resolved public export identity. It accepts only the matching `SourceOperationId`, a string payload, and the checked `str -> ()` declaration, captures the payload once, supplies unit, and resumes the saved continuation template once.

The exact 142-byte Types source runs through the CLI and returns `(42, Yulang)\n`. Two focused tests cover this output and reject a second use of the same continuation; all 44 playground library tests pass, and `cargo check` succeeds. This closes the bounded R325 implementation outcome only. Console's whole-module entrypoint, all unchanged samples, source/native adequacy, and the parent proof remain open.

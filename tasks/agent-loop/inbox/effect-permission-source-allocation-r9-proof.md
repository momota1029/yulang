# R9 source-allocation Lean construction handoff

Revision: 1. Author: `/root/effect_permission_source_allocation_r9_lean`, registered `lean_prover`. Status: CONSTRUCTED, UNCHECKED; all writes STOPPED at freeze. Primary owns every executable audit and independent review.

## Frozen identity and boundaries

- Artifact: `notes/theory/lean/YulangClosure/FormalPermissionSourceAllocation.lean`, 19391 bytes, SHA-256 `795e63e850f73d75f18f721224d3e0723c187a57c7437ffe3ef08a4dbd80648a`.
- Baseline: R7 revision 2, 17822 bytes, SHA-256 `5f11254fe698905a4d1a24ccb9cfe799058a55a27c9bc01dd66033548d49e6b4`.
- Contract: `tasks/agent-loop/sprints/effect-permission-source-allocation-20261029-r9.md`, SHA-256 `edbdb9062b7cd78066a29ef917e2d46ae93f5bef8873fb3e285e53ef8565550c`.
- Manifest: `tasks/agent-loop/sprints/effect-permission-source-allocation-20261029-r9-inputs.json`, 104 pinned entries, SHA-256 `878348a8d51362170895f1032cac42f213251c7e209971e517c0e083f02a6c17`.
- R8 diagnosis: SHA-256 `2f6d22c337b804b8e30c49ce2dfc11501397c245d34dc5495e0435abd0b9dd2a`.
- Direct import remains `YulangClosure.FormalPermissionAuthenticatedNativeDecode`, SHA-256 `ea97baf7c98becef27df9e0c416d8d5fb00e9e1b5b63f37021b01598231936dc`. No dependency, root import, manifest, compiler, test, scheduling or Git change.

Only the artifact and this handoff were edited. No scratch paths or generated outputs exist from this leaf. Other writers' paths were not modified.

## Original parent and source mapping

The original parent is `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §1: every supported original source program and lawful finite construction history, preserving original typing, required principal coverage, soundness, progress and termination with one coherent source witness. The current qualification correction is `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6: immutable source Value birth levels and SCC in the induced graph at that birth, with the parent preservation obligations still open.

This packet addresses a conditional selected-fragment transcription ending at successful return of `candidate_formal_value_pair`, not that whole-language parent. Inspected exact source: `candidate_effect.rs:1617–1744`; Function evaluates argument value at reversed variance, result value at current variance, argument Effect port at reversed variance, then result Effect port at current variance. Tuple evaluates in source order and rejects empty/effect-bearing elements. Allocation/permission helper boundaries follow the frozen R6 source handoff; no Rust execution is asserted. `FormalPermissionExportWitness.lean:77–83` makes the port decoder witness dependent on entry State, and its `decodeValue` Function branch preserves this exact sequence.

The source fragment still contains Int, Unit, Function and guarded nonempty Tuple; ports remain omitted or negative nonempty concrete without variables. Variables, holes, Bool/Str, positive-concrete/symbolic/delegated ports and failed guards are not added. This selected fragment is the same as the baseline and is not presented as the whole source language.

## Construction changes

Replaced the four failing code-size recursive theorem bodies with two private paired derivation eliminations, `source_pair_checks` and `source_tuples_checks`. Each paired motive concludes decoder equality AND the allocation trace, with shared context fixed and polarity, annotations, code, entry state and decoded output varying. The public four declarations project these conjunctions. `SourcePair.rec` supplies the pair-root induction and `SourceTuples.rec` the tuple-root induction. This removes the sizeOf recursion package whose generated call had the separate R7 line239 polarity mismatch. Exact elaboration of these recursor applications remains to be checked.

Within each Function decoder case, `cases hao` eliminates the argument-port output equality throughout the context BEFORE `port_decoder re` constructs the dependent result witness. Result output and both birth equalities are then eliminated before simplification. Allocation composes argument, result, argument-port, result-port traces in that order with `AllocationTrace.append`. Tuple cons composes the head trace with the tail trace at the actual head output State. Moved the unchanged `source_port_allocation` declaration before the private helpers because the conjunction motives use it.

No public statement, quantifier, relation constructor, FreshReady/FreshStep premise, HelperFrames premise, tuple guard, source cut or witness-sharing requirement changed. The private conjunctions derive both original conclusions rather than assume either.

## Exact public proof surface to audit

All names below are under `YulangClosure.FormalPermissionSourceAllocation`:

1. `fresh_success_ordinal`: arbitrary four aligned Lists and payloads plus FreshReady imply ordinal bound and all four one-entry push lengths.
2. `nonallocating_helpers_frame`: any HelperFrames derivation implies both projected coordinate equalities.
3. `AllocationTrace.append`: compatible chronological traces compose by list append.
4. `fresh_step_equations`: every FreshStep n has ordinal n, next n+1, and preserved permissions.
5. `source_port_event`: any SourcePortSuccess yields the corresponding PortEvent with identical c/p/code/entry/output/births.
6. `port_decoder`: any SourcePortSuccess yields an actual dependent PortDecoded witness whose decoder, output and births match.
7. `source_pair_decoder_correspondence`: for all context, polarity, annotation, code, entry State and decoded output, SourcePair implies decodeValue = some output.
8. `source_tuples_decoder`: the corresponding universally quantified SourceTuples implication for decodeTuple.
9. `source_port_allocation`: SourcePortSuccess implies AllocationTrace from entry nextEffect through exactly births to output nextEffect.
10. `successful_pair_allocation_footprint`: SourcePair implies that same exact allocation footprint.
11. `successful_tuples_allocation`: SourceTuples implies that same exact allocation footprint.
12. `successful_pair_permission_entries`: each SAME retained output entry supplies its Origin, Owned metadata and membership of its allocated row in the output births.
13. `r5_source_allocation_instance`: universally in entry State s and output, the still-explicit SourcePair for the exact R5 tree/code implies output equality, exact retained entries, four consecutive births and final nextEffect s.nextEffect+4.

Actual printed types: NOT_RUN. Actual transitive axiom lists: NOT_RUN. Pinned toolchain files were inspected and specify Lean 4.35.0, no external dependencies, per-process -j1/-M1024. No Lean/Lake version command, elaboration probe, checker, tests or Cargo ran from this leaf because none was released. No acceptance, axiom-free claim, independent review or production approval is claimed.

## Failure evidence and remaining parent application

R6 and both R7 audits remain failed historical evidence; they are not replaced by this construction. R7 attempt 2 stdout hash `bbac3d71f0061f02f6d7b2090ec65140127a77a3572daf336f07776bbf512de5` records the dependent Function rewrite failure and separate polarity-index recursion mismatch. R8 diagnosed both without execution. This revision applies that proposed method but has no executable receipt yet.

The final theorem still applies decoder correspondence to the SAME explicit R5 SourcePair, then uses accepted R5 output equations. The first remaining premise for a concrete source instance is construction of that exact SourcePair with actual FreshReady/FreshStep availability and concrete nonallocating helper frames, owned by the source/native bridge lane and primary. Full permission-prefix preservation/reattachment and native entry State (including any 21 assertion) remain open. Original source preservation, effect hygiene, consumer residual, unequal transport, soundness, principality, termination and production remain OPEN.

## Resource and stop receipt

Finite lane grant: 600 seconds, no descendants. Exact launch wall-clock timestamp: UNKNOWN (primary confirmed no exact timestamp available). First captured live status: 2026-10-29 12:34:49 UTC; subsequent captured statuses 12:35:47 and 12:36:37 UTC, giving 108 seconds of observed elapsed span through the freeze preparation; this is not asserted to be total lane time. Resource use: source reads and two-file construction only; zero executable audit invocations and no generated/cache ownership. Writes STOPPED at revision-1 freeze; available for a bounded explicitly returned repair only if primary audit1 fails within the original lane bound. No autonomous continuation or execution release is assumed.

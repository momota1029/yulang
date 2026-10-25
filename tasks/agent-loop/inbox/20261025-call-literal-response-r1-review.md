# Independent review: call literal response r1–r3

Verdict: **CLEAN**, within the literal representation and formal response-application scope. No blocking, major, or minor finding.

Reviewer: `/root/call_literal_response_review_astra_r1`. I did not author or contribute to the candidate proofs or primary repairs. Requested runtime: Astra/medium; observed model and effort: UNKNOWN. This is an independent source/receipt review, not an independent Lean execution. Root AGENTS.md, AGENTS.pre-sprint.md, current state, sprint workflow and exact r1/r2/r3 contracts were consulted. The primary retains adjudication and Git authority.

## Stage 1: literal representation and preserved safety

The baseline diff against `3a1af4d9c1c31b13d4d6bbc5e12acf3d55b08484` adds seven Val constructors and their typing/erasure cases. CoreSyntax's existing Literal domains are preserved exactly: unit, Bool, Int, UInt64 float bits, String, List UInt8 bytes, List UInt8 path, and String char. Literal.toVal maps unit to the existing Val.unit; there is no second literal-unit constructor. Bytes/path and char/string remain distinct constructors. No character validity, float conversion, integer normalization or native encoding premise is introduced.

CoreSyntax:138–157 defines the total base and value maps. CallLiteralResponse:9–48 proves exact raw atoms, total typing in arbitrary contexts, injectivity, uniqueness of all typing (and thus base typing), and arbitrary rename/substitution invariance. Its literal cases are direct constructor proofs; the data are not erased or replaced by a generic atom.

CoreSubstitution's exact diff adds the seven inert cases in rename/substitution, both mutual typed proofs, and both mutual raw-commutation proofs. Existing computation recursion, lifted binders, context hypotheses and theorem statements remain unchanged. I inspected those mutual proofs and the single-response substitution connection.

CoreExecution is byte-identical to baseline. In particular raw_step_lifts still consumes an arbitrary RawStep from a closed typed image, and raw_finite_safety still quantifies over every finite raw prefix. Closed-thunk/union/intersection inversion and the typed image exclude invalid eliminations; the extension does not replace arbitrary raw successors with a chosen typed transition. Existing raw failure rules are unchanged. This remains safety of the formal fragment, not a claim about every native constructor.

R2's sole ControlComposition change is exactly the two impossible request_progress branches. All ten FrameTyped constructors were inspected: neither typedCallBind nor typedCallAdapter can conclude a FrameTyped judgment. No typing relation, statement or transition changed.

## Stage 2: actual request application

CallLiteralResponse:58–70 constructs Value.original l.toVal and its closed ValueTyped derivation. The original-value typing constructor requires Original.emptyContext; the proof supplies precisely that judgment. The only operation compatibility premise is the explicit `op.responseType = .base l.base` equality.

Both new Control theorems apply the existing initial/completed actual-request theorems with this constructed derivation. Neither takes hv as a premise. Arbitrary world/metadata, actual prefix lengths, literal suffix, operation, continuation, observed views and completed endpoints remain quantified. The initial theorem retains the full length, exact requested head, empty frames, result type, suffix, payload/captured typing, cancellation equality and plugged typing conjunction. The completed theorem retains exact completion length/endpoint and both response typings. The unchanged original theorems continue to permit the existing typed external host protocol.

I inspected captureBind's `upCall Nat.succ` shift, responseSubstitution at index zero, the inverse substitution proof under binders, and both bind/adapter cases of plugResponse_captureFrames. Saved bodies retain their own binder; substituting the response cancels only the inserted response binder. The query's open-variable and mixed-frame examples discriminate frame order and wrong binder shifts; the module also instantiates cancellation with integer 11.

The module's 10 examples plus the final query's 23 examples cover legacy unit, Bool/Int typing separation, 11 versus 23, negative integers, empty/Unicode strings, bytes/path, bit payloads, char/string, and response capture. Universal constructor lemmas supply all payloads and binder maps, not just the examples.

## Stage 3: execution receipts, amendments and trust boundary

Reviewed JSONL SHA-256: `4328e908b606fb5bd8cadb38a32daecfe3d59d92913fd39c95fcf816f046a763`. It has 33 rows and sums to 19.340464230008365 recorded Lean seconds. Every recorded before/after input map agrees; timestamps are sequential. For all 30 admitted modules' latest successful rows and the final query, every recorded current input and output digest was independently recalculated and matched. Imported project objects also match preceding successful output hashes in receipt order. No stale dependent object was found in that chain.

Row 8 retains the missing two Frame branches and three unused-simp warnings; row 9 recompiles the authorized repair successfully. Row 20 retains the historical consumer' errors. The entry-spine r3 contract explicitly labels that predecessor FAILED_VERIFICATION / UNACCEPTED, and its accepted outcome names CallEntrySpineComposition with the identical completeCallEntry_typed proposition. Current row 19 successfully rebuilds that unchanged replacement. All five excluded historical candidates are unchanged against baseline and absent from the final query's import closure. Their exclusion does not remove an accepted theorem.

The final query source matches its embedded receipt bytes and prints 38 signatures and 38 axiom reports. New literal and literal-response construction lemmas use no axioms; the two actual-prefix applications use propext. Other strict targets stay within [propext, Quot.sound]. Exactly resume_reusable, finite_trace_safety and finite_prefix_control report [propext, Classical.choice, Quot.sound]. Their full statements and proof bodies were compared against baseline and are byte-identical; the entire containing file differs only by the two authorized branches elsewhere. README:88 and the accepted lean-control outcome:36 document these dependencies. R3 explicitly corrects the blanket R1 criterion; no additional exception is inferred.

No project axiom, proof hole, unsafe declaration or native_decide was found in the inspected import closure; text-scan hits for admit/sorry were explanatory comments. The checker records source text, streams, UTC times, elapsed monotonic duration, exit/timeout and imported/generated hashes and fsyncs each row. This audits recorded execution; I did not rerun Lean, tests or builds. Existing Control unusedSimp warnings and CallViewedForceReachability's unused hsuffix warning remain recorded; no warning-free claim is made.

## Frozen inputs

| Input | SHA-256 |
| --- | --- |
| CoreSyntax | `c5a25cb7d935159b62f377b7fa88b3e92e4cdf429118d566e53f7859f6ea5375` |
| CoreSubstitution | `ae1dfd4947d9e87c05dfa893b93067175d860ed3b5da000d61257d7789208b55` |
| CoreExecution | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| ControlComposition | `4e8e4cb4fdf106bbffa11e21cd9f7030bda1f296f14e1a554560ea802f02dc5e` |
| CallLiteralResponse | `62cffcd2bcf5ce879c3c7b75ff6908b19470a27e5ca73e5973ec1affbeaac3fb` |
| CallEntrySpineComposition | `a296a5ae738cb3ca8f88a6009495e0fe84a2a394976aafeb4630d6cdd25a11bf` |
| Final query | `adfbfb535d6801a46ce2e17b20174f4707f6a5af3bb9df3f2837185094fd4726` |
| Checker | `2501d5b134d04958b54a92b2d4f0f0cb8bf7ef759c8cd478a0760459d416556c` |
| Author handoff | `c27af8b71ed5a59c4b28256a995183416478bb178bd010df3778a45410f27c56` |

All three contract hashes match the assignment. Full source/native callable, operation-instance, environment, template and trace correspondence, Force realization and original inference A/B remain OPEN. Literal lexical validity/native encoding and source host-response formation are not established here.

STOP receipt: all three assigned stages complete; full 300-second reservation charged, not an assertion of 300 measured execution seconds. No descendants, Lean/build/test/runtime jobs, background processes, Git mutations, external contacts or source edits. Only bounded read/hash commands were used (the unavailable `python` command was retried as `python3`). The only written path is this review. Writes STOPPED after this report; no continuing subprocesses. The report digest is returned separately to avoid a self-referential hash.

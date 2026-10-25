Primary archival note: the following report was delivered by `/root/call_entry_spine_r3_review` in its final response. The reviewer was read-only and did not edit this file. Luna transcribed the report verbatim below after reviewer STOP.

# Frozen independent review — LEAN-CALL-ENTRY-SPINE-20261025/r3

**Verdict: CLEAN.** No BLOCKING, major, or minor finding.

Requested role/effort: `compiler_referee` / medium. Effective model/effort: **UNKNOWN**.

## Scope and evidence

Reviewed the frozen r3 contract, P, Q, composition, relevant syntax/substitution/entry/plugging dependencies, `ControlSyntax.peelWrap`, exact query, full r3 JSONL, and successful P/Q records in the r2 JSONL. Implementer handoffs were hashed for pin validation, without using their explanations as correctness evidence.

All supplied source, contract, query, JSONL, toolchain, and lakefile hashes match. Current dependency and P/Q `.olean`/`.ilean` hashes match the receipt chain. Composition output hashes match both its compilation record and the query's imported-artifact record.

## Correctness audit

- **Cause and ownership:** `CallEntrySpineComposition.lean:33–49` uses the existing existential `consumer` after dependent inversion. Its body and endpoint evidence come directly from `FunctionTyped`. This repairs the branch-local elaboration reference without weakening the theorem or moving responsibility downstream.
- **Exact proposition:** `CallEntrySpineComposition.lean:9–25` matches the contract. No additional hypothesis, narrowed pending list, mode restriction, or source-domain restriction appears.
- **Value entry:** `CallEntryTypingRepair.lean:25–38` forces the typed thunk, binds the lambda body at the argument type, applies the declared consumer, then applies pending adapters.
- **Computation entry:** `CallEntryTypingRepair.lean:39–51` uses the existing substitution theorem to pass the thunk itself. Consumer and pending typing follow the same endpoints.
- **Consumer endpoints:** Composition lines 36–49 transport `hleafPending` through `consumer.output = typedLeafResult`; `hconsumer` supplies the body-to-consumer input equality. Both lambda constructors are covered.
- **Peeling and quantifiers:** `CallPeelingTyping.lean:35–55` constructs decomposition independently of typing. Lines 78–100 preserve arbitrary typed carriers and pending suffixes.
- **Nested wraps:** For outer/inner wraps with distinct intermediate types, peeling constructs `delayArgument (delayArgument carrier outerArgument) innerArgument` and `innerResult :: outerResult :: pending`. Argument typing follows outer input → middle → leaf; result typing follows leaf → middle → outer → original suffix. This agrees with the actual plugging equations.
- **Receipt preservation:** Q's lambda constructor retains the exact receipt, mode, body, consumer, and type fields. Composition returns that same witness. The packet makes no receipt-attachment or operational-preservation claim.
- **Trust boundary:** No `sorry`, custom axiom, `unsafe`, implementation override, or additional operational rule appears in the reviewed modules. The syntax theorem does not claim execution safety, effects preservation, source/native correspondence, Call A/B, inference A/B, or production closure.

## Verification receipt audit

The r3 JSONL contains one reuse record and exactly two invocation records:

1. Composition compilation: exit `0`, elapsed `0.220242s`, no timeout, empty stdout/stderr.
2. Exact query: exit `0`, elapsed `0.206938s`, no timeout, complete five-signature and five-axiom output.

Both record full argv/cwd, UTC boundaries, elapsed time, timeout settings, source hashes, and artifact hashes. The query signatures agree with the reviewed propositions. Reported axioms are `[propext]` for P/composition and none for Q existence, delayed argument typing, and Q preservation, within the allowed set.

I ran no Lean, compiler, tests, or Git operations. Filesystem inspection and hash comparison were read-only. Historical output absence and fsync execution cannot be independently reconstructed from the frozen JSONL alone; no contradictory evidence was found.

**Report frozen; STOP.** The report file was not written because the higher-priority review instruction requires remaining read-only.

# R83 amendment 01 — one diagnostic-directed assembly repair

Status: proposed by primary Luna after failed prefix audit 1; awaiting independent read-only review. Original static review artifact SHA-256: `2398dff142232ac96149f2c0c5775ccec97297b2813a5d32fb37025a70cb200d`. This versioned amendment changes audit sequencing only. It does not change source declarations, theorem statements, semantics, authority, total sprint budget, per-audit timeout, or the absolute three-invocation / 360-second ceiling.

## Trigger and frozen evidence

Audit 1 (`17fb225ba`) used the exact 92,456-byte authorized prefix and exited 1 in 9.072 seconds. Its complete streams are retained in the R83 proof handoff and summarized by `tasks/agent-loop/history/effect-permission-root-closure-20261031-r83-audit1-result.md`. First failures are ambiguous unqualified `unique` in R77/R81 slices opened from both R55 and R57. Later invalid field, unsolved proof goals, fixture reductions and `pp.width` diagnostics are **unclassified** until the prefix is repaired and checked. No R83 theorem is accepted.

## Exact source-only assembly repair

Do not modify R55, R57, R77, R81, the frozen R83 candidate file, or any pinned dependency. Preserve every source slice and hash. In the in-memory assembly only, insert one local notation immediately after the listed original `open` command in each namespace:

```lean
-- In SourceInternalChoiceR77, after its original open:
local notation "unique" => SourceInternalContextR55.unique

-- In ConstructedSourceIncidenceR81, after its original open:
local notation "unique" => SourceInternalContextR55.unique

-- In ConstructedPhysicalRootR83, after its original open:
local notation "unique" => ProviderNativeContextR57.unique
```

The R57 owner declaration is `ProviderNativeContextR57.unique`, whose unchanged source definition delegates directly to `SourceInternalContextR55.unique`; thus both functions have the same body. R77/R81 read source-owned recipe/plan/permission/construction/receipt records; R83 selects a native Origin. The notation resolves only the flattened open-name collision. It does not change any source declaration or theorem.

In the prefix/full query preamble only, remove the diagnostic-rejected line `set_option pp.width 160`. Retain the three accepted `pp.*` options and every `#check` / `#print axioms` query unchanged. This changes output formatting only.

Static input reconstruction before audit 2 produced:

- Repaired dependency body: 78,116 bytes; SHA-256 `886990606fbe866e1e8682664883820d08cffbba2646797f63abc8a3399652d3`.
- Repaired prefix input (215 named checks): 92,550 bytes; SHA-256 `65d6e1c9ccd282bd905203da157135bd9eccf8f0cb1a22a55672c34b52caa302`.
- Proposed repaired full candidate input (13 theorem type and axiom pairs): 102,876 bytes; SHA-256 `fc6f1754dfa0235a4ae2ca4c74102fd103d1eeaad1cc507a2ec80bfc41cddf11`.

The repaired full preamble contains exactly three accepted `pp.*` options followed by thirteen candidate query pairs; it contains no prefix `#check` line. These inputs have not been invoked. The reviewer must independently verify the exact in-memory recipe and hashes.

## Amended remaining sequence

1. Audit 1 is consumed and failed. Preserve it; do not repeat it.
2. Audit 2, after this amendment and its exact input authorization are separately committed and pushed, checks only the repaired dependency prefix. It must exit 0 with all 215 requested declaration checks accepted. Any failure ends R83 incomplete; no further prefix repair is allowed.
3. Only if audit 2 passes, separately commit and push audit 3 authorization, then run the exact full candidate input above. Audit 3 is the last invocation and includes all thirteen unchanged theorem queries and complete transitive axiom reports. A failure ends R83 incomplete with no retry.

Thus the total remains at most three invocations and 360 seconds, with no fourth audit or budget increase. A successful repaired prefix alone accepts no theorem. Original R66/A-B, authenticated Rust extraction, whole-language and production gates remain open.

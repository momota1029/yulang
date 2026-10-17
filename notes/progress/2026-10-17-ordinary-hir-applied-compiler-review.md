# Applied compiler review: ordinary HIR admission candidate

Assignment `HIR-APP-IMPLEMENTATION-REVIEW-1`. Target commit `4f4dcb7b9`,
implementation handoff revision 1 SHA-256
`7c9bfe915052638e915694b5c61790ecff8682e360d8a849df6540af1e7f05f5`,
sprint rev3 SHA-256
`47d160176e72306e150675b2daf6e548d74e1e8d3dfc794c8dbf40ac0ba674e2`.
All five source/test hashes are pinned in that handoff and matched. Review was
read-only; no build/test/Cargo/probe ran. Requested Sol/medium; observed model
and effort UNKNOWN. 180/180 seconds charged.

Result: **1 BLOCKING, 6 major**.

1. `module.rs`: `lower_body` moves `causal_errors` into
   `lower_ordinary_admission(Vec)` and reuses it on the fallback path. Static
   Rust ownership error. Borrow it or return ownership on refusal.
2. `module.rs`: CallTail admission checks associated child count only. A
   recovery-free trailing comma `f(a,)` has two associated children and is
   admitted, although rev4 excludes comma/one-tuple forms. Inspect authentic
   punctuation and refuse the whole body without operand diagnostics.
3. `module.rs`: operand `UnresolvedName` events emit before retained
   `DuplicateDefinition` events, reversing the prior ordinary atom path for
   `my x = 1; my x = missing`. Preserve existing retained record order by
   staging leaf events until the original semantic-error scheduling point.
4. `module.rs`: binding `EvaluationClass` is computed from temporary Error
   placeholder, then only `binding.value` is replaced. Literal and lambda
   classifications can therefore be wrong. Derive/store classification from
   final canonical value.
5. `module.rs`: source nodes/keys are reconstructed by new `(kind, range)` and
   `(kind, range.end)` CST searches. Adopted rev4 §5 requires the actual
   construction-owned source node/key; range reconstruction is not authority.
   Carry authentic ownership through association/descent or produce a reviewed
   alternative with corresponding authority/evidence.
6. `module.rs`: finalization scans all `items` from the beginning for every
   admission root. A module of n simple bindings and V=n,E=R=0 incurs Θ(n²)
   root-search work, outside the output-sensitive error-list cost and existing
   module-pass accounting. Retain owning item position or finalize linearly.
7. New HIR integration test: grouped fixture uses undeclared `f` and `x` but
   expects every Apply error list empty. Supply declarations or assert authentic
   errors. Strengthen source-key checks from mere `is_some()` to exact keys and
   distinct operands.

The reviewer found no unsafe defect in the custom fallible `try_box`; checked R
and byte counts and per-list reservations are present. These do not close the
other findings. Carrier ordering/private staging and the exact standard consumer
claim were otherwise within intended boundaries, but no implementation or
runtime behavior is verified. Parent theorem gates remain OPEN; no tests ran.

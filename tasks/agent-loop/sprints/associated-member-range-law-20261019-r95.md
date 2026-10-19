# R95: test the actual associated receiver range law

Status: ACTIVE; final test-only adjudication of the R93 source bridge.
Revision: 1. Baseline: R94 frozen test and R93 frozen implementation.
Primary: Luna `/root`.

## Outcome and exact source distinction

R94 compiled and ran the focused suite, but its new test incorrectly required
every receiver range to begin with whitespace. Preserve R94's failure receipt.
Before Luna edits, a fresh spec reviewer must read the actual association
constructors and approve this exact expected-value correction.

The existing constructors establish two different range relationships:

1. For the first tail in `x.first.second`, its receiver is the actual
   IdentifierExpression; the HIR range equals the paired source-node range.
2. For the second tail, its receiver is the previous FieldTail continuation.
   `structural_continuation` gives that HIR value the span from the previous
   left receiver's start through the previous FieldTail node's end, while its
   paired provenance source is that FieldTail node alone. The HIR range must
   not be equated with the source-node range.
3. The second receiver's child zero must be pointer-identical to the first
   receiver borrowed from the first associated continuation. Its paired
   provenance source key must resolve through the same artifact's public
   checked `source_position` to the first FieldTail's retained position.

Remove only the overstrong universal `starts_with(' ')` requirement. Preserve
the exact source-node range assertion for the first IdentifierExpression;
replace the second-tail range comparison with the two endpoint equalities
above; check the child-zero pointer and same-artifact source-position join.
Keep field order, occurrence, role/impl identity checks and all other tests.
No whitespace trimming, production change, visibility change or other test
expectation change is authorized.

## Frozen source and prior receipts

Only code-write lease:
- `crates/yu-hir/src/tests/shadow_method_role_source.rs`

Frozen read-only:
- `crates/yu-hir/src/shadow.rs` SHA-256
  `9f7a80055076a01cbd99a3eb9c5bc8c3f0db512f2e84032a53af0eacdad2375b`
- R93 proof note SHA-256
  `6d3a4d0357f99fa9f1b6978bd66d6210409a6e95a1fe046a53239a09f82e012c`
- R93 proof handoff SHA-256
  `3cc0e62f7d9f5e4bc3513b5768e551df2c6f0bc9ecb067ef7001db0431705d34`
- R93 implementation handoff SHA-256
  `3c42330197fec74e032f43baba13aaade700709f0049843403205cda077fab80`
- R93 failed closeout SHA-256
  `c235ca1ad17c45327a2fd98508b2ff1b83a582f803f434090661a0fed65b13b2`
- R94 failed closeout SHA-256
  `541a05aae0bf4fc0d98a23b508f3b3b27c90c3d424a66811290a27e5ae6b3b83`
- Test starting SHA-256
  `9989e108c874d30804bfbe6d2d96d26f3889934dd2104c74f0b161cca0d41e93`

Primary-only paths: this contract, `tasks/agent-loop/current.json`,
`notes/progress/2026-10-19-r95-final-source-correspondence-verification.md`.
Fresh spec reviewer writes only
`tasks/agent-loop/inbox/20261019-r95-spec-review.md` before and after the test
freeze. Fresh compiler/source reviewer writes only
`tasks/agent-loop/inbox/20261019-r95-compiler-review.md` after verification.
All R76/R77/R93/R94 artifacts, source constructors, expected outputs, and
production files are read-only.

## Exact leases and sequence

1. Luna issues the spec reviewer the frozen R95 contract, R93 proof, R93/R94
   closeouts, and unchanged constructor sources. The reviewer confirms that
   the two range equations and identity assertion follow from the cited
   constructors and do not weaken the source claim. No code write before this
   receipt.
2. If spec review is clean, Luna edits only the specified receiver range and
   identity assertions in the one focused test. Freeze the test hash and ask
   the same spec reviewer to confirm the exact delta within its single grant.
3. Luna runs exactly one command:

   `CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-hir --lib shadow_method_role_source -- --nocapture`

4. A fresh compiler/source reviewer checks the frozen R93 code and proof against
   exact constructors and the R95 output; the reviewer reports limitations and
   any blocking/major/minor findings. No author self-certifies.

One timeout, compile error, failed assertion, dependency drift, or blocking/
major finding stops R95. No repair/retry follows under R95.

## Resource cap and boundary

Fresh cap 780 seconds: Luna edit 120, verification up to 120, spec review 180,
compiler/source review 240, integration 120; Astra 0. All R93/R94 elapsed time
remains charged and unknown where not measured. R95 does not reset, refund or
renew those grants. Only this exact test contract receives a fresh envelope.

Success plus clean independent reviews may accept only the bounded
source-correspondence prerequisite. No method typing, lookup, dispatch,
RoleId, constraint generation, evaluator behavior, original Simple-sub/A-B
closure, R50 adoption, R85 adoption or production promotion follows. After
R95, return to one owner-specific evidence slice among the six effect-hygiene
fronts and retain the already verified R92 runnable effectful source example.

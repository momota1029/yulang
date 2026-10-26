# Native integer addition/subtraction: frozen proof handoff

Status: constructed and checker-accepted; independent source/proof review pending.
Baseline supplied by primary: `adfed0dbcc8875ac0c9e66c40a0b967b3e9df073`, branch `yulang3`.
Author: `/root/inference_frontier`, generic fallback for `.codex/agents/lean-prover.toml`; inherited model/effort, effective metadata not observed. No children.

## Original claim, authority and exact improvement

The original numerical semantics requires IntAdd and IntSub to compute mathematical
integer addition/subtraction, without a machine-integer cutoff. The existing
`docs/yulang-operational-type-safety-ja.tex` primitive table, line 901, states the
mathematical-integer interpretation. Its opening source/owner correction remains
in force; this packet does not promote that manuscript to new semantic authority.
The selected top-level inference principles remain unchanged.

The actual native owners are `runtime/machine.rs::decimal_add` and
`runtime/decimal.rs::negate`, reached by the pinned IntAdd/IntSub branches. The
accepted native literal producer argument explicitly left numeric correctness of
decimal_add and Product open; it had established grammar, not arithmetic. The new
proof computes digits by the existing carry/borrow operations and then proves
that the independent positional readback is the required sum/difference. It does
not define output by decoding, adding/subtracting Ints and printing that result.

Parent application: RESPONSE-ENCODING-1 and the existing actual completed-request
native-literal theorem. Two `Control.actual_call_request_completed_*_response`
corollaries apply the arithmetic result to that original theorem, discharge its
`WellFormed datum` producer premise for these computed integer outputs, and fix
the literal to `int (a + b)` or `int (a - b)`. The actual prefixes, current world,
immutable metadata, request, captured frames, suffix, operation instance and
continuation typing conclusions are retained. Input readback, actual acceptance,
operation-instance interpretation and the supplied prefix facts remain explicit.

This is a source-matched Lean model of the inspected successful helper bodies,
with independently checked arithmetic and byte/String transport. It is not a
Lean interpreter of Rust, an extraction certificate, or a proof that allocator
success is guaranteed. Native checked-size/reserve failure may return None before
publication; those allocation gates are abstracted out of the pure helper model.
The source-to-model reading below still requires the fresh independent review.

## Leased outputs and frozen state

- New module: `notes/theory/lean/YulangClosure/NativeIntegerArithmetic.lean`.
- This handoff only: `tasks/agent-loop/inbox/20261026-proof-advance-native-arithmetic.md`.
- Scratch/project/cache: `/workspace/scratch/f98087c7ac1a/native-arithmetic/`.
- Root imports, all existing Lean sources, all compiler sources, source semantics,
  questions, existing records, toolchain/manifests, Git index/refs and expected
  outputs were not changed. The full default import root was not built or edited.
- All 97 copied baseline Lean sources were rehashed against the repository after
  the final proof check; every byte matched. The new tracked module is byte-equal
  to the checker-accepted isolated module.

## Principal declarations and complete quantifiers

In namespace `YulangClosure.NativeIntegerArithmetic`:

```lean
decimalAdd_decode :
  ∀ {left right : String} {a b : Int},
    NativeLiteral.decodeInteger left = some a →
    NativeLiteral.decodeInteger right = some b →
    ∃ output, decimalAdd left right = some output ∧
      NativeLiteral.decodeInteger output = some (a + b)

decimalSubtract_decode :
  ∀ {left right : String} {a b : Int},
    NativeLiteral.decodeInteger left = some a →
    NativeLiteral.decodeInteger right = some b →
    ∃ output, decimalSubtract left right = some output ∧
      NativeLiteral.decodeInteger output = some (a - b)

decimalSubtract_eq_negate_add : ∀ left right,
  decimalSubtract left right = (do
    let negative ← negate right
    decimalAdd left negative)
```

`decimalAdd_result` and `decimalSubtract_result` quantify over any `output` with
the corresponding successful helper equation, and conclude exact decoding.
`decimalAdd_response` and `decimalSubtract_response` additionally construct the
existing closed `TypedCall.literalResponse` typing. Neither output grammar,
arithmetic correctness nor output typing is an assumed premise.

The complete native-request corollary types and every auxiliary theorem type are
printed in the retained checker transcript below. These are actual theorem
declarations, not Prop aliases or assumed LocalLaws instances.

## Source-to-Lean map

| Native owner at the pinned source | Formal construction and consumed theorem |
| --- | --- |
| machine.rs:2831 `decimal_add::split` | `splitAddBytes` validates exactly one optional minus and nonempty ASCII digits, trims the magnitude, and deliberately retains the raw sign of negative zero. `splitAddBytes_spec` proves value preservation. |
| machine.rs:2837 `add_magnitude` | `lowDigits` views the same bytes from the low end; `addDigits` consumes one digit from each nonempty side, uses zero for missing high digits, and handles the carry-only final iteration. `addDigits_value` proves the positional equation; `addDigits_digits`, `carry_step_bounds`, `final_carry_iteration` and `addDigits_length` establish digit/range/finite-iteration facts. |
| machine.rs:2853 `compare_magnitude` | Reuses `NativeIntegerComparison.magnitude_value`, with its normalized canonical magnitude hypotheses. `magnitude_gt_length`/`magnitude_lt_length` recover the length fact needed by the selected subtraction branch. |
| machine.rs:2856 `subtract_magnitude` | `subtractDigit` is the signed i16 borrow branch written in nonnegative-digit coordinates. `subtractDigits` visits precisely the larger input length, retaining the final borrow in its proof result. `subtractDigits_spec` proves `out + rhs + borrowIn = lhs + 10^length * borrowOut`; `subtractDigits_value` derives final borrow zero from the actual magnitude order and digit bound. |
| machine.rs:2869 high-zero trimming and reversal | `magnitudeBytes` reverses the emitted low digits. `trimLeadingKeepOne` expresses the source high-zero loop after reversal. `trimLeadingKeepOne_normalize` and `subtractMagnitude_nativeTrim` prove exact equality to the normalizer used by `subtractMagnitude`, retaining one zero byte. |
| machine.rs:2823 `signed` and 2873–2890 signed dispatch | `signedBytes` suppresses the minus exactly for the singleton zero magnitude; `addParsed` preserves every equal-sign, equal-magnitude, greater and lesser branch. `addParsed_decode` uses the already proved magnitude ordering and the same decoded operands for all branches. |
| decimal.rs:5 `parts`, :28 `negate` | `parseBytes_spec`, `negateBytes`, `negateBytes_decode` reuse the actual parser's normalized zero sign. This is intentionally distinct from `decimal_add::split`. |
| String::from_utf8 successful output | `asciiChar_bytes` and `asciiString_bytes` prove that converting the already computed ASCII bytes produces exactly those UTF-8 bytes; `asciiString_decode` connects them to the pre-existing `decodeInteger`. No textual encoding assumption is input. |
| machine.rs:2774 IntAdd / :2779 IntSub | `decimalAdd` and `decimalSubtract`; the latter's unconditional `decimalSubtract_eq_negate_add` proves exact composition through the intermediate String, including malformed-input rejection. |
| `CallNativeLiteralResponse.actual_call_request_completed_native_literal_response` | `Control.actual_call_request_completed_add_response` and `...subtract_response` supply computed readback/grammar and preserve the full original completed-request conclusion with the exact numerical literal. |

The list representation is a view of the native low-to-high indexed loop, not a
new algorithm: source `index` corresponds to the consumed prefix length, the
remaining lists to the unvisited reversed bytes, and the accumulated emitted
prefix is represented by consing the output digits before the final reversal.
The native final carry branch emits carry mod 10; the proved carry bound makes
that exactly the stored carry and its next quotient zero. The helper's u8 sum is
at most 19; the subtraction i16 intermediate is in [-10,9]. The comparison proof
is reused rather than assumed anew.

Represented cases: arbitrary finite decimal widths; unequal lengths; arbitrary
leading zeros; negative zero; all four sign pairings; cancellation; carry and
borrow chains; trailing result zeros; the final carry-only iteration; absent
high digits; malformed sign, empty and non-ASCII digit rejection at the parser;
exact String byte encoding; add and negate-then-add subtraction; the unchanged
actual request/frame/suffix application.

Omitted from closure: multiplication/Product, division/modulo, other primitive
constructors, IntToString formatting, allocator/resource behavior, Rust memory
safety, native arena/handle-to-formal-value realization, complete operation
instance/source trace mapping, nonprimitive responses, full-paper primitive
execution coverage, graph guardedness, effect/lifetime adequacy, whole-language
progress, and original inference A/B/principality/termination. These remain OPEN
at their original owners; no source domain or authority was narrowed.

## Verification and failures retained

Pinned native Lake: `/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
Observed Lake `5.0.0-src+eb6cafb` / Lean `4.35.0`, release commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
The repository's `check_lean.py` was used with `--project` pointing only to the
isolated project, `--module YulangClosure.NativeIntegerArithmetic`, all named
theorems, and `--timeout 120`. The wrapper imposes 120 seconds per invocation;
`LEAN_NUM_THREADS=1`, `-j1 -M1024` apply to Lean. Commands were issued sequentially.
The initial Lake dependency build used that single-thread environment and normal
Lake scheduling; an independent child-process census was not retained, so the
receipt does not claim an observed process-count trace inside that build.

The final new module has no warnings. The successful audit faithfully replays
seven existing warnings in the frozen NativeIntegerComparison dependency
(unused simp arguments/deprecated if_pos/if_neg); those bytes were not altered.
Thirteen `decide +kernel` examples are checked in the module and discriminate
large carry/borrow chains, the sign branches, zero normalization and bad inputs.
There is no `native_decide`, `sorry`, `admit`, project axiom or checker bypass in
the new module. The full named-declaration audit follows below.

Material construction failures were elaboration/debugging failures, not numeric
counterexamples: checks 2/4/5 fixed unfolding/coercions, unavailable by_contra and
map congruence; 6/7 fixed normalizer sign and cast/zero simplification; 9 fixed
String.toUTF8 simplification; 10 fixed a nonexistent Nat lemma and used kernel
rather than tactic reduction for well-founded digit computations; 14/15 retained
the failed exact Option/String composition proof, repaired before final audit 16.
All original outputs and source snapshots remain in the scratch manifest below.
No failed log was replaced by a success log. No Cargo/compiler test was run.

One incidental artifact was detected after the first handoff write: importing the repository checker to retain its audit source generated `.agents/skills/yulang-lean-proofs/scripts/__pycache__/check_lean.cpython-312.pyc` at 00:42:25.182125 UTC, outside the intended scratch lease. Its exact timestamp identified this packet as the producer. The first cleanup command had a Python syntax error and made no changes; the corrected command removed only that generated bytecode and its then-empty directory, restoring the source tree. The checker source was unchanged. Subsequent inspection used Python `-B`. This cleanup did not change the proof or final checker receipt.

## Remaining owner action and stop

Primary: assign fresh non-author source/proof review of this exact module hash,
especially low-digit/index correspondence, retained negative-zero distinctions,
trim equivalence, signed branch order, and the actual-request premise removal.
Only after that review should the primary integrate the isolated module and
appropriate import target, synchronize shared status and perform Git actions.
There is no new decision requiring user approval in this packet.

The first remaining source/native bridge is the existing mapping of successful
Rust helper invocation/publication and operand handles to the modeled input and
output strings, followed by operation-instance and actual Call trace realization.
The proof does not assume that bridge is already closed. The isolated numeric
helper theorem itself has no missing arithmetic case.

Frozen module SHA-256: `5adb30eb53f64fa4ccad80e83ed78c27f442436f20a8eceb8bc4fb59aac33ad1`.

Author freeze/stop receipt timestamp: `2026-10-26T00:45:47.186884+00:00`. No checker process or descendant remains; writes stop after this handoff is created.

## Input hashes

| Path | SHA-256 |
| --- | --- |
| `tools/inference-playground/src/runtime/machine.rs` | `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e` |
| `tools/inference-playground/src/runtime/decimal.rs` | `83ba443036c7da05f9d72d4bbba98b05c4cab2135062743ffe8e3f05250d1cae` |
| `notes/theory/lean/YulangClosure/NativeIntegerComparison.lean` | `2352602b7047611e9f9722d788ed1acdf9f4960d178c48f6a08b1a7054f93e79` |
| `notes/theory/lean/YulangClosure/NativeLiteralReadback.lean` | `53a745397fed4b319225541b8e764a32cdc72032ca4e8be48d9d4a23d3901c54` |
| `notes/theory/lean/YulangClosure/CallNativeLiteralResponse.lean` | `7b0c27ba851f982d3e13fa3e27c258fe907a56585a92123af14f9ad4d765d2cd` |
| `notes/theory/lean/YulangClosure/CallLiteralResponse.lean` | `62cffcd2bcf5ce879c3c7b75ff6908b19470a27e5ca73e5973ec1affbeaac3fb` |
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `notes/theory/2026-10-25-native-literal-producer-invariant.md` | `1f73d0a4e221cb2d2a182876cf9928ebd3cab34edd6d36f4a46bb6bd3ca9a651` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

## Check-call ledger

16 bounded wrapper calls; aggregate wrapper elapsed 69.752088308 seconds, including Lake/audit subprocess time. These are measured elapsed intervals, not CPU totals.

| Call | Exit | Elapsed seconds | Source snapshot SHA-256 | Output files |
| --- | --- | --- | --- | --- |
| 1 | 0 | 22.703992367 | `None` | `check-001.stdout`, `check-001.stderr` |
| 2 | 1 | 0.955268145 | `4ef57e358d88cf1476a86a358ad74028dc960971d22f20cb862c04293b039364` | `check-002.stdout`, `check-002.stderr` |
| 3 | 0 | 1.063944101 | `d1749095cf658cf3ddfe5055ccc5096ab839f5847eb6914a40ea241622779c76` | `check-003.stdout`, `check-003.stderr` |
| 4 | 1 | 2.274397612 | `ab513b4689889fe3e1bc471486b65dd3e89db27f3d21083af1abf9c87befd5f4` | `check-004.stdout`, `check-004.stderr` |
| 5 | 1 | 2.894659519 | `7397ea177c8a8b42cbbe8d995254718f796f84652d1f04c859df92d7cc26d55a` | `check-005.stdout`, `check-005.stderr` |
| 6 | 1 | 2.052069664 | `59516eaeae34957f9e40828a305e395f5b71e34e5ce967c8d460ddc88011426c` | `check-006.stdout`, `check-006.stderr` |
| 7 | 1 | 2.376005888 | `f6dbd234a9d6a7c8ca9c18ac5c1e948717f976ff4adf059fa0f4b84b05abb80b` | `check-007.stdout`, `check-007.stderr` |
| 8 | 0 | 2.994268417 | `c8d3ea51143f8165b12f3cf5f2b4f6ac1e492aea2c12575f91426bc0f91036e7` | `check-008.stdout`, `check-008.stderr` |
| 9 | 1 | 2.729512215 | `7ebc5ec0629c2301e619c712d8ffd8e6df2ee2695ee5dda0477b0df17dbc527f` | `check-009.stdout`, `check-009.stderr` |
| 10 | 1 | 3.325926304 | `6439ad67f93a078d8da6a4f5b35ce0bd6899151a9d25d792f7a817f96f488327` | `check-010.stdout`, `check-010.stderr` |
| 11 | 0 | 2.843771696 | `d385c1e36eeab40841077a1d23cf585da8a2b025e497b96aae722184785fce90` | `check-011.stdout`, `check-011.stderr` |
| 12 | 0 | 0.614332914 | `744340c0020e79deaed2e5cbcd92267c9125f92cc94e1883b56f048e3fd37cca` | `check-012.stdout`, `check-012.stderr` |
| 13 | 0 | 4.004923582 | `744340c0020e79deaed2e5cbcd92267c9125f92cc94e1883b56f048e3fd37cca` | `check-013.stdout`, `check-013.stderr` |
| 14 | 1 | 3.995444775 | `265bbb6862c9b7d061a99c24c0f910a9870129b9126fdc1c50e4bd98efdabeee` | `check-014.stdout`, `check-014.stderr` |
| 15 | 1 | 4.815305710 | `265bbb6862c9b7d061a99c24c0f910a9870129b9126fdc1c50e4bd98efdabeee` | `check-015.stdout`, `check-015.stderr` |
| 16 | 0 | 10.108265400 | `5adb30eb53f64fa4ccad80e83ed78c27f442436f20a8eceb8bc4fb59aac33ad1` | `check-016.stdout`, `check-016.stderr` |

## Complete named-theorem axiom sets

All 62 named declarations were checked as theorem declarations. Standard axiom union: `propext`, `Classical.choice`, `Quot.sound`; no other axiom occurs. Empty sets are printed explicitly.

| Declaration | Exact axiom set |
| --- | --- |
| `YulangClosure.NativeIntegerArithmetic.addDigits_value` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.addDigits_digits` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.subtractDigit_spec` | `["propext", "Classical.choice", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.subtractDigit_equation` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.little_bound` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.subtractDigits_spec` | `["propext", "Classical.choice", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.subtractDigits_value` | `["propext", "Classical.choice", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.little_append` | `["propext"]` |
| `YulangClosure.NativeIntegerArithmetic.lowDigits_value` | `["propext"]` |
| `YulangClosure.NativeIntegerArithmetic.digits10_append` | `[]` |
| `YulangClosure.NativeIntegerArithmetic.lowDigits_digits` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.byteDigit_spec` | `["propext", "Classical.choice", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.digits_append` | `[]` |
| `YulangClosure.NativeIntegerArithmetic.magnitudeBytes_digits` | `["propext", "Classical.choice", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.lowDigits_magnitudeBytes` | `["propext", "Classical.choice", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.magnitudeBytes_value` | `["propext", "Classical.choice", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.decodeBytes_string` | `[]` |
| `YulangClosure.NativeIntegerArithmetic.splitSign_digits` | `["propext"]` |
| `YulangClosure.NativeIntegerArithmetic.signedBytes_decode` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.canonical_nonempty` | `["propext"]` |
| `YulangClosure.NativeIntegerArithmetic.normalize_false_sign` | `[]` |
| `YulangClosure.NativeIntegerArithmetic.normalize_false_value` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.splitAddBytes_spec` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.splitAddBytes_exists` | `[]` |
| `YulangClosure.NativeIntegerArithmetic.addDigits_nonempty` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.lowDigits_nonempty` | `["propext"]` |
| `YulangClosure.NativeIntegerArithmetic.magnitudeBytes_nonempty` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.addMagnitude_spec` | `["propext", "Classical.choice", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.subtractMagnitude_spec` | `["propext", "Classical.choice", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.signedValue_add` | `["propext"]` |
| `YulangClosure.NativeIntegerArithmetic.signedValue_difference` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.magnitude_gt_length` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.magnitude_lt_length` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.addParsed_decode` | `["propext", "Classical.choice", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.decimalAddBytes_decode` | `["propext", "Classical.choice", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.decodeBytes_exact` | `["propext"]` |
| `YulangClosure.NativeIntegerArithmetic.parseBytes_spec` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.signedValue_negate` | `["propext"]` |
| `YulangClosure.NativeIntegerArithmetic.negateBytes_decode` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.decimalSubtractBytes_decode` | `["propext", "Classical.choice", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.asciiChar_bytes` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.asciiString_bytes` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.digits_ascii` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.byteGrammar_ascii` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.asciiString_decode` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.negateBytes_grammar` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.decimalSubtract_eq_negate_add` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.decimalAdd_decode` | `["propext", "Classical.choice", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.negate_decode` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.decimalSubtract_decode` | `["propext", "Classical.choice", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.decimalAdd_result` | `["propext", "Classical.choice", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.decimalSubtract_result` | `["propext", "Classical.choice", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.decimalAdd_response` | `["propext", "Classical.choice", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.decimalSubtract_response` | `["propext", "Classical.choice", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.carry_step_bounds` | `["propext", "Classical.choice", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.final_carry_iteration` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.borrow_step_bounds` | `["propext", "Classical.choice", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.addDigits_length` | `["propext", "Quot.sound"]` |
| `YulangClosure.NativeIntegerArithmetic.trimLeadingKeepOne_normalize` | `["propext"]` |
| `YulangClosure.NativeIntegerArithmetic.subtractMagnitude_nativeTrim` | `["propext", "Classical.choice", "Quot.sound"]` |
| `YulangClosure.Control.actual_call_request_completed_add_response` | `["propext", "Classical.choice", "Quot.sound"]` |
| `YulangClosure.Control.actual_call_request_completed_subtract_response` | `["propext", "Classical.choice", "Quot.sound"]` |

## Scratch manifest

All paths below are relative to `/workspace/scratch/f98087c7ac1a/native-arithmetic/`. The isolated `project/` contains the 97 frozen baseline modules, the new module, copied fixed project metadata and its owned `.lake/` cache. No cache from another owner was changed.

| File | SHA-256 |
| --- | --- |
| `audit_driver.py` | `c145d184c58368b919d42722ab1b080f6f30d4e3792e2e458ff568c411ed20a4` |
| `axioms.json` | `2ded7998954780f1b50459b199d84974fdd8b40fe5106e53fcb2a24ed7b6b5bf` |
| `check-001.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `check-001.stdout` | `ba12d0bdf73edc37e58aa2184b2d5cfd91b39e212dd6d403855f73c153fc8072` |
| `check-002.lean` | `4ef57e358d88cf1476a86a358ad74028dc960971d22f20cb862c04293b039364` |
| `check-002.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `check-002.stdout` | `3f555895a6e82c3afd82bd2b008e4cbed23fd660f6a2142c0ab30d02f5284f67` |
| `check-003.lean` | `d1749095cf658cf3ddfe5055ccc5096ab839f5847eb6914a40ea241622779c76` |
| `check-003.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `check-003.stdout` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `check-004.lean` | `ab513b4689889fe3e1bc471486b65dd3e89db27f3d21083af1abf9c87befd5f4` |
| `check-004.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `check-004.stdout` | `6f5d9efae14cf338a8a911ec5cfe282c76d5d4def7d564d965b7cfefc2944748` |
| `check-005.lean` | `7397ea177c8a8b42cbbe8d995254718f796f84652d1f04c859df92d7cc26d55a` |
| `check-005.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `check-005.stdout` | `f8d1d69123d811d66c4018850bc9d0c89e69af0d0f4ab4ba61a7ae0eb57041a1` |
| `check-006.lean` | `59516eaeae34957f9e40828a305e395f5b71e34e5ce967c8d460ddc88011426c` |
| `check-006.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `check-006.stdout` | `a0a58a18dc3672f30e04a9b8a208add110cd7b3f6da45e6dcde597db96b1d0b6` |
| `check-007.lean` | `f6dbd234a9d6a7c8ca9c18ac5c1e948717f976ff4adf059fa0f4b84b05abb80b` |
| `check-007.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `check-007.stdout` | `34d3dfd01dd5249ddbfed687f20510f17076d46e9bc20fffbc19b2d65424a516` |
| `check-008.lean` | `c8d3ea51143f8165b12f3cf5f2b4f6ac1e492aea2c12575f91426bc0f91036e7` |
| `check-008.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `check-008.stdout` | `b764393613dc09fce95bcd68a87bc0f0755fb8cd6f0e8fb5786d27bf26555fe1` |
| `check-009.lean` | `7ebc5ec0629c2301e619c712d8ffd8e6df2ee2695ee5dda0477b0df17dbc527f` |
| `check-009.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `check-009.stdout` | `9ae6152f51a42108892cc2cc688edd769e604ecc51beb575f13524d2eb54f625` |
| `check-010.lean` | `6439ad67f93a078d8da6a4f5b35ce0bd6899151a9d25d792f7a817f96f488327` |
| `check-010.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `check-010.stdout` | `6407b9537473047a80f41e328104732b424bd404c40439a5da3c0cfd2ee0d80a` |
| `check-011.lean` | `d385c1e36eeab40841077a1d23cf585da8a2b025e497b96aae722184785fce90` |
| `check-011.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `check-011.stdout` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `check-012.lean` | `744340c0020e79deaed2e5cbcd92267c9125f92cc94e1883b56f048e3fd37cca` |
| `check-012.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `check-012.stdout` | `a55d68d8786b1af749044897686226406d6f89c5377615635bfc18975b94eb5f` |
| `check-013.lean` | `744340c0020e79deaed2e5cbcd92267c9125f92cc94e1883b56f048e3fd37cca` |
| `check-013.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `check-013.stdout` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `check-014.lean` | `265bbb6862c9b7d061a99c24c0f910a9870129b9126fdc1c50e4bd98efdabeee` |
| `check-014.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `check-014.stdout` | `d2cbb507c3ae993da9a3036ca86bf37ab14071279e34d8d97f09233a9a1fe4c4` |
| `check-015.lean` | `265bbb6862c9b7d061a99c24c0f910a9870129b9126fdc1c50e4bd98efdabeee` |
| `check-015.stderr` | `0edf2d238840b65a26de68075c964d099167cf4cae51705f162bcfa4e7addc60` |
| `check-015.stdout` | `5820241be290b33dffc5a712243dfe99994b52f8faf286f54aefaa1356db42fc` |
| `check-016.lean` | `5adb30eb53f64fa4ccad80e83ed78c27f442436f20a8eceb8bc4fb59aac33ad1` |
| `check-016.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `check-016.stdout` | `6a031a47db3037c31147b028721e51811fa5922786153b09daedcfaf1b4ec38e` |
| `checks.jsonl` | `dac387c8856cd0574b40341fe59c2d025494d26f8073794dc8679137fee62b6f` |
| `inputs.json` | `805cecaf3efeddea327ed44bf42b3db12f5fcdfb79ed742468de72b692373f86` |
| `run_check.py` | `67472ad198ca1645609df8c714e25ed952cf8d36c47556579f2717ea293647f0` |
| `source-inputs.json` | `cd7a0a587b7f15d59442424d90d18eaddc355f04501e3b44ceddb741865a5259` |
| `theorems.json` | `39719d67c73722c48b5bf45a35f249c9bb5f0f14fad86e77a41f6354372fb454` |
| `project/NativeArithmeticAudit.lean` | `e218a699643d0804821024968dbdf7196219cd6159aeff82932ddf4cee720442` |

## Full final checker transcript

The following is the complete successful check-016 output, including version commands, the actual build command, every printed theorem type, every axiom result and the helper validation result.

```text
cwd: /workspace/scratch/f98087c7ac1a/native-arithmetic/project
$ /workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake --version
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
[exit 0]
cwd: /workspace/scratch/f98087c7ac1a/native-arithmetic/project
$ /workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake --no-cache env lean --version
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
[exit 0]
cwd: /workspace/scratch/f98087c7ac1a/native-arithmetic/project
$ /workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake --no-cache build +YulangClosure.NativeIntegerArithmetic
⚠ [25/27] Replayed YulangClosure.NativeIntegerComparison
warning: YulangClosure/NativeIntegerComparison.lean:25:33: This simp argument is unused:
  Nat.add_mul

Hint: Omit it from the simp argument list.
  [apply] simp [value, Nat.pow_succ, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/NativeIntegerComparison.lean:26:37: This simp argument is unused:
  Nat.mul_left_comm

Hint: Omit it from the simp argument list.
  [apply] simp [value, Nat.pow_succ, Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.add_assoc]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/NativeIntegerComparison.lean:118:32: This simp argument is unused:
  Prod.fst

Hint: Omit it from the simp argument list.
  [apply] simp only [normalize, he, Prod.snd]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/NativeIntegerComparison.lean:118:42: This simp argument is unused:
  Prod.snd

Hint: Omit it from the simp argument list.
  [apply] simp only [normalize, he, Prod.fst]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/NativeIntegerComparison.lean:213:28: `if_pos` has been deprecated: Use `ite_eq_left` instead

Hint: Replace the deprecated name:
  i̵f̵_̵p̵o̵s̵i̲t̲e̲_̲e̲q̲_̲l̲e̲f̲t̲
warning: YulangClosure/NativeIntegerComparison.lean:219:30: `if_neg` has been deprecated: Use `ite_eq_right` instead

Hint: Replace the deprecated name:
  i̵f̵_̵n̵e̵g̵i̲t̲e̲_̲e̲q̲_̲r̲i̲g̲h̲t̲
warning: YulangClosure/NativeIntegerComparison.lean:219:42: `if_pos` has been deprecated: Use `ite_eq_left` instead

Hint: Replace the deprecated name:
  i̵f̵_̵p̵o̵s̵i̲t̲e̲_̲e̲q̲_̲l̲e̲f̲t̲
✔ [27/27] Built YulangClosure.NativeIntegerArithmetic (4.5s)
Build completed successfully (27 jobs).
[exit 0]
cwd: /workspace/scratch/f98087c7ac1a/native-arithmetic/project
$ /workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake --no-cache env lean -j1 -M1024 --root=/tmp/yulang-lean-audit-f4g4menc /tmp/yulang-lean-audit-f4g4menc/YulangProofAudit.lean
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.addDigits_value
YulangClosure.NativeIntegerArithmetic.addDigits_value : ∀ (xs ys : List Nat) (carry : Nat),
  YulangClosure.NativeIntegerArithmetic.little (YulangClosure.NativeIntegerArithmetic.addDigits xs ys carry) =
    YulangClosure.NativeIntegerArithmetic.little xs + YulangClosure.NativeIntegerArithmetic.little ys + carry
'YulangClosure.NativeIntegerArithmetic.addDigits_value' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.addDigits_value
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.addDigits_digits
@YulangClosure.NativeIntegerArithmetic.addDigits_digits : ∀ {xs ys : List Nat} {carry : Nat},
  YulangClosure.NativeIntegerArithmetic.Digits10 xs →
    YulangClosure.NativeIntegerArithmetic.Digits10 ys →
      carry ≤ 1 →
        YulangClosure.NativeIntegerArithmetic.Digits10 (YulangClosure.NativeIntegerArithmetic.addDigits xs ys carry)
'YulangClosure.NativeIntegerArithmetic.addDigits_digits' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.addDigits_digits
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.subtractDigit_spec
@YulangClosure.NativeIntegerArithmetic.subtractDigit_spec : ∀ {a b borrow : Nat},
  a < 10 →
    b < 10 →
      borrow ≤ 1 →
        (YulangClosure.NativeIntegerArithmetic.subtractDigit a b borrow).fst < 10 ∧
          (YulangClosure.NativeIntegerArithmetic.subtractDigit a b borrow).snd ≤ 1 ∧
            ↑(YulangClosure.NativeIntegerArithmetic.subtractDigit a b borrow).fst -
                10 * ↑(YulangClosure.NativeIntegerArithmetic.subtractDigit a b borrow).snd =
              ↑a - ↑b - ↑borrow
'YulangClosure.NativeIntegerArithmetic.subtractDigit_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.subtractDigit_spec
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.subtractDigit_equation
@YulangClosure.NativeIntegerArithmetic.subtractDigit_equation : ∀ {a b borrow : Nat},
  a < 10 →
    b < 10 →
      borrow ≤ 1 →
        (YulangClosure.NativeIntegerArithmetic.subtractDigit a b borrow).fst + b + borrow =
          a + 10 * (YulangClosure.NativeIntegerArithmetic.subtractDigit a b borrow).snd
'YulangClosure.NativeIntegerArithmetic.subtractDigit_equation' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.subtractDigit_equation
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.little_bound
@YulangClosure.NativeIntegerArithmetic.little_bound : ∀ {ds : List Nat},
  YulangClosure.NativeIntegerArithmetic.Digits10 ds → YulangClosure.NativeIntegerArithmetic.little ds < 10 ^ ds.length
'YulangClosure.NativeIntegerArithmetic.little_bound' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.little_bound
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.subtractDigits_spec
@YulangClosure.NativeIntegerArithmetic.subtractDigits_spec : ∀ {xs ys : List Nat} {borrow : Nat},
  YulangClosure.NativeIntegerArithmetic.Digits10 xs →
    YulangClosure.NativeIntegerArithmetic.Digits10 ys →
      borrow ≤ 1 →
        ys.length ≤ xs.length →
          YulangClosure.NativeIntegerArithmetic.Digits10
              (YulangClosure.NativeIntegerArithmetic.subtractDigits xs ys borrow).fst ∧
            (YulangClosure.NativeIntegerArithmetic.subtractDigits xs ys borrow).fst.length = xs.length ∧
              (YulangClosure.NativeIntegerArithmetic.subtractDigits xs ys borrow).snd ≤ 1 ∧
                YulangClosure.NativeIntegerArithmetic.little
                        (YulangClosure.NativeIntegerArithmetic.subtractDigits xs ys borrow).fst +
                      YulangClosure.NativeIntegerArithmetic.little ys +
                    borrow =
                  YulangClosure.NativeIntegerArithmetic.little xs +
                    10 ^ xs.length * (YulangClosure.NativeIntegerArithmetic.subtractDigits xs ys borrow).snd
'YulangClosure.NativeIntegerArithmetic.subtractDigits_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.subtractDigits_spec
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.subtractDigits_value
@YulangClosure.NativeIntegerArithmetic.subtractDigits_value : ∀ {xs ys : List Nat},
  YulangClosure.NativeIntegerArithmetic.Digits10 xs →
    YulangClosure.NativeIntegerArithmetic.Digits10 ys →
      ys.length ≤ xs.length →
        YulangClosure.NativeIntegerArithmetic.little ys ≤ YulangClosure.NativeIntegerArithmetic.little xs →
          (YulangClosure.NativeIntegerArithmetic.subtractDigits xs ys 0).snd = 0 ∧
            YulangClosure.NativeIntegerArithmetic.little
                (YulangClosure.NativeIntegerArithmetic.subtractDigits xs ys 0).fst =
              YulangClosure.NativeIntegerArithmetic.little xs - YulangClosure.NativeIntegerArithmetic.little ys
'YulangClosure.NativeIntegerArithmetic.subtractDigits_value' depends on axioms: [propext, Classical.choice, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.subtractDigits_value
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.little_append
YulangClosure.NativeIntegerArithmetic.little_append : ∀ (xs ys : List Nat),
  YulangClosure.NativeIntegerArithmetic.little (xs ++ ys) =
    YulangClosure.NativeIntegerArithmetic.little xs + 10 ^ xs.length * YulangClosure.NativeIntegerArithmetic.little ys
'YulangClosure.NativeIntegerArithmetic.little_append' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.little_append
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.lowDigits_value
YulangClosure.NativeIntegerArithmetic.lowDigits_value : ∀ (bytes : List UInt8),
  YulangClosure.NativeIntegerArithmetic.little (YulangClosure.NativeIntegerArithmetic.lowDigits bytes) =
    YulangClosure.NativeIntegerComparison.value bytes
'YulangClosure.NativeIntegerArithmetic.lowDigits_value' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.lowDigits_value
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.digits10_append
@YulangClosure.NativeIntegerArithmetic.digits10_append : ∀ {xs ys : List Nat},
  YulangClosure.NativeIntegerArithmetic.Digits10 xs →
    YulangClosure.NativeIntegerArithmetic.Digits10 ys → YulangClosure.NativeIntegerArithmetic.Digits10 (xs ++ ys)
'YulangClosure.NativeIntegerArithmetic.digits10_append' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.digits10_append
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.lowDigits_digits
@YulangClosure.NativeIntegerArithmetic.lowDigits_digits : ∀ {bytes : List UInt8},
  YulangClosure.NativeLiteral.Digits bytes →
    YulangClosure.NativeIntegerArithmetic.Digits10 (YulangClosure.NativeIntegerArithmetic.lowDigits bytes)
'YulangClosure.NativeIntegerArithmetic.lowDigits_digits' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.lowDigits_digits
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.byteDigit_spec
@YulangClosure.NativeIntegerArithmetic.byteDigit_spec : ∀ {d : Nat},
  d < 10 → (UInt8.ofNat (48 + d)).toNat = 48 + d ∧ YulangClosure.NativeLiteral.AsciiDigit (UInt8.ofNat (48 + d))
'YulangClosure.NativeIntegerArithmetic.byteDigit_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.byteDigit_spec
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.digits_append
@YulangClosure.NativeIntegerArithmetic.digits_append : ∀ {xs ys : List UInt8},
  YulangClosure.NativeLiteral.Digits xs →
    YulangClosure.NativeLiteral.Digits ys → YulangClosure.NativeLiteral.Digits (xs ++ ys)
'YulangClosure.NativeIntegerArithmetic.digits_append' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.digits_append
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.magnitudeBytes_digits
@YulangClosure.NativeIntegerArithmetic.magnitudeBytes_digits : ∀ {ds : List Nat},
  YulangClosure.NativeIntegerArithmetic.Digits10 ds →
    YulangClosure.NativeLiteral.Digits (YulangClosure.NativeIntegerArithmetic.magnitudeBytes ds)
'YulangClosure.NativeIntegerArithmetic.magnitudeBytes_digits' depends on axioms: [propext, Classical.choice, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.magnitudeBytes_digits
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.lowDigits_magnitudeBytes
@YulangClosure.NativeIntegerArithmetic.lowDigits_magnitudeBytes : ∀ {ds : List Nat},
  YulangClosure.NativeIntegerArithmetic.Digits10 ds →
    YulangClosure.NativeIntegerArithmetic.lowDigits (YulangClosure.NativeIntegerArithmetic.magnitudeBytes ds) = ds
'YulangClosure.NativeIntegerArithmetic.lowDigits_magnitudeBytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.lowDigits_magnitudeBytes
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.magnitudeBytes_value
@YulangClosure.NativeIntegerArithmetic.magnitudeBytes_value : ∀ {ds : List Nat},
  YulangClosure.NativeIntegerArithmetic.Digits10 ds →
    YulangClosure.NativeIntegerComparison.value (YulangClosure.NativeIntegerArithmetic.magnitudeBytes ds) =
      YulangClosure.NativeIntegerArithmetic.little ds
'YulangClosure.NativeIntegerArithmetic.magnitudeBytes_value' depends on axioms: [propext, Classical.choice, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.magnitudeBytes_value
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.decodeBytes_string
YulangClosure.NativeIntegerArithmetic.decodeBytes_string : ∀ (text : String),
  YulangClosure.NativeIntegerArithmetic.decodeBytes text.toUTF8.data.toList =
    YulangClosure.NativeLiteral.decodeInteger text
'YulangClosure.NativeIntegerArithmetic.decodeBytes_string' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.decodeBytes_string
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.splitSign_digits
@YulangClosure.NativeIntegerArithmetic.splitSign_digits : ∀ {ds : List UInt8},
  YulangClosure.NativeLiteral.Digits ds → YulangClosure.NativeLiteral.splitSign ds = (Bool.false, ds)
'YulangClosure.NativeIntegerArithmetic.splitSign_digits' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.splitSign_digits
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.signedBytes_decode
@YulangClosure.NativeIntegerArithmetic.signedBytes_decode : ∀ {ds : List UInt8} (negative : Bool),
  YulangClosure.NativeLiteral.Digits ds →
    ds ≠ [] →
      YulangClosure.NativeIntegerArithmetic.decodeBytes
          (YulangClosure.NativeIntegerArithmetic.signedBytes negative ds) =
        Option.some (YulangClosure.NativeLiteral.signedValue negative (YulangClosure.NativeIntegerComparison.value ds))
'YulangClosure.NativeIntegerArithmetic.signedBytes_decode' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.signedBytes_decode
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.canonical_nonempty
@YulangClosure.NativeIntegerArithmetic.canonical_nonempty : ∀ {ds : List UInt8},
  YulangClosure.NativeIntegerComparison.Canonical ds → ds ≠ []
'YulangClosure.NativeIntegerArithmetic.canonical_nonempty' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.canonical_nonempty
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.normalize_false_sign
YulangClosure.NativeIntegerArithmetic.normalize_false_sign : ∀ (ds : List UInt8),
  (YulangClosure.NativeIntegerComparison.normalize Bool.false ds).fst = Bool.false
'YulangClosure.NativeIntegerArithmetic.normalize_false_sign' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.normalize_false_sign
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.normalize_false_value
@YulangClosure.NativeIntegerArithmetic.normalize_false_value : ∀ {ds : List UInt8},
  YulangClosure.NativeLiteral.Digits ds →
    YulangClosure.NativeIntegerComparison.value (YulangClosure.NativeIntegerComparison.normalize Bool.false ds).snd =
      YulangClosure.NativeIntegerComparison.value ds
'YulangClosure.NativeIntegerArithmetic.normalize_false_value' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.normalize_false_value
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.splitAddBytes_spec
@YulangClosure.NativeIntegerArithmetic.splitAddBytes_spec : ∀ {bytes : List UInt8} {p : Bool × List UInt8},
  YulangClosure.NativeIntegerArithmetic.splitAddBytes bytes = Option.some p →
    YulangClosure.NativeIntegerArithmetic.ByteGrammar bytes ∧
      YulangClosure.NativeLiteral.Digits p.snd ∧
        YulangClosure.NativeIntegerComparison.Canonical p.snd ∧
          YulangClosure.NativeLiteral.signedValue p.fst (YulangClosure.NativeIntegerComparison.value p.snd) =
            YulangClosure.NativeLiteral.signedValue (YulangClosure.NativeLiteral.splitSign bytes).fst
              (YulangClosure.NativeLiteral.decimalFold 0 (YulangClosure.NativeLiteral.splitSign bytes).snd)
'YulangClosure.NativeIntegerArithmetic.splitAddBytes_spec' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.splitAddBytes_spec
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.splitAddBytes_exists
@YulangClosure.NativeIntegerArithmetic.splitAddBytes_exists : ∀ {bytes : List UInt8},
  YulangClosure.NativeIntegerArithmetic.ByteGrammar bytes →
    ∃ p, YulangClosure.NativeIntegerArithmetic.splitAddBytes bytes = Option.some p
'YulangClosure.NativeIntegerArithmetic.splitAddBytes_exists' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.splitAddBytes_exists
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.addDigits_nonempty
@YulangClosure.NativeIntegerArithmetic.addDigits_nonempty : ∀ {xs ys : List Nat},
  xs ≠ [] → ∀ (carry : Nat), YulangClosure.NativeIntegerArithmetic.addDigits xs ys carry ≠ []
'YulangClosure.NativeIntegerArithmetic.addDigits_nonempty' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.addDigits_nonempty
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.lowDigits_nonempty
@YulangClosure.NativeIntegerArithmetic.lowDigits_nonempty : ∀ {ds : List UInt8},
  ds ≠ [] → YulangClosure.NativeIntegerArithmetic.lowDigits ds ≠ []
'YulangClosure.NativeIntegerArithmetic.lowDigits_nonempty' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.lowDigits_nonempty
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.magnitudeBytes_nonempty
@YulangClosure.NativeIntegerArithmetic.magnitudeBytes_nonempty : ∀ {ds : List Nat},
  ds ≠ [] → YulangClosure.NativeIntegerArithmetic.magnitudeBytes ds ≠ []
'YulangClosure.NativeIntegerArithmetic.magnitudeBytes_nonempty' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.magnitudeBytes_nonempty
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.addMagnitude_spec
@YulangClosure.NativeIntegerArithmetic.addMagnitude_spec : ∀ {left right : List UInt8},
  YulangClosure.NativeLiteral.Digits left →
    YulangClosure.NativeLiteral.Digits right →
      left ≠ [] →
        YulangClosure.NativeLiteral.Digits (YulangClosure.NativeIntegerArithmetic.addMagnitude left right) ∧
          YulangClosure.NativeIntegerArithmetic.addMagnitude left right ≠ [] ∧
            YulangClosure.NativeIntegerComparison.value
                (YulangClosure.NativeIntegerArithmetic.addMagnitude left right) =
              YulangClosure.NativeIntegerComparison.value left + YulangClosure.NativeIntegerComparison.value right
'YulangClosure.NativeIntegerArithmetic.addMagnitude_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.addMagnitude_spec
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.subtractMagnitude_spec
@YulangClosure.NativeIntegerArithmetic.subtractMagnitude_spec : ∀ {left right : List UInt8},
  YulangClosure.NativeLiteral.Digits left →
    YulangClosure.NativeLiteral.Digits right →
      right.length ≤ left.length →
        YulangClosure.NativeIntegerComparison.value right ≤ YulangClosure.NativeIntegerComparison.value left →
          YulangClosure.NativeLiteral.Digits (YulangClosure.NativeIntegerArithmetic.subtractMagnitude left right) ∧
            YulangClosure.NativeIntegerComparison.Canonical
                (YulangClosure.NativeIntegerArithmetic.subtractMagnitude left right) ∧
              YulangClosure.NativeIntegerComparison.value
                  (YulangClosure.NativeIntegerArithmetic.subtractMagnitude left right) =
                YulangClosure.NativeIntegerComparison.value left - YulangClosure.NativeIntegerComparison.value right
'YulangClosure.NativeIntegerArithmetic.subtractMagnitude_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.subtractMagnitude_spec
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.signedValue_add
YulangClosure.NativeIntegerArithmetic.signedValue_add : ∀ (negative : Bool) (a b : Nat),
  YulangClosure.NativeLiteral.signedValue negative (a + b) =
    YulangClosure.NativeLiteral.signedValue negative a + YulangClosure.NativeLiteral.signedValue negative b
'YulangClosure.NativeIntegerArithmetic.signedValue_add' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.signedValue_add
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.signedValue_difference
YulangClosure.NativeIntegerArithmetic.signedValue_difference : ∀ (negative : Bool) {a b : Nat},
  b ≤ a →
    YulangClosure.NativeLiteral.signedValue negative (a - b) =
      YulangClosure.NativeLiteral.signedValue negative a + YulangClosure.NativeLiteral.signedValue (!negative) b
'YulangClosure.NativeIntegerArithmetic.signedValue_difference' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.signedValue_difference
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.magnitude_gt_length
@YulangClosure.NativeIntegerArithmetic.magnitude_gt_length : ∀ {left right : List UInt8},
  YulangClosure.NativeIntegerComparison.magnitude left right = Ordering.gt → right.length ≤ left.length
'YulangClosure.NativeIntegerArithmetic.magnitude_gt_length' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.magnitude_gt_length
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.magnitude_lt_length
@YulangClosure.NativeIntegerArithmetic.magnitude_lt_length : ∀ {left right : List UInt8},
  YulangClosure.NativeIntegerComparison.magnitude left right = Ordering.lt → left.length ≤ right.length
'YulangClosure.NativeIntegerArithmetic.magnitude_lt_length' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.magnitude_lt_length
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.addParsed_decode
@YulangClosure.NativeIntegerArithmetic.addParsed_decode : ∀ {left right : Bool × List UInt8},
  YulangClosure.NativeLiteral.Digits left.snd →
    YulangClosure.NativeLiteral.Digits right.snd →
      YulangClosure.NativeIntegerComparison.Canonical left.snd →
        YulangClosure.NativeIntegerComparison.Canonical right.snd →
          YulangClosure.NativeIntegerArithmetic.decodeBytes
              (YulangClosure.NativeIntegerArithmetic.addParsed left right) =
            Option.some
              (YulangClosure.NativeLiteral.signedValue left.fst (YulangClosure.NativeIntegerComparison.value left.snd) +
                YulangClosure.NativeLiteral.signedValue right.fst
                  (YulangClosure.NativeIntegerComparison.value right.snd))
'YulangClosure.NativeIntegerArithmetic.addParsed_decode' depends on axioms: [propext, Classical.choice, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.addParsed_decode
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.decimalAddBytes_decode
@YulangClosure.NativeIntegerArithmetic.decimalAddBytes_decode : ∀ {left right : List UInt8} {a b : Int},
  YulangClosure.NativeIntegerArithmetic.decodeBytes left = Option.some a →
    YulangClosure.NativeIntegerArithmetic.decodeBytes right = Option.some b →
      ∃ output,
        YulangClosure.NativeIntegerArithmetic.decimalAddBytes left right = Option.some output ∧
          YulangClosure.NativeIntegerArithmetic.decodeBytes output = Option.some (a + b)
'YulangClosure.NativeIntegerArithmetic.decimalAddBytes_decode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.decimalAddBytes_decode
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.decodeBytes_exact
@YulangClosure.NativeIntegerArithmetic.decodeBytes_exact : ∀ {bytes : List UInt8} {a : Int},
  YulangClosure.NativeIntegerArithmetic.decodeBytes bytes = Option.some a ↔
    YulangClosure.NativeIntegerArithmetic.ByteGrammar bytes ∧
      YulangClosure.NativeLiteral.signedValue (YulangClosure.NativeLiteral.splitSign bytes).fst
          (YulangClosure.NativeLiteral.decimalFold 0 (YulangClosure.NativeLiteral.splitSign bytes).snd) =
        a
'YulangClosure.NativeIntegerArithmetic.decodeBytes_exact' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.decodeBytes_exact
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.parseBytes_spec
@YulangClosure.NativeIntegerArithmetic.parseBytes_spec : ∀ {bytes : List UInt8} {p : Bool × List UInt8},
  YulangClosure.NativeIntegerComparison.parseBytes bytes = Option.some p →
    YulangClosure.NativeIntegerArithmetic.ByteGrammar bytes ∧
      YulangClosure.NativeLiteral.Digits p.snd ∧
        YulangClosure.NativeIntegerComparison.Canonical p.snd ∧
          YulangClosure.NativeLiteral.signedValue p.fst (YulangClosure.NativeIntegerComparison.value p.snd) =
            YulangClosure.NativeLiteral.signedValue (YulangClosure.NativeLiteral.splitSign bytes).fst
              (YulangClosure.NativeLiteral.decimalFold 0 (YulangClosure.NativeLiteral.splitSign bytes).snd)
'YulangClosure.NativeIntegerArithmetic.parseBytes_spec' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.parseBytes_spec
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.signedValue_negate
YulangClosure.NativeIntegerArithmetic.signedValue_negate : ∀ (negative : Bool) (a : Nat),
  YulangClosure.NativeLiteral.signedValue (!negative) a = -YulangClosure.NativeLiteral.signedValue negative a
'YulangClosure.NativeIntegerArithmetic.signedValue_negate' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.signedValue_negate
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.negateBytes_decode
@YulangClosure.NativeIntegerArithmetic.negateBytes_decode : ∀ {bytes : List UInt8} {a : Int},
  YulangClosure.NativeIntegerArithmetic.decodeBytes bytes = Option.some a →
    ∃ output,
      YulangClosure.NativeIntegerArithmetic.negateBytes bytes = Option.some output ∧
        YulangClosure.NativeIntegerArithmetic.decodeBytes output = Option.some (-a)
'YulangClosure.NativeIntegerArithmetic.negateBytes_decode' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.negateBytes_decode
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.decimalSubtractBytes_decode
@YulangClosure.NativeIntegerArithmetic.decimalSubtractBytes_decode : ∀ {left right : List UInt8} {a b : Int},
  YulangClosure.NativeIntegerArithmetic.decodeBytes left = Option.some a →
    YulangClosure.NativeIntegerArithmetic.decodeBytes right = Option.some b →
      ∃ output,
        YulangClosure.NativeIntegerArithmetic.decimalSubtractBytes left right = Option.some output ∧
          YulangClosure.NativeIntegerArithmetic.decodeBytes output = Option.some (a - b)
'YulangClosure.NativeIntegerArithmetic.decimalSubtractBytes_decode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.decimalSubtractBytes_decode
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.asciiChar_bytes
YulangClosure.NativeIntegerArithmetic.asciiChar_bytes : ∀ (b : UInt8),
  b.toNat < 128 → String.utf8EncodeChar (Char.ofNat b.toNat) = [b]
'YulangClosure.NativeIntegerArithmetic.asciiChar_bytes' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.asciiChar_bytes
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.asciiString_bytes
@YulangClosure.NativeIntegerArithmetic.asciiString_bytes : ∀ {bytes : List UInt8},
  (∀ (b : UInt8), b ∈ bytes → b.toNat < 128) →
    (YulangClosure.NativeIntegerArithmetic.asciiString bytes).toUTF8.data.toList = bytes
'YulangClosure.NativeIntegerArithmetic.asciiString_bytes' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.asciiString_bytes
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.digits_ascii
@YulangClosure.NativeIntegerArithmetic.digits_ascii : ∀ {bytes : List UInt8},
  YulangClosure.NativeLiteral.Digits bytes → ∀ (b : UInt8), b ∈ bytes → b.toNat < 128
'YulangClosure.NativeIntegerArithmetic.digits_ascii' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.digits_ascii
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.byteGrammar_ascii
@YulangClosure.NativeIntegerArithmetic.byteGrammar_ascii : ∀ {bytes : List UInt8},
  YulangClosure.NativeIntegerArithmetic.ByteGrammar bytes → ∀ (b : UInt8), b ∈ bytes → b.toNat < 128
'YulangClosure.NativeIntegerArithmetic.byteGrammar_ascii' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.byteGrammar_ascii
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.asciiString_decode
@YulangClosure.NativeIntegerArithmetic.asciiString_decode : ∀ {bytes : List UInt8} {a : Int},
  YulangClosure.NativeIntegerArithmetic.decodeBytes bytes = Option.some a →
    YulangClosure.NativeLiteral.decodeInteger (YulangClosure.NativeIntegerArithmetic.asciiString bytes) = Option.some a
'YulangClosure.NativeIntegerArithmetic.asciiString_decode' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.asciiString_decode
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.negateBytes_grammar
@YulangClosure.NativeIntegerArithmetic.negateBytes_grammar : ∀ {bytes output : List UInt8},
  YulangClosure.NativeIntegerArithmetic.negateBytes bytes = Option.some output →
    YulangClosure.NativeIntegerArithmetic.ByteGrammar output
'YulangClosure.NativeIntegerArithmetic.negateBytes_grammar' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.negateBytes_grammar
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.decimalSubtract_eq_negate_add
YulangClosure.NativeIntegerArithmetic.decimalSubtract_eq_negate_add : ∀ (left right : String),
  YulangClosure.NativeIntegerArithmetic.decimalSubtract left right = do
    let negative ← YulangClosure.NativeIntegerArithmetic.negate right
    YulangClosure.NativeIntegerArithmetic.decimalAdd left negative
'YulangClosure.NativeIntegerArithmetic.decimalSubtract_eq_negate_add' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.decimalSubtract_eq_negate_add
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.decimalAdd_decode
@YulangClosure.NativeIntegerArithmetic.decimalAdd_decode : ∀ {left right : String} {a b : Int},
  YulangClosure.NativeLiteral.decodeInteger left = Option.some a →
    YulangClosure.NativeLiteral.decodeInteger right = Option.some b →
      ∃ output,
        YulangClosure.NativeIntegerArithmetic.decimalAdd left right = Option.some output ∧
          YulangClosure.NativeLiteral.decodeInteger output = Option.some (a + b)
'YulangClosure.NativeIntegerArithmetic.decimalAdd_decode' depends on axioms: [propext, Classical.choice, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.decimalAdd_decode
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.negate_decode
@YulangClosure.NativeIntegerArithmetic.negate_decode : ∀ {text : String} {a : Int},
  YulangClosure.NativeLiteral.decodeInteger text = Option.some a →
    ∃ output,
      YulangClosure.NativeIntegerArithmetic.negate text = Option.some output ∧
        YulangClosure.NativeLiteral.decodeInteger output = Option.some (-a)
'YulangClosure.NativeIntegerArithmetic.negate_decode' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.negate_decode
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.decimalSubtract_decode
@YulangClosure.NativeIntegerArithmetic.decimalSubtract_decode : ∀ {left right : String} {a b : Int},
  YulangClosure.NativeLiteral.decodeInteger left = Option.some a →
    YulangClosure.NativeLiteral.decodeInteger right = Option.some b →
      ∃ output,
        YulangClosure.NativeIntegerArithmetic.decimalSubtract left right = Option.some output ∧
          YulangClosure.NativeLiteral.decodeInteger output = Option.some (a - b)
'YulangClosure.NativeIntegerArithmetic.decimalSubtract_decode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.decimalSubtract_decode
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.decimalAdd_result
@YulangClosure.NativeIntegerArithmetic.decimalAdd_result : ∀ {left right output : String} {a b : Int},
  YulangClosure.NativeLiteral.decodeInteger left = Option.some a →
    YulangClosure.NativeLiteral.decodeInteger right = Option.some b →
      YulangClosure.NativeIntegerArithmetic.decimalAdd left right = Option.some output →
        YulangClosure.NativeLiteral.decodeInteger output = Option.some (a + b)
'YulangClosure.NativeIntegerArithmetic.decimalAdd_result' depends on axioms: [propext, Classical.choice, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.decimalAdd_result
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.decimalSubtract_result
@YulangClosure.NativeIntegerArithmetic.decimalSubtract_result : ∀ {left right output : String} {a b : Int},
  YulangClosure.NativeLiteral.decodeInteger left = Option.some a →
    YulangClosure.NativeLiteral.decodeInteger right = Option.some b →
      YulangClosure.NativeIntegerArithmetic.decimalSubtract left right = Option.some output →
        YulangClosure.NativeLiteral.decodeInteger output = Option.some (a - b)
'YulangClosure.NativeIntegerArithmetic.decimalSubtract_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.decimalSubtract_result
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.decimalAdd_response
@YulangClosure.NativeIntegerArithmetic.decimalAdd_response : ∀ {left right output : String} {a b : Int},
  YulangClosure.NativeLiteral.decodeInteger left = Option.some a →
    YulangClosure.NativeLiteral.decodeInteger right = Option.some b →
      YulangClosure.NativeIntegerArithmetic.decimalAdd left right = Option.some output →
        YulangClosure.NativeLiteral.readback (YulangClosure.NativeLiteral.Datum.integer output) =
            Option.some (YulangClosure.Original.Literal.int (a + b)) ∧
          YulangClosure.TypedCall.ValueTyped YulangClosure.Original.emptyContext
            (YulangClosure.TypedCall.literalResponse (YulangClosure.Original.Literal.int (a + b)))
            (YulangClosure.Original.Ty.base YulangClosure.Original.Base.int)
'YulangClosure.NativeIntegerArithmetic.decimalAdd_response' depends on axioms: [propext, Classical.choice, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.decimalAdd_response
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.decimalSubtract_response
@YulangClosure.NativeIntegerArithmetic.decimalSubtract_response : ∀ {left right output : String} {a b : Int},
  YulangClosure.NativeLiteral.decodeInteger left = Option.some a →
    YulangClosure.NativeLiteral.decodeInteger right = Option.some b →
      YulangClosure.NativeIntegerArithmetic.decimalSubtract left right = Option.some output →
        YulangClosure.NativeLiteral.readback (YulangClosure.NativeLiteral.Datum.integer output) =
            Option.some (YulangClosure.Original.Literal.int (a - b)) ∧
          YulangClosure.TypedCall.ValueTyped YulangClosure.Original.emptyContext
            (YulangClosure.TypedCall.literalResponse (YulangClosure.Original.Literal.int (a - b)))
            (YulangClosure.Original.Ty.base YulangClosure.Original.Base.int)
'YulangClosure.NativeIntegerArithmetic.decimalSubtract_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.decimalSubtract_response
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.carry_step_bounds
@YulangClosure.NativeIntegerArithmetic.carry_step_bounds : ∀ {a b carry : Nat},
  a < 10 → b < 10 → carry ≤ 1 → a + b + carry ≤ 19 ∧ (a + b + carry) % 10 < 10 ∧ (a + b + carry) / 10 ≤ 1
'YulangClosure.NativeIntegerArithmetic.carry_step_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.carry_step_bounds
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.final_carry_iteration
@YulangClosure.NativeIntegerArithmetic.final_carry_iteration : ∀ {carry : Nat},
  carry ≤ 1 →
    carry % 10 = carry ∧
      carry / 10 = 0 ∧
        YulangClosure.NativeIntegerArithmetic.addDigits [] [] carry = if carry = 0 then [] else [carry % 10]
'YulangClosure.NativeIntegerArithmetic.final_carry_iteration' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.final_carry_iteration
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.borrow_step_bounds
@YulangClosure.NativeIntegerArithmetic.borrow_step_bounds : ∀ {a b borrow : Nat},
  a < 10 → b < 10 → borrow ≤ 1 → -10 ≤ ↑a - ↑borrow - ↑b ∧ ↑a - ↑borrow - ↑b ≤ 9
'YulangClosure.NativeIntegerArithmetic.borrow_step_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.borrow_step_bounds
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.addDigits_length
YulangClosure.NativeIntegerArithmetic.addDigits_length : ∀ (xs ys : List Nat) (carry : Nat),
  (YulangClosure.NativeIntegerArithmetic.addDigits xs ys carry).length ≤ Max.max xs.length ys.length + 1
'YulangClosure.NativeIntegerArithmetic.addDigits_length' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.addDigits_length
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.trimLeadingKeepOne_normalize
@YulangClosure.NativeIntegerArithmetic.trimLeadingKeepOne_normalize : ∀ {ds : List UInt8},
  ds ≠ [] →
    YulangClosure.NativeIntegerArithmetic.trimLeadingKeepOne ds =
      (YulangClosure.NativeIntegerComparison.normalize Bool.false ds).snd
'YulangClosure.NativeIntegerArithmetic.trimLeadingKeepOne_normalize' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.trimLeadingKeepOne_normalize
YULANG_AUDIT_BEGIN YulangClosure.NativeIntegerArithmetic.subtractMagnitude_nativeTrim
@YulangClosure.NativeIntegerArithmetic.subtractMagnitude_nativeTrim : ∀ {left right : List UInt8},
  YulangClosure.NativeLiteral.Digits left →
    YulangClosure.NativeLiteral.Digits right →
      right.length ≤ left.length →
        left ≠ [] →
          YulangClosure.NativeIntegerArithmetic.subtractMagnitude left right =
            YulangClosure.NativeIntegerArithmetic.trimLeadingKeepOne
              (YulangClosure.NativeIntegerArithmetic.magnitudeBytes
                (YulangClosure.NativeIntegerArithmetic.subtractDigits
                    (YulangClosure.NativeIntegerArithmetic.lowDigits left)
                    (YulangClosure.NativeIntegerArithmetic.lowDigits right) 0).fst)
'YulangClosure.NativeIntegerArithmetic.subtractMagnitude_nativeTrim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeIntegerArithmetic.subtractMagnitude_nativeTrim
YULANG_AUDIT_BEGIN YulangClosure.Control.actual_call_request_completed_add_response
@YulangClosure.Control.actual_call_request_completed_add_response : ∀ {W : Type} {sig : YulangClosure.Control.Signature}
  {md : YulangClosure.Control.Metadata W} {term : YulangClosure.TypedCall.CallTerm} {world : W}
  {suffix : List YulangClosure.Control.Frame} {result : YulangClosure.Control.Ty} {n m : Nat}
  {s t : YulangClosure.Control.CallState W} {op : YulangClosure.TypedCall.OperationInstance}
  {payload : YulangClosure.TypedCall.Value} {k : YulangClosure.TypedCall.Comp}
  {observed : List YulangClosure.TypedCall.ViewOccurrence},
  YulangClosure.Control.FramesTyped sig suffix (YulangClosure.Control.Ty.original term.resultType) result →
    YulangClosure.Prefix (YulangClosure.Control.CallControlStep md) n
        (YulangClosure.Control.CallState.initial term world suffix) s →
      s.head = YulangClosure.Control.CallHead.requesting op payload k observed →
        YulangClosure.Prefix (YulangClosure.Control.CallControlStep md) m s t →
          (∃ op' payload' k', t.head = YulangClosure.Control.CallHead.requested op' payload' k') →
            ∀ {left right output : String} {a b : Int},
              YulangClosure.NativeLiteral.decodeInteger left = Option.some a →
                YulangClosure.NativeLiteral.decodeInteger right = Option.some b →
                  YulangClosure.NativeIntegerArithmetic.decimalAdd left right = Option.some output →
                    ∀ {role : YulangClosure.NativeLiteral.Role} {sameValue : Prop},
                      YulangClosure.NativeLiteral.Accepted (Option.some YulangClosure.Original.Base.int) role sameValue
                          (YulangClosure.NativeLiteral.Datum.integer output) →
                        op.responseType = YulangClosure.Original.Ty.base YulangClosure.Original.Base.int →
                          YulangClosure.NativeLiteral.readback (YulangClosure.NativeLiteral.Datum.integer output) =
                              Option.some (YulangClosure.Original.Literal.int (a + b)) ∧
                            YulangClosure.TypedCall.ValueTyped YulangClosure.Original.emptyContext
                                (YulangClosure.TypedCall.literalResponse (YulangClosure.Original.Literal.int (a + b)))
                                op.responseType ∧
                              m = s.frames.length + 1 ∧
                                t = YulangClosure.Control.CallState.requestBoundary md (s.frames.length + 1) s ∧
                                  t.head =
                                      YulangClosure.Control.CallHead.requested op payload
                                        (YulangClosure.Control.CallState.captureFrames s.frames k) ∧
                                    YulangClosure.Control.CallStateTyped sig t result ∧
                                      t.literalSuffix = suffix ∧
                                        YulangClosure.TypedCall.CompTyped YulangClosure.Original.emptyContext
                                            (YulangClosure.Control.plugResponse
                                              (YulangClosure.Control.CallState.captureFrames s.frames k)
                                              (YulangClosure.TypedCall.literalResponse
                                                (YulangClosure.Original.Literal.int (a + b))))
                                            term.resultType ∧
                                          YulangClosure.TypedCall.CompTyped YulangClosure.Original.emptyContext
                                            (YulangClosure.TypedCall.plugFrames s.frames
                                              (YulangClosure.Control.plugResponse k
                                                (YulangClosure.TypedCall.literalResponse
                                                  (YulangClosure.Original.Literal.int (a + b)))))
                                            term.resultType
'YulangClosure.Control.actual_call_request_completed_add_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.Control.actual_call_request_completed_add_response
YULANG_AUDIT_BEGIN YulangClosure.Control.actual_call_request_completed_subtract_response
@YulangClosure.Control.actual_call_request_completed_subtract_response : ∀ {W : Type}
  {sig : YulangClosure.Control.Signature} {md : YulangClosure.Control.Metadata W}
  {term : YulangClosure.TypedCall.CallTerm} {world : W} {suffix : List YulangClosure.Control.Frame}
  {result : YulangClosure.Control.Ty} {n m : Nat} {s t : YulangClosure.Control.CallState W}
  {op : YulangClosure.TypedCall.OperationInstance} {payload : YulangClosure.TypedCall.Value}
  {k : YulangClosure.TypedCall.Comp} {observed : List YulangClosure.TypedCall.ViewOccurrence},
  YulangClosure.Control.FramesTyped sig suffix (YulangClosure.Control.Ty.original term.resultType) result →
    YulangClosure.Prefix (YulangClosure.Control.CallControlStep md) n
        (YulangClosure.Control.CallState.initial term world suffix) s →
      s.head = YulangClosure.Control.CallHead.requesting op payload k observed →
        YulangClosure.Prefix (YulangClosure.Control.CallControlStep md) m s t →
          (∃ op' payload' k', t.head = YulangClosure.Control.CallHead.requested op' payload' k') →
            ∀ {left right output : String} {a b : Int},
              YulangClosure.NativeLiteral.decodeInteger left = Option.some a →
                YulangClosure.NativeLiteral.decodeInteger right = Option.some b →
                  YulangClosure.NativeIntegerArithmetic.decimalSubtract left right = Option.some output →
                    ∀ {role : YulangClosure.NativeLiteral.Role} {sameValue : Prop},
                      YulangClosure.NativeLiteral.Accepted (Option.some YulangClosure.Original.Base.int) role sameValue
                          (YulangClosure.NativeLiteral.Datum.integer output) →
                        op.responseType = YulangClosure.Original.Ty.base YulangClosure.Original.Base.int →
                          YulangClosure.NativeLiteral.readback (YulangClosure.NativeLiteral.Datum.integer output) =
                              Option.some (YulangClosure.Original.Literal.int (a - b)) ∧
                            YulangClosure.TypedCall.ValueTyped YulangClosure.Original.emptyContext
                                (YulangClosure.TypedCall.literalResponse (YulangClosure.Original.Literal.int (a - b)))
                                op.responseType ∧
                              m = s.frames.length + 1 ∧
                                t = YulangClosure.Control.CallState.requestBoundary md (s.frames.length + 1) s ∧
                                  t.head =
                                      YulangClosure.Control.CallHead.requested op payload
                                        (YulangClosure.Control.CallState.captureFrames s.frames k) ∧
                                    YulangClosure.Control.CallStateTyped sig t result ∧
                                      t.literalSuffix = suffix ∧
                                        YulangClosure.TypedCall.CompTyped YulangClosure.Original.emptyContext
                                            (YulangClosure.Control.plugResponse
                                              (YulangClosure.Control.CallState.captureFrames s.frames k)
                                              (YulangClosure.TypedCall.literalResponse
                                                (YulangClosure.Original.Literal.int (a - b))))
                                            term.resultType ∧
                                          YulangClosure.TypedCall.CompTyped YulangClosure.Original.emptyContext
                                            (YulangClosure.TypedCall.plugFrames s.frames
                                              (YulangClosure.Control.plugResponse k
                                                (YulangClosure.TypedCall.literalResponse
                                                  (YulangClosure.Original.Literal.int (a - b)))))
                                            term.resultType
'YulangClosure.Control.actual_call_request_completed_subtract_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.Control.actual_call_request_completed_subtract_response
[exit 0]
PASS: YulangClosure.NativeIntegerArithmetic.addDigits_value, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.addDigits_digits, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.subtractDigit_spec, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.subtractDigit_equation, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.little_bound, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.subtractDigits_spec, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.subtractDigits_value, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.little_append, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.lowDigits_value, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.digits10_append, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.lowDigits_digits, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.byteDigit_spec, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.digits_append, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.magnitudeBytes_digits, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.lowDigits_magnitudeBytes, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.magnitudeBytes_value, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.decodeBytes_string, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.splitSign_digits, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.signedBytes_decode, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.canonical_nonempty, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.normalize_false_sign, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.normalize_false_value, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.splitAddBytes_spec, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.splitAddBytes_exists, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.addDigits_nonempty, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.lowDigits_nonempty, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.magnitudeBytes_nonempty, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.addMagnitude_spec, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.subtractMagnitude_spec, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.signedValue_add, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.signedValue_difference, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.magnitude_gt_length, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.magnitude_lt_length, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.addParsed_decode, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.decimalAddBytes_decode, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.decodeBytes_exact, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.parseBytes_spec, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.signedValue_negate, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.negateBytes_decode, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.decimalSubtractBytes_decode, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.asciiChar_bytes, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.asciiString_bytes, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.digits_ascii, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.byteGrammar_ascii, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.asciiString_decode, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.negateBytes_grammar, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.decimalSubtract_eq_negate_add, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.decimalAdd_decode, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.negate_decode, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.decimalSubtract_decode, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.decimalAdd_result, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.decimalSubtract_result, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.decimalAdd_response, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.decimalSubtract_response, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.carry_step_bounds, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.final_carry_iteration, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.borrow_step_bounds, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.addDigits_length, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.trimLeadingKeepOne_normalize, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeIntegerArithmetic.subtractMagnitude_nativeTrim, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.Control.actual_call_request_completed_add_response, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.Control.actual_call_request_completed_subtract_response, under its printed hypotheses; axiom whitelist satisfied.
Named declarations only; ordinary-mistake check, not independent review or source correspondence.

```

# Independent review: native integer addition/subtraction

Reviewer: `/root/execution_frontier`, non-author of the arithmetic module and
its producer handoff. Bounded independent source/proof review, 2026-10-26.
No source repair, checker rerun, children, Git operation or cache modification.

## Decision and frozen target

**ACCEPT for the explicitly stated successful-helper algorithm/readback and
completed-request application scope.** No BLOCKING, MAJOR or MINOR findings.
This accepts the new constructive result and its source correspondence at the
inspected helper bodies. It does not close the omitted native realization or
whole-language obligations.

- Module: `notes/theory/lean/YulangClosure/NativeIntegerArithmetic.lean`
- Module SHA-256:
  `5adb30eb53f64fa4ccad80e83ed78c27f442436f20a8eceb8bc4fb59aac33ad1`
- Producer handoff: `tasks/agent-loop/inbox/20261026-proof-advance-native-arithmetic.md`
- Handoff SHA-256:
  `78f7ab9ccb55b42bfd2d1fd4bd22e55b38b914aac9c059f3c9988199fc5645e1`

The module hash matches the assigned frozen target, the producer's final
`check-016.lean`, and its isolated project source. The nine source hashes in
`native-arithmetic/source-inputs.json` match the current source bytes. All 26
local Lean files in the target's import cone match the isolated checked project.

## Inspected claim and implementation

I read the complete new module, its substantive handoff sections, the actual
Rust IntAdd/IntSub branches and decimal helpers, the imported decoder and
comparison definitions/contracts, the original completed-request consumer,
and the final checker transcript with its printed theorem types.

Relevant original source:

- `docs/yulang-operational-type-safety-ja.tex:880–929`: mathematical-integer
  primitive interpretation and primitive type-preservation boundary.
- `tools/inference-playground/src/runtime/machine.rs:2774–2783`: IntAdd directly
  calls `decimal_add`; IntSub negates the right operand and then adds.
- `tools/inference-playground/src/runtime/machine.rs:2822–2898`: sign/parser,
  low-to-high carry loop, magnitude comparison, borrow loop, trim/reverse and
  all signed dispatch branches.
- `tools/inference-playground/src/runtime/decimal.rs:5–36`: zero-normalizing
  parser and negate, including its conditional minus and resource checks.
- `notes/theory/2026-10-25-native-literal-producer-invariant.md`: the pre-existing
  grammar/producer claim explicitly leaves arithmetic correctness open.

### Digit loops and signed cases

`addDigits` computes the output independently of `little` or mathematical Int
addition. Its recursive consumption agrees with the indexed Rust loop under
the derived digit/carry invariant. Missing high digits are zero. The source's
carry-only iteration is matched by `final_carry_iteration` under `carry <= 1`;
the generalized internal function outside that invariant is not passed off as
an unrestricted model of arbitrary native carry states. `carry_step_bounds`
establishes the u8 intermediate bound of 19 and next-carry bound of one.

`subtractDigit` matches `a - borrow - b`, its sign test, and the corrective ten
in the Rust i16 loop. The proof establishes both the output digit range and
the signed equation. `subtractDigits_spec` retains the complete borrow-in/out
equation for every recursive suffix. `subtractDigits_value` derives final
borrow zero from digit bounds and the proved input order; zero borrow is not
an assumption. The length/order premises used at that leaf are discharged in
`addParsed_decode` by the actual magnitude branch and
`NativeIntegerComparison.magnitude_value`.

`subtractMagnitude_nativeTrim` connects the chosen normalizer to the
keep-at-least-one-digit trim. Viewing the source's high-zero popping after its
final reversal gives exactly this leading-zero operation. The low-digit
traversal, emitted-byte reversal and UInt8 conversion retain positional order;
`byteDigit_spec` proves that `UInt8.ofNat (48 + d)` does not wrap for an emitted
digit. The i16 intermediate lies in [-10,9], and the corrected output is 0–9.

The two native parser conventions are kept distinct. `splitAddBytes` trims the
magnitude but retains the original negative-zero sign, as `decimal_add::split`
does. `negateBytes` uses the existing parser that normalizes zero's sign, as
`decimal.rs::parts` does. `signedBytes` suppresses a minus exactly for the
singleton zero magnitude. Equal signs, opposite signs, equal magnitudes and
both magnitude orderings retain the native branch and operand order. Arbitrary
leading zeros and negative zero require no extra hypothesis.

### Exact arithmetic, bytes and String readback

The principal theorem types require only successful input decoding. Neither
arithmetic correctness, output grammar, final borrow, output typing nor a
successful output decoder is supplied as an assumption.

`decimalAdd_decode` constructs a computed output and proves its existing
decoder returns `a + b`. `decimalSubtract_decode` proves `a - b` through the
same computed negate/add route. `decimalSubtract_eq_negate_add` establishes
the exact String-level composition for all strings, including parser failure.
The proof does not replace the output by printing an independently computed Int.

`asciiString_bytes` proves the computed ASCII byte list is exactly the resulting
String's UTF-8 byte list. Its ASCII premise is derived for arithmetic outputs
from their proved decoder/grammar result. `asciiString_decode` therefore
connects the actual generated text to `NativeLiteral.decodeInteger` without a
free text-encoding hypothesis. The loop bounds also justify the difference
between native UInt8/i16 arithmetic and the Nat/Int specification.

### Original completed-request application

Both `Control.actual_call_request_completed_add_response` and
`...subtract_response` apply the original
`actual_call_request_completed_native_literal_response`. They derive its
`WellFormed` producer premise from the arithmetic result and recover exactly
`.int (a + b)` or `.int (a - b)` by decoder-result uniqueness.

The types retain the arbitrary `W`, signature, metadata, initial/current world,
actual prefix and post-prefix, original operation/payload/continuation,
observed occurrences, full typed suffix and final result. They retain the
original acceptance condition and explicit
`op.responseType = .base .int` correspondence. Their conclusions keep the
exact request-boundary state, original operation and payload, captured frames,
literal suffix and both continuation typing conclusions. Neither a fresh
instance, saved-world restoration nor an assumed output response typing was
substituted for these premises.

## Evidence inspected; no rerun required

I inspected `native-arithmetic/check-016.stdout`, its empty stderr, the source
snapshot/hash, `checks.jsonl`, `theorems.json`, `axioms.json`, `audit_driver.py`
and `run_check.py`. The final transcript identifies Lean 4.35.0 with commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, refreshes the target via Lake, and
ends with exit 0.

There are 62 named theorems in the source, 62 unique requested declarations,
and precisely the expected ordered BEGIN/END audit pairs. All printed types
and axiom reports are present. The standard axiom union is exactly
`propext`, `Classical.choice`, `Quot.sound`; the handoff preserves the individual
sets, including empty sets. No new-module warnings, proof holes, project axiom
declarations, native-evaluation proof assumptions or listed checker bypasses
were found. Thirteen kernel computation examples supplement the universal
proofs; they are not the basis for accepting the universal claim.

The final theorem types were read directly, with particular attention to
`subtractDigits_value`, the String arithmetic theorems, the unconditional
negate/add equation and both full actual-request corollaries. Earlier failed
checks remain in the producer's ledger; the final checked source is the frozen
source under review. No concrete discrepancy required an additional build or
test, so none was run.

## Limits of this acceptance

The pure helper model abstracts native checked-size and allocation failures.
Its existential successful result is not a proof that a Rust allocation or
every native invocation succeeds. The successful computed-byte correspondence
is supported by the inspected source map; a formal Rust execution/heap/arena
realization is still absent and is explicitly retained in the handoff.

Multiplication, division/modulo, the remaining primitive table, IntToString,
native handles, actual operation-instance realization, arbitrary Rust traces,
complete effect/lifetime semantics, whole-language progress and inference A/B
are outside this review's accepted conclusion. I did not re-audit every old
imported proof or the Lean kernel, run Rust tests, independently rebuild the
target, or review unrelated repository changes. Existing imported theorem
interfaces and source bytes were checked where this result uses them.

## Incidental bytecode provenance and stop

My earlier Call packet executed the checker as a main-script subprocess and
did not import it via importlib. I could not attribute its module `.pyc` to
that lane. The arithmetic producer's final handoff identifies its own helper
import as the producer and records removal of only that generated bytecode.
The primary confirmed that cleanup; no additional cleanup was performed here.
This review used `PYTHONDONTWRITEBYTECODE=1` for its Python inspection.

Only this review receipt was written. No reviewed source, my own frozen Call
files, shared cache/configuration or Git state was modified.

**Review writes STOPPED at this frozen receipt.** The primary owns acceptance
adjudication, integration, root verification and Git/push.

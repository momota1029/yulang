# NATIVE-LITERAL-READBACK-AUTHOR / handoff revision 1

Sprint: LEAN-NATIVE-LITERAL-READBACK-20261025/r1, contract SHA256
`f476c30b01eb0315a97f23ba59ff21d839e298970695162482af8afa3fb230e1`.
Baseline `a2d093870f7dbe86609a62bfe46649f5375e3a24` (provided; no Git invoked).
Author: `/root/native_literal_readback_astra_r1`; session
LEAN-NATIVE-LITERAL-READBACK-20261025/root-r1. Actual task receipt received from
/root. Requested gpt-6-astra/medium; observed model/effort UNKNOWN/UNKNOWN.
No descendants, other authors or executing compiler processes in this packet.
Primary is the complementary source-proof author and cannot independently
certify the combined component. Fresh reviewer belongs to Luna.

Outcome: **candidate conditional mathematics; NOT elaborated or reviewed**.
Original full semantics/inference A/B and Call source-domain parents stay OPEN.
This candidate removes the primitive integer-text-to-formal-datum premise,
conditional on the producer grammar and exact source observation mapping.

## Frozen artifacts and dependencies

Exact output leases, and all new paths written:

- `notes/theory/lean/YulangClosure/NativeLiteralReadback.lean`:
  `b8ba65a2217cd384ffdc336a2d56c3a02d7ba208ec383b6c30438a4b73e0721c`.
- `notes/theory/lean/YulangClosure/CallNativeLiteralResponse.lean`:
  `7b0c27ba851f982d3e13fa3e27c258fe907a56585a92123af14f9ad4d765d2cd`.
- This exact inbox; hash transmitted separately to avoid self-reference.

No scratch paths. Direct accepted import CallLiteralResponse SHA256
`62cffcd2bcf5ce879c3c7b75ff6908b19470a27e5ca73e5973ec1affbeaac3fb`.
CallNativeLiteralResponse imports the new NativeLiteralReadback at the hash above.
All41 dependency rows in the frozen contract were reread and SHA256 matched
(0 mismatches). The contract records the complete transitive source hash table.
No imported source changed. Historical failed candidates/Force constructions
were not reused. Accepted literalResponse_typed and
actual_call_request_completed_literal_response are reused under their actual
unchanged premises and arbitrary real prefix/suffix quantifiers.

## Construction and parent application

Stage1 defines ASCII digit bounds48..57, exactly one optional minus, nonempty
remaining digits, and the independent positional recurrence
`decimalFold acc (c::cs) = decimalFold (10*acc+(c.toNat-48)) cs`.
Signed mathematical value is unbounded Int, with leading zeros and negative zero
allowed. decodeInteger checks this grammar and computes that explicit fold;
success iff grammar and exact mathematical value, rejection iff invalid grammar,
and unique successful value are stated and proved without arbitrary default Int.
The decoder is separate from native acceptance. No text injectivity, canonical
spelling, arithmetic primitive correctness, lexical lowering or IntToString
roundtrip is inferred.

Stage2 keeps integer payload String, boolean Bool, decoded string String and unit.
An explicit unsupported datum covers other native value kinds; expected none
covers non-base source types, while all8 formal bases remain representable.
Accepted separately retains Value role, sameValue proposition (the actual
receiving.matches_value observation), nonempty expected type and primitive tag
agreement. It contains no decimal validation. WellFormed alone carries Grammar
for Integer. readback_exists and accepted_readback construct the exact literal
and its closed ValueTyped derivation from the accepted literal theorem.

Stage3 actual_call_request_completed_native_literal_response existentially
returns that readback literal, base equality, constructed operation response
ValueTyped, and the WHOLE old conclusion: exact unwind count/state/head, state
typing and unchanged literal suffix, captured and frame-plugged response typing.
No hv hypothesis. The explicit `op.responseType = .base expected` premise
remains the unresolved native declaration/operation-instance interpretation.
No shared polymorphic type vector is fabricated.

Source inspected directly: machine::primitive_matches1769 retains Value role,
receiving.matches_value and Unit/Int/Bool/Str kind matching only. Operational
safety docs1140–1174 permit the original typed external host protocol and do not
move internal producer safety to that host. Primary reports four Integer
publication sites696/2723/2777/2783 and private immutable arena; its separate
source artifact must justify those claims and bridge them to Grammar. This
packet does not claim Lean verifies Rust execution.

Examples cover negative, -0, leading zeros, a30-digit integer, empty/sign-only,
non-ASCII/fullwidth digits, plus-sign and malformed text, bool/int separation,
Unicode decoded String,11/23 readbacks and distinct resumed response-binder
results. An accepted malformed Integer example explicitly exposes why tag
acceptance alone cannot establish grammar. Examples are written but NOT run.
No native_decide, axiom or sorry is introduced. Axiom subset must still be queried.

## Checks, TODOs and cessation

Checks performed: source/manual proof inspection and SHA256 validation only.
Lean/build/tests/runtime executions: ZERO. Elaboration, recursive Decidable
instance elaboration, reduction examples and final axiom reports are UNVERIFIED.
Primary may repair elaboration after this STOP under its frozen contract; any
changed bytes require new verification/review hashes.

Resource charge: full300-second author allocation, three substantive stages;
no renewal, descendants or retained subprocesses. Exact observed active duration
UNKNOWN; no resource refund requested. Writes STOPPED after freezing this file.
This worker ends the assignment and does not remain running while review waits.

Mutual TODO READBACK-PRODUCERS-1: primary supplies all-source Grammar argument at
literal::integer, machine::decimal_add, decimal::negate, Product::new/advance/
finish and each actual publication; falsifier is any successful reachable
Integer payload outside optional-minus/nonempty-ASCII-digit grammar.

Mutual TODO READBACK-CHECK-1: primary runs bounded elaboration and complete
signature/axiom queries on the two exact frozen files and accepted dependency
chain. Falsifier: any elaboration failure, new axiom or weakened old conclusion.

Mutual TODO RESPONSE-INSTANCE-1: Luna retains declaration-to-OperationInstance
responseType equality, receiving/view and source trace correspondence; a primitive
tag cannot discharge this. Callable/environment, template/view/owner, source
lowering, full arithmetic observations and original inference A/B remain OPEN.
No production implementation TODO follows: NO_SAFE_CODE_SLICE remains in force.

Next in-envelope owner: primary bounded verification/repairs and combined freeze,
then fresh nonauthor review. Not commit-ready until those steps succeed.

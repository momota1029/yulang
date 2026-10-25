# Direct byte readback correspondence

Status: **candidate r2 correspondence amendment; independent review pending**.
Author `/root`; baseline `a2d093870f7dbe86609a62bfe46649f5375e3a24`.
Authority: LEAN-NATIVE-LITERAL-READBACK-20261025/r2. No native code is changed.

The source argument
`notes/theory/2026-10-25-native-literal-producer-invariant.md`, SHA
`1f73d0a4e221cb2d2a182876cf9928ebd3cab34edd6d36f4a46bb6bd3ca9a651`, remains
frozen. Its four-producer inventory, private arena induction, signed-byte grammar,
carry/borrow/index/length reasoning and publication/pause boundaries are reused
without changes. This note supersedes only the final section's description of
the Lean observer as a List Char/scalar conversion. The old description matches
the frozen author candidate, not the final byte implementation.

## Exact final observation and same grammar

NativeLiteral now observes a String's UTF8 byte array and its exact ordered
list, `text.toUTF8.data.toList`. AsciiDigit tests a UInt8's natural value between
48 and57 inclusive. splitSign removes one leading byte45 if present. Grammar
requires a nonempty remaining byte list whose elements all satisfy AsciiDigit.
For each digit, the mathematical fold uses `10 * acc + (byte.toNat - 48)`;
the Boolean sign optionally negates the unbounded Int magnitude. The recurrence
is proved with List.foldl_cons, retaining the same equation as the author.

Every native SD word from the old source proof is a byte word in exactly this
grammar: byte45 optionally precedes a nonempty word in48..57. Observe the same
UTF8 bytes in Lean; no character decoding or Unicode property is needed to
supply Grammar. For comparison with the earlier scalar presentation, all these
ASCII scalars have exactly those single-byte encodings, so the position and
value of every digit and the optional minus are identical. Conversely, a valid
UTF8 string with any non-ASCII scalar has at least one byte>=128, outside these
bounds; the parser cannot accept it as a digit. Non-ASCII minus and fullwidth
digits are rejected. Empty text, sign-only, a second sign, plus or whitespace
also fail. Leading zeros and negative zero remain accepted with their same
mathematical values; text injectivity/canonical roundtrip is still not asserted.

String input is retained. readback of Datum.string returns exactly the original
String literal, including non-ASCII data. Byte parsing applies only to
Datum.integer; it does not replace string payloads with byte literals. Unit and
Boolean payloads are unchanged, and unsupported still has no readback.

## Apply the producer proof and preserve the trust boundary

For the exact value looked up by received.value, the arena induction supplies
WellFormed: integer text has the SD byte grammar; the other supported kinds
require no extra payload predicate. The actual primitive_matches branch
supplies Accepted by its unchanged Value-interface, same-value-view and
source-type/kind checks. In particular the decoder's validation is not added
to that native predicate. An artificially malformed Integer still illustrates
that tag acceptance alone cannot supply WellFormed; the producer proof does.

accepted_readback constructs a literal, its exact readback/base match and closed
typing. actual_call_request_completed_native_literal_response applies it with
the same actual-prefix/suffix quantifiers and explicit hinstance as before.
The observation does not interpret whole native states, operation IDs, type
arguments, captured environments or templates. Whole source/native execution
and the operation-instance equality therefore remain open. Full numerical
correctness of add/subtract/product and IntToString observations also remain
open; digit-range proofs are not arithmetic correctness proofs.

## Why the implementation changed and how it is checked

The old String.toList brings [propext, Classical.choice, Quot.sound] through
the installed standard library, as retained query rows9–11 show. Row11 shows
String.toUTF8, Array.toList and UInt8.toNat themselves have no axioms. The final
kernel declarations must independently pass the original strict [propext,
Quot.sound] subset; the source change is not an exception to that condition.
No String.toList declaration is used by the final decoder. Old attempts and
queries remain in the receipt with their exact source snapshots.

The primary made the fold elaboration repair and this byte observer change and
is a contributor, not a reviewer. Final signatures, axioms, examples and hash
chain are recorded by the primary verification owner; fresh independent review
checks both source notes and the final Lean files. No native/compiler/test
execution, source behavior change or parent-theorem closure follows from this
representation repair alone.

# Native literal producer invariant and response readback

Status: **candidate source argument; independent review pending**.
Primary author: `/root`. Contract LEAN-NATIVE-LITERAL-READBACK-20261025/r1,
SHA `f476c30b01eb0315a97f23ba59ff21d839e298970695162482af8afa3fb230e1`.
Baseline `a2d093870f7dbe86609a62bfe46649f5375e3a24` on
`research/simple-sub-intrusion`. The complementary Lean author owns the decoder
and actual-request application; neither contributor is an independent reviewer.

## Claim, representation and limits

Let D be the ASCII bytes 0x30 through 0x39. Let SD consist of a nonempty word
over D, optionally preceded by exactly one ASCII minus byte. SD permits leading
zeros and negative zero. Each word has a unique mathematical integer: fold its
digits left with accumulator `10 * n + digit`, then negate iff it has the minus
prefix. No bounded machine integer conversion is involved. Uniqueness here is
of the value of each word, not injectivity from all words to integers.

**Producer claim:** every Integer(text) successfully appended to the private
Machine value arena, starting through RuntimeProgram::start_with_schedule and
following the inspected production methods, has text in SD. The same claim
holds for a retained Integer value used by a primitive response. The arguments
below establish the necessary producer cases directly from their source; this
is not a Lean model of the entire Rust machine or proof of all its memory safety.

This claim is deliberately a representation/grammar invariant. It does not
prove that decimal_add computes mathematical addition, Product computes the
product, that all spellings are canonical, or that IntToString observations
roundtrip through the mathematical representation. Those stronger semantics
remain open and cannot be inferred from the digit bounds proved here. Formal
arithmetic safety and full source/native adequacy retain their original scope.

Native RuntimeValueKind::Integer stores Box<str> (machine.rs:118–122), not Int.
The tag check at primitive_matches:1769 is insufficient for this claim by
itself: a manually fabricated Integer("bad") would pass the kind branch.
The actual private-arena formation argument, not that tag, rules it out here.
No source-reachable malformed-integer counterexample is asserted.

## Exhaustive publication and mutation ownership

The production value arena is private (machine:29–34), starts empty (:441–445),
and has exactly one insertion statement, `self.values.push(RuntimeValue { ... })`
in allocate (:2700–2715). Public value (:572–574) returns an immutable reference.
The inspected source has no mutation/replacement/extension of existing entries.
RuntimeValue's public fields do not grant access to this private arena, and no
production entrypoint takes a caller-supplied RuntimeValue for insertion.
resume_host_write takes continuation/operation identifiers and constructs Unit.

Search across tools/inference-playground/src for Integer construction,
RuntimeValue construction, arena writes, allocate, ground_data and data gives
the following complete Integer publication cases. Pattern matches, output
formatting and test-only assertions are consumers, not additional producers.

| Native allocation path | Data supplier | Proof below |
| --- | --- | --- |
| evaluate Instruction::Integer, machine:696–702 | literal::integer success | unsigned literal |
| PrimitiveArgument then pinned_primitive_apply IntAdd, :1173–1175, :2774–2777 | decimal_add success | addition/subtraction helper |
| Same consumer, IntSub, :2779–2783 | decimal::negate then decimal_add success | sign helper plus addition/subtraction helper |
| advance_integer_product, :2720–2725 | Product::finish after advance reports complete | private Product invariant |

All remaining direct allocation sites are Unit, Closure, Computation, Primitive,
Record, Tuple, Variant or Operation. The generic `value` locals passed to data
at :744 and :1674 are explicitly Tuple/Variant branches. Lambda creates Closure;
continuation binding creates Closure; delayed arguments and request carriers
create Computation. The other generic primitive-result path is exhaustively
covered by pinned_primitive_apply. Its remaining branches create Boolean/String
or return None, while IntMul is handled by the private Product state.

Bindings, frames, tuple elements, views and continuation replay copy or retain
handles/ReceivedValue; they do not edit the referenced Integer text. Consequently
an induction on successful arena append events reduces the global representation
claim to the four rows. Empty initialization is the base; each other constructor
preserves the claim vacuously. Existing values remain unchanged at every event.
The producer lemmas below actually validate their input text themselves; they
do not circularly rely on the arena claim for malformed inputs.

## Unsigned literal and sign helpers

literal.rs:3–9 rejects empty input or any byte outside D before doing anything
else. Trimming initial ASCII zeros leaves either a nonempty suffix over D or
the empty word. The latter is replaced by the one-byte word "0". Both successful
results are nonempty words over D and hence in SD. Source lowering's integer
spelling is not assumed trustworthy to prove this local property.

decimal.rs::parts:5–10 removes at most one leading minus, then independently
requires nonempty all-ASCII-digit remainder. Trimming zeros returns either a
nonempty D-word or "0" (with false sign). A second minus, plus, whitespace or
non-ASCII digit fails the digit predicate. The returned magnitude therefore
always has at least one ASCII digit.

decimal::negate:29–36 calls parts. It copies that magnitude unchanged and inserts
at most one minus. Length overflow/allocation failure returns None before a
result is returned. Every Some output lies in SD, including zero. This is the
only extra textual helper on the IntSub allocation path.

## decimal_add: every successful branch preserves grammar

machine.rs:2823–2901 contains the helper. Its split function removes at most one
minus, rejects empty/nondigit input, and normalizes an all-zero magnitude to "0".
Thus both returned magnitudes are nonempty D-words. The sign bit and magnitude
remain separate until signed inserts at most one minus. signed has no other
character-producing branch; failure returns None.

For add_magnitude, let L and R be the positive input lengths and W=max(L,R).
The successful reserve uses checked `W+1`, so the final carry iteration and
index increments fit usize. Before each iteration carry is 0 or 1, and each
selected input digit a,b is 0..9; missing high digits are zero. Hence
`0 <= a+b+carry <= 19`, so u8 addition is defined, the emitted remainder is
0..9 and the next carry is 0 or 1. The first iteration exists since W>=1.
Every output byte is 0x30 plus that remainder. Reversal preserves the alphabet
and nonemptiness; successful String::from_utf8 therefore returns a D-word.
The optional last carry iteration likewise emits a digit and then clears carry.

For subtract_magnitude, before every iteration borrow is 0 or 1. With a,b in
0..9, `a-borrow-b` lies in [-10,9], within i16. If negative, adding10 yields
0..9 and borrow becomes1; otherwise the digit already lies in0..9 and borrow
becomes0. The cast to u8 and addition of0x30 therefore emit an ASCII digit.
The larger input is nonempty, so at least one byte is emitted. Every indexed
read is within its loop-bound input or is checked and returns None; no successful
path substitutes an invalid byte. Trimming high zeros tests length>1, preserving
at least one digit. Reversal and UTF8 conversion preserve the D-word property.
This grammar proof does not require a theorem about the final borrow or the
correctness of magnitude comparison; those belong to arithmetic semantics.

The outer equal-sign branch uses add_magnitude then signed. Opposite signs
choose either the literal "0" or subtract_magnitude followed by signed. All
successful branches are therefore in SD. The magnitude comparison affects the
mathematical arithmetic result but cannot break the alphabet/length argument.
None from validation, checked arithmetic, reserve, read or UTF8 conversion is
propagated by `?`, so it cannot publish an Integer on this path.

## Product: digit bounds, indices and publication

The Product fields are private to decimal.rs; production construction is through
Product::new:51–68. Both inputs first pass parts. magnitude reverses ASCII digits
and subtracts0x30, so each stored digit is in0..9. Denote positive lengths by L,R.
The accumulator has length W=L+R, checked before allocation, initially all zero.
Maintain this invariant:

1. left/right lengths are L,R>=1; every input/accumulator digit is0..9; accumulator
   length is W=L+R; carry is0..9.
2. 0<=row<=L. If row<L, 0<=column<R. At a completed row boundary column=carry=0.
3. No partially computed accumulator is an arena value; it belongs solely to
   State::IntegerProduct until the completion publication below.

For nonzero inputs new sets row=column=carry=0, establishing the invariant.
For a zero input it uses left=right=[0], W=2, row=1=L and column=carry=0;
that state is already complete and the invariant still holds.

advance:70–87 returns immediately if row=L. Otherwise row<L and column<R, so
`row+column <= L+R-2 < W`; the sum cannot overflow usize because W was checked.
All three input reads use valid indices. The numeric sum of an accumulator
digit, the product of two input digits and carry is at most9+81+9=99. It fits
u8; remainder and quotient by10 are both0..9. Updating the accumulator/carry
therefore preserves their bounds.

Incremented column is at most R (R<W). If it equals R, the high-digit write is
at row+R<=L+R-1, within the accumulator. The assigned carry is0..9. Incremented
row is at most L, and column/carry reset to0. Otherwise column remains<R.
Thus all invariant clauses hold after each successful advance. This range
argument does not use the stronger multiplication correctness assertion about
which earlier rows have contributed to each high digit.

finish:90–100 refuses row!=L. It retains at least one accumulator digit while
trimming, reverses, then adds0x30 to each0..9 digit. All bytes are in D; no u8
overflow occurs. At most one minus is inserted from the stored Boolean sign.
Reserve/UTF8 failure returns None. Every successful output is consequently SD,
whether or not a separate numerical multiplication theorem has been proved.

machine:1162–1171 enters IntegerProduct only with a successfully created Product.
step:674 invokes advance_integer_product; :2721–2725 calls finish and ground_data
only if advance reports completion, and otherwise retains the private Product.
run:585–597 returns ResourceExhausted for a depleted budget without publishing
the accumulator. A later run resumes the same invariant. Any helper failure
returns an unavailable result, not a malformed Integer. Private fields cannot
be supplied by an external caller through the inspected production API.

## Other ground data and the actual response consumer

Unit has its unique payload. Boolean(bool) has exactly its native Boolean data.
Every String(Box<str>) carries valid UTF8 and is interpreted as the same scalar
sequence. Producers include literal::string, DecodedString, bool/int-to-string
and concatenation (:707–715, :2766–2772, :2805–2816). No source-string decoder
is reapplied to an already-decoded runtime payload. This does not prove the
source escape decoder agrees with the complete language specification.

ParameterRole has precisely Value/Computation (program:202–205). The actual
primitive_matches predicate is the conjunction of Value interface, same-value
view and the four Unit/Int/Bool/Str kind matches. receiving::matches_value:293
checks only `views[view].value == value`; unknown flags, images and effect
coverage are not added to or inferred from this predicate. ground:196 creates
a view for the same handle. The usize handle observation into mathematical Nat
retains equality; it is not a mapping of operation declaration identities.

ResumeArgument:1006–1077 reads the retained template declaration's result type,
accepts primitive_matches OR the separate exact-v1 callable branch, and places
the exact ReceivedValue into EnterTemplate. This component applies only to the
primitive branch; it does not silently replace the disjunction by its first arm.
For Integer responses the arena invariant supplies SD independently of acceptance;
for the other three branches native payloads already have their literal domains.
The constructed literal's base agrees with the matched source primitive type.
The formal operation's response type must still be interpreted as that same base.
No shared polymorphic type-instance vector or full source/native trace mapping
is fabricated. Host-write's separately constructed Unit is also representable.

The complementary NativeLiteralReadback file defines AsciiDigit by scalar bounds
48..57, Digits recursively over characters, splitSign removing exactly one '-'
and Grammar requiring a nonempty remaining digit list. An SD byte word is ASCII,
so its UTF8 decoding has one matching scalar per byte. Conversely, those scalar
bounds encode exactly D. Mapping a valid native Box<str> to the same Lean String
therefore sends every proved SD producer output to NativeLiteral.Grammar.
The absence or presence of ASCII '-' is preserved by that mapping.

NativeLiteral.decimalFold uses the recurrence above, and decodeInteger checks
Grammar separately before returning mathematicalValue. decodeInteger_exact
states its precise successful value; reject/unique are separate results. The
native guard has not been modified: Accepted retains only role, sameValue,
nonempty expected primitive base and kindBase agreement. WellFormed adds Grammar
only for integer data, discharged at the four actual producer paths above.
Unit/Boolean/String copy their exact payloads; unsupported cannot decode or pass
the primitive match. Source Unit/Int/Bool/Str map to the respective formal bases;
Variable/Hole/Tuple/Function map to no primitive base for this predicate. This
last rejection is about primitive_matches, not the separate callable branch.

Instantiate datum with the kind and text of the exact `received.value` lookup,
role with that ReceivedValue's interface, and sameValue with the view equality
actually checked. The source guard supplies Accepted and the arena argument
supplies WellFormed. accepted_readback then constructs the exact Literal,
readback equality, base match and closed ValueTyped. The observer is a finite
field projection for this branch; it does not interpret an entire native state.
Role.other represents the one native Computation alternative, and unsupported
forgets data only for kinds for which this primitive theorem has no success.

CallNativeLiteralResponse::actual_call_request_completed_native_literal_response
uses this constructed literal in the accepted actual-request theorem, retaining
the complete old conclusion and explicit `hinstance` operation-type equality.
Neither response typing nor decoding success is assumed. The formal actual
prefix still needs source/native trace realization before it describes an
arbitrary Rust run; this packet does not supply that global simulation. The
kernel proof alone also does not verify the Rust producer inventory. Fresh
independent review must check both components and this ASCII correspondence.

## Remaining owners, falsifiers and receipt

RESPONSE-ENCODING-1: this packet targets primitive readback only. Callable types,
code and captured environments, source lexical correspondence and full numeric
operation correctness remain open. RESPONSE-INSTANCE-1 and RESPONSE-TEMPLATE-1
retain shared declaration/type-instance and frame/owner/view/nested-handle
simulation obligations. Full source/native and Call/inference A/B stay OPEN.
NO_SAFE_CODE_SLICE remains supported by ResumeArgument/primitive_matches and
capture_template/enter_template; no runtime defect or production edit follows.

Discriminators are malformed/empty/sign-only/non-ASCII integer text, distinct
11/23 responses, negative and negative-zero words, leading zeros, arbitrarily
long words, wrong primitive kind, Unicode strings, and incomplete Product state.
The source proof treats all producer iterations symbolically. No runtime tests,
sample-based arithmetic check, Cargo or native execution was run for this note.
Read/hash inspection is source evidence, not automatic source extraction or
whole-machine verification. All source hashes are pinned in the contract; final
Lean correspondence and artifact hashes belong in the frozen handoff/outcome.

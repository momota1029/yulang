# NATIVE-LITERAL-READBACK independent combined review / revision 1

Verdict: **CLEAN within the bounded primitive representation and response-typing scope.**
No blocking or major finding. This is independent source/proof review, not an
independent Lean execution or certification of full native semantics.

Reviewer: `/root/native_literal_readback_review_astra_r2`, current task launch
received from `/root`; session LEAN-NATIVE-LITERAL-READBACK-20261025/root-r1.
Requested gpt-6-astra/medium; observed model/effort UNKNOWN/UNKNOWN.
I did not author, repair or contribute to either Lean file or source argument.
Contributors are `/root/native_literal_readback_astra_r1` and `/root`; neither is
counted as this independent reviewer. No descendants were started.

Authority: r1 contract SHA
`f476c30b01eb0315a97f23ba59ff21d839e298970695162482af8afa3fb230e1`, amended by r2
SHA `dc69bde50aee51607e6e80dd55a56ced55f124f9d51d140425a9c4d6abde5cbb`.
Supplied baseline `a2d093870f7dbe86609a62bfe46649f5375e3a24`, branch
research/simple-sub-intrusion. Root AGENTS, pre-sprint hard invariants, current
state/README, sprint/review rules and both contracts were read. No Git operation.
Only write lease: this report; no other files were changed by this reviewer.

## Frozen targets independently hashed

| Target | SHA-256 |
| --- | --- |
| NativeLiteralReadback.lean | `53a745397fed4b319225541b8e764a32cdc72032ca4e8be48d9d4a23d3901c54` |
| CallNativeLiteralResponse.lean | `7b0c27ba851f982d3e13fa3e27c258fe907a56585a92123af14f9ad4d765d2cd` |
| 2026-10-25-native-literal-producer-invariant.md | `1f73d0a4e221cb2d2a182876cf9928ebd3cab34edd6d36f4a46bb6bd3ca9a651` |
| 2026-10-25-native-literal-byte-readback.md | `70fcd0610ff3455f36fa3c46cbb42042612a9969646e8e21cc95edffdf410a1d` |
| author handoff 20261025-native-literal-readback.md | `5639aa46a82d27dac308dccc48724f281594fdaa6c7097c49964846fd6c1fe01` |
| 20261025-native-literal-readback-r1-verification.jsonl | `1973287627645ae6c239e558dde01fb2e07fea0c949824669072b0c5a48b836c` |
| .lake/native-literal-readback-r1-check.lean | `82dc8c86d6274ab38f174ad521da3dd5298ded5f3f600cccd2a9cb168ada5239` |
| .lake/native-literal-readback-r1-run.py | `6bcc0b0a72f980dc73dc38740f7a866d68cc96867e90a2950037e9500e0923a9` |
| prior literal verification receipt | `4328e908b606fb5bd8cadb38a32daecfe3d59d92913fd39c95fcf816f046a763` |

All 41 contract dependency hashes match. The two source notes are read together:
the amendment replaces only the old final Char-observation account.

## Stage 1: actual producers and publication

Read the actual literal/decimal implementations and machine allocation owners,
and searched runtime sources for Integer/RuntimeValue formation and arena
mutation. Integer is Box<str>. The private arena begins empty, has one push in
allocate, and exposes only immutable value lookup. Public RuntimeValue fields
and Clone do not provide an insertion or mutation route into that arena.
The four Integer constructors are literal evaluation (machine:698), completed
Product (2723), IntAdd (2777) and IntSub (2783). Generic data locals at744/1674
are Tuple/Variant; the primitive-result supplier is the exhaustive match in
pinned_primitive_apply. Other allocation routes create noninteger kinds. Handles,
frames and retained received values preserve the stored bytes. The separately
named dispatch::Machine is not the value-arena Machine.

The source argument establishes optional minus plus nonempty ASCII digits:
literal::integer validates every byte before trimming zeros; its empty trimmed
case produces "0". Both sign splitters independently validate a nonempty digit
remainder; negate only prefixes one minus to that validated magnitude.
Addition's carry is at most1, sum at most19, with checked width+1 bounding its
last iteration and index increment. Subtraction's borrow is0/1 and temporary
digit lies in[-10,9]; adjustment produces0..9. Its loop is nonempty and trimming
keeps one byte. Neither branch needs numerical arithmetic correctness to prove
this grammar property.

Product::new establishes positive digit-array lengths L,R and checked W=L+R,
digits/carry in0..9. The zero shortcut has L=R=1, W=2 and row=L. Otherwise
row<L and column<R bound every read and row+column<W; sum<=99 preserves digit
and carry bounds. Row completion writes at row+R<W and resets column/carry.
finish requires completion, retains a digit when trimming and adds only ASCII
zero and an optional minus. The machine publishes only after advance completes
and finish succeeds. ResourceExhausted retains private state without publishing
a partial accumulator. Fallible helper failures do not publish an Integer;
infallible allocation aborts likewise provide no successful malformed output.
This is not a claim that every allocation failure is converted into Option or
that the entire Rust machine is verified memory safe.

## Stage 2: exact observation and application

The final observer uses the same String's toUTF8.data.toList. Byte45 is removed
at most once; the remainder must be nonempty with each byte in48..57. Thus the
source SD invariant supplies Grammar directly. Non-ASCII UTF8 necessarily has
bytes outside those bounds; empty, sign-only, double-minus, plus and whitespace
fail. Leading zeros and negative zero remain admissible.

The mathematical value is the explicit unbounded positional fold
10*acc+(byte.toNat-48), followed by the sign. The recurrence and exact/reject/
unique lemmas match that interpretation; uniqueness is per text, not injectivity
or canonical spelling. Unit/Bool/String retain their exact payloads, including
Unicode String data. Unsupported kinds have no primitive readback.

Accepted has role, sameValue, nonempty expected base and kind equality only.
WellFormed separately supplies integer Grammar. Actual primitive_matches and
receiving::matches_value justify that field projection on the exact retained
received.value; no unknown/image/effect condition is invented. The native
ResumeArgument callable alternative remains separate. The source's Unit/Int/
Bool/Str projection agrees with kindBase, with other source forms rejected by
this primitive predicate. The allowed typed external host protocol remains
unchanged and does not absorb internal producer obligations.

accepted_readback constructs the literal, successful readback, expected base
and closed typing. The consumer existentially constructs its response and
retains every old actual_call_request_completed_literal_response conjunct:
unwind count, boundary state, exact captured request head, state typing, original
suffix and both plugged response typings. Arbitrary actual prefixes/suffixes,
metadata/world and explicit hinstance remain. The field observation does not
pretend to establish Rust trace realization or operation-instance equality.

## Stage 3: recorded execution and axiom audit

Read the checker, final query and receipt. All14 source-text snapshots hash to
their recorded inputs, and every row has equal before/after input hashes.
Recorded Lean duration totals68.4758067709954 seconds. Failures1–6/9 remain;
rows7/8 are superseded compiled candidates. Rows9–11 expose String.toList's
Classical.choice dependency; those diagnostics are not accepted targets.
The r2 byte change removes that dependency without relaxing the whitelist.
Final rows12/13/14 succeed without timeout; current inputs/imports/outputs match
every recorded final hash. The final query has24 matching signature/axiom pairs,
all empty or[propext], and19 examples; the new modules have16 examples. No new
sorry, axiom, admit or native_decide token occurs in the proof files.

Independently rehashed the current source/import/output chains for all30 reused
accepted modules against their final successful prior receipt rows: no mismatch.
The five historical failed candidates are excluded from those accepted imports;
this review does not recertify their failed proofs. No old source/object was
written by this reviewer. The checker was inspected, not executed. The supplied
pre-Lean wrapper rejection is not counted as an additional Lean invocation.
Read/hash inspection used Python3 after an unavailable `python` command; neither
attempt ran Lean, Cargo, tests or the native runtime.

## Parent application, exclusions and cessation

This review supports accepting the bounded producer-grammar argument and its
application to the checked primitive readback/response theorem. It does not
close full arithmetic numerical correctness, canonical text/IntToString
observations, source lexical lowering, callable code/environment typing,
RESPONSE-INSTANCE-1, RESPONSE-TEMPLATE-1, full frame/view/owner/nested-handle
simulation, whole source/native traces or original Call/inference A/B parents.
Those remain OPEN with the primary's existing owners. No compiler production
promotion or new code slice is authorized. Next action belongs to primary:
adjudicate this frozen report and integrate/synchronize the coherent component.

Budget: full300 seconds charged; three substantive stages; no refund or renewal.
Exact active duration UNKNOWN; the work completed within the300-second wall
bound (first recorded clock05:26:44 UTC). No Lean/build/test/native execution,
external contact, nested CLI, background job or descendant was started.
All inspection commands completed. Remaining owned processes: none.
Writes STOPPED after freezing this report; no unresolved descendant leases.
Report SHA is transmitted separately to avoid a self-reference.

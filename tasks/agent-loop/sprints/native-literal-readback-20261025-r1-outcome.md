# LEAN-NATIVE-LITERAL-READBACK-20261025/r2 outcome

Primary adjudication: **ACCEPTED bounded source grammar, primitive readback and
actual Call response application**, following fresh independent CLEAN review.
Full Yulang source/native safety and original inference A/B remain **OPEN**.
Baseline: `a2d093870f7dbe86609a62bfe46649f5375e3a24`, branch
`research/simple-sub-intrusion`; that baseline was successfully pushed.
This outcome freezes before its new integration commit/push; their actual result
is recorded by the primary in the next compact-state update.

## Original obligation and before/after evidence

The previous literal-response theorem constructed a closed typed formal literal,
but actual native integers are `Box<str>`. The runtime primitive response check
checks role, same-value view and tag, without validating integer grammar. A
faithful representation bridge therefore needs the actual producer invariant.
The two source notes cover all four Integer construction routes: literal
execution (machine:698), completed Product (2723), IntAdd (2777), IntSub (2783).
The private arena starts empty, has one push and no entry-mutation route; other
generic allocation suppliers are exhaustively noninteger. Literal validation,
addition/subtraction carry and borrow bounds, and Product row/column/carry/index
invariants establish optional ASCII minus followed by nonempty ASCII digits.
Only completed Product state is published. Failures or retained partial work do
not produce a successful malformed Integer. This does not prove full numerical
arithmetic correctness, canonical text, or all allocation failures returning None.
Leading zeros and negative zero remain admitted by the grammar.

`NativeLiteralReadback.lean` observes exact UTF8 bytes and computes the unbounded
signed positional value. Its exact/reject/unique results and primitive acceptance
lemma construct a literal, matching expected base and closed typing. Unit, Bool
and String retain their exact runtime payloads. The formal acceptance projection
has precisely role/sameValue/kind fields; integer grammar is supplied separately
by the source argument. No external host obligation or native check is changed.
`CallNativeLiteralResponse.lean` applies the constructed literal to the complete
actual Call prefix/completion theorem, preserving every existing endpoint, step
count, captured head, suffix, state-typing and plugged-response conclusion.

Explicit `hinstance` still connects the formal operation response type to the
native expected primitive base. Whole native trace realization, shared operation
identity/type instance, callable code/environment representation, template/view/
owner/nested-handle simulation, source lexical lowering, IntToString/canonical
observations, Force and original Call/inference A/B remain OPEN. RESPONSE-ENCODING-1
is reduced only for primitive producer grammar/readback; its callable remainder,
RESPONSE-INSTANCE-1 and RESPONSE-TEMPLATE-1 retain their current owners.

Implementation: NO_SAFE_CODE_SLICE. Actual primitive_matches/receiving and all
Integer producer/allocation owners were inspected. No compiler/runtime semantics,
diagnostics, expectations, native tests or production promotion were changed.

## Checked evidence and preserved failures

R1 contract `f476c30b01eb0315a97f23ba59ff21d839e298970695162482af8afa3fb230e1`;
r2 amendment `dc69bde50aee51607e6e80dd55a56ced55f124f9d51d140425a9c4d6abde5cbb`.
All 41 dependency pins and the previous 30 accepted source/import/object chains
match. The old five failed Call entry/spine candidates are still excluded; the
accepted unchanged CallEntrySpineComposition supplies that dependency.

Verification JSONL has 14 actual Lean invocations totaling
68.4758067709954 seconds, single process, `-j1 -M1024`. Final rows12/13/14 compile
both modules and the final query; 24 matching signature/axiom pairs use no axioms
or only propext. There are 16 examples in the modules and 19 in the final query.
Rows1–6 retain elaboration/diagnostic heartbeat failures. Rows7/8 are superseded
compiled Char candidates; row9 retains a query DecidableEq failure and rows9–11
expose standard String.toList's Classical.choice dependency. The final r2 observer
uses String.toUTF8.data.toList, retaining the same ASCII grammar and mathematical
value while meeting the unchanged strict axiom gate. The fold uses List.foldl
with an explicit recurrence proof; no heartbeat limit was raised. The original
source note is immutable; the byte note supersedes only its final Char-observation
paragraph. A wrapper rejection before launching Lean is not a Lean invocation.
No old proof source/object was changed. No Cargo/native/runtime test was run.

## Frozen artifact hashes

| Artifact | SHA-256 |
| --- | --- |
| notes/theory/lean/YulangClosure/NativeLiteralReadback.lean | `53a745397fed4b319225541b8e764a32cdc72032ca4e8be48d9d4a23d3901c54` |
| notes/theory/lean/YulangClosure/CallNativeLiteralResponse.lean | `7b0c27ba851f982d3e13fa3e27c258fe907a56585a92123af14f9ad4d765d2cd` |
| notes/theory/2026-10-25-native-literal-producer-invariant.md | `1f73d0a4e221cb2d2a182876cf9928ebd3cab34edd6d36f4a46bb6bd3ca9a651` |
| notes/theory/2026-10-25-native-literal-byte-readback.md | `70fcd0610ff3455f36fa3c46cbb42042612a9969646e8e21cc95edffdf410a1d` |
| tasks/agent-loop/inbox/20261025-native-literal-readback.md | `5639aa46a82d27dac308dccc48724f281594fdaa6c7097c49964846fd6c1fe01` |
| tasks/agent-loop/inbox/20261025-native-literal-readback-r1-verification.jsonl | `1973287627645ae6c239e558dde01fb2e07fea0c949824669072b0c5a48b836c` |
| tasks/agent-loop/inbox/20261025-native-literal-readback-review.md | `bf29485d141089c4619e29e05029989b5f34394287009921f4da280f267c0330` |
| ignored .lake/native-literal-readback-r1-check.lean | `82dc8c86d6274ab38f174ad521da3dd5298ded5f3f600cccd2a9cb168ada5239` |
| ignored .lake/native-literal-readback-r1-run.py | `6bcc0b0a72f980dc73dc38740f7a866d68cc96867e90a2950037e9500e0923a9` |

Authors: `/root/native_literal_readback_astra_r1` and primary `/root` (fold/query
repair, byte amendment, source invariant/correspondence, checking/application).
Fresh nonauthor `/root/native_literal_readback_review_astra_r2` independently
reviewed all producer paths, loop invariants, exact byte readback, consumer and
receipts. CLEAN: no blocking/major finding; no independent Lean rerun. Primary
accepts that bounded verdict without treating it as full native verification.
Author and reviewer report writes STOPPED, no descendants or owned processes.
Requested Astra/medium; observed model/effort UNKNOWN throughout.

## Resource and integration boundary

Total authorized1800s: author300, primary production/repair690, Lean120,
reviewer300, integration120, dispatcher270; contingency0. Author300, primary690,
reviewer300 and dispatcher270 conservatively charged without refund. Dispatcher
lifetime reservation870 includes earlier600. Lean consumed14/32 calls and
68.4758067709954/120 seconds. Integration120 started05:29:33UTC; proof/source work
is frozen. Three unrelated UNKNOWN legacy reservations remain quarantined.
Current-state static checking is scheduler evidence only. No tests are implied.
Only primary stages the exact coherent reviewed component and performs the
nonforced push after inspecting the entire outbound range. At completion the
next dispatcher consultation must receive a separate bounded boundary grant;
no spent production grant renews silently.

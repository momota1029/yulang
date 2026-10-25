# Primitive operation instance independent review

Verdict: CLEAN for the frozen partial mathematical construction, its complete
formal Call application, and the scoped source correspondence argument. No
blocking or major findings. This verdict does not close the full native trace,
full source-domain or original inference A/B parents and grants no production
promotion.

Assignment PRIMITIVE-OPERATION-INSTANCE-REVIEW / handoff revision 1.
Sprint LEAN-PRIMITIVE-OPERATION-INSTANCE-20261025/r1; contract SHA-256
`2d885257c3e93748dc2b9b5e42a6bce1a3a5c615be382f561e484b3ea71f7c0a`.
Baseline `6d9e769abbd6c119bf71c4a2f9bb9202bed064de`.
Reviewer `/root/primitive_operation_instance_review_astra_r1`, session
LEAN-PRIMITIVE-OPERATION-INSTANCE-20261025/root-r1. Requested Astra/medium;
observed model/effort UNKNOWN. Launch receipt recorded by primary:
2026-10-25T05:38:50.564053+00:00. Reviewer supplied no construction, repair or
source argument to the target. Target contributors are author
`/root/primitive_operation_instance_astra_r1` and primary `/root`; neither is
being treated as independent reviewer. Sole reviewer write lease is this file.

## Frozen bytes and evidence audit

Independently recomputed SHA-256 for all 51 contract dependency pins and the
additional shadow.rs pin: no mismatches. Reviewed target hashes:

| Artifact | SHA-256 |
| --- | --- |
| PrimitiveOperationInstance.lean | c3b0f2ad86fd49f9ebcf22c80388b996951ff0704695e18afa546863ddcf8773 |
| CallDeclaredLiteralResponse.lean | f9c7f3b8b0c2ad0552df531a6a13ad1fb4863340bb0ea837319bf144a2bae255 |
| 2026-10-25-operation-declaration-coherence.md | 5acf2d32c897619ceb77e26db07e221c8f2ecd9a7da160d2828c211eb46c9736 |
| 20261025-primitive-operation-instance.md | 1b7bbb89e6b84c232ac3fd982a139a3e1781a9dd4b2786479641df8aab4e26a7 |
| 20261025-primitive-operation-instance-r1-verification.jsonl | 6ebc09a97251149f4ab281f9d081a077f306c7492869d4ad47ca1f20767861a9 |
| .lake/primitive-operation-instance-r1-check.lean | 2cbafb01d517e6d84bdfab391b3a4db6923b194be28254f2d0f41109f575ba5e |
| .lake/primitive-operation-instance-r1-run.py | 512d1e620b512527c6d43430462c82b63430d38c1d2778333f08668f0bdd9f38 |
| crates/yu-hir/src/shadow.rs | b964bab6dcdb7ebeca9f964c134ac8fb041c928c20ce0a895fea6b6af0fbb93e |

Read the checker and all four retained verification rows, including failed row 1.
Rows 2/3/4 succeed without timeout and with stable input snapshots; all their
current source/import/output hashes agree. Aggregate recorded Lean duration is
4.248637401993619 seconds, four calls, one process with -j1 -M1024. The repair
between rows 1 and 2 only quotes two keyword case names and replaces hn with rfl
after dependent elimination; no theorem statement changed. The author's original
PrimitiveOperationInstance hash remains historical evidence, not the reviewed
final target. No failed object is accepted.

Independently traversed the two prior receipts' final accepted rows for all 32
pinned modules and recomputed every recorded input/output hash, checking successful
exit, no timeout and stable inputs: no discrepancy. The five historical failed
modules are excluded from the accepted chain. Query source and output contain 22
signature/axiom pairs. Each printed axiom list is empty or a subset of propext and
Quot.sound. The 28 examples supplement the universal proofs. No sorry, added
axiom, classical choice or native_decide occurs in either new module.

## Stage 1: actual source suppliers and retention

Inspected SourceOperationId and declaration formation in source_annotation.rs,
SourceNodeKey minting/equality in full_parse.rs, source_identity::try_source_keys,
and module::index_source_effects. Complete identity retains module realm/path,
family key and member key. A key retains parse brand, green allocation and start;
retained immutable parses prevent address reuse or separately parsed equal text
from identifying different declarations. Actual members provide both identity
and signature in declarations_selected, with no alternative production record
constructor found in the searched HIR/runtime sources.

The primitive all-effects-None tree parses deterministically from immutable
member syntax. Group parsing preserves effects, while arrow parsing moves any
leading effects onto its argument; neither operation discards an effect that
could incorrectly enter the represented branch. Namespace-dependent row parsing
cannot affect this branch. Consequently two successful source formations of one
complete id have the same supported primitive endpoints even when separately
projected. This argument is narrower than general effect-row coherence and does
not authenticate publicly forged Rust records.

Read the public execute/execute_module/report preparation chain and all four
production selected-member-operation suppliers in lib.rs: provider, member,
exact implementation member and applicable member projection. Their effect
vectors come from index_source_effects over retained provider parses and selected
Act keys. Read selected_member_operation_paths, parse-bound export environment,
namespace installation, qualified operation lowering and local resolve_operation
for expressions and catch patterns. These paths retain the source-produced
operation record; id-based deduplication alone was not used as proof. Independent
request/handler resolution is accounted for by the deterministic supported
signature lemma, not declaration Arc pointer equality.

Read RuntimeProgram operation/catch lowering, Machine operation value creation,
operation application, OperationPayload, make_request_carrier and
execute_with_substitution. Request declaration originates from the operation
value and survives pending-request construction. propagate_request compares
handler id but capture_template receives the original request. Its sole
production append stores request.declaration.clone(). ResumeArgument reads the
retained template result; templates are append-only and handles checked. Host
resume validates the retained declaration and supplies Unit. Native handler
checks omit result.effects; the note correctly treats effect-bearing result
annotations as unsupported by this interpreter, not necessarily native rejection.

Finite coverage is supported at its actual owner: immutable RuntimeProgram.code
contains all Operation instructions and Catch resolutions; Machine starts with
an empty value arena, its sole production Operation value constructor clones a
code resolution, and its other value/request/template propagation introduces no
new declaration. Higher-order transport or duplicated values cannot mint new
ids. The public source routes expose no external operation-value injection into
this machine. Unlisted keys return none; whole open-world extension protocols
are explicitly outside this coverage argument.

## Stage 2: mathematical construction and parent application

number_get retrieves the exact complete key at every successful index;
number_collision_free follows from that retrieval. number_coverage handles every
list member, including duplicates, and repeat consistency requires no Nodup or
assumed injection. Keys are arbitrary decidable identities, not spellings or
hashes; one fixed program table is required throughout.

Annotation retains effect and hole payloads parametrically and distinguishes all
native annotation constructors. The source note gives the complete structural
case map. primitive_exact and decode_exact recover precisely a function with
primitive endpoints and None at all three effect positions. interpret_exists
constructs the instance from coverage/decoding; interpret_fields and
interpret_ground establish both endpoint projections and syntax-backed empty
type arguments. Unsupported variables, holes, tuples, callable endpoints and
any present effects cannot decode as arbitrary primitives.

interpret_response derives the former hinstance from the same declaration's
instance and expected observations. request/template are aliases; their equality
lemma is not mistaken for native correspondence. Compared the old and new Call
theorem text: every preexisting premise before hinstance and the entire conclusion
are byte-identical. The replacement retains world, signature, metadata, actual
prefix/suffix, request/completion, literal readback, boundary equality/state typing
and both continuation typing conclusions. hrequest and hexpected remain visible
representation premises; the source argument supplies local retention, while the
global native-to-formal head/prefix relation remains OPEN.

## Stage 3: falsifiers, limits and handoff

Checked same spelling across different module/family/member keys against complete
identity and the universal collision lemma; duplicate keys against first occurrence
numbering; changed signatures under one id against the actual source constructor
rather than forged records; effect annotations against native handler/response
checks; separately resolved handler versus captured request against capture_template;
and unknown/dynamically transported operations against the finite code inventory.
No source-qualified counterexample or unsupplied local producer was found within
the stated public source execution domain.

This accepts a reviewed local source argument plus a checked conditional formal
application, not an executable Rust-to-Lean extractor or complete Rust semantics
proof. Rowan/Arc immutable identity behavior is an explicit existing library
contract. Full polymorphic/effectful/callable operation interpretation, lexical and
numeric semantics, environments, owner/view/template replay, Force, whole native
traces and original Call/inference A/B remain OPEN. No production code changed;
NO_SAFE_CODE_SLICE is supported by the inspected capture_template and
ResumeArgument owners.

Remaining TODO POI-TRACE-1 belongs to the primary's future authorized lane:
construct native-to-formal request/head/prefix and expected-observation
correspondence using these source owners and the same fixed identity table.
Falsifier: a source-qualified native request/consumer cannot satisfy hrequest or
hexpected or simulate the formal prefix. This review does not lease that work.
Primary may adjudicate/integrate the frozen local result while preserving those
open gates. No reviewer repair or further delta review is requested.

Review used three stages within the 300-second envelope. Conservatively charge
all 300 seconds; precise launch-to-final duration is owned by primary. Reviewer
Lean/build/test/native executions: zero; Git operations: zero; scratch files:
zero; descendants: none. Read-only shell and Python3 hashing/text/receipt
inspection only; one attempted `python` hash command failed because that binary
was absent, then Python3 completed the inspection. No checker was rerun.

Worker STOPPED after freezing this report. Writes ceased, no background process
or descendant remains, and no other path was modified by this reviewer.

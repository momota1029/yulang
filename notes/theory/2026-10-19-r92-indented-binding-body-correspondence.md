# R92: unchanged indented binding bodies reach the existing Block consumer

Date: 2026-10-19. Revision: 1. Sole author: `/root/r92_proof`.
Status: **candidate source correspondence and finite runtime application; unreviewed**.
Sprint `indented-binding-body-local-source-bridge-20261019-r92`, revision 1,
contract SHA-256 `fba26b57c3c37ddaf9d7e4ebc41ade0e52c97d6464957513ac004efd277770f9`.
Supplied baseline `44a23937f99c55dea03714e82581e4a5a409576d`; no Git observation.

## Parent and result

The original effect-hygiene/source-native parent preserves provider, annotation
position, receiver, request, residual and witness lineages under the joint
assignment `xi=(nu,K,D)`, applicable receiving/selection evidence and independent
outward contributions. Its original inference/evaluator claims, source domain
and quantifiers remain unchanged. A/B remain OPEN 0→0. F1/FK1, R67, joint K,D,
native residual correspondence and the six hygiene frontiers remain OPEN;
R50 is NOT_ADOPTED and R85 is AWAITING_USER_ADOPTION.

For the byte-identical R91 fixture, the frozen adapter now forwards each actual
indented relay/receive body node to the existing Block constructor. The
correspondence below repairs the specific false R91 admission premise and
accounts for the retained body Block wrappers before reusing the candidate
runtime derivation. Under successful public preparation and the finite machine
path, that derivation reaches the original `write::ping first` suffix and an
independent outer positive Grant, then Integer 23. Public preparation/execution
has not been observed here; Luna's single authorized command and fresh source
and spec reviews remain required. This is no reviewed theorem or production
promotion.

Authority is existing syntax/projection and candidate runtime behavior, under
top-level inference principles §1/1.1, annotation integration §§1–1.2,
directional protection §§2–2.2 and charter §21. Their authority hashes match
R78 §8. Permissions are neither inflow nor residual. All ordinary Simple-sub
generation, accumulation, propagation, levels, extrusion, qualifying intrusion
and generalization obligations remain intact.

## Exact adapter delta and node simulation

The final `local_source.rs` SHA-256 is
`3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786`.
In memory only, replace its unique `body()` predicate
`!matches!(child.kind(), OperatorChain | IndentedStatementBlock)` with
`child.kind() != OperatorChain` (with the original qualified identifiers and
formatting). The resulting byte hash is the contract's baseline
`ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5`.
Thus the entire frozen-file delta is this admission predicate; the existing
constructors, work-stack consumers and validations in that file are unchanged.
No baseline file or scratch file was written.

`binding.rs:241–255` opens BindingBody around `binding_body_normalized`.
At `:328–337`, newline indentation four exceeds the column-zero binding
baseline for relay and receive, selecting
`statement::indented_statement_block_normalized`. That owner (`statement.rs:
474–515`) opens IndentedStatementBlock, emits its leading trivia and runs the
Indented sequence at indentation four. Its first canonical Statement is the
line-6 or line-8 Catch expression, respectively. Expression admission calls
`expr_from_nud_normalized`, which emits OperatorChain (`operator_chain.rs:
109–140`). The next column-zero `my` fails the equal-indentation successor
condition (`statement.rs:719–733`), ending this block. Therefore each wrapper
has one Statement containing its original OperatorChain; neither swallows the
next top-level definition. These are actual normal constructor branches, not a
test helper's expected transition. Existing R88 construction clauses supply
the unchanged Catch/pattern/formal productions at these explicit tokens.

`body()` (`local_source.rs:465–500`) still requires exactly BindingHeader and
BindingBody, the existing significant header sequence, and exactly one child
of BindingBody. It obtains `child` using `only_child` and returns that same
SyntaxNode. The new kind predicate admits the original IndentedStatementBlock;
it does not select its final child, flatten it, rebuild it or strip trivia.
For any previously admitted OperatorChain the predicate is still true and all
subsequent arguments and branches are byte-identical. Other child kinds and
malformed wrapper/header shapes still fail here. Recovery and supported-depth
checks in `form()` remain in force before construction.

Let `Ns`, `Nw` denote those actual indented child nodes; `key(N)` is
`Builder::key(N)`'s lookup in `counters.source_nodes`, and `range(N)` is the
existing `range_of(N)` byte range. These denote the real parsed source objects,
not guessed numeric node IDs or trimmed token ranges. `form()` retains the
original definition-owned formal IDs, allocates their Lambda bodies, and
queues `Work::Expression(body_chain.clone(), current, scope, named_group)`
(`:592–640`). Thus the node reaching `Builder::expression` is precisely Ns/Nw.
The branch at `:1086` calls `block(node,index,scope,named_group)` directly.

`block()` (`:1236–1362`) validates the original immediate children in order:
Statement with exactly one node, alternating with childless
BlockStatementSeparator. It requires a nonempty final OperatorChain and every
preceding statement to be a private supported BindingStatement with a valid
body/header/annotation. The new adapter performs none of these checks itself
and bypasses none of them. Each single-statement indented body passes with
zero local bindings. The consumer sets the body slot to
`Block([], final_expression=Hs/Hw)` using the original Ns/Nw node. `set()`
(`:818–845`) retains exactly `key(Ns/Nw)`, `range(Ns/Nw)`, the incoming scope and
named group; the final Catch retains its own source key/range and the block's
Expression scope. Original formal lexical entries remain live through this
work. No replacement formal is introduced.

For each definition independently, the actual slot allocation gives root
ordinal 0 = the original one-formal Lambda; ordinal 1 = its body Block;
ordinal 2 = that Block's final Catch. The named group's terminal body remains
ordinal 1. `LocalSource.body` remains the original root ordinal 0. Catch
scrutinee and arm-body slots are separately allocated beneath ordinal 2.
These are source-root-qualified indices, never globally equated across relay
and receive. The failed R91 formation emitted no authentic complete carrier
whose earlier numeric indices could be treated as an identity baseline.

## Original local binder, initializer and final write

The main definition keeps its inline OperatorChain admission. Its braced
relay argument is independently produced by `append_nud`'s LBrace branch
(`operator_chain.rs:351`) and `braced_nud_normalized` (`statement.rs:521–624`).
The Braced sequence uses the same statement progression owner, admits line 10
as Binding and line 11 as Expression, and retains their order. The equal-indent
newline terminates the initializer's OperatorChain (`operator_chain.rs:774–776`)
and becomes the next statement's separator; `emit_separator_leading`
(`statement.rs:1162–1167`) gives that separator trivia with no nested child.
The RBrace closes this block. This is the R91 braced construction confirmed in
its closeout; its new containing-body premise is established above, rather
than inherited from R91's false claim that Ns/Nw contain an admitted chain.

Write `B` for this authentic braced Block slot in main, `f` for the actual
`HirLocalId {owner=main root, ordinal=bindings.len()}`, `I` for its initializer
slot and `F` for the final-expression slot. `block()` pops the final
OperatorChain only after collecting the statements in source order. It
retains line 10's binder key, original name range, spelling `first`, no formal
parameters and `initializer=I`; the source identity records that same f/key
join. The Block contains `[f's binding ordinal]` and `final_expression=F`.
The source of B stays the original braced node; `set` derives source key/range
from each actual node, including the Apply tail/operation/Name nodes in I/F.
There is no claim that an Apply tail has the whole chain's range.

The LIFO work stack is pushed Restore, final Expression(F), then reversed
initializers. With one initializer, Work::Initializer(f) runs first, sets its
scope to LocalInitializer(f), schedules Publish(f,guard), then the original
`body(statement)` at I (`:654–698`). Since f has no parameters, there is no
temporary recursive self publication. After all I work finishes, Publish
restores the guard and pushes `first -> Local(f)` (`:700–706`). Only then does
the queued final expression run. Its IdentifierExpression lookup (`:1007–1044`)
therefore resolves first to that same f. The queued Restore finally removes
the local lexical entry. This is static lexical publication; the runtime cell
is allocated later, by its distinct owner.

`RuntimeProgram::from_hir` (`program.rs:298–329,435–566`) validates source-owned
indices and maps each to `Label(offset+ordinal)`, retaining f, I, F, expression
sites and the ordered Block bindings. Its actual source walk (`:334–393`)
marks recursion only on an active parameterized initializer self reference;
f has no parameters and no self reference, so its LocalBinding is nonrecursive.
Each indented body becomes an Instruction::Block with no bindings and the
authentic Catch label. `machine.rs:659,1889–1927` calls begin_local; for an
empty binding vector it directly evaluates that final label in the same
environment, adding no Local frame, receiver, view or handler. Consequently
the real Ns/Nw wrappers introduce no missing frame in R91's runtime stacks.

## Apply the repaired bridge to the finite runtime candidate

Reuse R91 rev2's runtime derivation only now, with its incorrect body-admission
sentence replaced by the exact wrapper simulation above. R88/R78 retain their
own authors and premises. R88's three example executions do not prove this
fixture; R78's source/HIR premise alone supplies no source constructor. R91's
reviewed failure and both earlier frozen candidates remain historical evidence.

Let S,W be the two actual Act declaration IDs and s,w their ping member IDs.
`source_annotation.rs:134–314` uses distinct Act/member source keys; the
namespace is keyed by `(family,member spelling)`. Therefore S differs from W
and s differs from w despite equal member spelling. The original signatures
are Unit→Int and Int→Int. `resolve_operation` is shared by expressions and
Catch patterns (`local_source.rs:1091–1103`); the unique public declarations
are retained. The inner continuation binder k is the relay arm's ordinal-1
CatchBinder; outer payload p is the receive arm's ordinal-0 CatchBinder.

The two original annotated Lambdas yield Computation roles/RootCompSchemas and
Execute consumption for their original formal Names (`program.rs:414–509`,
`receiving.rs:21–43`). The actual schema permissions are respectively S and W,
with Int results. Calls retain the whole inert Delay before body entry
(`machine.rs:879–1009`). Receive installs hw under its live invocation uW,
then its real pending Name read opens EW of VW. Relay installs hs under
distinct uS, then its real thunk read opens ES of VS. The empty-body Block
wrappers above change none of these operations.

`begin_local(Bcode,0,e)` allocates the original empty cell c and pushes
Local(Bcode,next=1,e,c,recursive=false), then evaluates Icode. The declared
signal Apply emits event qS with its own source and authentic EW/ES observations
(`machine.rs:1011–1069,1789–1804,1929–1956`). After saving Local and ending ES,
propagation reaches hs while uS is still live. Its own original signal row,
authentic uS/VS read receipt, qS observation and VS image reaching bS supply
the positive local Grant. No inference from an absent negative fact is used.

`capture_template` (`:1309–1378`) records Hole, Bind(the actual saved Local),
View(the original ES), then Owner(uS). The hs delimiter is removed shallowly.
Applying the arm's original k to 11 checks the declared Int response and
enters that template. Since uS is still active, Owner borrows it; View opens
ES' from the original view/receipt; Bind pushes the cloned frame with the same
Bcode, next, environment and c. No second local cell is allocated. Returning
11 through Local (`:1100–1158`) writes c, extends the environment by Local(f)→c
and calls begin_local(Bcode,1,e'). With one binding this evaluates the retained
Fcode. Its Name(Local(f)) reads that same 11, giving the original final write
payload. This identifies the suffix by actual indices/cell ownership, not text.

The declared write Apply emits fresh qW; monotone request allocation gives
qW≠qS, independently of w≠s. Its observations include EW and ES'. hs is gone.
The unwind ends ES', restores uK from borrowed uS, unwinds ResumeReturn,
deactivates uK then original uS, restores uW, and ends EW
(`machine.rs:1708–1760`). uW's ReceiverReturn lies below hw, so uW is still
live and `validate_handler_installation` accepts its actual installation.

The outer Grant is separate: `receiving.rs:232–323` authenticates qW's EW
observation, a genuine uW/VW receipt, VW's image reaching bW and bW's original
W permission. Ending EW retains its historical observation/receipt. Neither
qS's Grant nor VS's signal permission supplies this witness. This positive
Grant suffices even without the independent closed-primitive branch. The full
w declaration and Int payload match; p binds 11; wildcard continuation causes
no second capture. The retained outer arm returns 23 outside hw. This is the
finite candidate conclusion. `lib.rs:175–195` still calls prepare (including
candidate inference) before constructing/running this machine, so no observed
CLI acceptance, general solve, residual type or native theorem is asserted.

## Remaining evidence and handoff

`R92-EXECUTE-1` (Luna): run the contract's one exact public command against the
unchanged fixture and frozen implementation; expected exit 0/stdout 23.
Any lowering/runtime failure or other result falsifies the executable outcome.
No retry, another owner edit or semantic workaround is authorized by this note.
`R92-REVIEW-1` (Luna): fresh independent source/compiler and spec review of this
frozen component. Falsifier: a different child/key/range/order/index is emitted,
a body wrapper adds an unaccounted frame, lexical first resolves elsewhere,
resumption changes c/F, or the outer qW Grant lacks its own authentic evidence.
Those are pending checks, not producer certification.

Original `R78-NATIVE-HYGIENE-1` and `R78-UNIVERSAL-1` remain with Luna and their
original source/native/continuation owners: actual formal registration and
FormalEntry, candidate_source formal/Name, candidate_effect, FreshUse /
candidate_scheme, shadow_apply, Catch output and lifecycle consumers must
establish source-licensed mapped constraints, inflow/residual and joint K,D.
No native owner was audited here. F1/FK1 and arbitrary foreign continuations
retain independent quantifiers; this single local capture/resumption cannot
discharge them. No production implementation TODO is created beyond the already
frozen adapter; another mismatch requires Luna's new owner/lease decision.

Checks: static source inspection, initial/final SHA-256 inventory and an
in-memory reverse-admission hash. No parser/compiler execution, tests, builds,
runtime probes, Git, network or delegation. Initial and final pinned bytes
agree; this author wrote no constructor or consumer. Runtime cessation of the
implementation lane is supplied by Luna, not inferred from a hash. No claim of
unobservable continuous filesystem immutability is made.

Exact direct dependency hashes (all matched the contract; final local_source
replaces its baseline pin):

| Path | SHA-256 |
| --- | --- |
| crates/yu-hir/src/module/local_source.rs | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |
| crates/yu-syntax/src/declaration/binding.rs | `eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544` |
| crates/yu-syntax/src/expression/operator_chain.rs | `81db2aec4774f2cd1ddc12b64fd9206cf41cdf3eee00ed740676ffc6d7fc5669` |
| crates/yu-syntax/src/statement.rs | `fe8ba4e144b0c3ea5c8f451dddea42f718e9c3087aa77bb81447c61a9d213797` |
| crates/yu-hir/src/module.rs | `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a` |
| crates/yu-hir/src/module/source_annotation.rs | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| tools/inference-playground/src/lib.rs | `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b` |
| tools/inference-playground/src/runtime/program.rs | `484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11` |
| tools/inference-playground/src/runtime/machine.rs | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| tools/inference-playground/src/runtime/receiving.rs | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| notes/theory/2026-10-19-r91-original-suffix-outer-receiver-rev2.md | `f7605fbf7b4ec14d1fc916488d9757e7df4380856259db2bb9819033960cc729` |
| notes/theory/2026-10-19-r88-ordered-selection-source-bridge.md | `185eff03dfcef4cd9ea346434d60e34b39fcc0f34d46641b160decb58f0f1782` |
| notes/theory/2026-10-19-r78-receiving-selection-certificate.md | `a6fcf5c95169f7b71932476a5fff915e1ac450b7859755c595bf6d73a30af31c` |
| tools/inference-playground/examples/original-suffix-outer-receiver.yu | `0530c7ce6ef6d881d3106c9f69b42a992d701928f163c4c34c8b14f89408b6c7` |
| notes/progress/2026-10-19-r91-closeout.md | `8bf9558d6f1b7732dca259f1b41b2724f6f9d9eb462910003e98a357b1a8dbe3` |

Authority hashes (existing R78 dependencies): top-level principles
`7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`;
annotation integration `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`;
directional addendum `f11c6594e43c29fbfdbca1638b5c548cecc12a5beb192cac743e60f022c1cc73`;
charter `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed`.

Author `/root/r92_proof`, requested `gpt-6-sol/high`; observed effective model /
effort UNKNOWN / UNKNOWN. Session `current-conversation-2026-10-19-r92-indented-body`.
Grant 600 seconds charged, no renewal. Exact freeze/time receipt is in the one
handoff. Only new paths are this note and
`tasks/agent-loop/inbox/20261019-r92-proof.md`; no scratch/generated paths,
coauthors, descendants or unresolved descendant leases. After final hash
submission, writes stop. Assignment stop condition reached; next action belongs
to Luna's execution/review seam, with no active successor claimed.

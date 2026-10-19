# R91 revision 2: original suffix and distinct outer receiving

Date: 2026-10-19. Sole author: `/root/r91_proof`. Artifact revision: 1.
Status: **candidate finite source/runtime derivation; fresh review pending**.
Contract revision 2 SHA-256:
`e8542da6c674b78972f8d87207990b3a2aed36e0e50214176d318ce95caf0509`.
Original contract SHA-256:
`31cdcdde40d6fa322ffc518cd3c9d33c89ddb385ee8d22198de8b41971f169d9`.
Baseline supplied by Luna: `44a23937f99c55dea03714e82581e4a5a409576d`;
no Git observation. The fixture is precisely original contract §Exact source
fixture, UTF-8 with no final newline. No fixture bytes were written here.

## Parent and finite application

The original effect-hygiene/source-native obligation preserves provider,
annotation position, receiver, request, residual and witness lineages under
joint `xi=(nu,K,D)`, with actual receiving/selection evidence and independent
outward contributions. Original Simple-sub/evaluator claims, source domain and
universal quantifiers remain unchanged. A/B remain OPEN 0→0; F1/FK1, R67,
joint K,D, native residual correspondence and general hygiene remain OPEN.
R50 is NOT_ADOPTED; R85 is AWAITING_USER_ADOPTION and unused.

The added producers supply revision 1's missing braced-block case. Applied to
this fixture, the pinned constructors and consumers yield a candidate path:
the signal request captures the original local-initializer continuation;
resuming with 11 completes that same local cell, then evaluates the retained
final-expression label `write::ping first`; the outer write Catch has its own
live positive Grant and returns Integer 23. This is a derivation from inspected
branches, not an observed execution. Luna's authorized public CLI result and
fresh independent source/spec review remain pending. No source/native or
production theorem follows automatically.

## Static identities and authentic construction

Use symbolic names for the actual constructor results, never invented numeric
IDs. Let `Rs`, `Rw`, `Rm` be the relay, receive and main definition roots.

| Source position | Retained constructor identity |
| --- | --- |
| signal Act / its ping member, lines 1–2 | family `S=(module,ActKeyS)`; operation `s=(S,MemberKeyS)` |
| write Act / its ping member, lines 3–4 | family `W=(module,ActKeyW)`; operation `w=(W,MemberKeyW)` |
| relay thunk / consumed Name, lines 5–6 | original formal `ts=(Rs,0)` and `Name(Parameter(ts))` |
| receive pending / consumed Name, lines 7–8 | original formal `tw=(Rw,0)` and `Name(Parameter(tw))` |
| inner Catch / k / k 11, line 6 | `hs`; `ks=(Rs,ArmKeyS,1)`; Apply of `Name(CatchBinder(ks))` to Integer 11 |
| outer Catch / p / constant, line 8 | `hw`; `pw=(Rw,ArmKeyW,0)`; Integer 23; continuation Wildcard |
| braced argument, lines 9–12 | block index `B`, scope `Expression(B)`, owned by `Rm` |
| first / signal initializer, line 10 | local `f=(Rm,localOrdinal)`, initializer index `I`, scope `LocalInitializer(f)` |
| write::ping first, line 11 | final-expression index `F`, scope `Expression(B)`; payload Name resolves `Local(f)` |

SourceNodeKeys retain distinct declaration positions. `source_annotation.rs:
134–314` mints family/member IDs and indexes operations by `(family,spelling)`.
The two family keys differ, hence `S != W` and `s != w`, despite equal ping
spelling. The signatures are respectively Unit→Int and Int→Int. Operation
expressions and Catch patterns both use `resolve_operation`,
`local_source.rs:1088–1100`; unique public family/member entries resolve to
those exact declarations. A static occurrence is not a dynamic event.

R88's exact producer facts are reused only for existing syntax cases: Act
declarations, annotated original formal shapes, ground signatures, explicit
outer rows, operation paths, operation/continuation pattern pairs, empty
CallTail Unit, ordinary spaced application, Group and Catch body construction.
These constructor clauses instantiate at R91's explicit tokens; R88's three
completed U/O/S traces themselves do not prove this new input. R91's indented
relay/receive bodies follow pinned `binding.rs:320–365`: the next line's four
spaces select `indented_statement_block_normalized`, and LocalSource body
projection retains the contained OperatorChain. No recovery slot is needed.

For the new braced argument, `operator_chain.rs:109–140` creates OperatorChain;
its spaced-argument route at `:715–735,786–825` creates MlArgument, and
`append_nud` at `:351` sends LBrace to `statement::braced_nud_normalized`.
The actual `expr_from_nud_normalized` definition is in operator_chain.rs;
revision 1's mention of expression/mod.rs identified the dispatcher namespace,
not a separately inspected defining implementation.

`statement.rs:521–624` creates BracedStatementBlockExpression, emits `{`,
establishes the delimited statement baseline from the first interior line,
and enters its Braced sequence. Both interior statements begin at indentation
four. `statement_sequence_normalized` and `braced_statement_slot_normalized`
(`:631–721,935–1016`) consume them in source order. Statement admission routes
`my first = ...` to Binding and `write::ping first` to Expression
(`:332–374`). The initializer remains on line 10; equal-indentation newline
terminates its chain (`operator_chain.rs:774–776`), so it does not absorb the
line-11 expression. `braced_statement_successor_normalized`,
`statement.rs:1063–1132`, carries that newline to the next slot; the separator
owner at `:1162–1167` emits a childless BlockStatementSeparator containing
trivia. The closing RBrace terminates the block, followed by the existing
parenthesis closing the receive argument. Optional trailing separator trivia
contains no nested nodes. The new block therefore has the exact Statement /
separator / Statement shape required by the consumer, without recovery.

`local_source.rs:1233–1355` pops the final OperatorChain as `F`, retains the
preceding private BindingStatement as `f` with initializer `I`, and sets
`B=Block([f],F)`. Its LIFO work stack is pushed as Restore, final Expression,
then reversed initializers. There is one initializer: it runs first in
`LocalInitializer(f)`; Work::Publish restores its lexical guard and installs
`first -> Local(f)` before the queued final expression runs. Name lookup
`:1004–1040` therefore resolves the line-11 first to that original `f`.
The initializer has no parameters/self reference. No substitute formal,
reconstructed expression or name-based identity is introduced.

Catch construction `local_source.rs:1102–1180` assigns ordinal 1 to k and
ordinal 0 to p; only each arm's binders enter that arm's lexical scope. It
retains `hs: (s,Unit,ks)->k 11` and `hw: (w,pw,Wildcard)->23` in order.
Module construction `module.rs:2100–2138` passes the original formal IDs to
LocalSource, and `local_source.rs:815–842` brands every retained expression's
occurrence with its real node key/range. No numerical traversal-order claim
is needed.

## LocalSource to retained runtime code and receiving

`RuntimeProgram::from_hir`, `program.rs:277–566`, validates each source index
and maps it to `Label(offset+ordinal)`. It preserves `f`, `I`, `F`, expression
sites, resolved operations, original formal IDs and Catch binders/arm bodies.
Its source ownership walk marks a local recursive only for an actual self
reference in a parameterized initializer. Here `f` is nonrecursive, with no
self reference, so `LocalBinding(f,I,recursive=false)` is used.

The two annotated Lambdas become Computation-role closures with
RootCompSchemas; their actual formal Names become Execute consumers. The
schema constructor `receiving.rs:21–43` verifies original annotation/formal
ownership, explicit outer effects and Int value. The signal and write rows
are permissions; neither creates an operation occurrence, inferred inflow or
residual. The line-11 local Name has Observe consumption, not Execute.

`machine.rs:879–1009` allocates each whole argument as inert Delay before
selecting its entry role. Calling receive creates live invocation `uW`, Delay
`TW` for the original `(relay { ... })` argument, boundary `bW`, view `VW`,
and entry receipt for `tw`. The Catch `hw` installs under `uW`; consuming
pending records a genuine owner/read receipt `rW`, opens execution `EW`, and
executes TW (`:707–737,1858–1887`). Thus the outer Catch is already installed
when relay begins, and EW remains active through relay and its resumption.

Calling relay analogously creates distinct live `uS`, original block Delay
`TS`, boundary `bS`, view `VS`, entry receipt and genuine Name-read receipt
`rS`. It installs `hs` under `uS`, opens `ES`, and executes TS. These boundaries
are distinct even though both schemas have Int value. No inherited-image
equality between VS and VW is needed: both are genuinely executing views.

`begin_local`, `machine.rs:1889–1928`, allocates the original empty cell `c`,
pushes `Frame::Local{block=Bcode,next=1,environment=e,cell=c,recursive=false}`,
and evaluates `Icode`. The block pointer retains the same code containing F.
Operation Apply consumes Unit according to s's declared value payload,
returns a request carrier, and its declaration-owned result consumer executes
that carrier (`:1011–1069,1789–1804`). The operation-call receiver has already
returned before this request is emitted. `execute`, `:1929–1956`, allocates
fresh event `qS`, source equal to the line-10 application, and authentic
observations of both EW and ES. qS is not the static request occurrence.

## Capture and exact original suffix resumption

Propagation saves, innermost first, the Local frame and RootCompReturn(ES).
Popping RootCompReturn ends ES but preserves its historical receipt/execution
in the saved suffix. The next delimiter is the still-live hs under uS.
The relevant live stack, bottom to top, is then:

`module root; ReceiverReturn(uW); hw; RootCompReturn(EW); ReceiverReturn(uS); hs`.

`propagate_request`, `machine.rs:1550–1687`, validates hs's live installer and
exact s declaration. `Receiving::local_grant` is positive: qS observed VS,
its authentic rS belongs to uS, VS's image reaches bS, and bS's original row
contains S. Unknown older coverage is harmless to this positive witness.
Unit payload compatibility and Int response declaration also hold.

Because k is a Binder, `capture_template`, `:1309–1379`, builds from the actual
saved suffix, with no GlobalRead/Root materialization frame inside this local
capture. Its nodes are Hole; Bind(original Local frame); View(original ES);
Owner(original uS). Root traversal installs them in reverse nesting order,
recreating original Local above the execution-return and owner-return frames.
The selected hs delimiter is removed shallowly and is not reinstalled. Its
arm binds the captured template to the original CatchBinder ks, then runs k 11.

That Apply allocates a fresh continuation-call invocation `uK` and evaluates
the integer response. ResumeArgument verifies it against s's Int result
(`machine.rs:742–820`). `enter_template`, `:1380–1477`, borrows still-active
uS (`owned=false`, previous=uK), opens a fresh authentic execution `ES'` of the
original VS/receipt, and pushes the cloned Local frame with the **same block,
environment, next and cell c**. Hole returns the actual Integer 11 value.
No fresh local cell or replacement suffix expression is allocated.

Returning through Local (`:1100–1158`) writes that value into c, extends the
environment with `Binder::Local(f)->c`, and calls `begin_local(Bcode,1,e')`.
There is only one binding, so the no-more-bindings branch evaluates the
retained `Fcode`. Lookup by `Local(f)` reads c and yields that same Integer 11
as the w payload. This is the original post-request suffix, established by
retained indices and cell ownership, not by matching its printed text.

## Distinct write event and outer positive Grant

The declared w application emits fresh event `qW` with its own line-11 source
site and payload 11. Monotone `next_request` makes `qW != qS`; resolved
`w != s` independently. Its observations include EW and the resumed ES'.
The original inner Catch hs has been consumed. It cannot catch this request,
and no reconstructed inner handler is assumed.

The pending stack above hw is, top first:

`RootCompReturn(ES'); OwnerReturn(uS,owned=false,previous=uK); ResumeReturn;
ReceiverReturn(uK,previous=uS); ReceiverReturn(uS,previous=uW);
RootCompReturn(EW)`.

Propagation (`machine.rs:1706–1761`) ends ES', restores current owner uK from
the borrowed uS span, unwinds ResumeReturn, deactivates uK, deactivates the
original uS, restores uW, then ends EW. uW's ReceiverReturn lies below hw, so
uW is still active. `validate_handler_installation`, `:1516–1530`, now sees
hw's actual owner uW equal to the current execution owner.

The outer selection has its **own** positive Grant under
`receiving.rs:232–326`: qW's EW observation is authentic and event-specific;
the existing candidate-owner rW is for `(uW,VW)`; VW's image reaches bW;
bW's original annotation row contains W; uW remains live. Ending EW during
unwind does not invalidate its historical observation or receipt. VS, its
signal permission, and qS's grant are not substituted for any of these facts.
This establishes local_grant=true even without relying on the independent
closed-primitive certificate branch.

The arm's full declaration w matches, its declared Int payload accepts 11,
and p binds that request payload. Wildcard continuation means no second
capture: hw is popped, the already-unwound suffix is abandoned, and the arm's
retained Integer 23 is evaluated outside hw. The still-live outer receiver
returns and the module root caches/selects 23 (`machine.rs:1070–1087,
1200–1236,1805–1856`). The library's ordinary execute route renders a completed
Integer verbatim (`lib.rs:166–195`). No discard action is offered as proof of
an arbitrary foreign-continuation quantifier.

## Evidence boundary, remaining work and freeze

This derivation supplies a candidate application to the exact R91 construction
and runtime path. Fresh review must check the new block production, LIFO/source
order relation, original f/c/F joins, captured frame order, owner restoration
and independent outer Grant. The authorized CLI stage must still observe exit
0/stdout 23; it is not supplied by this author. `lib.rs::execute` first invokes
`prepare`, including candidate inference; this note proves no general solve,
constraint-derived residual or native supplier/consumer correspondence. No
uninspected native inference owner is claimed as established. The CLI stage
can supply finite acceptance evidence, never universal inference proof.

Mutual TODO `R91-REVIEW-2`, owner Luna: obtain fresh independent review of
these frozen bytes and dependencies. Falsifier: any actual constructor emits
a different node/ID/scope/index, the saved Local frame uses a different cell
or suffix label, owner unwinding fails, or qW lacks the authentic uW/VW/bW
grant. `R91-EXECUTE-1`, owner implementation lane then Luna: create only the
exact fixture and run only the original authorized command; parser rejection,
runtime unavailability or a result other than 23 falsifies the executable
expectation and requires adjudication, not a semantic workaround.
Original native/universal TODOs in R78 remain with their original owners.

No production implementation change is required by this candidate path, and
none is authorized. No new semantic law, bypass, effect cap, inferred empty
residual or permission-as-inflow assumption is used. Ordinary Simple-sub
generation, accumulation, propagation, levels, extrusion, qualifying intrusion
and generalization retain their complete obligations. This exact local
continuation example neither proves F1/FK1 nor collapses independent lineages.

All 17 original-plus-added dependency hashes and both contract hashes matched
before freeze. Original 15 values are the exact original contract table,
also preserved in revision 1's note. Added operator_chain.rs:
`81db2aec4774f2cd1ddc12b64fd9206cf41cdf3eee00ed740676ffc6d7fc5669`;
statement.rs:
`fe8ba4e144b0c3ea5c8f451dddea42f718e9c3087aa77bb81447c61a9d213797`.
Immutable prior proof/handoff hashes still match:
`924df42ae3385fe7f8dbf6943518d392227ff64d37986c7bf69590257ea7007c` /
`ef6dd2bc4b441afb22a4d6e2308e09585a3d01d8d757dc5aaa358ba41c65dc15`.
R78 `/root/r78_proof` and R88 `/root/r88_proof` retain their original authorship
and candidate premises; no historical producer is an independent R91 reviewer.

Checks: read-only pinned-source branch inspection and SHA-256 comparison;
no tests, builds, runtime probes, compiler execution, CLI, Git or network.
No descendants or scratch/generated paths. Sole author `/root/r91_proof`;
requested Sol/high, effective observed model/effort UNKNOWN/UNKNOWN. New
stage grant 300 seconds; cumulative charged cap 900 seconds including the
unchanged earlier 600. Stage start observed 2026-10-19 03:38:49 UTC; freeze
elapsed is in the handoff. Exact new paths: this artifact and
`tasks/agent-loop/inbox/20261019-r91-proof-rev2.md`. Revision 1 is unchanged.
After final hash submission, writes stop; next step is Luna's review and
execution seam, with no active successor or production/parent closure claim.

# R124: effectful response before saved tick-template entry

Status: **conditional finite source/runtime derivation; fresh review pending**.
Assignment `R124-PROOF`, revision1. Sole author/writer `/root/r118_proof_lane`;
no coauthors or descendants. Contract rev3 SHA-256
`0463b605f1b339966a6e1b69c2347d3d18133210b305dd35d56b5fffdd1c92c3`;
baseline `dfcdea084`.

## Exact claim and explicit premises

For the exact247-byte/no-final-LF source, specified SHA-256
`e50687fbb969684f41cb6b7f1cba627aed97602dd3847714b8379e40de928ea9`:

```yu
act io:
    our tick: int -> int
    our other: int -> int
my answer (pending:[io] int) = catch pending { io::other(p), j -> j p }
my relay (thunk:[io] int) = catch thunk { io::tick(p), k -> answer (k (io::other 11)) }
my main = relay (io::tick 7)
```

The finite successful path is:

```text
tick7 → capture Tk → answer entry → start actual k call activation
      → evaluate other11 once → capture Tj → call j with its own payload11
      → Tj restores pending ResumeArgument(Tk) with11
      → enter saved Tk with11 → complete k/j/answer/relay/main
```

The actual k call activation begins **before** forcing its delayed response;
entry into k's saved tick template occurs **after** j resumes that pending
response consumer. These are separate transitions, not interchangeable meanings
of “entry”. No event order/count is inferred from final output alone.

**H:** exact parsing/lowering/retained LocalSource succeeds with original
definition/formal/arm/binder/operation/Apply identities and lexical environments
described below, including authentic concrete io annotations and primitive
Int→Int declarations. **A:** ordinary candidate preflight/collection/solving
succeeds without conflicts and full RuntimeProgram/start admission succeeds
for that same HIR. Source typing, operation/arm compatibility and ordinary
view/transition correspondence retain their independent premises.
**E:** genuine schema/receipt/execution/observation, positive local Grant,
primitive response, owner/lifetime and template checks succeed.
**B:** no identity/resource/I/O failure and completion within public10,000 steps.
H/A and actual bounded transitions were not observed by this author.

Charter §§16/21 apply only under §24's receiver-role clarification: annotated
pending/thunk retain whole Comp arguments; continuation response demand occurs
inside the actual call activation. No universal function-as-handler or general
fresh-receiver law is imported. The reviewed template correspondence §§10–12
is reused only within its original typing/current-configuration premises;
its old source hashes are not substituted for current pins. Full arbitrary
resumption/foreign-continuation, general once-only effects, priority, projection,
all six hygiene parents, original Simple-sub/evaluator A/B, method M/T/A and
R85 adoption remain OPEN.

## Source identity and consumer correspondence

Let R_A/R_R/R_M be answer/relay/main's actual source roots. Their actual
definition-owned formals t_A=pending and t_R=thunk are distinct. Under H,
module.rs::lower_plan (2080 onward) mints each own parameter ID/source mapping;
LocalSource::form (596–634) retains each original annotation and installs its
Parameter resolution before the original body. Both own `[io] int` annotations
select Comp, irrespective of body use or solved effects.

For original answer arm key a_A, `catch_value_pattern` (local_source.rs1104
onward) constructs beta_A=(R_A,a_A,0) for p and gamma_j=(R_A,a_A,1) for j.
For original relay arm key a_R it constructs different beta_R=(R_R,a_R,0)
and gamma_k=(R_R,a_R,1). The two p tokens and two ordinal1 continuation
binders do not identify their keys/owners. Work::CatchArm installs exactly
those constructed resolutions before body Name formation; lexical latest
lookup precedes module lookup. Thus answer's `j p` reads gamma_j/beta_A;
relay's `k` reads gamma_k; answer's scrutinee reads t_A; relay's reads t_R.
Main relay and arm answer resolve to their own unique ModuleDefs under H.

`resolve_operation` (1091–1103) preserves distinct d_tick/d_other declarations
from original namespaces. Main's Operation tick and relay pattern tick share
d_tick; response-expression Operation other and answer pattern other share
d_other. Their use occurrences, enclosing Apply occurrences and source roots
remain separate. PendingRequest.source comes from the operation Apply's
Frame::Callee site through OperationPayload/make_request_carrier, not an
invented textual span or the operation-name occurrence.

The argument tree retains whole groups: answer's inert argument is
Group(Apply(Name(gamma_k),Group(Apply(Operation(d_other),Integer11)))). No group
executes its child during carrier creation. Candidate emission requires exact
HIR-owned LocalSource and occurrences; formal visits retain own annotation/
entry actions and parameter IDs. CatchOperation retains original declaration,
owner/body occurrence, payload and continuation endpoints (candidate_source.rs
991–1030,1045–1088). Apply follows its original child/endpoints/effects/level
and cause. This does not prove whole solving/admission or native propagation.

RuntimeProgram clones original resolutions, original arm/body labels and sites;
its own formal classifiers produce Comp and Execute for t_A/t_R (414–434,
488–516). Catch-binder Names Observe. RootCompSchema checks each own annotation
owner, explicit effects and ground Int. No synthetic transition object or
OperationV1 receipt is introduced: all responses use the original primitive
Int branch and ordinary default-evidence program path. The separate
Function-response/42 fixture supplies no premise here.

## Finite machine construction and saved frames

Use actual owners r=relay, a=answer, c=original k call, z=j call; c' below is
the generic owned reentry of c's saved span, not a repeated source call.
Use original execution views x_R/x_A, distinct events q_tick/q_other, and
distinct immutable template handles Tk/Tj. Stack notation is bottom→top.
R_main is main's original root publication frame; RR_i is an ordinary receiver
return. These symbols denote actual constructor results, not numeric IDs.

1. Main calls relay. The whole tick7 argument becomes inert D_R. Relay's Comp
   entry creates r, its own boundary/received view and entry receipt; it installs
   the tick Catch H_R. Reading thunk records a genuine r/view receipt, opens
   x_R and executes D_R. The operation's own Value entry evaluates payload7
   inside its temporary invocation and returns its request carrier; only after
   that invocation ends does OperationResultConsumer emit q_tick.
2. At matching H_R, stack is `[R_main,RR_r,H_R,RootCompReturn(x_R)]`.
   Propagation ends/saves x_R, then validates H_R with current live r. Its
   positive local Grant joins q_tick's authentic x_R observation, r's genuine
   same-view entry/read receipt and concrete io boundary. Primitive payload/
   response checks succeed under E. Capture forms
   `Tk = Owner(r,View(x_R,Hole))`, retaining original tick declaration/event.
   H_R is removed before evaluating its arm; RR_r remains live. It binds
   beta_R to7 and gamma_k to the callable handle Tk. No selected handler is
   included as ForwardHandler or automatically reinstalled.
3. The arm obtains answer's closure; any pure closure initialization completes
   before its argument runs. It makes inert D_A for the **whole** k(other11)
   group in the original relay arm environment containing gamma_k. Answer's
   Comp entry creates a, boundary/view and receipt; it installs H_A for other.
   Reading pending records its genuine a/view receipt, opens x_A and executes
   D_A. At this point r and a are live; x_R is ended, x_A is executing.
4. Evaluating k's Name only obtains Tk; it does not enter Tk. Frame::Callee
   (machine.rs880–916) creates inert D_C for the whole grouped other11 argument,
   calls new_invocation to create actual c, and pushes RR_c then
   `F = ResumeArgument {template:Tk, source:k_apply_site}`. It then executes
   D_C **inside c**. There is no EnterTemplate(Tk) in this branch.
   Stack is `[R_main,RR_r,RR_a,H_A,RootCompReturn(x_A),RR_c,F]`.
5. D_C executes the original other Apply exactly once. Its ordinary declared
   Value entry evaluates original Integer11; pinned literal::integer accepts
   its ASCII digits and returns canonical text11. After the temporary operation
   invocation returns, execute(Request) creates fresh q_other with payload H11,
   original d_other/Apply source and observations `[x_A]`. No x_R execution
   remains active. The code/environment of D_C still comes from the relay arm;
   static source root and dynamic owner c are distinct.
6. Request propagation pops F unchanged into its suffix, then pops RR_c,
   calls leave_owner(c,true,a), marks c inactive and saves ReceiverBoundary(c).
   It next ends/saves x_A. At H_A the current owner is a. Thus the exact suffix
   is `[Ordinary(F),ReceiverBoundary(c),Ordinary(RootCompReturn(x_A))]`.
   Original main publication and RR_a are below the selected bound and absent
   from capture. No pending cache-publication guard is bypassed.
7. H_A's own annotation permits original io. q_other's authentic x_A observation
   joins genuine candidate-owner a/view read receipt (or own-formal entry key),
   then its image reaches a's boundary. a remains active despite c's exit, so
   positive local Grant succeeds. Operation identity and primitive payload/
   response checks are independent. This route suffices without any claim
   about the uninspected closed-primitive classifier's boolean.
8. capture_template folds that actual suffix (1309–1381) into
   `Tj = Owner(a,View(x_A,Owner(c,Bind(Hole,F))))`.
   Tj retains q_other's declaration/event; F retains the already-existing Tk
   handle, checked against the same arena before publication. It does not
   retain D_C's argument code as an instruction to reexecute. Tj and Tk are
   different arena objects from distinct selected requests/binders.
   H_A is removed; beta_A is bound to q_other's payload H11, and gamma_j to Tj.

## j resumes the pending response consumer, then Tk enters

9. Original answer arm `j p` obtains Tj, creates inert argument Delay for
   Name(beta_A), creates actual call owner z, and installs RR_z/ResumeArgument(Tj).
   Forcing that Name Observe reads the original answer payload H11 without
   running other again. ResumeArgument(Tj) checks original **other** declaration's
   Int result via primitive_matches, pushes one ResumeReturn_j and enters Tj
   with a fresh control map (748–817).
10. Tj's Owner(a) borrows still-active a below z, recording owned=false and
    previous=z. Its View(x_A) opens a fresh execution occurrence on the original
    view/receipt and pushes its root-view completion. Its Owner(c) finds c
    inactive after step6. The actual generic owner branch obtains c's original
    call/provider descriptor, creates fresh owned executable span c', maps c→c'
    and installs OwnerReturn(c',true,previous=a). It does not repeat the source
    k Apply, call receiving.enter or force D_C again (1384–1440).
11. Bind pushes original F; Hole returns H11 directly. F consumes that returned
    response, checks the original **tick** declaration's Int result, pushes
    ResumeReturn_k and finally sets EnterTemplate(Tk). This is the first entry
    into Tk on this execution. Merely having created c earlier was not entry
    into this saved context.
12. Tk Owner(r) borrows still-active r, whose original RR_r lies below the whole
    answer/j computation. Its view reentry opens a fresh execution occurrence
    from original x_R's view/receipt. Hole returns H11; root-view completion
    projects its view while preserving its value handle; borrowed r completion
    restores c'; ResumeReturn_k passes the completed suffix result onward.
    Tk reentry creates no new receiving boundary/receipt or tick/other event.
13. Completion then follows Tj's parent frames: owned c' completion ends only c'
    and restores a; resumed x_A completion ends its execution; borrowed a
    completion restores z; ResumeReturn_j returns to RR_z. RR_z retires z,
    original RR_a retires a, original RR_r retires r. Only then main's original
    Root publishes H11 and source-schedule completion returns Completed(H11).
    These nested completions are not shortcuts that return to j before F/Tk.

All owner steps use current invocations/control state and original lexical
fields. No saved store/activity snapshot is restored and no expired receiving
boundary is revived. The c' branch is a concrete finite source/code case under
the generic implemented owner protocol, not a new fresh-receiver semantic law.

## Exact ordering/count consequence and evidence boundary

The specific other-expression Delay is executed once by the source k-call
branch before F can consume a returned value. At q_other it is already running
and its operation frames have returned. Tj saves the **pending response
consumer F**, not the expression Delay/code. Reentry supplies H11 to F directly;
F enters Tk without another execute(response) or source argument entry. Neither
source arm repeats j/k, nor does any template contain the other-expression
evaluation frame. The exact successful finite trace therefore evaluates/emits
this other request once, before saved Tk entry. This conclusion uses actual
constructors and the fixed source control flow; it does not generalize to
arbitrary reusable continuations, loops, recapture or foreign response carriers.

The existing runtime test (runtime_resume.rs491–499) contains this exact fixture
and asserts only Completed(Integer11) through a30,000-step helper. Its name
does not add order/count assertions. This author has not rerun it; no stronger
historical observation is inferred from its source assertion or final11.
The new public test's10,000-step completion is an independent B premise.

lib::prepare lowers once, solves a clone of that HIR Arc and returns it;
execute passes the returned HIR to RuntimeProgram::from_hir with ordinary
default evidence and starts its source schedule. Successful H/A is not proved
by this wiring. Under B, execute renders Integer11 plus LF; main prints it on
success and emits no error. Predicted public stdout is exactly `11\n` with
success/empty stderr. This observation alone cannot establish event count or
the private F/Tj/Tk/owner sequence. No OperationV1 receipt, Function-response
bridge or separate42 fixture is used.

## Remaining premises and mutual TODOs

- `R124-SOURCE-1` / Luna source reviewer, HIR/candidate owners: establish H/A
  for exact bytes and original gamma_j/gamma_k/beta/formal/declaration/Apply
  joins. Wrong binder or operation, source refusal/conflict, substituted HIR or
  unsupported admission falsifies the instance; assumed transitions do not prove it.
- `R124-ORDER-1` / compiler/source reviewer, machine/template owners: verify
  exact F/RR_c/x_A suffix, c lifetime/reentry, Tj supply of11 to F, and first
  EnterTemplate(Tk). Conflated activation/template, lost F, repeated response
  expression, early Tk entry or bypassed nested completion falsifies the trace.
- `R124-EVIDENCE-1` / receiving/source owners: preserve independent compatible
  response/source typing and authentic positive Grants/view/owner predicates.
  Historical reachability, same family or equal Int types alone is insufficient.
- `R124-CLI-1` / Luna implementation/verification lane: freeze the exact stdin
  cell and three CLEAN reviews, then only the authorized one-shot command.
  Failure, timeout/non-admission, budget exhaustion or stream mismatch leaves
  observation OPEN. Existing fixtures/expectations remain untouched.
- `R124-REVIEW-1` / Luna: fresh compiler/source, spec and regression review.
  Producers/coauthors cannot certify their outputs or general parent closure.

No production implementation TODO or enlarged dependency is requested.
Generation/accumulation/propagation/levels/extrusion/qualifying intrusion/
generalization and independent provider/residual/witness lineages are preserved.
Next writer step after freeze: none; Luna owns intake, review and command.

## Complete access/pin inventory and resources

All18 input pins matched before writes and are unchanged in rev3. B means body
inspected plus hash; H means hash-only inventory. Full paths are the contract's
exact paths. Every input accessed in this assignment is listed:

| Input | Access | SHA-256 |
| --- | --- | --- |
| R124 rev2 contract (preserved audit) | B | `6259fb4c7f667e63c54a859c0b06f0870620d88fb6ce55f25bc819ec76e93a3f` |
| R124 rev3 contract | B | `0463b605f1b339966a6e1b69c2347d3d18133210b305dd35d56b5fffdd1c92c3` |
| charter | B | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| inference principles | H | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| resume-template correspondence | B | `f3a4c925a197e63e5b7faf1ce1e1caf5736d76f1b86ba162c6acc85bfff8e7dd` |
| tests/runtime_resume.rs | B | `449c3ce11ef04fa60a49517c2fc8a7994d1547cb2dee058d6fdcbd0b095f8580` |
| tests/cli_local_resume.rs | H | `c315daccfd28279192b0052f55c5558fa11133509291855129f744037633e747` |
| playground Cargo.toml | H | `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56` |
| playground lib.rs | B | `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b` |
| playground main.rs | B | `75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100` |
| runtime/machine.rs | B | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| runtime/program.rs | B | `c2363ad42104b895519bb29a8eb9aeda545bd0176cebbd78750d3a2df90849ca` |
| runtime/continuation.rs | B | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| runtime/receiving.rs | B | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| runtime/mod.rs | H | `64d208743793a03501a76f56bc2b511c50ed40cff3f789757a00b7d608fc846b` |
| runtime/literal.rs | B | `2fff177a7ba0cabb4930251e1facc8f9be701ff3ec7baa695ce4c182fa1da35f` |
| HIR module.rs | B | `153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907` |
| HIR local_source.rs | B | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |
| HIR source_identity.rs | B | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| solver candidate_source.rs | B | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` |

Historical template proof is attributed to its assigned prover leaf; concrete
contributor IDs UNKNOWN here. Contract/status owner Luna; source/test/charter
byte authors UNKNOWN. Present author cannot independently certify this result.
Requested configured Sol/high; observed model/effort UNKNOWN/UNKNOWN, no switch.

Original cap480sec: first audit10:43:20–10:45:05 UTC=105 observed; Luna charged
165 including60sec conservative preclock locator work. No outputs existed on
that STOP. CLEAN rev3 regrant resumed same session at10:47:06 UTC, max315sec
remaining; no reset/borrowed budget. Final clock/accounting is in handoff.
Static listed read/hash inspection only; no unlisted owners, executable
verification/tests/builds/CLI/probes/formatter/Git, code/question edits or children.
Only this note and assigned inbox are new; no scratch/generated paths or other
writer files touched. **Freeze rev1 then STOP.** All original parents remain OPEN.

# R136: finite Boolean-selected reuse of one raw continuation

Status: FROZEN candidate source/native constructor derivation, revision 1;
independent review and actual specimen execution pending. Author:
`/root/r136_proof`, sole author, no descendants. Requested model/effort:
Sol/high; observed model/effort: UNKNOWN. No production authority.

## Parent, scope and premises

Frozen contract: `tasks/agent-loop/sprints/repeated-choice-20261020-r136-rev1.md`,
SHA-256 `2a9faf4255b2d74bb3c03cd2feff342d8d4c15ea9b544177a93f10c07930d28f`;
supplied baseline `6c04fc08f76bc4cc2d71a3910e4aa476097a378b`.
Luna's assignment reports both prospective reviews CLEAN and grants exactly
this note and `tasks/agent-loop/inbox/20261020-r136-proof.md`.

The parent outcome is proof-backed inference/evaluation breadth with unchanged
Yulang2 sample behavior. This packet contributes only the finite repeated-choice
example. It neither replaces nor closes the original Simple-sub/evaluator A/B,
effect-hygiene, soundness, principality, F5, native K/D or independent F1/FK1
obligations. No universal foreign-continuation conclusion follows from the local
active-owner action below.

The exact source to be related is the contract's specimen:

```yu
act signal:
    our choose: () -> bool
my relay (thunk:[signal] int) = catch thunk { signal::choose(), k -> { my first = k true; case first: 11 -> k false, _ -> first } }
my main = relay { my choice = signal::choose(); if choice: 11 else: 23 }
```

Claim: conditional on successful ordinary source preparation of these bytes,
with the retained identities/roles described below, current runtime constructors
derive `Completed(Integer("23"))` by the finite trace in this note. CLI text
`23\n` additionally needs the actual entry/formatting path; Web selection and
execution need their actual registered-example path. Those observations belong
to Luna's implementation/verification lane, not this static derivation.

Preparation means parser/HIR admission, successful `CandidateInference::solve`
with no candidate conflicts, and `RuntimeProgram::from_hir`/start on `main`.
Enough allocation/identity/step resources for this finite trace are required.
Neither admission of the combined specimen nor a runtime outcome has been
observed by this leaf. The operational steps below are derived from inspected
constructors and consumers, not a checker supplied with assumed transitions.

## Governing source and constructor/constraint bridge

The authoritative source reference is the intrusion charter §§13–18,20–21,24
and source-call-scheduling choice §§1–2: whole arguments are inertly reified;
explicit computation formals retain them; entry/consumption uses the selected
source interface; selection and arms run outside the shallow handler; selected
handlers are not restored by raw resume. §24 preserves the distinction between
receiver role and parameter entry. Top-level inference principles preserve
generation, accumulation, propagation, levels, extrusion, qualifying intrusion
and generalization. No runtime branch result is used to skip inference branches.

Typed-source-owner-realization §§1–3 supplies the decorated-source owner/context
reference, with its stronger elaborated-input premises explicit. It and the
ordinary-computation package remain Draft packages; their full-source adequacy
is not assumed. The current-machine finite construction is checked directly.

| Owner | Evidence and limit |
| --- | --- |
| `crates/yu-hir/src/module/local_source.rs::expression`, `resolve_operation`, `catch`, `case`, `conditional`, `block` | Retain Boolean/Integer/Apply/Block forms, source occurrences and lexical IDs. `catch` records one Unit payload pattern and the arm's continuation binder (ordinal 1); lexical resolution makes both `k` Names that same CatchBinder. `case` preserves Integer(11) then Wildcard order; `conditional` retains the colon-form condition, then body and else. This is constructor evidence conditional on actual parsing/lowering of the specimen. |
| `module/source_annotation.rs`, `RootCompSchema::from_parameter` | Resolve the concrete `signal` family and declaration-owned `choose`; retain `() -> bool` and `[signal] int`. The schema requires actual annotation/formal source ownership, explicit effects and primitive result. No general annotation meaning is inferred from syntax alone. |
| `candidate_source.rs::preflight_catch_signature`, `Work::CatchArms` | Referenced `k` requires both polarities of the primitive Boolean response. Retain its component and level; issue `Action::CatchOperation` against the original scrutinee endpoint/effect. Unit payload has no binder. |
| `candidate_source.rs` Catch/Case/If generation and action consumers | Catch merges scrutinee/arm effects and result contributions; Case adds integer scrutinee/pattern bounds and both arm result/effect contributions; If constrains the condition to Bool and includes both Int branch results and effects. Integer equality selects execution, not constraint generation. |
| `candidate_effect.rs::candidate_operation`, `candidate_catch_operation_inner` | The operation gets its declaration signature. The continuation pairs the same declared Boolean response with original scrutinee result endpoints, Value response entry, and conservative original/full-S effects. Slots 62/63 retain its two function bounds; slots 64/65 constrain entry/original effects into the returned effect. The code explicitly leaves precision/full handler hygiene OPEN. The operationally request-free suffix here does not justify changing that static bound. |
| `shadow_apply.rs::CandidateInference::solve_mode` | Performs source preflight, batch collection, `InferenceSession::try_new_candidate`, then `run_candidate`. Existing admission/live constraint consumers propagate the generated links. This packet does not prove solve success, extrusion/intrusion incidence, generalization preservation or a complete source/native evidence projection. |
| `runtime/program.rs::RuntimeProgram::from_hir` | Maps retained forms to Boolean, Integer, Apply, Block, If, Case, Operation and Catch instructions with source labels/IDs. Case decodes integer patterns and preserves source order. Parameter Names use their selected consumption; other Names Observe. Explicit `[signal] int` gives Computation entry and the genuine root schema. |

The inference bridge names actual source owners without substituting evaluator
success for an inference theorem. Baseline HIR/signature/solve owners were
explicitly approved by Luna for pinning during this packet; hashes are below.

## Finite runtime derivation

Let `r` be relay's invocation, `h` its one Catch occurrence, `v` the rooted
view for its received thunk, `c` the pending main-block cell for `choice`, and
`d` the distinct handler-block cell for `first`. Let `t` be the template handle
eventually bound once in the arm's lexical `k` cell. All identities are actual
constructor identities, never equations between names with equal spellings.

1. Apply obtains relay, delays the whole main block and enters `r`.
   The Computation formal branch in `Frame::Callee` creates the root boundary,
   genuine formal receipt and thunk binding. `Instruction::Catch` installs `h`
   under `r`. Consuming the formal Name records its ordinary receipt and opens
   execution of `v`; it then executes the delayed main block. `begin_local`
   allocates pending `c` and waits in `Frame::Local` for `choose()`.

2. Operation application consumes Unit inside its ordinary invocation, builds
   a request carrier, leaves that operation invocation, and only then executes
   the carrier through `OperationResultConsumer`. `execute` allocates one fresh
   request event with the declared operation ID, Unit payload and observations
   of the executing view. Hence its expired operation receiver is absent from
   the captured suffix. No request event is reissued by resumption.

3. `propagate_request` saves the pending Local frame, ends/saves the rooted
   execution, and reaches `h` while `r` remains active. Its exact operation ID
   matches. If a local grant is required (`!closed_primitive`), the existing
   formal/read receipt, authentic same-event observation, view image containing
   the `r` boundary and concrete `[signal]` schema satisfy `Receiving::local_grant`.
   This is the positive initial receive path, not an inference from absence of
   protection. Unit matches the declared payload; Bool is an admitted primitive
   continuation response. No additional receiving boundary is needed.

4. `capture_template(request,r)` constructs exactly:

   ```text
   n0 = Hole
   n1 = Bind(n0, Local(main-block,next=1,original-environment,c,recursive=false))
   n2 = View(n1, original execution of v)
   n3 = Owner(n2, Invocation(r))
   root = n3
   ```

   The selected `h` is popped after validation, then its arm binds
   `ExecutableValue::Continuation(t)` once as `k`. There is no ForwardHandler,
   crossed ReceiverBoundary, GlobalRead or Root node in `t`. Relay's own return
   delimiter lies below `h`; `capture_template` includes the containing owner
   explicitly but excludes source code beyond the bound. The template retains
   code, environment/cell references, declaration and original event, no store
   snapshot. This exact four-node chain is the finite construction to review.

5. Handler `begin_local` allocates distinct pending `d` for `first` and applies
   the lexical `k` to `true`. The continuation Callee branch creates ordinary
   call activation `a1`, delays and forces this Boolean argument once, then
   `ResumeArgument` checks `primitive_matches(Bool, true)`. It installs one
   `ResumeReturn` and enters the same `t` with a fresh empty control map.

6. Entering `n3` resolves still-active `r` and borrows it (`owned=false`), saving
   previous owner `a1`; the inactive-owner branch is not reached. `n2` opens a
   fresh execution occurrence using the retained view/receipt; it does not mint
   a replacement receiving boundary or rewrite the old receipt's owner. `n1`
   pushes the original Local frame; `n0` returns the actual `true` value. That
   Local writes `c=true`, extends the original environment with choice's ID
   and evaluates the original final `if`. Choice Observe returns true;
   `Frame::Condition` selects Integer(11). No operation occurs in this suffix.

7. Return closes that fresh view execution, completes borrowed `r` without
   popping it, restores `a1`, crosses the single ResumeReturn and ends `a1`.
   The pending handler Local receives Integer(11), writes `d=11` and evaluates
   `case first`. Case reads `d` and chooses its first Integer(11) arm by exact
   decoded integer equality. The Wildcard body is not executed. This establishes
   the required dependency on the first resumed result: `k false` is reached
   through that returned value's Case consumer.

8. The selected arm reads the same CatchBinder cell, hence the same `t`, and
   applies it to `false` under ordinary new call activation `a2`. Bool checking,
   fresh empty control map, borrowing active `r`, view re-execution and Local
   replay are exactly the constructors in steps 5–6 with response false.
   The shared cell is now `c=false`; `d` remains Integer(11), a different cell
   and value. The resumed original conditional selects its else Integer(23).
   No copy/reset of the store or second operation request occurs.

9. View completion and borrowed-owner completion restore `a2`; ResumeReturn
   and `ReceiverReturn(a2)` return 23 to the selected Case arm's continuation.
   There is no selected-handler restoration. The arm result returns through
   relay's original delimiter, ending `r` once, then main's normal root path
   publishes/completes Integer(23). There is no later use of `k` after `r` ends.

Thus the current transition constructors give the finite sequence
`choose() -> capture(t) -> t(true) -> 11 -> case(11) -> t(false) -> 23`,
conditional on the stated preparation/resource premises. Ordinary call
activations `a1/a2` and ordinary Name observations are source-prescribed;
they are not synthetic Receive grants inserted to repair a failed trace.

## Prior work, exclusions and parent application

Reuse: `runtime_resume.rs::reusable_raw_context_writes_its_original_pending_local_cell`
supplies an existing source/test pattern for the same pending-cell template
reuse; `raw_response_uses_the_declared_boolean_response_type` supplies the local
Boolean-response/conditional pattern. Their test bodies and current owners were
inspected; neither test was run here. R98's note supplies useful local binder,
suffix and active-owner audit structure, rechecked against current hashes.
Its distinct-receiver matrix never ran: the R98 closeout records E0618 during
test compilation. That failed matrix, N1/N2 outcome predictions and R99's
forbidden fresh-receiver repair are not evidence for R136. No R98/R99 repair
was attempted. The older resume-template characterization is contextual
history with its explicit source-typing/full-domain gaps, not a blanket theorem.

Application: the parent's R136 example slice now has an explicit finite
constructor derivation locating both data dependency and shared continuation
identity. The outstanding first evidence is actual preparation/execution of
this combined specimen and Web/CLI correspondence; independent review must
also confirm the four-node capture and ownership steps. All original general
inference/evaluator obligations retain their original quantifiers and OPEN
status. No production compiler change or provisional runtime fix is requested.

Mutual TODOs:

- `R136-OBS-1`, Luna/implementation: freeze the exact canonical source and CLI/Web
  registrations, then perform only the contract's focused checks. Falsifier:
  admission/conflict failure, non-23 result, missing first-result control,
  different lexical k/template, new request/authorization receive, inactive-owner
  replacement, copied store or altered handler. Stop on the first failure.
- `R136-REVIEW-1`, Luna/fresh reviewers: inspect frozen note plus source hashes;
  falsifier is any extra/missing suffix frame, wrong retained cell/environment,
  incorrect grant/owner attribution, or an assumption masquerading as observed
  source generation. Producer is ineligible to certify this result.
- Implementation owes proof intake the fixture hash and actual CLI/Web receipts;
  proof owes reviewers these immutable constructor/constraint premises. New
  semantics, a runtime repair or broader proof needs a new Luna decision.

## Frozen dependencies and resource receipt

SHA-256, actual inspected bytes:

```text
tools/inference-playground/tests/runtime_resume.rs 449c3ce11ef04fa60a49517c2fc8a7994d1547cb2dee058d6fdcbd0b095f8580
tools/inference-playground/src/runtime/machine.rs 4fb918732047f61184bc8f89b829bde68a8d1e6649a24d02640ec14500ae0acd
tools/inference-playground/src/runtime/continuation.rs 194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3
tools/inference-playground/src/runtime/receiving.rs 8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9
tools/inference-playground/src/runtime/program.rs 28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d
crates/yu-solver/src/candidate_source.rs cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7
crates/yu-solver/src/candidate_effect.rs 6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0
crates/yu-solver/src/shadow_apply.rs 838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543
crates/yu-hir/src/module/local_source.rs d9f516993c579ae8f4dd905abb8400ffc0769072a904a4b4c8d4ffbefcde6442
crates/yu-hir/src/module/source_annotation.rs b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f
notes/design/2026-09-29-scc-intrusion-redesign-charter.md 547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed
notes/design/2026-10-02-source-call-scheduling-choice.md 7b2d2556f4b6a93d7beb73a78f476bfea7d0f94de0c5f77649f6cd15ff69a530
notes/design/2026-10-02-typed-source-owner-realization.md 5cbd8110736ee4d43e0c65460fa9ecf700228bfdbe9fbaa7642ea0302d86f1aa
notes/design/2026-10-02-ordinary-computation-semantics-package.md ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917
notes/design/2026-10-11-yulang-inference-top-level-principles.md 7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81
notes/theory/2026-10-19-r98-continuation-current-context.md 923a01e7078d3861a819b4eeab67a61543f5db04ebdca5ae1be1a68294093975
notes/progress/2026-10-19-r98-continuation-current-context.md 51b1e67f32bd970809ae7a7fe341d1de1918f4bfc32365ec575ec8d065aff63c
notes/theory/2026-10-16-runtime-resume-template-correspondence.md f3a4c925a197e63e5b7faf1ce1e1caf5736d76f1b86ba162c6acc85bfff8e7dd
```

The six contract-pinned runtime/solver/test files and contract matched their
expected hashes. Web files are parallel implementation outputs, not evidence
consumed by this derivation. Baseline is supplied, not independently queried
through Git. Checks: read-only source/authority inspections and byte hashing;
zero tests/builds/compiler/CLI/Web runs, zero Git, zero external contact,
zero Astra, zero descendants. Searches included two nonexistent guessed solver
filenames; the actual owners were located in `candidate_effect.rs`, without
creating files. Exact elapsed/resource accounting is frozen in the handoff.
Only the two leased paths were created; no scratch outputs. Next step is Luna
intake and independent review/verification, not more leaf work.

Writer state: STOP / WRITES_STOPPED / NO_DESCENDANTS at handoff freeze.

# Sprint PAPER-CORE-CONTROL-20261026/r36 — ordinary let control

Status: READY; fresh worker receipt and Luna's committed RUNNING/cache acknowledgement required before checker work.
Branch: `research/simple-sub-intrusion`
Baseline: `ccc8ad9ce` (R35 bounded preservation proof, primary verification and CLEAN M1 review frozen)

## Fixed goal

Construct standalone `YulangClosure.PaperCoreControl`, importing the actual paper
execution syntax and R35 `PaperCoreStep`. Model only ordinary computation control
under nested `let` bodies. This is the first source/control bridge for the original
one-step preservation/display simulation parent at
`docs/yulang-operational-type-safety-ja.tex:1860–1875`.

Use states containing an actual `PaperExecutionSyntax.Computation` head and a
finite stack/list of actual let-body computations. Define a typed stack judgment
that composes the active head's intermediate type through each body to one fixed
final result type. The state judgment must retain arbitrary shared `D`, `Xi`, and
`Γ`; do not identify the head's intermediate type with the final result type.

Define the local control transition with this order:

1. For head `.letE first body`, descend into `first` and push the actual `body`.
   This is a stuttering transition under erasure.
2. For head `.ret value` with a nonempty let-body stack, instantiate the top body
   with R28's actual capture-avoiding single term substitution, pop that body,
   and retain the remaining stack.
3. Otherwise, apply R35's partial `PaperCoreStep.step` to the actual head and
   retain the stack when it returns `some`. A `none` result remains simply “no
   transition supplied by this partial operator.”

Prove state preservation for every supplied transition, retaining all shared
contexts and the original final result type. Push uses inversion of the paper let
typing rule; pop uses `PaperCoreStep.singleReplacement_typed` and the actual
`PaperComputationTyped.termSubstitute` theorem; delegated head steps use R35
`PaperCoreStep.preservation`.

Define erasure by plugging the active head into the finite nested let context
represented by the stack. Prove a stuttering simulation theorem of this exact
shape:

```text
controlStep s = some s' →
erase s = erase s' ∨ PaperLetContextStep (erase s) (erase s')
```

`PaperLetContextStep` is the local reflexion of a R35 principal `step` under
zero or more ordinary let active-child contexts. Push must erase to the same
computation. Pop must be the R35 let/return principal contraction under the
remaining stack. A delegated head step must be lifted through every stored let
frame. Do not claim this relation is the manuscript's full state machine or a
complete evaluation relation.

## Authority and scope

Primary authority: manuscript active-child clause `:331–334`, let reductions
`:305–316`, execution typing `:203–240`, frame typing/inversion `:1014–1026`,
and parent `:1860–1875`; actual grammar and typing are in
`PaperExecutionSyntax.lean`. R35 local partial step/preservation is the checked
bounded dependency, not a replacement for the manuscript parent.

`CoreControlBridge.lean` is for the separate `Original` grammar. Read it only to
confirm the boundary; do not reuse its syntax or imply its result transfers to the
paper grammar. This sprint covers only finite ordinary let frames and R35-supported
head steps. Do not include scope/expose/handle/mapop/wait, request, calls, handlers,
effects, recursive allocation, wrap, heap graph typing, administrative steps,
current-port inclusion, residual-graph transport, or full state simulation.

Falsifiers: head intermediate type confused with final result type; push changes
erasure; pop captures or shifts the wrong binder; stack order changes nested let
plugging; delegated R35 step is not lifted under every let; erasure theorem omits a
successful control transition; typed state preservation changes `D/Xi/Γ` or final
type; `none` is read as termination/Fail/Bad; unsupported axiom or proof hole.

The original one-step manuscript parent remains OPEN after this packet. The first
remaining bridge is current-port/residual-graph transport and full state/control
correspondence. Omitted evaluation frames, full source/native correspondence,
inference A/B and production gates remain OPEN. No compiler implementation slice
is authorized (`NO_SAFE_CODE_SLICE`); no tests, expected outputs, fixtures,
diagnostics, semantics or frozen inputs may change.

## Frozen inputs

- Manuscript `docs/yulang-operational-type-safety-ja.tex`, SHA-256
  `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
- `PaperExecutionSyntax.lean`, SHA-256
  `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`.
- `PaperExecutionTypingSubstitution.lean`, SHA-256
  `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41`.
- `PaperTermSubstitution.lean` (R28), SHA-256
  `a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f`.
- R35 `PaperCoreStep.lean`, SHA-256
  `503f81c162f7b9ceb0f7d27aa9796b8d7010345653267c675267ce14214c57e9`.
- R35 handoff, SHA-256
  `05cacac3b1536ff53eea589e71536cac2b5d34bbd1b71ef48e195a1aeb0eb128`.
- R35 review, SHA-256
  `5212dd2f014f5868d13aee909dfa794e530fedd872a8dc137081aa8d675364a5`.
- `CoreControlBridge.lean` boundary reference, SHA-256
  `30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a`.
- Pin `leanprover/lean4:v4.35.0`; toolchain, Lake config and manifest must match
  R35's frozen hashes before any checker command.

## Exact leases, commands and resources

One fresh registered `lean_prover` owns only:

- `notes/theory/lean/YulangClosure/PaperCoreControl.lean`
- `notes/theory/lean/.lake/R36Audit.lean`
- `notes/theory/lean/.lake/build` (single cache writer)
- `tasks/agent-loop/inbox/paper-core-control-r36-worker-checks.txt`
- `tasks/agent-loop/inbox/paper-core-control-r36.md`

Luna owns `tasks/agent-loop/inbox/paper-core-control-r36-primary-verification.txt`
and current state. One fresh non-author source-only `spec_auditor` reviews
`tasks/agent-loop/inbox/paper-core-control-r36-review.md` only after all proof,
checker and cache writers stop. No overlapping writers or descendants.

Before checker work, the worker sends actual identity/session, effective model and
effort (UNKNOWN if unavailable), exact hashes, cache/process status and waits for
Luna's committed RUNNING/cache lease acknowledgement. Use pinned native Lake/Lean
4.35.0 in `notes/theory/lean`. Build the project-scoped module
`+YulangClosure.PaperCoreControl`, then run the generated `.lake/R36Audit.lean`
with `lake env lean -j1 -M1024`. Audit every theorem declaration's complete type
and axioms with the Yulang skill's audit generator/validator. No default full build,
install/update, tests, Rust, network, dependency/config edits or unrelated checker
commands. First failed Lake/Lean/checker command stops the packet; retain full
output and do not repair/retry under this revision.

Fresh R36 envelope: 1800 active seconds, 14 native invocations (worker max 10,
primary max 4), 180 checker seconds (worker max 120, primary max 60). No reset or
extension. One heavy build at a time. Eight UNKNOWN reservations remain
quarantined. A sequential reviewer gets at most 180 active seconds and no
checker/cache/Git/write access. If aggregate time or capacity cannot be
established, stop. Luna owns review assignment, adjudication, integration, Git,
and any parent-gate update.

## Before/after evidence

Before: R35 preserves only its enumerated local redexes and does not represent
active let-child execution in a paper-syntax state. After success: a typed finite
let stack preserves one final result type; pushes stutter under erasure, and pops
or supported head steps map to the R35 principal step under let contexts. The
full manuscript state theorem and current-port/residual-graph bridge remain open.

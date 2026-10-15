# Definition writes in raw continuations: source reachability after correction

Status: constructive operational exclusion and source-owner characterization,
fresh independent proof review CLEAN. The original well-typed successor-source
reachability gate remains OPEN; no publication law or A/B answer selected.
Baseline: `1e62dfdc337bdfb4083f4df423fe62a18cda64f6`.
Authority: committed user-correction bundle `1e62dfdc3`, Oracle mono contract,
ordinary-computation package, runtime charter and top-level inference principles.
Lease: this new note; the primary separately authorized the already frozen
narrow G4 qualification recorded in §8. No production/question/record edits.

Integration review: compiler-referee `runtime_semantic_review` returned CLEAN
at producer SHA-256
`aec1b3d4f3632d6cd36ce397d812679d880ffd3c8a438e4d9c1fb827356d0303`.
Both sole publication sites, continuation constructors/composition, handler
forwarding, signal resolution and raw/host reentry were checked. The theorem
excludes capture of this same materialization invocation's pending write;
saved code may initiate a different invocation. It closes the Oracle
representation sub-obligation only, not successor-source reachability.

## 1. Frozen statement and distinctions

The original target is an authentic well-typed supported source module, its
original definitions and mixed ordered roots, one joint assignment
xi=(nu,K,D), original operation ports and selected-arm OpCompat, started in
fresh ModuleRun. Existing constructors include forward Names, ordinary local
bindings, functions/calls, retained Computations/Force, If, shallow Catch and
reusable raw continuations with shared current store. No new source restriction
is introduced. External execution contexts not in the supported module entry
are not assumed available.

Target event: an internal selected operation arm captures a raw continuation
containing an unfinished **top-level definition-cache write** W(d,j), where j
identifies this materialization invocation. Reusing that continuation completes
the same suspended W(d,j) repeatedly. Capturing a local binding, executing a
future InstanceRef, or starting another materialization invocation is distinct.
The question concerns this target, rather than every possible cache mutation.

Two claims must be kept separate:

1. **Oracle operational exclusion proved below:** neither inspected Oracle
   interpreter can include its pending instance-publication suffix in a raw
   request continuation. This holds even when evidence-vm evaluates a forward
   instance with ambient active catches. It does not depend on declaring all
   such forward evaluations ill typed.
2. **Successor source reachability remains unproved:** the playground explicitly
   represents a pending write as GlobalRead. No source/type construction proof
   yet shows whether a well-typed original module can expose its operation to
   a below-write handler and reach that guard. A concrete evaluator path or the
   old schematic example cannot supply this missing premise.

Thus the new result supplies an actual operational owner fact, not a universal
source impossibility theorem or a new conditional retirement of the parent.

## 2. Exact correction and actual source constructors

The question, answer-draft and approved-answer files equal committed HEAD.
The user rejects the earlier example: pending has value Int, while choice's
initialization effect is unresolved. The approved answer requests a valid typed
source/capture derivation before a publication choice. It selects neither a
new pending-read law nor unreachability.

Actual Oracle source ownership supports the distinction:

- `infer/src/lowering/name_ref.rs:96–119` allocates an exact-pure effect for
  an ordinary resolved Name, records its RefUse and target, and returns
  `Computation::value`. A Name does not directly copy its target initializer's
  effect into the reference occurrence.
- `infer/src/lowering/body/methods.rs:192–227` connects a binding annotation
  to that binding's computation, including its effect. At `:387–398`, the
  original body is retained, its value connected to the definition root, and
  `BindingFetch::runs_computation` determines ComputedDef root publication.
- `specialize/src/specialize2/emit.rs:169–200` solves and emits the original
  definition body under `RuntimeEvidenceTaskOwner::InstanceBody`. At `:372–418`,
  a resolved nonlocal Let reference emits its authentic `InstanceRef`; local
  definitions remain Local and operations remain EffectOp.
- Forward lookup is genuinely supported: `module_table/mod.rs:825` calls
  `value_at`; `query.rs:1256–1300` orders preceding candidates first and then
  later candidates, rather than rejecting every declaration after the site.

Consequently exact-pure Name plus initializer-owned effect **alone does not
prove** every forward execution under an ambient handler impossible. In
particular, the evidence interpreter retains ambient catches while evaluating
an instance (§4). A previous draft's first-capture argument inferred a universal
forward-source contradiction from the user's specific correction. That route
is withdrawn here. No such contradiction is needed for §4's operational proof.

The Oracle contract's source-order roots and prohibition on rerunning a computed
RHS at a later reference remain governing requirements. They do not, without
an additional actual source bridge, settle every before-publication forward
execution or its typing. There is no actual Oracle `GetDefinition` constructor;
that name in the older simulation note is a proposed interpretation, not source
evidence.

## 3. Mono-runtime: publication is outside request continuations

Actual owners are `mono-runtime/src/runtime/engine.rs:24–38,67–92`,
`runtime/eval.rs:20–23`, and `src/lib.rs:1219–1224`.

For invocation j of eval_instance(d):

```text
cached d -> return cloned Value
otherwise mark evaluating d
    r := eval_expr(original instance body, fresh environment)
    remove evaluating d
    v := strip_value_markers(expect_eval_value(r))
    instances[d] := v
    return v
```

`expect_eval_value` accepts only Value; Request becomes UnhandledEffect.
The root loop calls eval_instance synchronously for Instance/EvalInstance;
its outer host resolver therefore receives Value only on that route.
InstanceRef likewise synchronously calls eval_instance and then constructs a
Value result. Neither caller applies `continue_with` around a request returned
by eval_instance: that function's return type is Value/error, not EvalResult.

Mono continuations are explicit Rc callable values (`lib.rs:41,55–61`), not
captured Rust stacks. The write above occurs after a direct evaluator return;
no closure constructor in eval_instance reifies the remainder. Requests
handled internally can reuse their explicit continuations, but the pending
caller suffix containing the instance write is not one of them. An escaping
Request errors before the write. Value publication occurs once on this host
invocation's normal return; an error does not publish it.

This proves absence of the pending W(d,j) from every continuation returned or
stored by this invocation, regardless of whether the input passed source typing.
It does not assert that mono-runtime and evidence-vm resolve every effect alike.

## 4. Evidence-vm: ambient handlers do not capture publication

Actual owners are `evidence-vm/src/runtime.rs:14699–14726` (eval_instance),
`:14743–14825` (tail evaluation, resolution, active catches), `:15521–15522`
(Instance execution) and `:10551–10583` (root instance execution).

For invocation j:

```text
cached d -> return cloned SharedValue
otherwise mark evaluating d and authenticate instance index/id
    r := eval_tail_expr(original instance entry, fresh environment)
    remove evaluating d
    v := r?                         // SharedValue/error, never a request result
    instances[d] := v
    return v
```

`eval_tail_expr` calls `eval_tail_expr_result` and then `resolve_eval_result`.
The latter handles Value directly, and resolves every generic/direct/routed
signal before returning SharedValue. Its resolver uses `active_catch_frames`;
eval_instance does not reset that configuration. Thus a forward instance may
indeed run under ambient handlers. This observation refutes the attempted
argument “ambient handler implies the source path is necessarily impossible”.
It supplies no captured write, because the resolver is still called *inside*
the synchronous eval_instance invocation, before its write.

The reified representation is closed: `EvidenceContinuation` at :1186 is
Identity or Frame; all `EvidenceContinuationFrame` variants at :1192–1381
carry explicit next/scoped continuations, runtime expressions/environments,
values, handler/provider/marker state, or ordinary local/aggregate/reference
work. None carries an instance-publication callback/frame. In particular
BlockStmt/Let is an ordinary local completion, not instances[d] insertion.
The only `instances.insert` in this runtime is :14725. Its invocation j and
Rust return suffix are not among the frame payloads.

`continue_result` at :20465 appends the supplied explicit continuation to an
Effect or resumes it on Value. The Instance branch does **not** use it to append
a publication continuation: it returns `Value(self.eval_instance(instance)?)`.
The roots also call eval_instance synchronously. There is consequently no
constructor edge from pending W(d,j) to a captured frame. Resume/Then/handler
composition can compose existing explicit objects, not the suspended Rust
caller. Host/active-catch resolution can run those objects repeatedly while j
is waiting, but they still lack that caller's publication suffix.

Formally maintain `NoWrite_j(k)`: k contains no pending publication action of
this invocation j. Identity holds; each actual frame constructor preserves it,
because it only retains the listed explicit children/data and cannot retain
j's host stack. A saved expression containing InstanceRef may start a *new*
invocation j', but does not acquire W(d,j). Composition, shallow handler
selection/forwarding, continuation storage and reuse preserve NoWrite_j by
this same constructor induction. Once resolution returns a Value, the one
synchronous write occurs and j is finished. Once it errors/unwinds, that write
is not an executable saved suffix. This establishes exclusion over every finite
ordinary/request/resume prefix of the inspected runtime, including current-store
reuse, rather than merely a test or an absence-of-field assertion.

No conclusion about first/last publication among **different** invocations, host
snapshot behavior, or the broader evidence optimization proof is needed or made.

## 5. Roots, locals, delayed bodies and recursive demands

The successor Root completion is installed below the initializer; handlers
installed by the initializer execute above it. Its actual inside-handler raw
capture bound excludes the below-handler Root. Fresh ModuleRun has no source
handler outside the scheduler. Prior root completion leaves no handler installed
across subsequent roots. ExpressionReturn is cache-free. These are the reviewed
G4 relative-control facts, not a new initialization-effect adequacy theorem.

Inert functions/thunks are cached as values before a later call/Force consumes
their latent code. Such later code cannot capture the already finished write.
A computed initializer may run handlers/Force/calls internally; the Oracle
proof still uses the synchronous publication boundary, not an inertness
assumption about its whole body. Local bindings can be captured and completed
repeatedly: they are ordinary code inside the selected boundary, with no
instance-cache insertion. Stored continuations and current-store mutation can
change later ordinary results without adding the missing host suffix.

Recursive demand consults `evaluating_instances` and errors. This does not
choose a new source pending-read policy. It is an actual interpreter behavior,
separate from a suspended raw template which owns an instance write. A returned
continuation value may outlive its initializer; the outer invocation publishes
that value once, while its explicit continuation still lacks W(d,j).

## 6. Valid local contrast, and why it is not the requested witness

Established source syntax permits the following contrast:

```yu
act choice:
    our pick: () -> int
my relay(thunk: [choice] int) = catch thunk {
    choice::pick(), k -> { my first = k 0; k 1 },
    v -> v
}
my result = relay ({ my local = choice::pick(); local })
```

Its supplied block has Comp({choice},Int); local has Int. The original receiver
annotation permits choice; the operation has Unit payload/Int response. Both
raw calls supply Int and the local suffix returns Int; selected/value arms agree.
This is a direct local type/effect derivation, not a solver/probe result.
The suffix can retain Local and the receiving view. Relay's closure lookup has
already returned; the result root completion lies below the selected handler.
Thus this is a reusable local-completion example, not W(d,j) capture.

Replacing the block by a top-level Name pending and defining
`my pending = choice::pick()` does not establish an equivalent typed source:
Name is exact-pure and pending's initialization effect remains its own source
obligation. The user's correction specifically rejects the old unresolved
example. Neither that correction nor this note proves that *all* forward
instances with ambient handlers are impossible. The actual operational proof
above explains why ambient Oracle handling still does not reify publication.

## 7. Result and exact remaining bridge

Submitted theorem: pending instance-publication actions are absent from raw
continuations constructed by the two inspected Oracle runtimes. This is an
actual constructor/consumer induction, applying also to successfully typed input
because it proves the stronger interpreter representation property. It rules
out repeated completion of the same captured Oracle W(d,j). It does **not**
automatically prove the original successor-source target unreachable.

The successor's empty-global Name explicitly installs a GlobalRead completion
and executes the body under the caller. Capture currently detects Root or
GlobalRead in a candidate suffix and reports ContinuationMaterialization. That
new explicit write suffix has no corresponding Oracle continuation constructor.
Therefore older ordinary-runtime-simulation §5 lines538–549 cannot cite an
“existing GetDefinition law” as evidence for this source-to-control step.
A proof of source equivalence must establish which authentic typed forward
initialization requests can reach this step and how their synchronous Oracle
publication boundary is represented. Existing runtime control alone supplies
neither a valid typed witness nor source unreachability.

The exact remaining owner is the source-reference/BindingFetch/InstanceBody to
successor Name/GlobalRead materialization bridge, including its admitted
initialization effects and delimiter. This packet neither grants code repair
authority nor selects a new delimiter/publication law. Primary's next decisive
action is a bounded source-to-control packet at that owner: either derive a
well-typed admitted forward source with the entire initializer/root effect
accounted for and compare both actual traces, or prove from its authentic
source formation that no below-write handling path is admitted. An experiment
must establish type/effect admission before invoking the permissive HIR runtime.
No more cache-algebra or publication question is justified by the old example.

Original reachability, whole typed-runtime adequacy, general negative/profile/B
and broader runtime parents remain OPEN. Independent review is required for
this local operational theorem; the producer does not retire the parent.

## 8. Frozen dependencies, checks and commit packet

Bundle files equal committed HEAD (read-only diff, no differences):

```text
question.md f7aa97c5bf0c3f270ff0ce665e054822ea956f7aa01caa19a4946cab9d92b7d1
answer-draft.md 49e7b572c60edefad5ae5f1710526738e87d491cefa77cf6d7634f885fd46837
approved-answer.md b7fe31b1c5cb82cef6761aeb5f19b4e5ac0fa9198bcde94314f407e742e11cd8
Oracle mono contract 9f88e1e21387ebe0ef42e2d857fcd37ba52d51acd1962cdb3cb6b80666819388
ordinary-computation-semantics-package.md ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917
scc-intrusion-redesign-charter.md 547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed
yulang-inference-top-level-principles.md 7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81
```

Inspected Oracle capture files (under crates/):

```text
mono-runtime/src/runtime/engine.rs 1d5c55d94b2626309a6d0307c8d20c7b1e4a544ea0e4024df7ede55326fbf6f5
mono-runtime/src/runtime/eval.rs e78f2ba1b1fc1fec696a658bb1f6e56770a00d71b8863e8849dcfcafc724b090
mono-runtime/src/lib.rs 3a821fc693414e6d9feef6d16bf44df4caa13d3b17af137439155b74765a683f
evidence-vm/src/runtime.rs eb3f2d42752ff112b621d35471ebab79e767523f4597c7d6bd57329d02231ee7
infer/src/module_table/query.rs 5d9e44a5b214ab3d94107b7d83b8339db1abc11f354aa01b97ed416b8c965802
infer/src/module_table/mod.rs ff002a9eede92aef54bb28f6aedf8ab53d79b959634d70d2ae2f6b36c7da3ef7
infer/src/lowering/name_ref.rs 699c7dc84a2b4889355ffe9cd23b3e871c295957dbcb3fbad96ee9ee36470ede
infer/src/lowering/body/methods.rs 0f7d0ac524c4934a4491681e6f9901cdc81f8aff20da7f394888c691bb8c067b
specialize/src/specialize2/emit.rs 7318b132cef4217ae089d084577fb28f3abed34a5728474ee8569e4079d71e7c
```

Current inspected G4 runtime under tools/inference-playground/src/runtime:

```text
program.rs b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748
machine.rs e30bb19c54b1a4ee07f3b1d2f0a5e88e57f2226fd055071a6d1ca5f1bdfd5e3a
primitive.rs 97485b9439357497aaf3f19555b1d87eef4aabc955b3a2815f23cf49a65c0153
receiving.rs 5443c8ca55e58a37b6d003cf5b2985214d37776094f02637adfbe30200cc36bd
continuation.rs 194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3
mod.rs 64d208743793a03501a76f56bc2b511c50ed40cff3f789757a00b7d608fc846b
```

Machine's prior packet hash was e5713fac40a2823168564d9f35ce824a1eb09f2fe3590a663ba626676422892b.
Primary reports the independently precleared drift is solely cfg(test) helper
opt-in selection at :1657 onward; current code confirms that helper. Production
control proof uses the inspected current constructors, not equality with the
pre-G4 baseline. The earlier 1a64937f1 comparison predates G4 and is not a
production-equality check. No unexplained production drift is assumed away.

The separately leased narrow G4 §§4/10.4 qualification is frozen at
`f36e667265d7aaead29314bf27ddf1aad4a5488ab005638a850d70ad3734e352`.
It preserves the original structural relative-control theorem and leaves whole
typed initialization adequacy OPEN; it proves neither source reachability nor
unreachability. No other prior note/question/shared record changed here.

Checks: bounded authority/actual-source reads, bundle equality, source hashes,
artifact whitespace and final hashes. No tests/builds/runtime probes, Git
mutation/network/delegation or production edits. One bounded static leaf;
requested Sol/high, observed model/effort unknown. Zero heavy processes or
measurements. Independent review pending.

Commit packet: this new note plus the separately handed-off narrow G4 delta;
baseline `1e62dfdc337bdfb4083f4df423fe62a18cda64f6`, exact dependencies above.
Suggested checkpoint: `research: locate definition publication outside Oracle raw continuations`.
Shared-record delta for primary: retain original reachability gate OPEN; record
the operational exclusion and exact missing Name/GlobalRead source bridge.
Do not select A/B, declare all forward Names invalid, or retire whole source
adequacy from this representation theorem.

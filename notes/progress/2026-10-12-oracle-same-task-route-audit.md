# Oracle direct/provider: selection of the same specialization task

Date: 2026-10-12
Status: frozen bounded source characterization; unreviewed; M and original H OPEN
Claim class: static producer/consumer derivation and an exact missing materialization premise
Y3 baseline: `1e33acf04be76ac420cab2014a00c4e1f1fcfa4d`
Oracle baseline supplied by primary: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle read root: `/tmp/yulang2-oracle-read`
Exclusive lease: this note only; leaf, no delegation or Git mutations

## Objective and fixed premises

Determine whether the particular source route's actual/consumer/ref maps and
emitted boundary plans follow from the retained source and artifacts without a
new dump or run, and whether that evidence joins provider origin b and the
annotation's fresh inference image alpha_u through Force to complete output.
The input is the [specialization audit](2026-10-12-oracle-direct-provider-specialization-audit.md),
independently reviewed according to the primary packet and `tasks/current.md`,
plus the existing [source-route derivation](../theory/2026-10-12-oracle-direct-provider-hygiene-counterexample-proof.md),
[R](../theory/2026-10-12-oracle-provider-row-replay-proof.md),
[P](../theory/2026-10-12-oracle-direct-return-projection-proof.md), and the
[retained probe](2026-10-11-oracle-callback-reuse-projection-probe.md).
Their inference replay and cancellation arguments are not repeated.

Governing meaning is [hygiene integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–2, [contextual attachment](../design/2026-10-10-contextual-attachment-admission-design.md)
§§1,3, and [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. Original [H](../theory/2026-10-11-oracle-global-effect-hygiene-proof.md)
§1 retains all its source, occurrence, scope, binder, use and Call/output
quantifiers. In particular, lack of a top-level runtime invocation does not
exclude the latent nested Call from H. Unequal origins do not classify attachment.

The finite source remains:

```yulang
pub act tick:
    pub ping: () -> ()
my direct(cb: (() -> [tick] ())) = cb
my provider() = tick::ping()
my observed_direct() = (direct provider) ()
```

Hypotheses for the source facts below are the pinned source bytes, successful
resolution/lowering of this ordinary fragment, and normal completed native
construction without resource failure. The historical CLI result is consumed
only as the probe recorded it. No successful specialization, selected latent
invocation signature, reached force, attachment interpretation or complete
output is assumed.

## 1. What the retained command actually produced

Oracle locators below are relative to the read root.

The retained command is `dump /dev/stdin --poly`, with
`--no-prelude --no-cache`. `crates/yulang/src/support.rs:199–217` sets only
`selection.poly` for `--poly`; `main.rs:3148–3153` dispatches the no-prelude
route. `support.rs:247–269` calls the poly builder and printer for that selection,
and calls mono/control builders only for their separate selected flags.
`main.rs:2425–2431` makes no-cache use `build_poly_from_collected_sources`.
`main.rs:2988–3004` prints the compact poly arena and returns text, file count
and lowering errors. The builder's output construction
(`source/mod.rs:5502–5533`) retains the poly arena and provenance sidecars in
memory; the printed result does not return a SolvedTask or mono Program.

Therefore the recorded successful poly command did not emit the requested
same-task boundary plans. The source supports the stronger negative statement
about that command's pipeline, rather than merely a failure to find a dump.
This statement does not exclude internal inference or role-check tasks and
does not claim no other unrecorded process could have specialized the source.

## 2. Native emission of the literal fragment has no selected instance

The production delegate is `specialize/src/lib.rs:77–82`. In Specializer2,
`specialize2/emit.rs:5–18` initializes the instance list and pending worklist
empty. `:47–87` seeds work solely from `arena.runtime_roots`: an Expr root
calls `solve_root_expr`; a ComputedDef root calls the computed-signature path.
`:88–100` then drains the pending worklist and assembles the Program.

For this fragment, each ordinary value definition is a lambda. Its wrapper
returns `Computation::value` (`infer/src/lowering/expr/lambda.rs:954–975`).
`infer/src/typing.rs:42–44,84–94` assigns Evaluation::Value, FetchValue and
`runs_computation() == false`. The binding publication owner
(`lowering/body/methods.rs:387–398`) consequently does not publish a ComputedDef
runtime root. The source contains no expression statement; the expression-root
publisher (`lowering/body/mod.rs:2137–2141`) therefore contributes none. The
bodyless ping operation reaches `lower_act_body_contents` and then
`lower_act_operation_binding` (`lowering/body/act.rs:505–521,63–138`), which
registers its operation/type without publishing a runtime root. The suppression
at `act.rs:449–466` applies only to copied internal Act source.

Thus, conditional on successfully passing any preceding readiness check, a
native specialization of this literal arena has empty roots, instances and
pending-instance work. No observed/direct/provider instance task is selected
by that invocation of the emitter. This is a finite source/control-flow
derivation, not an observed specialization run or an empty complete-output
result for the latent outer Call. It disproves treating a latent source App
as an already emitted App merely because it occurs in the poly arena.

## 3. The first missing contract for a symbolic invocation

A static derivation of a latent invocation remains possible in principle.
The code gives its construction recipe, but the existing emission pipeline
has selected no such task for this literal input:

1. `emit.rs:112–170` requires an incoming signature for `ensure_def_instance`;
   it records separate inference/runtime/marker signatures and schedules that
   definition. `:179–195` passes the inference signature into `solve_def_body`.
2. `task_solver.rs:29–51` solves the actual body against that supplied signature.
   Ordinary variable uses instantiate the selected declaration's scheme and
   record their task-local use (`:424–461`). Actual Apply builds consumers from
   the callee's task type (`:479–569`); ping's Apply has its own operation-scheme
   constructor (`:572–588`).
3. `task_solver/finish.rs:125–170` solves slots, resolves actual/consumer maps,
   and resolves each ref signature from its consumer when one exists, otherwise
   from its instantiated use type. `emit.rs:409–418` feeds that resolved ref
   signature into the referenced definition's instance selection. Consequently
   the original inferred scheme is not interchangeable with the selected
   provider or direct instance signature.
4. Once those exact maps and source argument contracts are established,
   `emit.rs:248–266,723–749,806–829,1013–1055` determines the App argument,
   lambda return and generic boundaries. A concrete solve may also fail before
   emission. Substituting a guessed pure signature suppresses precisely the
   premise under examination.

The **first missing producer/consumer contract** is therefore:

> For the same latent outer Call and its actual source/provider/formal spine,
> derive a source-qualified incoming specialization signature and the native
> materialization/solve image (or authentic rejection). Show that its resolved
> actual/consumer/ref signatures select those same referenced instances and
> boundary plans. Do not supply those maps independently of the source call.

Neither a historical numeric task record nor a runtime root is a necessary
mathematical premise for such a lemma. A symbolic construction with justified
inputs can supply it. This audit has not established that construction or proved
it impossible. The retained P/R images and source identity lemmas are legitimate
inputs to it; they do not themselves establish the task image. This stops at the
first missing contract rather than executing another supplied-transition model.

## 4. Why a solved shape would still need the b/alpha_u join

One narrow producer fact prevents an overstatement about discarded IDs:
`specialize/src/types/materialize.rs:396–413` copies a supplied poly stack
entry's numeric `entry.id.0`, pops and family profiles into the mono weight.
Thus specialization does not universally erase every SubtractId at
materialization. This fact is conditional on the actual input weight; it does
not identify that weight with R's alpha_u or select its originating use map.

Conversely, adapter hygiene consumes actual/target types and the argument
contract (`specialize/src/hygiene.rs:15–66`), while its runtime marker
instantiation calls `fresh_guard_id` for each marker
(`mono-runtime/src/runtime/flow.rs:391–418`). Numeric equality between such a
fresh GuardId and a supplied stack ID establishes no identity or attachment.
The prior audit's missing interpretation remains necessary even if the typed
task image is obtained. A nonnumeric construction-history interpretation could
establish it; absence of a field does not prove that interpretation impossible.

The reached runtime consumer is also conditional: forcing an actual
`Thunk::Effect` calls `emit_effect_request`
(`mono-runtime/src/runtime/thunk.rs:117–126`). No task image or selected Force
for this latent invocation was derived here, and that rule alone does not show
that b's contribution reaches it or belongs to the complete output. The audit
therefore supplies neither M nor an H counterexample. Original M/H, complete
Call, soundness, principality and cutover remain OPEN.

One recommended next action: have the constructive lane derive the latent
Call's source-to-materialization lemma in §3 with its original source context
and inputs; consume its selected boundary image at M's attachment/force owner.
Avoid another inference replay or broad record-schema census.

## Checks and frozen dependencies

Checks: bounded `rg`, `sed`/numbered source reads, SHA-256 fingerprints, final
Markdown link/whitespace/hash inspection. The supplied Oracle revision was not
rechecked with Git; emitter/task/finish/flow hashes match the earlier frozen
audit. No Oracle invocation, build/test, executable probe, mutation, seed/range,
compiler edit, shared-record write or child dispatch. Maximum concurrent read
batch: two lightweight processes; zero heavyweight processes or samples.
An initial startup inadvertently used read-only `git status --short` and
`git rev-parse HEAD`; the latter matched the assigned Y3 baseline and the former
was empty. The primary was informed. No Git mutation occurred; no further Git
command was used. CPU/RSS and exact reasoning wall time are unknown; this
packet is bounded by 30 minutes. No independent oracle or review was performed.

Direct dependency fingerprints:

```text
specialization audit  86a8e35c432018d2b38fa2e7a34b1496ea7c65db1ab0d431e3ec8dfe00af2495
retained probe        975c2f7460ca5a9663938485cc2ce8669160b864c19928151589c9904016ccd2
source-route note     3e548eda14ec0101febdd949733dc2c1fe6ab3770d34892c9bd60668bbeef268
R                     7cf7803bcc79ddd5ce255aa337b2bebf46e27353e07088f3ea928c6d24a77ba5
P                     0799b609879e52de59fdd58b8b71bc8035eca6b1d953f3c4c4ae0743e465afa7
original H            6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1
hygiene integration   503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a
contextual attachment 717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc
top-level principles  edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389
```

Oracle owners, relative to `crates/`:

```text
yulang/src/main.rs                         a6f7b226145ad26328895d403de8a528cec724876e8d9b394a31c0fcc42f2c7a
yulang/src/support.rs                      9ea2413c9c6c4b4b30ee9c794b94f83eacad5c0b6c225e83e011959575a7879f
yulang/src/source/mod.rs                   0ac0d078323428abf42292e765d2987fb072cc89afb140cb3a86bb98129af3f9
infer/src/lowering/expr/lambda.rs           2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9
infer/src/lowering/body/methods.rs          0f7d0ac524c4934a4491681e6f9901cdc81f8aff20da7f394888c691bb8c067b
infer/src/lowering/body/mod.rs              f5e82c2109a11938cab6a5b48d8a155f6ac3029c4d26cb7f4570790e8d5f9cb1
infer/src/lowering/body/act.rs              dfb8bbe305fe369e2fc4f0f413be2009d44343aaa43c3dc1f73dcacf9479fe4d
infer/src/typing.rs                        b6ade453931d288c03332770fa76022abf90f1276466faeefa3d647be63bcef6
specialize/src/lib.rs                      6b573e1c4db7e9dea838e7afb964d300c57287c5bc8923d88401422672704449
specialize/src/specialize2/emit.rs          7318b132cef4217ae089d084577fb28f3abed34a5728474ee8569e4079d71e7c
specialize/src/specialize2/task_solver.rs   cc534583e8fd154b51e8c857ef7b17df19fe68e9410fd9acb74c1d13cb1d2f66
specialize/src/specialize2/task_solver/finish.rs 8ee9baf8bdac1ada4efb6f33331efab15e9f2a61674a7c492180ceac7acf0d28
specialize/src/types/materialize.rs         8c02aa7ca9d8e0394e4f4f915086537548d2dae748f19d22d12675b502588183
specialize/src/hygiene.rs                   266c05f4c937fc9f9d95cb6b1c435e9ff74181ffc5e8d7719faeefc7a8ff33e4
mono-runtime/src/runtime/flow.rs            83331d4d18066e8361a1ef3f89de2dffeddb7e0e2acb8e910bd5edd44dfffd40
mono-runtime/src/runtime/thunk.rs           27b6d57ee711dbb7b8bb8da9ec5c05c46ad8ec7f01a29f381664ca3aa4509739
```

No dependency was edited. Unverified scope: all symbolic task outcomes and
their attachment/complete-output adequacy; surrounding sources, recursion,
resource failures and other backend routes. This is one static attempt and
contains no claim of independent certification. Writes stopped at submission.

## Commit packet

Exact leased changed path:
`notes/progress/2026-10-12-oracle-same-task-route-audit.md`.
Baseline: `1e33acf04be76ac420cab2014a00c4e1f1fcfa4d`.
Dependency hash changes: none made by this lane; revalidated fingerprints above.
Review status: frozen unreviewed bounded characterization; M/H OPEN.
Checks already run: static source/hash inspection and final local links,
whitespace and dependency consistency check; no execution/build/test.
Proposed checkpoint message:
`research: localize Oracle same-task route materialization premise`.
Shared-record deltas intentionally left to primary/curator: distinguish the
retained poly observation from absent native selected tasks; record the precise
latent Call-to-task materialization premise and conditional stack-ID retention;
retain H's latent source domain and M's attachment/force/output join as OPEN.
No shared task/index/authority or question-board file changed.

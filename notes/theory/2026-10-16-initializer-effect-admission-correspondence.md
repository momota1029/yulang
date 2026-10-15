# Initializer effect admission: actual constructor obstruction

Status: bounded actual-source characterization and minimized failed-admission
bridge, fresh independent review CLEAN. The original well-typed forward-source
reachability and successor-runtime adequacy parent remain OPEN.
Baseline: `c6c7a20218b084a43d8c0d20505546ecebb517f2`; runtime integration
`35e87f844`. Oracle inputs are the frozen sibling capture.
Authority: user correction bundle `1e62dfdc3`; original Oracle mono VM roots
contract; ordinary-computation package, runtime charter, top-level inference
principles. Exclusive output lease: this note only.

Integration review: compiler-referee `runtime_semantic_review` returned CLEAN
at producer SHA-256
`7af1e7fe88825aff89f36cefc4c51978a73a80394bd76ca995d9b728d9ba03b8`.
The result defeats the proposed value-scheme certificate route. It does not
prove a compiler defect or require every unhandled/effectful root to be rejected
by type checking. Existing authority does not impose blanket root purity.
The next owner is authentic source/root/InstanceBody-to-Name/GlobalRead control
correspondence; no new admission constraint or cache law is authorized.

## 1. Frozen target and outcome

Fix an authentic source initializer d, original body b, original published value
scheme S_d, and the original complete body effect E_b. Keep original definitions,
operation declarations/ports, one joint assignment and source root order; do
not choose body/value witnesses independently. Forward Names are supported.
The sought local premise is:

> The actual admission of d's original InstanceBody/root-effect obligation
> excludes a Request escaping b before publication which can be selected only
> by an already active caller-side handler around an early reference to d.

This must follow independently of the reference Name's pure effect, and from
actual constraints/consumers rather than assumed compiler soundness. It would
supply a missing source-to-successor Name/GlobalRead premise; it is not merely
Oracle's already proved absence of publication in explicit raw continuations.

**Result:** the traced admission chain does not establish that premise. Binding
commit carries only the body value into the stored scheme. Both specialization
body checks compare a computation shape with that value scheme using a subtype
rule that explicitly projects the computation's effect away. ComputedDef root
publication neither adds nor consumes a residual-root-effect obligation.
The exact ground derivation is in §4. This defeats the proposed inference from
stored-scheme body checking; it is not a newly certified valid forward source,
a counterexample to the user's correction, or a whole-source impossibility proof.

The first missing producer/consumer is the original computed binding's complete
initialization-effect admission output at binding commit/root publication,
and its consumption before treating a successful InstanceBody value comparison
as proof of source initialization validity. No unconditional such consumer is
present on the audited path. No new root-purity law, source restriction or
runtime delimiter is adopted here.

## 2. Input theorem consumed, without repeating it

The independently reviewed Oracle exclusion packet is
`2026-10-16-resumed-definition-source-reachability.md`, producer SHA-256
`aec1b3d4f3632d6cd36ce397d812679d880ffd3c8a438e4d9c1fb827356d0303`.
It establishes that actual Oracle eval_instance publication is synchronous
outside explicit request continuations. It also establishes that forward Name
lookup is allowed and that evidence-vm preserves ambient active catches during
forward instance evaluation. These facts do not by themselves settle typing
or the successor's explicitly represented GlobalRead suffix.

The committed user correction rejects the old unresolved choice initializer
example. It supplies no universal prohibition of every forward definition,
no A/B publication choice and no new pending-read protocol. Exact-pure Name
formation cannot transfer its initializer effect, and also cannot certify that
the initializer's separate original obligation was discharged. This packet
therefore inspects that separate obligation at its actual admission owners.

## 3. BindingFetch, original body and ComputedDef ownership

Oracle paths below are relative to the sibling capture's `crates/` directory.

1. `infer/src/typing.rs:16–22,56–105` keeps `Computation.value`, `.effect` and
   `.evaluation` distinct. Evaluation controls expansiveness; BindingFetch maps
   Value/Computation to FetchValue/FetchComputation and selects a generalization
   level. Pure expansive expressions exist. Therefore FetchComputation proves
   neither E_b nonempty nor E_b empty.
2. `infer/src/lowering/body/mod.rs:2258–2365` lowers the original ordinary
   binding, optionally connects its annotation, then calls finish_binding.
   `body/methods.rs:192–227` returns immediately when an annotation is absent.
   An annotation may generate its original explicit effect constraints; it is
   not an unconditional initialization-effect validity certificate.
3. More precisely, `infer/src/annotation/constraints.rs:223–247` connects
   target.effect only for AnnType::Effectful. A plain value annotation such as
   Int calls connect_value_detailed; it does not supply an implicit empty-effect
   constraint for the initializer. No inference from annotation absence is used.
4. `body/methods.rs:375–398` stores the original body expression, calls
   `constrain_def_body(root, computation.value)`, records BindingFetch, and, if
   runs_computation and publication is enabled, appends ComputedDef(d).
   `constrain_def_body` at :442–453 generates body-value <: definition-root.
   It does not compare computation.effect with any source root allowance.
5. `infer/src/analysis/session/lifecycle.rs:1062–1065` records BindingFetch
   and sends the SCC generalization event. That event is not a residual-effect
   admission consumer.
6. `specialize/src/specialize2/emit.rs:73–74` converts ComputedDef(d) to
   EvalInstance(ensure_computed_def_instance(d)). At :102–109 the latter
   obtains the authentic Let body, solves its computed signature and passes
   that signature to ensure_def_instance. It inserts no root effect expectation.

This is an actual loss-of-premise trace, rather than an argument from a missing
field: a root-effect obligation is not generated by these value constraints,
then no later step in the proposed chain adds it. Original annotation effect
constraints and nested function/operation effects are real and remain in their
own scope. Their existence does not add a universal residual-root consumer.

## 4. Exact TaskSolver/TypeGraph derivation

### The body is re-solved, but against a value scheme

`specialize/src/specialize2/task_solver.rs:78–119` authenticates S_d, instantiates
it with provenance, infers the original body b, consumes b at S_d, and queues
both actual(b) <: S_d and S_d <: actual(b). It calls finish, retrieves the solved
actual body type and returns `forced_computation_value_type(actual(b))`.
The returned type projects one outer Thunk to its value at
`runtime_shape.rs:544–549`.

Pending instance emission (`emit.rs:169–200`) then calls solve_def_body with
that value signature. `task_solver.rs:29–52` infers the same original body,
consumes it at the signature, queues actual <: signature and finishes. The
retained RuntimeEvidenceTaskOwner::InstanceBody is authentic provenance, not
an added effect expectation. `consume_expr` at :212–235 queues the same full
shape comparison and passes the consumer value to block-tail checking; it does
not invoke consume_expr_computation with an empty initialization allowance.

### A real effect survives inference, but does not constrain value admission

For the source expression kernel `signal::ping()` with an authentic declaration
`our ping: () -> int`, the operation producer adds its declared family to the
original return-effect row (`infer/.../body/signature_helpers.rs:217–256`).
The specialization effect-operation application (`task_solver.rs:573–588`)
checks the Unit payload, joins argument/operation return effects, and constructs
runtime_shape(E_signal,Int). For a nonpure ground E_signal this is
Thunk(E_signal,Int), by `specialize/src/types/mod.rs:419–428`.
This is a typed expression kernel, not a claim that a module leaving that
initializer effect unresolved is valid source.

Let the original stored *value* scheme S_d be Int. The proposed independent
admission certificate would have to exclude the unresolved E_signal. Actual
queued constraints reduce as follows:

```text
actual(b) = Thunk(E_signal,Int)          S_d = Int
consume: Thunk(E_signal,Int) <: Int
forward: Thunk(E_signal,Int) <: Int
reverse: Int <: Thunk(E_signal,Int)

consume/forward -> Int <: Int           [lower Thunk projection]
reverse         -> Int <: Int
                   Pure <: E_signal    [upper Thunk introduction]
```

These are exact TypeGraph branches at `type_graph.rs:613–663`:
Thunk-to-Thunk compares both components; ordinary lower-to-Thunk compares the
value plus Pure <: upper.effect; Thunk-to-ordinary upper compares only the lower
value, discarding its effect from this comparison. Empty-stack concrete
Int <: Int is reflexive; Pure is EffectRow([]) (`mono/src/lib.rs:89–95`),
the empty/bottom effect rather than an upper bound on
E_signal. Thus no E_signal <: Pure, no proof that the initializer handled its
own request, and no constraint referring to a caller's active Catch follows.
The graph worklist executes these branches (`:479–491`); deferred accumulation
does not insert an additional effect check at activation.

`task_solver/finish.rs:144–180,250–284` solves roles/slots and resolves required
actual bodies. It preserves the non-reference body's actual shape before the
explicit forced-value projection. It checks concrete output/role boundaries;
it does not require every required expression's effect to be empty. The second
solve_def_body again uses the lower-Thunk projection against Int. Re-solving
the authentic body twice cannot turn either missing effect upper bound into a
root-effect discharge.

This is the minimized obstruction to the **proposed actual admission route**.
It is stronger than “BindingFetch has no effect field” or “the solver has no
runtime stack”: the actual source operation effect can be nonempty and the
actual owning comparisons still generate only the displayed value obligations.
It does not establish full module admission under all original semantic
requirements, which is exactly the distinction required by the user correction.

## 5. Why other mechanisms do not repair this premise

An initializer with its own source Catch may remove/handle its own operation
through the ordinary Catch constraints. Such programs are useful controls,
but do not prove a universal initialization admission law. Functions and
retained computations keep their latent effects; publishing an inert value
then executing it later is distinct from an unfinished initialization. Local
binding effects remain part of their containing computation. None permits
using a published Name's pure effect as a replacement for E_b.

Forward lookup does not reject all later declarations; source order still owns
the computed root. A reference can cause an instance to be demanded early in
actual Oracle execution, but that operational fact proves neither rejection
nor admission under the corrected source initialization contract. Shallow
Catch, raw Resume and shared current store affect operational control after
source admission; they cannot add the missing root-effect source constraint.
No counterexample using malformed HIR or candidate solver success is accepted.

The successor CLI is also not the missing consumer. At
`tools/inference-playground/src/lib.rs:149–152`, execute obtains
`(hir, _candidate)` and constructs RuntimeProgram with RuntimeEvidence::default().
`runtime/program.rs:55–57` supplies only NameConsumption evidence. There is no
initialization-effect admission certificate carried through that interface.
A successful CLI execution, conflict-free candidate listing or permissive
from_hir construction therefore cannot certify this local source lemma.

A future justified delimiter, if separately authorized, would have to cover
only initialization and restore the caller before NameConsumption or latent
execution; no receiver-owner reset or store copy follows from this packet.
The current result grants no implementation or semantic adoption authority.

## 6. Smallest next evidence and stop condition

The original conclusion cannot be proved from the inspected admission owners.
No new valid forward-source witness has been established. Stop at the exact
missing original initialization-effect admission output/consumer, rather than
assuming whole-compiler soundness or creating another transport lemma.

Primary-only proposed admission sentry (not run; **not** called valid source):

```yu
act signal:
    our ping: () -> int
my pending = signal::ping()
my main = pending
```

Compare it with the internally handled control:

```yu
act signal:
    our ping: () -> int
my pending = catch signal::ping() { signal::ping(), _ -> 1, v -> v }
my main = pending
```

The primary can inspect original b's value/effect, its stored scheme, ComputedDef
and both specialization tasks, recording the exact source admission decision.
For the first case, acceptance of the displayed value constraints is not proof
of module validity; the consumed user correction requires accounting for the
unresolved initialization operation. Locate any additional genuine root-effect
admission consumer, or record its absence as the concrete compiler/source
correspondence gap. Only after that decision is authenticated should a forward
variant place `my main = catch pending { signal::ping(), k -> k 1, v -> v }`
before pending and inspect selected request/capture paths. This is a diagnostic
negative-admission probe, not a resurrection of the rejected valid example.

A decisive falsifier of the desired source theorem remains a genuinely admitted
well-typed forward initializer with its entire original root effect justified,
whose before-publication request is selected only by the caller. Conversely,
a real owning admission constraint or source control theorem excluding that
selection would discharge the remaining premise. Neither is replaced here by
the local ground constraint characterization.

Proof-economy audit: this is an A/B source-to-execution obligation. The original
body's effect is known at the binding constructor; the proposed downstream
value-scheme reconstruction discarded its independent role. Retention is useful
only after the actual source admission judgment is identified, not as a new
postulated certificate or a policy making every initializer pure. No additional
publication algebra, blanket forward restriction or A/B question is justified.

## 7. Frozen dependency hashes and commit packet

Baseline c6c7a20218b084a43d8c0d20505546ecebb517f2; Oracle paths below are
relative to its sibling capture's crates/:

```text
mono/src/lib.rs 713c195d46f33725a3447062f82f9dea23f3746be0c8b2f569ad9e411e79e83d
infer/src/typing.rs b6ade453931d288c03332770fa76022abf90f1276466faeefa3d647be63bcef6
infer/src/analysis/session/lifecycle.rs 196b0f1eeef891e3547bf77e3d00f5f0574399e24bc59c4697219df6ff93d5ed
infer/src/lowering/body/mod.rs f5e82c2109a11938cab6a5b48d8a155f6ac3029c4d26cb7f4570790e8d5f9cb1
infer/src/lowering/body/methods.rs 0f7d0ac524c4934a4491681e6f9901cdc81f8aff20da7f394888c691bb8c067b
infer/src/annotation/constraints.rs 3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db
infer/src/lowering/body/signature_helpers.rs 8302de665ec38ef4a1cf2e00b762b74c7f5fb85e866526224ec527d487cea4cd
specialize/src/specialize2/emit.rs 7318b132cef4217ae089d084577fb28f3abed34a5728474ee8569e4079d71e7c
specialize/src/specialize2/task_solver.rs cc534583e8fd154b51e8c857ef7b17df19fe68e9410fd9acb74c1d13cb1d2f66
specialize/src/specialize2/type_graph.rs 845cdd0040b5ea3f0794957b4606b4609ac054ffca880bb4081526e1a8344eaf
specialize/src/specialize2/task_solver/finish.rs 8ee9baf8bdac1ada4efb6f33331efab15e9f2a61674a7c492180ceac7acf0d28
specialize/src/specialize2/runtime_shape.rs e4443fa1c23a1ea0d957d4582f484abea53e1aa0dffe2f86a3f44fc70aa2e0e4
specialize/src/types/mod.rs ccf204a0f8e32eebbf8556f5b3519f7197f07d580c8231d6687b64ef2ddf4c6f
```

Reviewed Oracle exclusion producer/current file hash:
`aec1b3d4f3632d6cd36ce397d812679d880ffd3c8a438e4d9c1fb827356d0303`.
Runtime production is unchanged from the G4 packet; the inspected machine whole
file hash is e30bb19c54b1a4ee07f3b1d2f0a5e88e57f2226fd055071a6d1ca5f1bdfd5e3a.
Successor lib.rs hash bace98ef2f11c9bb638b4f1f7536178c668ca8b0448fb0276986fbf0772f524b;
program.rs b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748.
Authority/package hashes are retained in the reviewed exclusion dependency list;
user correction is the exact committed bundle1e62dfdc3, not an unapproved draft.

Checks: static exact-source/authority reads, hashes and artifact whitespace;
no tests/builds/probes, code edits, Git mutations, delegation or measurements.
One bounded Sol/high leaf; observed model/effort unknown. Independent review
pending; no parent closure or producer self-certification.

Commit packet: sole new path
`notes/theory/2026-10-16-initializer-effect-admission-correspondence.md`, baseline
c6c7a20218b084a43d8c0d20505546ecebb517f2, dependencies above. Suggested checkpoint:
`research: trace missing initializer-effect admission at actual body checks`.
Shared-record delta for primary: consume the ground projection obstruction;
retain original source reachability/adequacy OPEN at initialization-effect
admission and Name/GlobalRead correspondence. No A/B law or barrier selected.

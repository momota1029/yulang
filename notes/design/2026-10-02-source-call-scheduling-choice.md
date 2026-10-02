# Source application: argument computation construction

Date: 2026-10-02
Status: Draft; source scheduling clarification pending; no implementation authority
Scope: argument construction before the common invocation of charter §16
Approved-by: none for either alternative
Drafted-by: primary with bounded architect and frozen-source mapping
Reviewed-by: compiler_referee, 2026-10-02; no blocking/major finding; internal-constructor notation clarified by primary
Supersedes: none

## 1. The selected rule and the remaining boundary

Charter §16 fixes one invocation: receive a computation, then execute the
declared entry and body. A value parameter forces/rebinds at entry in that
same activation; a computation parameter retains its input. This is not an
outstanding choice. Neither alternative below moves that entry force back
into the caller.

The remaining question is what evaluating an **argument expression** does
before its carrier reaches that invocation. A carrier is a runtime value
holding a computation; code that constructs it can itself run. Fixing force
after receipt alone does not decide whether that construction runs before
receipt or is itself part of the argument's suspended computation.

The question is global source evaluation order, not a callback fixture or a
new family/handler selector. Existing frozen instruction placement is
characterization evidence. Both alternatives still need source soundness,
principal inference and the same symbolic family/typed-path invariants.

## 2. Two complete scheduling alternatives at the argument boundary

For this comparison, keep callee evaluation, the common `Invoke`, result
completion/adaptation and every typed owner/view delimiter fixed. Let
`ArgumentCode(e)` denote executable code for the complete argument
computation; this notation is not a claim that its source elaboration is
already proved.

### A. Reify the whole argument computation

After obtaining the callee value `f`, application passes

```text
Invoke(f, Delay(ArgumentCode(e)), current C)
```

Reification stores code and lexical typed-value references; it runs none of
`e` merely to produce the incoming carrier. The function's entry or body
executes that computation when it forces the carrier. A computation receiver
which ignores its input does not execute any of the argument expression.
An ordinary value receiver forces the argument at its selected entry point.

This has one source construction rule and no producer-shape dispatch at
argument passage. It is a coherent proposal for that boundary, not a result
derived from §16, a complete source elaborator, or an approved successor rule.

### B. Preserve construction before receipt

After obtaining `f`, application instead performs

```text
ConstructArgumentCarrier(e) >>= lambda t.
  Invoke(f,t,current C)
```

Here a source-derived construction prefix may execute before the receiving
function starts. The receiver still forces/rebinds its received carrier only
after entry. Ignoring the carrier skips its retained computation, not
necessarily its construction prefix.

This requires a source relation that determines the prefix compositionally.
It must not merely copy Oracle shape tests, weights or emission flags.
In particular, "evaluate every producer first" is not the already observed
frozen behavior either: some expression-level lifts place the entire code
inside a thunk. The corrected active production map and both branch shapes
are in source-computation-role §§6/9.

## 3. A discriminator and its exact evidence boundary

In the ordinary call-by-value carrier kernel, let `g` diverge purely and let
`op` be an operation with a value payload. The producer

```text
p = Run(g()) >>= lambda a. Return(MakeRequestThunk(op,a))
```

cannot return its request carrier because payload evaluation does not finish.
Here `MakeRequestThunk` is the internal constructor on an already acquired
typed payload, not the public operation invocation's computation input.
An invocation that discards its computation parameter distinguishes passing
that preconstructed carrier from passing `Delay(ArgumentCode(op(g())))`:
the construction-first path diverges; whole-argument suspension reaches the
receiver and lets it return. This is the kernel non-equivalence already
proved in source-computation-role §9. No operation request need be emitted.
Pure effects do not imply termination.

A concrete source candidate is:

```yu
act e:
    pub op: unit -> unit

my spin(): [] unit = spin()
my ignore(x: [e] unit): unit = ()

ignore(e::op(spin()))
```

**This complete program has not been executed or certified as accepted.**
The following frozen `a58eefc3` evidence establishes component facts only:

| Component | Evidence | Missing conclusion |
|---|---|---|
| Computation parameter and direct passing | `crates/yulang/src/source/tests/case_01.rs:334–354`; concrete effect parameters in `crates/infer/src/lowering/tests/case_04.rs:156–176` | Those receivers consume their input; ignored computation-parameter acceptance is not thereby proved |
| Unused ordinary parameters | `crates/infer/src/lowering/tests/application_provenance.rs:43–45,105` | Does not establish an unused concrete computation contract |
| Parameter annotation does not itself insert a body use | `crates/infer/src/lowering/expr/lambda.rs:349–368,1266–1280,1308–1334` | Complete inference/specialization of this ignored parameter remains unverified |
| Recursive definitions | `crates/infer/src/lowering/tests/case_06.rs:670–700`; `bench/loop_recursive_20_discard.yu:1–11` | No located accepted endless `spin(): [] unit` witness |
| Explicit result annotations | `crates/infer/src/lowering/tests/case_05.rs:622–646` | That fixture is not the divergent recursive function |
| Direct operation payload syntax | `crates/yulang/src/source/tests/case_01.rs:105–120` | Does not certify the complete nested composition above |

Even if those two definitions infer separately, their composition must also
specialize without an additional suspending boundary before claiming a
concrete Oracle runtime divergence. The inspected operation-carrier recipe
predicts the timing conditionally; it is not a substitute for those remaining
acceptance premises. No compatibility loss is approved by this record.

## 4. Source result completion is a separate invariant

This choice concerns argument scheduling only. A completed source interface
`Comp(E,A)` returns an `A`; an internal thunk storing that computation is not
itself the result `A`. The existing role-preservation theorem forces only the
identified outer computation layer and keeps a latent `A` as a value.

The comparison fixes the same existing decorated result/continuation protocol
on both sides, including its return delimiter. It does not introduce a new
ordering between callee return and result adapters. Deriving that protocol
from arbitrary source remains part of the representation proof.

Likewise, describing a complete interface does not prove that its carrier's
force may move across a source invocation return delimiter. Native operation
thunk construction/force, result adaptation, receiver expiry and complete view
observation must retain their specified positions until a representation
simulation justifies another placement. Endpoint agreement alone does not
preserve handler visibility. The scheduling clarification must not silently
select a second invocation-lifetime change.

## 5. Next action

The primary asked the user whether arguments should be reified as complete
computations or retain a construction prefix before receipt. Neither choice
is inferred from elapsed time or from the current compiler. Both retain the
selected same-activation entry rule and the common shallow handler semantics.

Once this source boundary is fixed, construct one source computation judgment
for literals, names, closures, local binding, application, operations and
handlers, with explicit typed result completion. Prove its simulation and
effective symbolic closure as a package. Do not substitute finite syntax
templates for finite principal inference, or introduce a source restriction
because the current construction is incomplete.

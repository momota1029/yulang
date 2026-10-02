# Source application: argument computation construction

Date: 2026-10-02
Status: Authoritative for source scheduling; elaboration/proofs remain separately scoped; no compiler implementation authority
Scope: whole-argument reification before the common invocation of charter §§16–17
Approved-by: user; A records the originally intended Oracle source semantics
Approved-at: 2026-10-02
Drafted-by: primary with bounded architect and frozen-source mapping
Reviewed-by: compiler_referee, 2026-10-02; no blocking/major finding; internal-constructor notation clarified by primary
Selected-law review: independent compiler_referee and spec_auditor, 2026-10-02; no findings in A/inert-introduction authority delta and its conditional realization dependency
Supersedes: the pending A/B choice in this record and the carrier-producing argument evaluation in ordinary-computation §3

## 1. Selected source rule

Charter §16 fixes one invocation: receive a computation, then execute the
declared entry and body. A value parameter forces/rebinds at entry in that
same activation; a computation parameter retains its input. This is not an
outstanding choice.

The user selected **A: reify the whole argument expression**, explicitly as
the originally intended source semantics. After obtaining the callee, the
application passes the entire argument as a computation. No part of that
expression executes before receiver entry merely to construct its carrier.

The user's further clarification supplies the reason: effectful computations
are first-class data. Introducing their value is inert; running any
source-derived prefix would partially execute the represented computation.
Only explicit receiver elimination (`Force` or handling) begins execution.
This is a source introduction/elimination law, not merely a scheduling
preference. `Delay` below is notation for inert computation introduction, not
a newly proposed surface keyword or an extra authority-generating boundary.

This settles global source evaluation order. It introduces no callback,
family or handler selector. Frozen instruction placement is characterization
evidence; it can implement A only under an observational-equivalence proof.
Source soundness, principal inference and symbolic family/typed-path
preservation remain proof obligations, not consequences of user approval.

## 2. Selected schedule and rejected source alternative

For this comparison, keep callee evaluation, the common `Invoke`, result
completion/adaptation and every typed owner/view delimiter fixed. Let
`ArgumentCode(e)` denote executable code for the complete argument
computation; this notation is not a claim that its source elaboration is
already proved.

### A. Reify the whole argument computation — selected

After obtaining the callee value `f`, application passes

```text
Invoke(f, Delay(ArgumentCode(e)), current C)
```

Reification stores code and lexical typed-value references; it runs none of
`e` merely to produce the incoming carrier. The function's entry or body
executes that computation when it forces the carrier. A computation receiver
which ignores its input does not execute any of the argument expression.
An ordinary value receiver forces the argument at its selected entry point.

The receiver's statically known interface determines entry demand. A value
parameter forces and rebinds in that same activation; a computation parameter
retains its carrier. Unknown portions are not guessed or executed in advance.
The result of force remains a value even when it is a function/thunk/latent
value; that shape alone does not demand another force. This is the same
principle as a handler acting only on its currently known effect interface.

In particular, looking up, storing, passing or returning a computation value
does not itself eliminate it. Any elaborated force must correspond to an
explicit source consumer (including the declared value-parameter entry
expansion), not a runtime shape test or a desire to complete a carrier.

This is one source construction rule with no producer-shape dispatch at
argument passage. It is source authority, not yet a complete source elaborator
or compiler implementation approval.

### B. Construction before receipt — rejected as source semantics

The previously considered alternative would perform, after obtaining `f`,

```text
ConstructArgumentCarrier(e) >>= lambda t.
  Invoke(f,t,current C)
```

Here a source-derived construction prefix may execute before the receiving
function starts. The receiver still forces/rebinds its received carrier only
after entry. Ignoring the carrier skips its retained computation, not
necessarily its construction prefix.

This is not the selected source relation. A compiler may perform such a
transformation only after proving observational equivalence to A, including
divergence, store behavior, request order and current boundary eligibility.
Neither purity alone nor Oracle shape tests, weights or emission flags prove it.
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
acceptance premises. The selected successor behavior is A; this kernel
discriminator prohibits a blanket construction-hoisting law. No verified
whole-source Oracle acceptance loss is established here. A concrete frozen
placement incompatible with A is not the user's intended source semantics;
its final-acceptance impact must still be recorded if demonstrated.

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

The pending choice is closed by the user's explicit A decision. There is no
remaining permission gate on whole-argument reification. Charter §17 records
the decision; ordinary-computation §3 is the corresponding call rule.

Construct one source computation judgment
for literals, names, closures, local binding, application, operations and
handlers, with explicit typed result completion. Prove its simulation and
effective symbolic closure as a package. Do not substitute finite syntax
templates for finite principal inference, or introduce a source restriction
because the current construction is incomplete.

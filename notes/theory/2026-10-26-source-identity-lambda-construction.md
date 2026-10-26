# Identity Lambda: direct constructor attempt and checked contextual core

Date: 2026-10-26. Baseline: `b26e7de1aada0e15ac5147feb8654ec34ac90275`.
Status: source construction attempt and checked paper-core result; independent
review pending. Original contextual Function introduction **OPEN**.
Author: `/root/source_lambda_construction`, generic `lean_prover` fallback.
No compiler, semantic-policy, production, or parent-gate change is claimed.

## 1. Result and unchanged target

The new checked result constructs the identity closure by the existing
syntax-directed paper rules, fills an **arbitrary independently typed
represented callable context** with that constructed value, and preserves the
filled program through every finite interaction admitted by the existing paper
executor's response protocol. The context is typed under a variable assumption;
identity typing, substitution success, and the filled context's typing are
conclusions. No Lambda-safety, body-typing, Call-typing, `LocalLaws`, or source
derivation `T` premise is supplied.

This is useful constructor evidence, but it does not prove the original
`ValueMem_F(W,r,e)`. The original `D_F/P_F`, their joint worlds, provider and
authority fields are not the paper's `PaperValueTyped` and `InteractionTrace`.
The original leaf remains open; this note does not rename the new theorem into
that leaf or count a syntactic core instance as full inference soundness.

The source attempt goes beyond extracting an already typed result. It uses the
selected generic `Strict` constructor to form the identity's canonical complete
interface, derives its actual inlet calculation, and constructs its precise
Return/rebind/Name suffix. It then locates the missing original evidence at the
uniform interpretation of the punctured context and full invocation envelope.
The algebraic relative-coinduction step is already available; it is not the
missing theorem and is not reproved here.

The parent remains the full supported-language inference/executor obligation:
successful ordinary generation, accumulation, propagation, levels, extrusion,
qualified intrusion, generalization and use must produce one original scoped
source witness, with complete Call and all source effects and continuations.
See [whole proof closure](../../docs/yulang-whole-proof-closure-ja.md) §1 and
[original A/B statement](2026-10-13-intrusion-source-preservation-proof.md) §1,
with the current birth-level SCC qualification. This single fixture is a leaf,
not a reduction of that universal theorem.

## 2. Exact source and distinct constructors

The source remains:

```yulang
my relay (thunk:[] (int -> int)) = thunk
my main = relay (\x -> x)
```

Keep the resolved lexical identities and actual source incidences. `C` is the
Call's delayed argument computation. Its execution constructs and returns the
identity closure `W`. They are different objects. The fixture has no subsequent
Call of `W`.

The corrected [relay account](2026-10-26-source-relay-return-instance.md) and its
[independent review](../../tasks/agent-loop/inbox/source-relay-return-instance-20261026-review.md)
are retained. Direct inspection at this baseline also confirms:

| Owner | Actual operation | Consequence for the proof |
| --- | --- | --- |
| `program.rs:719–739,819–835` | Explicit outer effect syntax selects Computation entry and Execute name consumption; unannotated `x` selects Value entry. | The relay and identity require different introduction/entry cases. |
| `machine.rs:1284–1328` | Value entry executes the delayed argument before installing its result; Computation entry binds the received carrier and enters its body. | No Value-entry Force/rebind may be inserted into relay's entry. |
| `machine.rs:2469–2500` | Execute consumption of retained `thunk` runs that same carrier. | Relay's Result is not a pure return of `C` as a Function. |
| `machine.rs:1087–1096` | `RootCompReturn` closes its execution occurrence and returns the unchanged received record. | It does not create `W`'s semantic membership or rewrite its result view as ground. |
| `machine.rs:3115–3156` | The existing fixture tests actual-result-record preservation. | This is not a Function-membership test or a later Call of `W`. No test was run here. |

The native files are under `tools/inference-playground/src/runtime/`. These are
static owner observations, not a native execution or a proved source/native
simulation. The paper core uses the same ordering but still lacks the full
native provider/world interpretation.

## 3. Canonical complete source interface, before testing membership

[Source-Generalize](2026-10-08-source-generalize-definition-and-proof.md) §3.1
introduces a flexible value endpoint `A_x` at unannotated Parameter's original
typing scope. That scope precedes the invocation challenge. Let `I_x` be the
same source-owned complete Value-entry carrier interface and let `IF_id` be
the actual complete entry/body/return interface generated at this Lambda.
Neither is just the printed result type.

The raw finite source construction is:

1. Parameter registers `x`, its Value entry, `A_x`, and `I_x`.
2. The body Name uses the resolved edge to this formal.
3. Result on that Value returns the same binding; it introduces no consumer of
   a latent value. Its body descriptor is the existing `PureReturn(A_x)`.
4. Lambda stores this body and its original captures. For `\x -> x`, the
   source free-capture set is empty. Its complete interface inserts the entry,
   actual rebind, body, invocation-return and future ports.

The selected [complete closure definition](../design/2026-10-08-captured-closure-constructor-definition.md)
§2 adopts the generic descriptor constructor, not only its displayed captured
Call body. It therefore supplies the following *constructed interface*:

```text
F† = Strict(I_x, x:A_x, PureReturn(A_x), IF_id)
   = ContextualFunction(Pure, ValueEntry(I_x),
       receipt; Force_I_x(wholeCarrier);
       actual-Return/rebind-x; PureReturn(A_x); invocation-return).
```

Its domain and observation contract are the complete relations of
[captured closure introduction](2026-10-08-captured-call-closure-introduction.md)
§3.1. They retain arbitrary admitted argument effects, raw resumptions,
divergence, zero-step prefixes, scopes, authority and hard joint dependencies.
The interface is formed independently of acceptance or safety of `W`.

[Complete source-interface construction](2026-10-08-call-source-interface-construction.md)
§§3–6 supplies the original port insertion and reference-use maps for this
finite formation. It expressly does not turn an uninhabited semantic guard
into a proof. The selected
[native signature formation](../design/2026-10-08-native-signature-formation-definition.md)
§§2–4 also applies: the catalogue, provenance and unannotated local
full-protection/no-concrete-removal policy are available. They are not new
unknown foreign-profile assumptions.

`F†` must remain distinguished from an independently supplied original `F`
and from the relay's written `int -> int` boundary. Naming the same two value
endpoints does not establish equality of their complete challenge/envelope
relations. This note constructs no annotation realization or whole comparison
from `F†` into that independently fixed boundary. It does not replace the
original `F` with a convenient new descriptor.

## 4. Direct inlet calculation at the constructed interface

Take an arbitrary independently admitted `d : D_F†`, before invoking `W`.
The generic Strict domain supplies this same whole carrier's admission at
`I_x`, and the original receipt, typed-path and context preconditions. Actual
closure inversion gives the registered provider `U_id` and

```text
CarrierContract(U_id) = I_x.
```

This equality comes from the Parameter/Lambda constructor and its retained
formal port; it is not inferred from equality of printed Function shapes.
Rewrite only the inlet index of `d`'s existing whole-carrier certificate using
that equality, and pair it with the same context/receipt preconditions. This is
exactly the two-field construction of `ActualAdm(W,U_id,d)` in
[semantic input realization](2026-10-08-call-semantic-input-realization.md) §2.
The carrier, actual event/world, witness, `eta0` and original `xi` do not change.
No invocation result, Function membership, Q success, receipt establishment,
or termination is used.

This calculation is uniform over the complete Strict domain. Its source
application needs the actual original interface identification just stated.
It cannot admit arbitrary challenges of a different complete `F` merely
because its printed input is also `A_x`. Conversely, the domain's cardinality
is no obstacle: this is an arbitrary-challenge argument, not an enumeration.

## 5. Direct observation construction and the exact unfinished step

### 5.1 The real body and continuation

The actual Value-entry invocation has the following ordered suffix after the
argument's unfinished execution:

```text
S_id = actual-rebind-x; Name(x); Result; invocation-return.
Request(q,C,k_arg) >>= S_id
  = Request(q,C,(response,C'). k_arg(response,C') >>= S_id).
```

The raw finite source witnesses are constructed by the selected Name/Result,
entry and Bind rules in captured closure introduction §4. There is no source
Call in the identity's body. A request in the arbitrary carrier retains its
original operation witness, raw handle and this ordered suffix. Repeated
requests retain the unfinished suffix again; receipt is not prepended. A
divergent carrier contributes every finite prefix without a fabricated result
or binding. Zero-step and administrative prefixes retain their actual phase.

On a real carrier Return `(a,r_a,C',w')`, the entry's result clause supplies
the result certificate at that tuple. Typed rebind installs that same value
at `x` in the same current world. Name follows this actual binding and Result
returns the same `a,r_a` without invoking it. The existing immutable-world and
Return cases of semantic input realization §§4.1–4.2 prove this suffix once
their original binding/world inputs are present. Future uses of a latent `a`
are covered by that returned value's hereditary certificate at their later live
events, not by a second Force in the identity body.

For a simultaneous construction, this argument is made at the positive
candidate occurrences: the parameter result is in `S.V`, its actual world in
`S.W`, and the new Return/continuation in `S.T`. It does **not** eliminate an
unfinished candidate as if it already belonged to the greatest fixed point.

### 5.2 Why empty captures do not remove the context obligation

An independently typed punctured caller may mention its declared callable
hole inside the argument carrier or other continuation fields. Schematically,
a future caller can form `h (h 1)` under the independent hole declaration
`h : int -> int`, with the tested callable as `h` and the whole argument
carrier retaining the inner call. This is an illustration of a permitted
context shape, not a second call present in the fixture or a new execution
counterexample. A proof must include such contexts if admitted by the fixed
original rules.

Consequently, treating all challenge fields as already completed ordinary
certificates containing `W` can assume the Function membership being proved.
The selected constructions avoid that circularity with the precise declared
value-hole background. One would take `H_id` to contain only the actual
`(F†,W,r,e)` tuples with original incidences and independently compatible event
restrictions; it contains no world, carrier, continuation, guard or authority
hole. Set `B_H = nu Y.(Phi(Y) with H_id added only to V)`, and put all its four
components into the candidate `S` together with the actual identity
construction/invocation worlds and observations.

The relative lift is already proved for arbitrary exact `H` by RP5 in
[original raw postfixedness](2026-10-24-original-raw-observation-postfixedness.md)
§3. It neither requires a finite set of challenges nor relies on the older
pair having exactly two values. Reproving that algebra would not solve this
task. The same paper §§5–6 preserves the distinct obligations of interpreting
the original challenge fields and proving every full `Phi` conjunct.

### 5.3 Unfilled original input interpretation and envelope action

The remaining first use cannot be silently supplied:

```text
For every d in the unchanged original D_F, interpret all its independently
typed punctured-context fields in the same original four-sort background
under only the exact W declaration; preserve every provider, carrier, live
world, raw continuation, scope, operation witness and xi incidence.

For each actual identity entry/body/return observation, construct every
conjunct of the original P_F[S](d), using those fields and the original
transition/descriptor cases, including initial and current-world guards.
```

These are not satisfied by adding the raw observation to `S.T`. The selected
positive operator explicitly retains the **entire** independently specified
hard envelope: its displayed Return/prefix/Bind cases identify positive
hereditary occurrences and do not replace that envelope. The world binding
part likewise does not establish every independent current-world guard.

The original contracts do provide the generic Strict composition, raw phase
equations, immutable binding/Return cases, native formation grammar and
arbitrary-H relative lift. They do not, at the inspected revision, supply an
exhaustive original punctured-context typing/interpretation judgment with a
proved evidence action for this actual identity occurrence and its whole
independent domain. Contextual Function definition §2 expressly leaves the
complete descriptor and context relations as independent inputs. The selected
pair/step proofs give their exact declared-hole instances with their listed
independent contracts; relabelling an arbitrary original certificate as
`B_H_id` is not a derivation.

This is partly a missing interpretation/constructor specification at the
original source owner, and partly the proof obligation of applying that
specification at the actual tuple. It is not evidence that the original
relations are inconsistent or that identity membership is impossible. No
replacement `D_F`, weakened `P_F`, new foreign guard, or safety-based typing
definition is introduced. In particular, unprovided W/Z semantics are not
invented as an obstacle to the local Name/Return calculation; complete
production claims retain their own separate original arm obligations.

A genuine original native context judgment with those complete fields, plus
its constructor-directed substitution/extension action, would allow the above
source case construction to continue. Merely assuming that action as a
`LocalLaws` field would leave the same source obligation open.

## 6. Checked construction in the existing paper judgment

The new module is
[SourceIdentityLambda.lean](lean/YulangClosure/SourceIdentityLambda.lean), under
namespace `YulangClosure.PaperTypes.SourceIdentityLambda`. It imports the
existing `PaperCallEntryFormation` and `PaperViewExecution`, defines only the
identity/relay raw terms, and introduces no new typing or safety relation.

The principal application is `identity_context_interactions`. Its inputs are:

- a table with genuinely typed template bodies;
- any existing `PaperComputationTyped` derivation of `punctured` under a
  callable variable `callable A A` plus the unchanged environment;
- an independently typed continuation stack;
- raw profile/parameter metadata.

It constructs `filled` and proves successful substitution of the actual
constructed identity into `punctured`, typing of `filled`, and preservation
of every existing finite `InteractionTrace` of `filled` whose external
responses satisfy the existing protocol. No terminating execution, identity
membership premise or filled-context typing premise is required. The trace's
reflexive constructor includes the zero-step prefix. Internal execution events
have no added safety condition. The response premise concerns only the
independent external response values.

This is the direct syntactic method needed at the source level, mechanically
realized at the existing represented paper judgment. The proof uses the
already checked term-substitution theorem after constructing identity typing,
then the existing finite-interaction theorem. It is not a context-extraction
lemma from a previously assumed typed identity.

| Source object/case | Exact Lean representation or theorem | Boundary |
| --- | --- | --- |
| Formal `x`, then Name/Result | `identityBody = ret (variable 0)`; `identity_body_typed` | De Bruijn binding in the represented environment; no native lexical-ID simulation. |
| New Value-entry closure W | `identity`; `identity_typed` | Paper callable type, not complete original `ValueMem`. Raw metadata is not independently proved profile validity. |
| Receipt/Force/rebind order | `identity_entry_formation` | Retains literal View and surrounding owner scope in `EnterTrace`; does not construct actual receipt/world guards. |
| Actual returned value and suffix | `identity_result_substitution`, `identity_result_step` | Same entire raw value and stack; no source semantic root/world interpretation is asserted. |
| Arbitrary typed argument plus identity suffix | `identity_argument_interactions` | Every admitted represented interaction prefix; no original-observation coverage theorem. |
| Independently typed callable hole | `identity_context_interactions` | Actual substitution/typing constructed for the paper judgment; no broad original context embedding is assumed. |
| Force of received delayed argument | `identity_argument_exposure` | Produces and retains `expose metadata argument`. Exposure execution is not erased or proved here. |
| Relay's retained C and designated body consumer | `relay_typed`, `relay_entry_formation` | Computation entry is distinct from identity Value entry; the View of C is substituted before body Force. |
| Concrete represented relay/identity Call | `relay_identity_call_typed` | Constructs both children and Call typing; this is not original `T`. |
| C versus W | `carrier_ne_identity` | Distinct raw constructors; no later Call of W is added. |

The interaction executor has no original live owner/world state, no complete
Function admission relation, and no claim to cover all source/native events.
In particular, the new Force/View theorem stops at the retained Exposure;
the existing extended executor does not execute that whole exposure or owner
scope. Original annotation permissions, complete effects/profiles, source
context domain, provider worlds, and arbitrary original future-use contracts
remain outside this Lean theorem. The paper substitution/typing inventory is
the existing represented one, not every raw or supported source constructor.

## 7. Application to relay and the unchanged parent

The paper specialization `A = base int` constructs the raw identity value,
the retained-entry relay at `callable A A`, the delayed identity argument, and
the Call returning that callable type. It does not prove the original
annotation `[] (int -> int)` or close its complete Function boundary. The
outer `[]` remains an open-row permission; it is not a closed purity claim.

No independently valid original `T`, original `ElimExport`/`CallableExport`,
full result-prefix action, ReturnView/FL12 application, or complete later W
consumer is constructed. Those cannot consume the new paper derivation by
renaming it. The inspected native return preserves W's record, and the source
result-interface theorem can use that fact only after its actual source
membership and same-instance inputs are supplied.

The next original-source evidence is precise: instantiate the original
context/descriptor interpretation at the actual identity formation, including
the full declared-hole field action and the identity phase-to-envelope maps;
identify its complete descriptor with the source/annotation boundary through
actual constructor or comparison evidence. The source construction in §§3–5
can then be applied without redoing the native spine or the relative-lift
algebra. The original all-language A/B, inference soundness, source/native
correspondence and production gates remain OPEN.

## 8. Verification boundary

The exact Lean module was checked with the official pinned Lean 4.35.0
distribution, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Lake reported
`5.0.0-src+eb6cafb (Lean version 4.35.0)`. The producer used an isolated baseline
project and never wrote the shared `.lake` or root imports.

Three focused checker calls ran within 120-second bounds, one CPU affinity,
`LEAN_NUM_THREADS=1`, `-j1 -M1024`, and a monitored aggregate 1-GiB RSS cap.
The first call built dependencies and exposed three invalid `rfl` reductions
through the existing well-founded substitution definitions; they were repaired
by their actual defining equations. It exited 1 after 93.34 seconds. The
second built the repaired module and audited every authored theorem, exiting 0
after 4.15 seconds. At the primary's request, the third ran the existing
originating-module census pattern with this singleton module and all twelve
required roots. It audited all fourteen originating theorem constants,
including both generated body equations, and exited 0 after 1.57 seconds.
Peak measured aggregate RSS was 943,357,952 bytes. Existing
dependency lint warnings were preserved; none was changed or suppressed.

All fourteen printed theorem types and complete axiom outputs are retained in
the assignment handoff. `identity_body_typed`, `carrier_ne_identity`, and the
two generated body equations use no axioms; each other new theorem uses
exactly `propext` and `Quot.sound`. No
`sorry`, `admit`, project axiom, native evaluation trust, or kernel-check bypass
is used. Checker acceptance is not independent review or original source
correspondence. No Cargo, runtime probe, test run, network, compiler edit,
dependency edit or Git mutation was performed by this worker.

Lean freeze SHA-256:
`831b297998509eb261f7a0596792c826c56078661d5a3ab66fc9afd67238d7a4`.
Exact input hashes and full audit evidence follow in the frozen handoff;
the source note remains a bounded attempt at the original introduction.

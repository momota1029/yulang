# R340 — Authentic K0 Apply and its protected continuation

Revision 1; **candidate conditional derivation and source/native evidence**.
Author: `/root/r340_apply_continuation_prover`. Fresh independent review and
Luna adjudication are pending. No production authority follows.

## Contract, unchanged parent and inputs

The parent remains the full Yulang2/Simple-sub source/native A/B theorem and
catalog. The immediate application is the user audit §6 C/M, with its original
`ValidK0`, independent source typing and runtime realization, and selected
definition entry (§4.1–4.5). This note repairs the R339 continuation gap only.
It neither changes source semantics nor makes successful execution a definition
of realization. Inference generation, accumulation, propagation, levels,
extrusion, qualifying intrusion and generalization retain their actual owners.

Baseline supplied by Luna: `research/simple-sub-intrusion`,
`e801dfa604c1e6e0b1ba5760d589fc0e77526406`; no Git command was run here.
All following SHA-256 pins were read and matched before writing:

| Direct input | SHA-256 |
| - | - |
| `tasks/agent-loop/sprints/r340-k0-apply-continuation-20261023.md`, rev1 | `5de2605641bc28bdea416be1d7eea69a0bff4a689d39b33a2c2738b23cc7642c` |
| User audit, `docs/Yulang Simple-sub 拡張：全体証明への移行監査・証明設計.md` | `b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895` |
| R339 D3, `notes/theory/2026-10-23-r339-k0-machine-call-simulation.md` | `4301ed7e184915e75646809102a477f8d4b27f874478e364c03886ae1cfd2666` |
| R339 outcome, `tasks/agent-loop/sprints/r339-k0-obligation-retirement-20261023-outcome.md` | `07abaf5ee285917a4f49ce94fbf287b115dfcdbd20f8275bdcb6bcc3acec0701` |
| R339 rev2 contract | `953d0edfffc99645ab137819ae44d35a7df03b8e775b4e97317f825657dfaa00` |
| R340 source census, frozen by Luna `/root` during this assignment | `5b9fd45dc51a902c96a23586b4965a674b8429554340d8c3d01d4410746ecf5f` |
| `tools/inference-playground/src/runtime/program.rs` | `df58f9a1d60e39fafe6d85b1e50331b35fde2a9142a2eaea84ad028d3048fdb0` |
| `tools/inference-playground/src/runtime/machine.rs` | `02adc26bcd58cca488a40e78289a264751146d7900c2897db19068b279a8d840` |
| `tools/inference-playground/src/runtime/dispatch.rs` | `f45057373f2ed3a7b6ce915611db093015fb93cdb05984a5e3b23cfd44720873` |
| `tools/inference-playground/src/runtime/receiving.rs` | `2170a3bcbc6710ce3fbf721a05129117f8266b9ecf21c67136db918815303551` |
| `tools/inference-playground/src/runtime/literal.rs` | `2fff177a7ba0cabb4930251e1facc8f9be701ff3ec7baa695ce4c182fa1da35f` |

The R339 source/value/environment representation clauses are reused as
definitions, not as a proved adequacy theorem. Its actual-handle lookup,
whole-Delay, fresh invocation and ValueEntry trace are reused below with the
previously missing stack and owner premises now explicit. Its stack-free
callee input and its unsupported inference of the preceding Apply push are
rejected. R339 D2 concerns a different obligation family and supplies no
runtime premise. No earlier F1/FK1, effect or foreign-continuation theorem is
claimed by this K0 result.

## 1. Typed boundary relation, defined before execution

Fix an authentic K0 occurrence `p = Apply f a`, its independent typing
derivation `D : Γ ⊢₀ p : τp ! εp`, and the particular premises of D for f and
a. In particular f has the Function demand for the same argument Value/Effect,
result Value and invocation Effect; retain all four ports and both outer
effect inclusions. These are the audit §4.3 source rules, not machine success
or native generated constraints used as source assumptions.

Let `P` be the fixed RuntimeProgram built from this same authentic HIR and
candidate. `CodeReal₀` relates source occurrences to their constructor-derived
labels; `EnvReal₀(σ,η)` relates typed source bindings to actual parameter-cell
lookups, and `ValReal₀`/`ClosureReal₀` have the pre-execution representation
clauses of pinned R339. In particular ClosureReal names an actual handle h,
its executable closure, exact formal/body and saved capture environment. It
does not say that h will successfully execute. The proof below never derives
ClosureReal merely from a Function type.

Write stacks bottom to top; `κ·F·s` puts F above κ and suffix s above F.
`κ` denotes the entire actual saved frame vector, including any root frame.
It is not an empty-stack assumption. If supplied, an independent typed source
evaluation context E has a hole judgment `τp ! εp ⇒ τroot ! εroot` when plugging the
derivation D into that context gives the independent root derivation. Its
runtime representation pairs its ordered pending source actions with κ.
The local typed continuation constructors needed here are:

- a source context waiting for the callee of `Apply [] a` corresponds to
  `Callee(k_a,ηcaller,site_p)`, with the source argument typing and caller
  source environment retained;
- the context waiting for a Value argument of a fixed source closure
  corresponds to `ValueEntry(x,false,None,k_b,ηc')`, retaining that closure's
  source binder/body derivation and capture-environment relation;
- `ReceiverReturn(i,previous)` is an operational delimiter with an identity
  source result hole; its owner data is kept, rather than erased;
- pending If tests and expression-only statement prefixes correspond in
  order to `Condition` and `BlockExpression`; their code/environment payloads
  retain the independently typed branches and remaining statements. Group and
  empty binding-free Block introduce no runtime frame; selected Root supplies
  the selected result hole.

These clauses define a typed *boundary certificate*, not a theorem that every
intermediate configuration has a supplied source typing. In particular the
ValueEntry clause requires capture-environment transport when used as a typed
source substitution. Full preservation, canonical forms and completeness of
this representation are separate suppliers.

Define `ApplyCfg₀(D,σcaller,ηcaller,k_p,k_f,k_a,site_p,κ,ω;M)` by:

1. the authentic p/f/a and their labels have CodeReal, with
   `P.code[k_p] = Code(site_p,Apply{k_f,k_a})`;
2. D is fixed and `EnvReal₀(σcaller,ηcaller)` holds in M;
3. M is actually reachable from the same ordinary selected-definition K0
   machine start, with `state=Evaluate(k_p,ηcaller)`, `frames=κ`, and
   `current_owner=ω`.

Actual reachability is operational, not an assertion of termination, return,
type preservation or successful execution. Private machine storage cannot be
externally fabricated. No complete typed representation of outer κ is an
extra premise: the result is parametric in every actually reachable κ. If an
outer context certificate is supplied by the larger simulation it is retained
unchanged. The local typed continuation certificate consists of D's fixed
callee/argument/result/effect premises paired with the actual waiting payload;
it does not assert full preservation of a typing for every transient suffix.

The successor boundary certificate `WaitCallee₀` retains the *same* tuple D,
p/f/a, labels, site, σcaller, ηcaller, κ and ω, and marks the actual freshly
pushed frame position `|κ|` as distinguished. This position distinguishes
recursive re-evaluation of the same source site. The local source context is
`Apply [] a`, whose hole typing follows by the Apply rule from D's fixed
argument premise; any supplied E composes with it. It is not an input premise
that Callee already exists.

**Candidate theorem.** For every such ApplyCfg and every actual finite K0
execution prefix, section 2 derives WaitCallee and section 3 preserves its
distinguished payload until the matching return boundary, if any. At that
boundary the current owner is ω. Given the explicit ClosureReal supplier and
available entry resources, section 4 derives the exact invocation/Delay/entry
successor. For every actual argument segment from that successor, section 5
preserves the entry prefix and proves the exact binding/body step on a matching
return. ValReal and capture transport supply only the final typed environment
conclusion. No existential return is asserted by any of these quantifiers.

## 2. Authentic Apply creates that exact waiting frame

`program.rs:597–603` checks each LocalSourceIndex and maps it to
`Label(offset+ordinal)`. Its `843–849` Apply arm uses the two authentic child
indices; `962–979` constructs Code with the source root/occurrence and that
instruction. Lambda role/formal/body are retained at `818–842`; the later
rewrite loop `1054–1107` rewrites FieldTail/operator instructions only. Those
source forms are excluded by ValidK0. Thus k_a is the whole source argument's
label, and site_p is p's containing Code site, without reconstructing p from
an eventual provider site.

The actual `Machine::step` dispatch is `machine.rs:650–674`.
`evaluate` fetches that Code (`678–687`), and Apply (`878–888`) performs:

```text
(Evaluate(k_p,ηcaller), κ, ω)
  → (Evaluate(k_f,ηcaller),
     κ·Callee(k_a,ηcaller,site_p), ω).
```

The arm has no other frame mutation or owner call. This proves the creation
step from ApplyCfg, including exact source argument/site/environment. Merely
starting at Evaluate(k_f,ηcaller) would not prove this fact.

## 3. Prefix and owner invariant over actual K0 transitions

The following structural observation is independent of source typing
adequacy. From the closed selected K0 root, executable labels reached by
evaluation are K0 children or the bodies of closures allocated from K0
Lambda instructions. User-observable values allocated on these paths are
literals or closures; internal argument Delay values are not bound as Comp
formals, since every K0 formal is Value. Parameter cells receive only actual
ValueEntry results. Names resolve parameters and use Observe
(`program.rs:717–740,775–801`; `machine.rs:773–855,2372–2401`). No K0
instruction allocates a Primitive, Continuation, Request, handler, template,
record default or Comp-entry closure. Consequently no Request unwinding or
template copying is entered on these prefixes. This is a constructor/transition
shape induction; it does not prove that any Function-typed value is callable
or any condition is Boolean. A noncallable value or invalid test can stop.

Use the actual transition relation of `step`, not a newly executable abstract
model. Let B be any protected bottom vector, o its baseline owner, and A the
active-receiver vector at its installation. Until the first transition that
would pop B's top frame, the invariant for a non-stopped machine is:

```text
frames = B·s
receiver frames in s, in bottom-to-top order:
  ReceiverReturn(i1,o),
  ReceiverReturn(i2,Invocation(i1)), ...,
  ReceiverReturn(im,Invocation(i(m-1)))
active_receivers = A·[i1,...,im]
current_owner = o                 if m=0
              = Invocation(im)  otherwise.
```

All listed invocations are active, their IDs distinct/fresh, and the previously
active invocations in A remain active. B and every payload in B remain
identical, not merely equal in length. On a stopped error prefix B still
remains unchanged; no general owner-chain assertion is made for a helper
that fails after changing the owner and before installing its delimiter.
Such a Stopped(Unavailable) machine cannot later return: `step` immediately
returns its stopped outcome. This distinction does not assume away runtime
failure and is sufficient for the matching-return claim.

**Proof by induction on actual finite transition prefixes.** At installation
s is empty, m=0, and all statements hold. In the step case:

| Actual K0 owner | Effect above B and induction argument |
| - | - |
| literal/Lambda, `evaluate:688–713,856–877`; `ground_data/data/allocate:2543–2557,2589–2619` | Set Return; append value/executable/view; no pop or owner change. Executable insertion uses a fresh value index, so an old handle's executable is not replaced. |
| parameter Name, `773–855,2372–2401` | Lookup and receipt/Observe return do not mutate frames or owners. Missing/invalid binding/view stops; no unwinding. Execute is excluded by the authentic unannotated formal role. |
| Forward, Apply, If, `767–772,878–917` | Change evaluation label, or push Callee/Condition above B. No owner change. |
| binding-free Block/StatementBlock, `2403–2449` | Either enter final expression or push BlockExpression for the next prefix expression. Local initialization is excluded by ValidK0. The ordering is retained. |
| Return with top Condition/BlockExpression, `1482–1530` | Pop only the top suffix frame. Condition selects a branch or pushes the next test frame; BlockExpression calls begin_local for the next statement. No owner change. Failed Boolean checking stops after this suffix pop, leaving B untouched. Else is present, so no DiscardToUnit is introduced by these K0 tests. |
| Return with top Callee in s, `1162–1309` | Pop this suffix Callee; allocate inert whole Delay. If the returned value is not executable, stop. A K0 executable callee is a Value closure. `new_invocation` appends fresh i, saves the current owner o_last, and sets Invocation(i); the branch pushes ReceiverReturn(i,o_last), then ValueEntry, and evaluates that Delay. Thus the receiver chain appends i exactly once. |
| Return with top ValueEntry in s, `1383–1415` | Pop only ValueEntry; bind actual received value and enter saved body. K0 unit/record special branches are absent. No owner change. The invocation's ReceiverReturn remains. |
| Return with top ReceiverReturn in s, `1370–1382,1721–1749` | By the induction hypothesis current owner is Invocation(im), active top is im and its descriptor is active. Every leave_owner guard succeeds. It pops im, marks that invocation inactive, and restores precisely its stored predecessor. Return keeps the same handle, view and dispatch, changing only interface to Value. Remove the final link in the chain. |
| `run(step_budget)`, `578–588` | Performs the above finite steps. At budget depletion it reports ResourceExhausted without changing the live state, frames, owner or active vector. Repeated run calls continue the same invariant. |

These cases exhaust the non-stopped K0 segment before the protected pop:
its state is Evaluate or Return; no K0 producer enters Request, EnterTemplate
or IntegerProduct. Root/GlobalRead/ExpressionReturn cannot be top above B:
they are not introduced during this segment. Any root frame below B is
untouched. No K0 operation scans/modifies a lower frame. A Return with s empty
is the boundary, not an induction step allowed to consume B.

On a successful closure-call arm all helper effects are exactly as listed.
In ordinary K0 `RuntimeEvidence` starts with contextual_dispatch=false;
the only assignment to true is within field-tail selection (`program.rs:412`),
which requires source forms outside K0. `1231–1242` therefore constructs no
dictionaries. `substitute_environment` (`machine.rs:2509–2513`) returns the
original environment immediately on this route. Even when keeping ηc' as the
actual substitution output for comparison with R339, there is no silently
assumed successful dispatch transformation. An IdentityExhausted failure in
`new_invocation:1707–1710` occurs before invocation/owner mutation; other
terminal failures require no return claim. Finite allocation is not promised.

The actual owner constructors are `new_invocation:1701–1719` and
`leave_owner:1721–1749`: initial `next_receiver=0`, invocations/active vectors
empty and ModuleRun owner (`433–460`); each successful allocation takes the
next unused ordinal and appends its descriptor before returning. No K0
transition reuses an ordinal or reactivates an inactive descriptor. This also
establishes global owner coherence at each reachable live Apply boundary;
the prefix theorem never assumes ω is ModuleRun.

This proves preservation for every finite live prefix, budget pause and
stopped prefix as stated. Infinite divergence has all finite protected
prefixes, but supplies no return. No termination/progress conclusion is used.

## 4. Apply the invariant to the callee and reapply R339

Instantiate section 3 with
`B=κ·Callee(k_a,ηcaller,site_p)`, `o=ω`, and the active vector at the actual
Apply push. Define the matching callee-return boundary as the first reached
`State::Return(r_f)` with `frames=B`, immediately before that distinguished
Callee is popped. This definition names an observable boundary; it does not
assume that the boundary exists. Every earlier reachable prefix retains that
same frame payload. At the boundary s is empty; hence `current_owner=ω` and
the active vector is the saved A, including after arbitrarily many nested
Value calls, conditional branches, statement prefixes and pauses.

Now use the explicit R339 supplier
`ClosureReal₀(τ_f,v_f,h,ηc)` for `h=r_f.value`, with authentic source closure
`v_f=⟨λx.b,σc⟩`, binder x, body label k_b and saved ηc. This supplier is
required at this boundary, not inferred from return or site identity.
`return_value` pops the exact distinguished frame and:

1. allocates fresh internal handle d with executable
   `Delay{code:k_a,environment:ηcaller}` (`1169–1177`);
2. performs lookup by `r_f.value.0=h.0` (`1179`), cloning that actual
   executable closure's x, body and ηc (`1204–1212`);
3. takes `values[h].source` as provider metadata, and invokes
   `new_invocation(site_p,provider)` (`1225–1230`). Since owner is now ω,
   the fresh activation i has previous=ω, call=site_p and its actual
   provider metadata; SourceSite is never used as closure-handle identity;
4. computes the actual ηc' using `substitute_environment(ηc,r_f.dispatch)`
   (`1259`), pushes ReceiverReturn then ValueEntry (`1260–1274`), and calls
   execute(d,site_p). In ordinary K0 ηc'=ηc by the source argument above;
5. `execute` passes substitution=None (`2451–2453`); the Delay arm and
   substitute_environment therefore enter exactly k_a under ηcaller
   (`2454–2461,2509–2513`). `Receiving::delay` (`receiving.rs:135–148`)
   creates a view for d without changing its code/environment or forcing it.

Thus the actual successor of this matching return, whenever the entry step
is available within finite identity/allocation resources, is:

```text
state   = Evaluate(k_a,ηcaller)
frames  = κ·ReceiverReturn(i,ω)
             ·ValueEntry(x,false,None,k_b,ηc')
owner   = Invocation(i)
active  = A·[i].
```

No argument prefix ran before this invocation; the Delay is the whole stored
argument, not a separately selected existential Value-port witness. The
trace concerns exactly the returned h and its executable fields. Closure
storage and saved environments are append-only along these K0 paths; later
allocation at a new handle cannot replace h's executable or ηc's bindings.

## 5. Conditional argument boundary and the exact binding

Instantiate section 3 again, now with the entire protected vector
`B'=κ·ReceiverReturn(i,ω)·ValueEntry(x,false,None,k_b,ηc')`, baseline owner
Invocation(i), and active vector A·[i]. This use is essential: a local
ValueEntry action alone says nothing about nested argument evaluation.
Every actual finite argument-evaluation prefix retains *both* frames, and
every matching argument-return boundary `Return(r_a), frames=B'` restores
Invocation(i). Divergence, stop and pause do not assert such a boundary.

At an actual matching return, `return_value:1383–1415` pops only ValueEntry.
Because unit_pattern=false and record_pattern=None, it binds:

```text
r_a' = ReceivedValue { value:r_a.value, view:r_a.view,
                       dispatch:r_a.dispatch, interface:Value }
cell = old cells.len(); cells.push(Some(r_a'))
ηbody = extend(ηc', Binder::Parameter(x), cell)
state = Evaluate(k_b,ηbody)
frames = κ·ReceiverReturn(i,ω); owner = Invocation(i).
```

`bind/extend:2529–2541` create exactly that cell/environment; lookup at
`2488–2498` finds x in its first frame and resolves every other parameter
through parent ηc'. This proves identity of actual argument value, exact
formal, body and capture parent. It does not turn the returned value into a
typed source value. If the independent argument supplier gives source v_a
with `ValReal₀(τ_a,v_a,r_a.value)`, and the independent capture-transport
supplier gives `EnvReal₀(σc,ηc')`, pointwise lookup yields
`EnvReal₀(σc[x↦(τ_a,v_a)],ηbody)`. The same handle/view/dispatch are bound;
no new argument witness is chosen. The retained ReceiverReturn still closes
this exact i on an eventual body return; the present result does not prove
that body returns, has its declared result, or satisfies the future interface.

## 6. Parent application, missing suppliers and stop

Before this note, R339's input Evaluate(k_f,ηcaller) could not supply the
Callee frame its trace consumed. The candidate result now derives that frame
from the authentic Apply and preserves it through actual nested K0 callee
transitions, restores ω at its matching return, and composes the same proof
through the argument segment. The conditional R339 trace can therefore be
applied at that authentic boundary with its original explicit realization
premises. This reduces the immediate §6 C/M obstruction; it does not close C,
D3, M, S0, A/B or production. No source-qualified falsifying trace was found
by this static derivation; no exhaustive trace search is claimed.

Exact remaining requests for Luna, with unchanged parent and source owners:

| Request | First missing evidence and owners | Discriminating falsifier |
| - | - | - |
| R340-VREAL | Independent typing/evaluation supplies the R339 ValReal/ClosureReal for the actual callee return, including non-syntactic callees. Source Lambda/Name/If/Apply and runtime `evaluate`, `allocate`, `lookup`, `return_value` own the bridge. | Authentic well-typed K0 callee reaches a Function-typed value whose actual handle does not realize that same source closure/capture. |
| R340-CAPTURE | Relate actual saved/substituted ηc' to σc for the same h, then transport typed argument/environment into exact body. Owners: closure creation `856–877`, `substitute_environment`, `bind/extend/lookup`; independent closure/environment substitution proof. | A captured free parameter resolves to a different value after entry despite the stated source capture and argument relations. |
| R340-M-REST | All source cases of preservation/progress, argument/body/result realization and same-witness result/future interface; independent four-port Function interpretation plus candidate Call producer/consumer owners remain required. | Authentic accepted typed execution reaches a wrong result/interface or unavailable normal step beyond the conditional prefix. |

No implementation TODO is justified: `NO_SAFE_CODE_SLICE`; no compiler defect
was established. The next in-contract action is freeze this candidate for
Luna's fresh non-contributor review together with the independent source
census. Any new source/implementation supplier, semantic change or lease needs
Luna's allocation. The author cannot certify the combined result.

Checks: read-only source/authority inspection, dependency SHA-256 comparison,
and manual case coverage against the actual `step/evaluate/return_value`
owners. No tests, Cargo/builds, probes, source edits, external contact, Git,
scratch files or descendants. Resource grant: 1,200 seconds, charged in full;
no renewal/carryover. Requested Sol/high; effective observed model/effort
UNKNOWN. Runtime identity `/root/r340_apply_continuation_prover`, session
`4a30d8bc-cf58-442a-ac35-a6026b4e35b5`; no model-switch claim.

Only new paths are this note and
`tasks/agent-loop/inbox/20261023-r340-k0-continuation-prover.md`. Revision 1
freezes on submission. Writer cessation follows the frozen inbox receipt;
there are no descendant or scratch leases. Review and parent status belong
to Luna.

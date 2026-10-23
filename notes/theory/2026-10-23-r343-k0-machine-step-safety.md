# R343 — K0 reachable machine-step preservation and progress

Status: **frozen producer candidate, revision 1; fresh independent review required**.
Assignment `R343-K0-MACHINE-STEP`, author
`/root/r343_k0_machine_step_prover`. This is a constructive hand proof and
source correspondence argument. It is not independent certification,
machine checking, full M, or production authority.

## 1. Parent, statement and explicit boundary

The parent remains the user-directed full Yulang2/Simple-sub source/native
theorem and original A/B, with the original quantifiers and accepted source
domain. The immediate application is audit §§4.1, 5, 6 C/M and S, and 10.3:
supply the bounded D3 machine-state preservation/progress and semantic
unavailability exclusion left open by R340–R342. This packet retains the
independent D0 judgment and finite type algebra of R336 revision 4.

Fix arbitrary authentic `ValidK0(s)`, a particular independent derivation
`Droot : ∅ ⊢₀ body(s) : Troot ! Eroot`, and the ordinary RuntimeProgram P
constructed from that same authentic HIR/candidate with no extra source
roots. The independent derivation is supplied before execution. Neither
`NativeComplete₀`, graph/model existence, `unresolved().is_empty()`, nor an
observed output type is a premise of the machine theorem. In the separate
S0 application in §9, R341 supplies Droot under its unchanged four premises.

The entry is exactly `P.start_source_schedule(&def_s)`, hence selected
Definition entry through `RuntimeProgram::start/start_with_schedule`,
`begin_root` and `complete_selected_definition`. The same proof covers
`P.start(&def_s, &[])`. It does not cover arbitrary injected execution-root
schedules. For the sole definition and no expression/module/import roots,
P's authentic schedule is either empty or `[Definition(def_s)]
(`program.rs`, definition publication at 980–1004). Both cases enter this
same body once with environment 0 and its actual Root frame.

Subject to the ordinary execution of Rust operations returning rather than
host allocation failure/panic, the candidate theorem is:

* Every active state reachable by any finite sequence of actual `step`
  calls from that start has the independent typed-state certificate in §4.
* Its next `step` either returns Running with a preserved certificate,
  completes the selected definition with that source result at Troot, or
  stops with the checked resource refusal `Unavailable(IdentityExhausted)`.
  Every other `Unavailable` is unreachable.
* A depleted `run` budget returns `ResourceExhausted { steps }` with the
  same live state and certificate. A later `run` resumes it. It publishes no
  Completed result.
* A normally stopped state returns its same Completed outcome on further
  `step/run` calls. An identity-refused state similarly remains stopped;
  it is not a resumable budget pause.

All quantification over finite prefixes includes prefixes ending during
callee, whole argument, or body evaluation. No return existence, program
termination, solver termination, host-OOM protection or full native
receiver/result/future-interface interpretation is claimed.

The accepted K0 grammar is unchanged: canonical decoder-valid literals,
enclosing-parameter Name, simple annotation-free Value Lambda, Apply,
else-complete If, Group and binding-free Block/StatementBlock. Authentic
DecodedString remains only the excluded interpolation carrier case, not a
new standalone source constructor. The decoder arm is nevertheless covered
conditionally on its authentic source ownership. Zero-test If, if admitted
by the authentic carrier, directly selects its explicit else; no additional
syntactic restriction is needed. No Comp, local binding, annotation, record,
default, variant/case, operation/handler, member/operator, global/import or
whole-module case is promoted.

## 2. Frozen authority, inputs and authors

Baseline supplied by Luna: `research/simple-sub-intrusion` commit
`2ddee9031fc43bb5fdf7b93424b86822de599407`. No Git command was used.
Every following direct pin matched before construction of this candidate.

| Input | SHA-256 |
| --- | --- |
| R343 contract rev1, `tasks/agent-loop/sprints/r343-k0-machine-step-safety-20261023.md` | `e6fdba88c644fdc094ea451f83fd8ce35d87d9b513db9a99f06e5bd3aa82fa16` |
| User audit, `docs/Yulang Simple-sub 拡張：全体証明への移行監査・証明設計.md` | `b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895` |
| R336 D0/D1 rev4, `notes/theory/2026-10-23-r336-k0-d0-d1-rev4.md` | `4bcbe71ec9f2372baca884e3db737c16fc19ad2a51103965ade5ca4c2ecf4973` |
| R339 D3, `notes/theory/2026-10-23-r339-k0-machine-call-simulation.md` | `4301ed7e184915e75646809102a477f8d4b27f874478e364c03886ae1cfd2666` |
| R340 proof, `notes/theory/2026-10-23-r340-k0-apply-continuation.md` | `7ae75ef26d6bfa441989e9655dda89fbed2927d0061f5d8445246d587a0d7737` |
| R340 final census, `notes/theory/2026-10-23-r340-k0-machine-continuation-source-census.md` | `de3902d834a68f0d4f5b269f4bddac7d900d44bfe8dc118b05b451372cf24078` |
| R341 proof, `notes/theory/2026-10-23-r341-k0-source-constraint-retention.md` | `f8607d11c417734c1a7fb5aafe1af7ca78a587c5f5e7189c8cf3dcbc2064343f` |
| R341 accepted outcome, `tasks/agent-loop/sprints/r341-k0-source-constraint-retention-20261023-outcome.md` | `7e5a5905a49335cf7c314da6fd33e800a9552109b638ee5914b050f2b20602bc` |
| R342 proof, `notes/theory/2026-10-23-r342-k0-value-environment-realization.md` | `ab5b86070acbb75639172ce96182a1ea08bdc8fe22f185d691fe542a80fee420` |
| R342 accepted outcome rev2, `tasks/agent-loop/sprints/r342-k0-value-environment-realization-20261023-outcome.md` | `93dff5d9704c747366d822eff588a348f346eaff5270a47882a03928e6e1b988` |
| R342 census, `notes/theory/2026-10-23-r342-k0-value-environment-source-census.md` | `18a4eef622ee8feacc8db48d4360321fdcbd8d5f330636866705f42b8551b1b5` |
| R343 primary census rev1, `notes/theory/2026-10-23-r343-k0-machine-step-source-census.md` | `0816397bd4e6ef493a050f95b13e3e10d90a67fe98e804e577fb33bddecfbe1a` |

| Read-only runtime source | SHA-256 |
| --- | --- |
| `tools/inference-playground/src/runtime/machine.rs` | `02adc26bcd58cca488a40e78289a264751146d7900c2897db19068b279a8d840` |
| `tools/inference-playground/src/runtime/program.rs` | `df58f9a1d60e39fafe6d85b1e50331b35fde2a9142a2eaea84ad028d3048fdb0` |
| `tools/inference-playground/src/runtime/dispatch.rs` | `f45057373f2ed3a7b6ce915611db093015fb93cdb05984a5e3b23cfd44720873` |
| `tools/inference-playground/src/runtime/literal.rs` | `2fff177a7ba0cabb4930251e1facc8f9be701ff3ec7baa695ce4c182fa1da35f` |
| `tools/inference-playground/src/runtime/receiving.rs` | `2170a3bcbc6710ce3fbf721a05129117f8266b9ecf21c67136db918815303551` |

Sole new proof author: `/root/r343_k0_machine_step_prover`; no descendants.
Reused proof authors are R336's primary and
`/root/r336_k0_algebra_prover`, `/root/r340_apply_continuation_prover`,
`/root/r341_k0_source_retention_prover`, and
`/root/r342_value_environment_prover`, as identified in the pinned artifacts;
source censuses and acceptance receipts belong to Luna `/root`. Historical
author/model labels do not independently establish authority. Their review
dispositions are used only as stated in the pinned acceptance receipts.

## 3. Independent value, environment and storage facts

Use exactly R342 §3's finite source values `Lit(site,c)` and
`Clos(siteλ,x,b,σc)`, persistent source environments, `TypedVal₀`,
`TypedEnv₀`, `CodeReal₀`, `Repr₀`, `EnvRep₀`, `RecvReal₀` and
`EnvReal₀`. Their definitions mention no future execution. In particular a
closure's typing witness contains an independent derivation

```text
Dc : Γc,x:Ac ⊢₀ b:Bc ! EBc,
EAc ⊆ ERc, EBc ⊆ ERc,
Fun(Ac,EAc,ERc,Bc) ≤V F,
EnvReal₀(Γc,σc,ηc),
executables[hf.0] = Closure(x,false,None,Value,None,kb,ηc).
```

The last equation names the **actual saved numeric environment** in that
actual handle's executable. It cannot be replaced by an environment with
merely equal lookups or by the Lambda provider site.

R342 §4 proves, in the entire least finite bounded-lattice preorder, including
Value subsumption and arbitrary finite joins/meets:

```text
TypedVal₀(v,F) ∧ F ≤V Fun(A,EA,K,R)
  ⇒ v = Clos(siteλ,x,b,σc),
     A ≤V Ac, EA ⊆ EAc, ERc ⊆ K, Bc ≤V R;
TypedVal₀(v,U) ∧ U ≤V Bool ⇒ v is a Boolean literal.
```

These are independent canonical-form/inversion lemmas, not the finite-return
theorem. They can therefore be used in the induction below at a Return
certificate already established by preservation. No assumption that a
Function-shaped expression returns a closure is made. Typed values are
closed under Value subsumption; an inhabited bottom value is excluded by
R342's value-introduction inversion.

The storage part `Store₀(P,M,G)` of the new certificate records:

1. All used labels/sites are the authentic constructor-derived CodeReal
   labels/sites in P. Lambda entries keep the exact formal/body and Value
   role; all Names use their exact parameter ID and Observe. No excluded
   instruction or frame is introduced by K0 lowering.
2. Every environment index mentioned by a focus, closure, Delay or frame is
   valid. Environment 0 has no binder or parent; every new parameter
   environment points to an earlier valid environment and a populated valid
   parameter cell. A ghost source environment object is associated with each
   such environment and has the exact EnvRep lookups. The TypedEnv witnesses
   required by focus, closure or suspended action are retained explicitly.
3. Every source-value handle in the focus, cells or certificates has its
   exact Repr witness. All allocated K0 values are either such literal/closure
   representations, or internal argument Delays. A Delay has its own fresh
   handle and executable `Delay(ka,ηcaller)` with valid whole-argument label
   and caller environment; it is not asserted to be a TypedVal. Each has an
   append-only ghost allocation record identifying its actual Apply event.
   No Delay is placed in a K0 parameter cell or returned as a source value.
4. Every used received record has `interface=Value`, a valid existing view
   whose stored value is exactly its handle, and `dispatch=None`.
   Ground/opaque/Delay views have their actual ground/unknown flag and
   `image=None`; no absence of coverage is a negative protection certificate.
   Parameter cells retain the entire same received record on binding.
5. P has `dictionaries=None` and no operation-v1 route. Environments have
   default dispatch; no K0 transition changes it. R342 §5's constructor
   argument supplies the no-dictionary fact for the same ordinary K0 P.
   Hence initializer/substitute-environment and dispatch-Name take their
   identity branches; no algebraic commutativity/idempotence of dispatch is
   assumed. The direct-formal-root probe returns None: the argument root
   is either not Name or is a parameter Name with Observe, never Execute.
6. No receiving boundaries/images, executing views, handlers, continuations,
   requests, templates or tuple prefixes are allocated on these paths.
   Name consumption may append an authentic receipt for its exact
   `(current_owner,view,site,None)`. Receipts do not change the view or value.
7. The sole Definition cache cell has the root protocol in §4. Parameter
   cells have distinct fresh indices after this initial cell; they are never
   overwritten. Values, executables, views, parameter cells and environments
   are append-only. Closure capture witnesses therefore persist across
   arbitrarily many later finite steps.

These are syntactic storage equations with independent source typing
witnesses. Store₀ is not defined by reaching success. The append-only fact
comes from actual `allocate/data/ground_data`, `bind/extend`, receiving
constructors and the reachable frame arms. The sole overwrite is root cache
publication to its separate cell. Source closures/environments stay finite:
a new closure captures the already existing finite source environment; a new
parameter frame extends one with an already existing finite value. No K0
binding creates a recursive cell knot.

## 4. Typed continuation and machine-state relation

Stacks are written bottom to top. Define a ghost continuation certificate K
whose runtime erasure is the **entire actual frame vector** κ, including the
Root. `Accept(K,T)` means K accepts an independently typed source value at T
and ultimately produces the fixed selected result type Troot. This judgment
has the rule

```text
Accept(K,U) ∧ T ≤V U ⇒ Accept(K,T).
```

This changes no runtime frame and adds no source expression typing rule.
It composes the existing value-subsumption rule with the waiting consumer.
The following are all structural constructors of K; each retains all
displayed independent derivations, source IDs and environments. K has no
constructor justified by a machine's success, a type tag, or graph existence.

| Top source action / exact runtime frame | Input and retained obligations |
| --- | --- |
| Selected result / `Root {next,cell}` | Accepts Troot. It is the sole bottom frame, cell is exactly selected, cache is None and selected is initializing; next is the exhausted authentic schedule ordinal. Current owner at this layer is ModuleRun. |
| Callee of p=f a / `Callee {argument:ka,environment:ηcaller,site:sitep}` | Accepts F from Dp's `Df:Γ⊢f:F!EF`; retains `Da:Γ⊢a:A!EA`, `F≤Fun(A,EA,Keff,R)`, `EF⊆Ep`, `Keff⊆Ep`, caller σ/η with EnvReal, exact p/f/a labels/sites, and a suffix accepting R. |
| Whole argument of a fixed call / `ValueEntry {x,false,None,kb,ηc}` | Accepts Ac; suffix is that same call's ReceiverReturn below. Retains call witness W below, including Da at A with `A≤Ac`; no argument result is assumed. |
| Result of that call / `ReceiverReturn {activation:i,previous:ω}` | Accepts Bc, with `Bc≤R` and a suffix accepting R. Retains W and its phase, either waiting for the argument with the matching ValueEntry above, or evaluating/returning the exact body after binding. |
| Ordered If test j / `Condition {conditional:codeIf,arm:j,environment:η}` | Accepts Uj with `Uj≤Bool`; retains all D0 test/branch derivations, every branch type≤Rif, all child-effect inclusions, explicit else, `0≤j<arms.len()`, exact codeIf and its σ/η, and suffix accepting Rif. |
| Statement prefix j / `BlockExpression {block,next:j+1,environment:η}` | Accepts the actual prefix's Uj; retains the full binding-free block D0 derivation, all ordered remaining prefixes/final expression and exact block/σ/η, with suffix accepting Rblock. `j<statements.len()` and the statement is Expression. |

Binding-free Block has no Local frame; Group has no runtime frame. A Group
child or selected If/block-final child uses the same suffix via its source
subtype to the enclosing result. Final expression subsumption similarly
changes Accept, rather than creating a synthetic runtime frame.

Each Callee certificate retains its real Dp, including final Value
subsumptions. Stripping these exposes an R accepted by the original suffix:
compose the stripped `R≤Tp` with `Accept(suffix,Tp)`. This device also handles
all other final source subsumptions without a new runtime instruction.

The call witness W is a finite ghost record containing

```text
(p, sitep, Dp, f, a, Da, σcaller, ηcaller,
 vf, hf, received_callee, siteλ, x, b, kb, σc, ηc, Dc,
 Ac,EAc,ERc,Bc, A,EA,Keff,R,
 hδ, viewδ, Delay(ka,ηcaller), i, ω, phase).
```

It includes actual callee RecvReal, the intrinsic closure typing/capture
witness from §3, four-port inequalities, actual fresh inert Delay and view,
and the one actual invocation descriptor `(call=sitep,provider=siteλ)`.
The descriptor's provider is a source site; `hf` and its executable/capture
remain separate fields. In phase `Argument`, the matching ValueEntry is
above its ReceiverReturn and the source argument runs in **ηcaller**. In
phase `Body`, W also retains the actual returned argument `(va,ra)` with
RecvReal at Ac and the new exact environment

```text
ηbody = bind(ηc,Parameter(x),ra),
EnvReal₀(Γc[x:Ac],σc[x↦va],ηbody).
```

The body runs in ηbody. W keeps the original caller environment and Delay
throughout; neither is replaced by ηc or ηbody. Historical completed W
records may remain as ghost history for allocated Delays; they are not live
frames or invocation authorities.

The owner component is not inferred from provider sites. Enumerate all
ReceiverReturn frames in κ from bottom to top as

```text
(i1,ModuleRun), (i2,Invocation(i1)), …, (im,Invocation(i(m−1))).
```

They have distinct IDs and active descriptors; these IDs are exactly
`active_receivers`. Current owner is ModuleRun when m=0 and Invocation(im)
otherwise. Every other descriptor is inactive. `next_receiver` equals
`invocations.len()`; descriptors are allocated in that order. Each local
action/focus carries the owner of its stack segment. In particular an
argument executes under its new invocation, while its lexical environment
remains the original caller's; this distinction is mandatory.

Define `TState₀(Droot;M,G)` independently of execution as Store₀, such a K
with exact erasure κ and owner component, and one of:

* **Eval:** state is `Evaluate(ke,η)`, with authentic source e, CodeReal,
  `D:Γ⊢e:T!E`, EnvReal(Γ,σ,η), `Accept(K,T)` and `E⊆Eroot`.
* **Ret:** state is `Return(r)`, with an independently typed source value v
  and `RecvReal₀(T,v,r)`, `Accept(K,T)`, and all suspended derivations/effect
  bounds retained. K is nonempty; its bottom is the selected Root.

The exact effect credit E⊆Eroot is available on every focus. A callee uses
EF⊆Ep; an argument uses `EA⊆EAc⊆ERc⊆Keff⊆Ep`; a body uses
`EBc⊆ERc⊆Keff⊆Ep`; If/Group/block children use their D0 child inclusion.
Compose with the parent's credit. No general Effect-subsumption rule is
added and no symbolic latent Effect is set to empty. The runtime event trace
of this fragment is empty because the source has no event constructor; this
observation does not interpret a higher-order native future interface.

For terminal states use separate predicates. `Done₀` names selected cell,
actual cached received record r, source v with `σempty⊢body(s)⇓v` in R342's
independent finite evaluation notation, RecvReal at Troot, Completed(r.value),
empty stack and ModuleRun owner. `RefusedId₀` names Stopped(Unavailable
IdentityExhausted), the checked failing invocation allocation and absence of
Completed publication. It makes no resumability or active-state typing claim
after the resource refusal has popped its Callee frame.

Actual finite reachability is defined separately using the source `step`
implementation. It is not a premise inside TState₀, TypedVal or EnvReal.
The theorem proves existence of G along that operational reachability.

## 5. Initialization and evaluate-step preservation

`start_with_schedule` constructs empty values/executables/frames/receiving,
one parentless environment 0, None root cell, ModuleRun owner, zero receiver
counter and no invocations. `start` finds the selected authentic DefId in
the constructor's definition_indices. The only authentic schedule slot,
if present, is unique; therefore no MissingDefinition,
ModuleInitializationOrder or invalid-expression guard fails.

With an empty schedule, `complete_selected_definition(0,selected)` pushes
Root(next=0,cell=selected); with the singleton schedule `begin_root(0)`
pushes Root(next=1,cell=selected). The cell is None, the initializer is this
body and `initializer_environment(selected,0)=0` because dictionaries=None.
Both enter Evaluate(kbody,0) with the initializing marker. The empty
source environment is TypedEnv and EnvRep at 0. Droot and Accept(Root,Troot)
give TState₀ with Eroot⊆Eroot. Temporary
Stopped(Running) inside constructors/`step` is not a state returned by this
entry or by a successful active step.

Now suppose TState₀ is Eval. Strip final D0 Value-subsumptions and use input
subsumption of Accept. Invert the exposed source rule. The actual evaluate
fetch uses CodeReal's valid label, then takes exactly its corresponding arm.

| Authentic evaluate case | New certificate and exact source operation |
| --- | --- |
| Literal | `ground_data` allocates fresh h with that literal's authentic site and decoded payload, and `ground` allocates a view whose value is h. Integer validity follows from nonempty ASCII digits; String validity is the unchanged decoder-valid K0 spelling premise. The independent literal rule gives `Atom(c)≤T`; therefore the new actual Return has RecvReal at T and the same K. DecodedString, at its permitted owning boundary, directly stores its given payload. |
| Parameter Name | EnvReal supplies the exact most-recent parameter cell, populated record r and typed lookup value v. All environment/cell/view indices are valid by Store₀. `dispatch_name` returns r unchanged. `consume`'s view/value guard holds and Observe returns that same r; the new receipt has this source Name site and current invocation owner. Parameter inversion and Value subsumption give RecvReal at T. No missing binding, uninitialized cell or Execute arm is reachable. |
| Value Lambda | Construct source `Clos(siteλ,x,b,σ)` using current σ. The inverted D supplies its independent body derivation and intrinsic Function witness. `data/allocate` append h and its exact closure executable with **current η**, then an opaque matching view. Retain the input EnvReal for that exact capture. This establishes TypedVal/Repr/RecvReal at the source type before any invocation exists. |
| Apply p=f a | Push precisely Callee(ka,ηcaller,sitep) and retain Dp, Da, caller σ/η and four-port/outer-Effect premises in its certificate. Enter f with its original Df, same environment and owner; its EF credit follows from Dp. This constructs the waiting Callee rather than assuming one was already present. |
| Group | Authentic Forward enters its exact child with the same η, owner and K. Child Value inclusion and Accept subsumption give the required input type; its Effect inclusion gives the new credit. No Group value/site replaces a child's eventual allocation site. |
| Else-complete If | For a first test push Condition with j=0 and its authentic code/σ/η/all derivations, then enter that exact test. Its type≤Bool and Effect inclusion establish the case. If there are no tests, enter the explicit else directly with Value/Effect inclusion into the same K. No absent-else/unit-discard branch is taken. |
| Binding-free Block/StatementBlock | `begin_local` has the authentic matching instruction. Block with zero bindings enters its final expression. StatementBlock enters the first Expression prefix with BlockExpression(next=1), or its final expression if there are no prefixes. Record exact block/σ/η/order/all remaining derivations. Prefix type is unrestricted but independently derived; final type is below the block result, and every child's Effect is included. No Local frame/cell/initializer is created. |

These evaluate cases append only the permitted storage objects and do not
change owners. Fresh executable insertion keys are fresh value indices; no
old closure or capture is overwritten. EnvRep/RecvReal of suspended layers
persist. Each case therefore either returns a valid Ret certificate or
another Eval certificate. No evaluate case has a checked IdentityExhausted
branch in authentic K0; host allocations are outside this resource claim.

## 6. Return-step preservation: every authentic frame

Suppose TState₀ is Ret. By following the finite Accept derivation's input
subsumptions, subsume the same source value/received record to the top frame's
declared input. This is ordinary value subsumption, not a different port
witness. The exact-erasure and Root clauses ensure a frame exists; the raw
`return_value` empty-stack completion arm is unreachable on this selected
root path.

### Callee

The Callee certificate supplies F and Dp's authentic demand. RecvReal and
canonical form in §3 expose **this** returned source closure vf and **this**
actual executable at hf, including its exact Dc, σc and ηc. The four-port
inversion gives `A≤Ac`, `EA⊆EAc`, `ERc⊆Keff`, `Bc≤R` together, from that
single intrinsic closure witness and that single demand.

The actual frame arm first allocates fresh internal hδ with
`Delay {code:ka,environment:ηcaller}` at sitep. `direct_formal_root` is None
by Observe, and `receiving.delay(hδ,None)` makes a valid unknown view of hδ.
This does not execute an argument prefix or manufacture an argument value.
Lookup at hf.0 takes the closure arm; the primitive, continuation, operation,
nonclosure and Computation-entry arms are impossible by Repr and K0 role.

`new_invocation(sitep,values[hf].source)` has two outcomes. At counter overflow
its checked_add fails with IdentityExhausted before descriptor/active-owner
mutation; the machine stops as described in §8. Otherwise it appends exactly
i=old next_receiver, descriptor `(sitep,siteλ,active=true)` and active i,
sets current owner Invocation(i) and saves the exact previous ω. It does not
identify hf with siteλ. The no-dictionary substitute helper returns **ηc**.
The actual arm pushes ReceiverReturn(i,ω), then ValueEntry(x,false,None,kb,ηc),
and executes **hδ**, whose exact executable switches to Evaluate(ka,ηcaller).
Its substitution argument is None. No ExpectedComputation branch can occur.

Construct W in phase Argument from these actual fields. The suffix K accepts
R; ReceiverReturn accepts Bc by Bc≤R. Its matching ValueEntry accepts Ac,
thus accepts Da's A by A≤Ac. The new focus has Da, caller EnvReal and the
Effect chain `EA⊆EAc⊆ERc⊆Keff⊆Ep⊆Eroot`. The owner chain extends by
exactly i. This proves a typed **argument-entry** successor without assuming
that argument evaluation returns.

### ValueEntry

The exact Arg-phase W and input subsumption supply RecvReal(Ac,va,ra).
This frame's `unit_pattern=false,record_pattern=None` equations exclude
the unit check and record/default consumers. `bind` appends a populated cell
containing `{value:ra.value,view:ra.view,dispatch:ra.dispatch,interface:Value}`
and extends **ηc** under the exact x from hf. Since ra was already Value,
this is the same record. R342 §5's lookup/extension lemma supplies
EnvReal for `σc[x↦va]` at the actual ηbody. Fresh cell identity and most-recent
binder lookup handle repeated dynamic activations of the same source x;
distinct existing binders keep their cells.

Update that same W to phase Body, storing va/ra/ηbody, and enter Evaluate(kb,
ηbody) with **Dc**, not a body derivation reconstructed from site equality.
The matching ReceiverReturn remains, accepting Bc. The body Effect credit is
`EBc⊆ERc⊆Keff⊆Ep⊆Eroot`. Owner and active receivers do not change.
No body return is assumed or promised.

### ReceiverReturn

This frame's Body-phase W accepts the same received body value at Bc.
There is no outstanding ValueEntry for i above it. The owner-chain equation
makes i the current and top active invocation and makes ω exactly its
predecessor. Its descriptor exists and is active. Consequently every
`leave_owner(Invocation(i),true,ω)` guard succeeds: current owner matches,
active_receivers.pop() is Some(i), the descriptor exists and was active.
The helper marks precisely i inactive and restores ω.

The actual new Return preserves value, view and dispatch and sets interface
Value, which it already had. Subsuming `Bc≤R` and then using the suffix
Accept gives its typed Ret certificate. Remove only this ReceiverReturn
certificate; retain W as historical provenance if needed for the inert
Delay's allocation record. This closes the owner step for every nested call,
not just one local frame with an assumed outer owner.

### Condition

The current source value has type Uj≤Bool. Bool canonical form and Repr give
exactly the Boolean payload that the machine indexes; ExpectedBoolean is
excluded before choosing a branch. The frame's authentic If instruction and
valid j justify `arms[j]`; the explicit else excludes DiscardToUnit.

If true, enter the exact j-th branch with its saved σ/η and independent
branch derivation. Its Value inclusion uses the suffix accepting Rif; its
Effect inclusion supplies the focus credit. If false with another test,
increment j within arms.len(), retain the same If/code/σ/η, push the new
Condition, and enter exactly that next test with its D0 premises. If all
tests are false, enter the explicit else in the same environment. No branch
is retyped using the observed constant and no unselected branch premise is
discarded from the original source derivation. Owner is unchanged.

### BlockExpression

Its authentic binding-free StatementBlock and saved next ordinal justify
`begin_local`. The just-returned prefix's independently typed value is
discarded. Enter the next ordered Expression with a new BlockExpression, or
the exact final expression when next equals statements.len(). The saved
σ/η and all remaining derivations are unchanged. D0 supplies each child's
Effect credit and the final Value inclusion into the original suffix.
There is no local cell mutation, Local frame or binding case.

### Root

At the only Root, input subsumption yields RecvReal(Troot,v,r). All nested
ReceiverReturn frames are already gone, so the owner chain gives ModuleRun,
empty active_receivers and inactive completed descriptors. The frame's cell
is the selected cache cell; the authentic schedule is exhausted at next.

`return_value` stores the same r (its interface is already Value), removes
that cell's initializing marker and calls `begin_root(next)`. Its ModuleRun
guard holds. No later schedule slot exists, so it calls
`complete_selected_definition(next,selected)`, reads **this** populated cell
and installs Stopped(Completed(r.value)). It does not re-evaluate the root or
manufacture module Unit. Stack is now empty.

To establish Done₀'s independent source-result clause, now and only now use
accepted R342 §6. The finite actual prefix from the initial body Evaluate to
the state just before this Root pop is a matching RetSeg for the **same**
body/empty environment and protected Root. Root was installed at entry and
has not been popped or overwritten by any preceding active transition.
R340's protected-prefix result, or the explicit stack preservation above,
gives the required segment boundary. R342 produces
`σempty⊢body(s)⇓vroot` and RecvReal(Troot,vroot,r) for this exact r.value.
Thus the completed result is the selected source result with its source
type. This use observes a finite return already present in the trace; it
does not supply a typing premise for any earlier state or future result.

These six Return-frame cases exhaust the reachable ordinary frame set.
Group has no frame, and all non-K0 frames listed in the Rust enum lack a
constructor in the induction. This is derived from the authentic lowered
instructions and returned closure records, rather than assumed from a
hand-written transition model.

## 7. Reachability induction and guard census

Initialization supplies TState₀. Induct on the number of actual `step` calls,
simultaneously for all G/foci/continuations/source environments and all
dynamic call instances. §§5–6 construct the successor ghost certificate for
each active success. Their only checked resource error is the Callee
invocation allocator. A completed/refused state stays stopped under `step`.
Therefore every finite prefix has an active TState₀ or the appropriate
Done₀/RefusedId₀ terminal; none reaches a semantic Unavailable. The induction
uses transition count, not source-tree size, and does not assume termination
when a Lambda site or binder is revisited dynamically.

The following table includes direct indexing prerequisites as well as
explicit Result errors. A valid index is necessary even when Rust would
panic rather than return Unavailable; no general panic/OOM protection is
inferred from these typed-path index arguments.

| Actual owner/guard | Supplier at the transition; falsifier |
| --- | --- |
| `start`, definition lookup; schedule duplicate/expression validation | Exact constructed selected DefId and authentic empty/singleton source schedule. A same-HIR K0 constructor emitting another/missing root falsifies initialization. Arbitrary external schedules are outside this fixed entry. |
| `evaluate`, code.get | CodeReal for the focus and every child/body label. A constructor-derived label outside P.code or wrong source site is a source-correspondence falsifier. |
| Integer/String `LiteralDecoding` | Original syntactically decoder-valid K0 spellings, checked against the pinned `literal.rs::integer/string` functions rather than evaluation success. A permitted spelling rejected there falsifies this exact premise. |
| Name MissingBinding / UninitializedBinding; cells[cell] index | Exact EnvReal populated lookup, valid environment parent/cell indices; Observe from parameter-role lowering. A reached same-ID lexical lookup returning None, a wrong cell or an unpopulated cell falsifies Store₀ preservation at bind/extend/lookup. |
| `dispatch_name`, initializer/substitute environment | dictionaries=None is supplied by ordinary K0 construction, so helpers return identity without executing generic dictionary code. A K0 source enabling contextual dispatch is the exact constructor falsifier; the generic present-dictionary identity lemma is insufficient for progress. |
| `consume`, matches_value and receipt | Valid view/handle from constructors and same-record cells; exact Value interface/Observe. Invalid view indexing or a mismatched view/handle falsifies the receiving/bind invariant. No MissingConsumptionEvidence or RootComp execution branch is reached. |
| `Frame::Callee`, values[hf], executable lookup and ExpectedCallable | RecvReal plus canonical form and exact h-keyed closure executable; all fields are from that same object. A typed source value whose actual handle lacks its Repr executable is the precise missing-source-invariant falsifier. |
| Callee Delay / `direct_formal_root` / `execute_with_substitution` | Whole ka/ηcaller retained by Callee; Observe implies inherited=None; fresh hδ has exact Delay executable. Thus ExpectedComputation is excluded. Executing another label/environment would falsify W. |
| `new_invocation`, checked_add | Overflow alone gives IdentityExhausted. Otherwise next_receiver=len(invocations), append at i, owner-chain extension. Wrong descriptor/active order is an owner falsifier. |
| `ValueEntry`, unit/record branches; bind/extend parent index | Exact closure's false/None fields, EnvReal at saved ηc, actual returned ra and fresh populated cell. There is no record/default/unit guard in this reachable case. |
| `Condition`, values[h], Boolean and arms[j] | RecvReal, Bool canonical form, CodeReal If, certified j in range and explicit else. A non-Bool typed reached test or wrong arm selection falsifies these independent facts. |
| `begin_local`, matching Block/StatementBlock and ordinal | Exact saved authentic block; bindings empty, all statements Expressions, next in range or final boundary. No Local/recursive-initializer branch can execute. |
| `leave_owner`, current owner / active pop / descriptor activity | The full ReceiverReturn/active-receiver chain, established inductively for all nested calls. A valid reachable chain whose top differs falsifies the owner induction. |
| `Frame::Root`, cache cell and begin_root ModuleRun guard | Sole selected cell, bottom Root, no active invocation, exhausted next and actual returned r. Completion reading another handle falsifies the selected-root protocol. |
| `step`, State dispatch / empty Return frame | Every active state is Eval or Ret with a bottom Root; no EnterTemplate, Request or IntegerProduct producer is reached. Stopped outcomes are returned without another transition. A new authentic K0 producer for another state/frame is a coverage finding requiring its inclusion. |

No source-qualified counterexample or missing local supplier was found in
this hand derivation. The proposed result still requires fresh review of
the whole certificate and its source correspondence; this statement is a
producer claim, not a review disposition.

## 8. Budget pauses, identity refusal and completion

`step` increments `steps` with saturating_add; no semantic refusal is
introduced by saturation. It moves the state temporarily to Stopped(Running)
while executing the arm; §§5–6 show the actual successful arm sets a new
Eval/Ret or Completed state. Any checked error becomes Stopped(Unavailable).
The only such reachable error here is new_invocation's IdentityExhausted.

At that refusal the Callee has been popped and an inert Delay/view may have
been appended, but the checked overflow happens before appending a new
invocation, changing the owner or publishing a result. `step` installs the
stopped resource error. Nothing exposes a partial Completed result, and
further `step/run` returns the same refusal. TState₀ is deliberately not
asserted for this stopped, partially advanced internal configuration.
No claim about exact rollback or capacity restoration is necessary.

`run(budget)` makes at most budget calls to step. Any non-Running outcome is
returned immediately. If the budget is depleted while the state is active,
the final match returns ResourceExhausted with the current saturated step
counter and makes **no** state/frame/storage/owner mutation. Thus the last
TState₀ witness remains available for a later run. A zero budget pauses an
active machine immediately. If state is already stopped, the same final
match returns its terminal outcome even at zero budget; it does not relabel
completion/refusal as a budget pause. No ResourceExhausted is stored as a
semantic State on these calls.

Only Done₀ establishes selected-definition completion with its actual
source result/type. Running is an advance, ResourceExhausted is a resumable
caller pause, IdentityExhausted is a stopped checked resource refusal, and
all other Unavailable variants are excluded under the explicit premises.
Unchecked vector/hash/string allocation behavior is outside the assertion.

## 9. Apply the result to the original proof obligation

This candidate supplies `R343-K0-STEP` and `R343-K0-SEMANTIC-AVAILABLE` for
all authentic K0 states/frames from an independently typed root. It extends
R340's call prefix using the actual callee/Delay/argument/body/owner at every
reachable stage and R342's independent value/environment definitions and
canonical-form lemmas. Future argument/body return is never an induction
premise. When completion is actually reached, R342's accepted finite-return
theorem identifies the same selected source result, as used in §6.

Now take arbitrary s,S,ρ satisfying the **same four** accepted S0 premises:

```text
ValidK0(s) ∧ NativeComplete₀(s,S) ∧ ρ ⊨ H(S) ∧ Reifiable₀(ρ).
```

R341 derives independent
`∅⊢₀ body(s):ρ(v_s)!ρ(ε_s)`. If the ordinary RuntimeProgram for the same
HIR/candidate has been constructed as pinned here and is entered by the
selected-definition path, instantiate this packet with that derivation.
Every finite active execution prefix then preserves TState₀, semantic
Unavailable is excluded, caller-budget pauses are resumable, and any normal
completion is the actual selected result at `ρ(v_s)`. This is a concrete
conditional safety composition for audit S/D3, preserving every original
S0 premise. It proves neither that ρ exists nor that the candidate/runtime
construction or evaluation terminates. RuntimeProgram construction failures
before this entry are not silently converted into a successful machine.

Full M remains OPEN: the mathematical interpretation of native
receiver/result/future interfaces and effect/continuation obligations is not
provided by this finite typed K0 step relation. F1/FK1, arbitrary foreign
continuations, Comp/operation/handler cases, source/native inference
completeness, N/cache retirement outside accepted families, W, Z, recursive
model/reification, export witness transport, principality, full original
A/B/catalog and production retain their owners and OPEN status. A whole
actual K0 stack induction here does not resolve an independent quantifier
over foreign continuations in a different theorem.

No Simple-sub generation, accumulation, propagation, levels, extrusion,
qualifying intrusion or generalization mechanism is edited or bypassed.
R336's no-high-copy K0 fact is compatible with this proof; it does not retire
the broader intrusion/source or generalization obligations.

## 10. Reuse, mutual TODOs, checks and freeze

Reused within actual premises: R336 rev4's finite algebra, independent D0
rules and Value-subsumption/root interface; R340's authentic Apply push,
protected entire prefix/owner and whole-Delay identity; R341's accepted
conditional S0 under four premises; R342's independent value/environment
relations, full-preorder canonical forms, capture/lookup/same-value binding
and finite-return theorem **at actual completed boundaries only**. R339's
trace/representation idea is historical source guidance, not an imported
adequacy/progress proof. Rejected: stack-free callee inputs, output-shape
typing, independent existential Function ports, provider-site closure
identity, assumed success/empty unresolved, uninhabited bottom environments,
and a single local owner action standing for all foreign continuations.

Mutual TODO `R343-STEP-REVIEW-1`, owner Luna: allocate the contract's fresh
non-contributor review of this frozen note/handoff, primary census and all
direct pins. First discriminating evidence is a failure in (a) Accept/input
subsumption with the original D0 rules, (b) a source constructor omitted by
the lowering/Store₀ induction, (c) a reachable h/η/Delay/view/owner mismatch,
(d) an unaccounted semantic guard or (e) selected-root completion. Output is
bounded acceptance or the exact source-qualified missing invariant/trace,
not a test of assumed transitions. This producer cannot appoint or perform
that review.

Mutual TODO `R343-M-REST-1`, owner Luna and the retained audit C/M source
owners from R342-M-REST: after adjudication, consume the accepted machine
supplier in S0+M and separately allocate the same-witness native
receiver/result/future-interface interpretation. Required input is the
original native Function/Call meaning with its independent quantifiers;
falsifier is an authentic same-provider Call satisfying the native premise
but lacking the demanded same-result/future/effect witness. This is a
request for a later frozen packet, not lease/dependency expansion here.

Implementation disposition: **NO_SAFE_CODE_SLICE**. Direct inspection of
`Machine::evaluate/return_value/new_invocation/leave_owner/begin_root`,
`RuntimeProgram` lowering/selected entry, literal decoding and receiving
constructors found no concrete authentic typed K0 defect. No provisional
implementation TODO is needed to complete this candidate. A future code
evidence packet, if review identifies an actual missing supplier, must be
minimal and owned by Luna; its exact falsifier is the responsible row in
§7. No compiler repair is authorized by this note.

Checks: direct source/authority reads, byte hashing, manual coverage of all
seven D0 forms, six K0 runtime frames, both active states, both stopped
terminal classes and external caller-budget behavior. No tests, execution
probes, Cargo/builds, network, Git, nested CLI, model-policy/config changes,
central-state changes or descendants. These checks are not independent
review or machine verification.

Requested model/effort: configured `gpt-6.1-sol` / `high`. Effective observed
model/effort: **UNKNOWN / UNKNOWN**, because no runtime metadata attests
them. Worker ID `/root/r343_k0_machine_step_prover`; own session/launch clock
UNKNOWN; containing primary session from current.json
`4a30d8bc-cf58-442a-ac35-a6026b4e35b5`, not asserted to be the child session.
First observed clock: `2026-10-23 07:36:16 UTC`. Grant: 3,000 seconds total,
no carryover and no descendants. The final clock and observed elapsed span
are recorded in the handoff; exact active CPU/model time remains UNKNOWN.
No budget expansion is requested.

Only new paths: this note and
`tasks/agent-loop/inbox/20261023-r343-k0-machine-step-prover.md`. No scratch
paths or unresolved descendant leases exist. Next in-scope action is the
frozen handoff and immediate writing cessation. Both byte hashes accompany
submission; the handoff contains this artifact's hash and its own hash is
returned separately to avoid a self-hash cycle. Revision 1 is immutable on
submission. The writer is STOPPED after that receipt, rather than RUNNING
while awaiting Luna's review/integration.

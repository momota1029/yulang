# R40: Application result formation at `loop y`

Status: frozen candidate partial source derivation and exact formation
obstruction; independent review NOT_RUN. No new rule, impossibility theorem,
source-qualified counterexample, implementation authority or parent closure.

Assignment `R40-PROOF-APPLICATION-RESULT`, handoff revision 1. Sole author/writer:
`/root/r40_application_result_proof`; no descendants. Requested Sol/high;
observed effective model/effort UNKNOWN/UNKNOWN. Launch evidence: Luna's
current-session assignment delivered to this worker identity. Opaque runtime
session ID UNKNOWN. Baseline supplied by Luna:
`887eed4370278cd9e789fb2b9b10ff58369da540`; no Git observation.

## Result and parent application

The forward source derivation reaches q's Application row with its two actual
resolved operands. That row **constructs the symbolic result name** `A_q` in
`Computation(E_q,A_q)`. It is therefore inaccurate to treat the symbolic name
itself as something that only a later native Result consumer could supply.
What remains unprovided is the original *typed output-parameter formation*
that authenticates that name as an ordinary source description, or authenticates
its reference to an already introduced description. The source synthesis row
does not instantiate that formation judgment's owner, scope and ordered
dependencies. Its result role is determined; its ordinary declaration is not.

The partial derivation below locates this hole between forming the two child
interfaces and using `Comp(E_q,A_q),o_q` as Code-Call's original result input.
Backward inversion through the actual recursive loop binding does not fill it:
the loop body forwards the result of a different `helper x` Application, and
the existing Call constraints relate ports without being declaration rules.
An authentic complete `Q_q` with its original output-parameter binder and all
arm interfaces is still needed. This is a precise missing rule instance in
the pinned supplier envelope, not a repository-wide nonexistence claim.

Apply the result to the unchanged full Yulang inference/executor theorem and
original Simple-sub A/B claims at R40's **Parent and fixed outcome** and R36
§1. Original parent conditions discharged: **0 -> 0**. R36's definition
`D_hat := R` still lacks an authenticated source R/context for this native q
result. Neither Generalize eligibility nor either actual CopyScope follows.
Preserve every original source, provider, assignment, component, world,
context, occurrence, event, guard, continuation, interaction, future and
history quantifier; arbitrary well-scoped W; both independent incoming frames
and aliases. F1 and FK1 retain their independent quantifiers. Complete
Call/effects, N-Transport, soundness, required principality, termination,
source/native correspondence and production remain OPEN.

## 1. Exact syntax and the forward partial derivation

The unchanged literal is at
`crates/yu-solver/tests/candidate_local_self_recursion.rs:106`:

```yu
my outer = { my loop x = { my direct = loop x; my helper y = loop y; my first = helper x; my second = helper x; helper x }; loop }
```

Let f be the registered local `loop`, g the local `helper`, and q the Apply
which is g's lambda body, with callee Name resolving to f and argument Name
resolving to g's formal y. Let t be the different `loop x` in `direct`.
Let h1, h2, h3 be the three literal `helper x` Applications in source order.
These are structural addresses, not measured numerical occurrence IDs or
observed FreshUse maps. The fixture's resolution predicates at lines 109–122
select the two recursive callee Names by local binding identity; neither
`calls[0]` nor endpoint shape selects q.

Use `E_gcap` for the *lexical binding-certificate telescope* selected by
Capture-Lambda and `E_gbody` for its ValueBind extension. These are not names
for the unknown ordinary type-dependency telescope of `A_q`. The following
is a specialization of the existing rules, with the outstanding formation
premises explicitly retained; it is not a completed semantic typing proof.

1. **Registration and the callee.** Generalize §3.1's recursive reference rule
   selects f's existing monomorphic registered description. Write its symbolic
   Value interface as `Value(A_f)`. Capture-Lambda and Data-Name
   (`call-input-construction-proof.md:200–220`, `:161–165`) follow g's actual
   dependency-closed capture/reference path to that same registration.
   No new provider, ordinary description or independently instantiated loop
   interface is introduced by the read. Its joint recursive semantic law
   remains the genuine L4 premise; successful inference is not used here.
2. **The formal and argument.** The unannotated y selects `Value(B)` before
   body synthesis (typed core §6, lines 335–376). Generalize §3.3 assigns its
   genuine Parameter introduction the record
   `Desc(C_B,rho_B,ValueDescription,sigma_B,Delta_B)` at that parameter's
   original type scope, before g's invocation challenge. Neither `Delta_B`
   nor the validating registration fields are reconstructed from a native
   level. Entry-Value forms
   `E_gbody = ValueBind(E_gcap,y,r_y,B,entry/rebind-origin)`.
   Data-Name at y selects that formal's B, rather than a fresh B for the read.
3. **The two code children.** Data-Name followed by Code-Result gives exactly

   ```text
   cf = result(name loop) : Comp(empty,A_f)
   ca = result(name y)    : Comp(empty,B)
   ```

   at their separate source operands in `E_gbody`. These are source-diagonal
   code interfaces. In particular, `ca` returning an already rebound y does
   not restrict independently admitted whole-carrier fillings of a Call hole
   to returning/pure carriers.
4. **Application, not Name or Result, supplies the new result-name role.**
   Instantiate typed core §6's Application row at these exact children:

   ```text
   I_q = Computation(E_q,A_q)
   d_q = reify(call(cf,ca))
   n_q = Normalize(I_q,d_q) = eliminate_pq(d_q)
   ```

   The last equality uses the already selected Computation tag and its known
   designated port, not a solved latent shape. Lines 412–423 require the
   complete invocation relation for the symbolic result endpoints. The rule
   constructs endpoint names before solving; no Callable success, source
   execution or satisfying assignment is demanded. The unresolved typed
   result-formation premise is recorded in §3 below.
5. **The complete source operation remains separately indexed.** With the
   original Application/Reify/operand origins, Code-Call would assemble

   ```text
   t_arg = Delay(ca,original lexical references)
   cf >>= (actual_f,current_C1).
       ExecuteCallable(actual_f,t_arg,current_C1)
     : Comp(E_q,A_q) at original result port o_q.
   ```

   Code-Call explicitly takes `Comp(E_q,A_q),o_q` as its original input
   (`call-input-construction-proof.md:310–346`). Its `Check_q` packages that
   input with the operand origins; it does not supply the missing output
   declaration. For contextual h, `t_arg` is the original open whole-carrier
   hole with h's lawful world action, not the source diagonal substituted
   for every filling.
6. **The helper body boundary forwards that interface.** Synthesis A gives
   `Result(I_q)=Comp(E_q,A_q)` and the lambda body/result skeleton
   `Fun(Value(B),Comp(E_q,A_q))`. This introduces no extra pure layer.
   It describes g's body Result; g's full invocation also includes its own
   carrier/receipt/entry/rebind and consumer/return interfaces. This step
   cannot classify `A_q` by treating the body return witness as a Desc.

The first symbolic occurrence introduced specifically for q is thus at step
4. Steps 5–6 consume/forward it. The actual type-formation certificate for that
occurrence is exactly what is absent from this partial derivation.

## 2. Backward inversion through the recursive binding

The source's enclosing binding spine, displaying only already selected code
constructors, is

```text
lambda x.
  bind direct = t in
  bind helper = result(lambda y. q) in
  bind first = h1 in
  bind second = h2 in
  h3.
```

The result of each ordinary Bind is the second computation's result endpoint
(Code-Bind, lines 267–288). Consequently loop's body Result forwards h3's
symbolic output `A_h3`; h1, h2, t and q keep their own Application origins.
Neither recursive Name resolution nor this Bind inversion equates `A_h3`
with `A_q`. Any relation supplied by calling g or f is an actual complete
Call constraint, not an original endpoint-declaration introduction.

There is a registered cycle in the description graph. Theorem IF's two-pass
construction registers the interfaces *at their existing symbolic interfaces*
and retains recursive references (`call-source-interface-construction.md:
482–496`). It neither solves the recursive equations nor supplies a missing
output-parameter binder. Reaching f's registered complete interface therefore
does not authorize selecting one of its result fields as `A_q` without an
original typed reference/projection. No such q-indexed projection is supplied
in the pinned rules. Equal solved rows would also be insufficient.

This rejects a specific alternate supplier route: a monomorphic recursive
reference keeps its existing interface; it does not retroactively declare
every distinct calling occurrence's symbolic result. It also leaves the f/g
registrations distinct. Value-reference SCC membership supplies no rule that
merges their validating components or logical scopes.

## 3. Exact unmet formation judgment and all arm obligations

At step 4 the source tag and expected coordinate sort are known: `A_q` is the
value-description coordinate of the **complete q Call result**. For using it
as an ordinary inference endpoint, the missing source datum is an authentic
output-parameter declaration/reference at that exact port. In meta notation,
the outstanding obligation is:

```text
original Application(q,callee_q,argument_q), original binder tree T,
actual typed input cursor and complete original Call operation Q_q
  |- form the output-description parameter/reference at o_q,
     with its authentic declaration origin rho_A,
     validating component C_A, source sort, original type scope sigma_A,
     ordered Delta_A = (d1:S1, ..., dn:Sn(d1,...,d(n-1))),
     and its actual typed inclusion/reference into q's complete result.
```

This display names required evidence; it adds no source rule. If the output
is a new ordinary inference declaration, the supplied output must include
`Desc(C_A,rho_A,ValueDescription,sigma_A,Delta_A)` and its Description edge.
If it references an earlier declaration, supply that actual declaration and
the original scoped reference/projection, then trace to its first authentic
introduction. A native row or constraint inclusion is neither alternative.
Whether the selected original Application does introduce an ordinary Desc
is itself unestablished; that classification is not assumed in the conclusion.

The supplier owner is the **original Application/Call output-parameter
formation rule**, specifically the source rule instance supplying Code-Call's
line-315 input and the authentic `Q_q.ReturnFutureRef`/`SpecCall_q` declaration.
Generalize Build (§4, lines 364–408) retains records from actual introductions;
it does not choose missing input scopes. The generic permission for another
independently specified inference introduction in §3.3 is not this instance.
The authentic binder must precede every dependent use, and no dependency may
be hoisted out of an enclosing event or proof telescope.

`C_A`, `rho_A`, `sigma_A`, `Delta_A` and a complete q-indexed arm interface are
therefore UNKNOWN. In particular `C_A=C_g`, `Delta_A=Gamma_q`, an empty
Delta, a native level, and a body-region label are not inferred. The complete
ordered declaration context cannot be printed without inventing its fields.
The requested evidence must include each dependent field's original type and
reference, not an unordered list of names or free-variable support.

The following obligations describe the required complete `Q_q` instance;
they are not claimed to be supplied arm instances. Opaque predicate bodies
may remain opaque once their authentic typed interfaces are supplied.

| Required original region | Ordered dependency/evidence that must be supplied at q |
| --- | --- |
| Structural Call | Actual callee interface, whole-carrier hole, callee-return provider/current C1, provider-dependent dispatch/entry, complete return at `o_q`/current C2, output-provider-dependent future interface. The original result-description binder and its scoped uses are required. |
| Callee-pending | Original response/current-state telescope and raw callee continuation, followed by the unreached carrier/receiver/entry/body/consumer/return/future suffix. The source-diagonal callee Name is not grounds for deleting this independently quantified interface. |
| Receiver-pending | Actual remaining Force/rebind/body/native/consumer/return suffix under the resumed current world; preserve raw handle/continuation and receipt position without replay. |
| Conservative W | Whole original input/output witness relation, changed and unchanged coordinates, hard guard, original admission/license evidence, and each changed output provider's own dependent latent/future contract. |
| Z and other declared alternatives | Every actual callee-local, receiver-local, whole-Call or future-root arm with its original root/reference, parameters, whole witness, hard guard/license and any introduced provider's own future/admission fields. No source anchor or finite enumeration of witnesses is required. |

The IF frame's outer order (callee, arg, callee_result, receiver, return,
future, arms, source) does not determine the internal dependent telescope of
any of those fields. `CallSpec` names its genuine input declarations; it does
not create the absent q-specific parameter/arm interfaces. Conversely, unknown
W/Z predicate internals alone would not block the selected interface theorem.
The missing object here is the authentic declaration and complete typed
interface/reference, including its ordered binder dependencies.

## 4. Source/native boundary, falsifiers and next owner

Two inspected code owners delimit the correspondence task:

- `ConstraintBatch::emit_candidate_source`, `candidate_source.rs:863–900`,
  allocates occurrence positions and retains y's Parameter endpoint route.
  Its active-initializer handling (`:1090–1100`, `:1245–1252`) sends q's Local
  loop Name to the active registered endpoint. Its Apply case (`:1316–1359`)
  retains q's result position, checking occurrence, operands and recipe;
  `ApplySourceInput` starts with `introduction:None`. That field concerns the
  directional-introduction route; its absence is not by itself evidence that
  no ordinary Desc exists. The code supplies no logical output-declaration
  certificate or complete dependent telescope in those fields.
- `CandidateSourceCall::pending_construction` /
  `PendingCallConstruction::suppliers`, `candidate_call.rs:380–427`, retains
  a q-tied request for original Gen-Call-0, whole carrier and complete
  receiver/result/future suppliers. A supplier request is not the formation
  judgment it requests.

The R40 native lane separately owns the corrected typed Function Result
child, Preserve admission, dependency, Context/Dispatch consumption, helper
body endpoint and extrusion copies. This artifact neither disputes that
structural path nor certifies its trace. Even a CLEAN native trace must be
joined to the source formation above by a typed complete-tuple map; a native
result row does not supply an output-provider/world/future declaration.

`NO_SAFE_CODE_SLICE`: these two owners do not provide the missing original
source judgment as code evidence, and the contract grants no code edits.
Writing a retention patch before the source header exists cannot authenticate
that header. No provisional implementation is requested now.

| Stable mutual TODO / owner | First evidence, proposed output and exact falsifier |
| --- | --- |
| R40-Q-OUTPUT-FORMATION / original Application/Call source-rule owner via Luna | Supply the actual q rule instance at step 4, its output-parameter binder or original reference, `C_A,rho_A,sort,sigma_A,Delta_A`, all dependent field types and complete `Q_q`/arm references. Output one actual formation derivation, or seek authority if a new rule is required. Falsifier of this obstruction: an existing pinned original rule instance supplies these fields for this q without solved-row inference or R38 adoption. |
| R40-RESULT-COMMUTATION / source/native bridge owner after that formation, coordinated with R40 native lane | Map that same complete source result tuple to q's Apply result, retained/extruded copies, typed Result child and actual consumer. Falsifier: any admitted result is associated with t/h1/h2/h3, an invocation-effect port, a different provider, or an inaccessible/reordered source dependency. |
| R40-COPY-PUBLICATION / actual CopyScope and Generalize owners | After the source/map premises, authenticate both actual copy scopes and both incoming frame actions with aliases, W and original continuation families. Falsifier: an omitted fixed dependency, a copied OneShot/Shared witness, or a continuation contract selected only for one local frame. |

The two methods here were forward syntax-directed specialization and backward
recursive-binding/result inversion. They leave the typed output-parameter
formation premise untouched. The next step must change the missing input or
its supplier owner, not issue another equivalent conditional theorem. No
further derivation is claimed beyond that missing supplier input; continuing
the same two routes would reuse it as an assumption. Return it to Luna at
this boundary; a new rule/adoption, dependency,
lease or budget requires Luna before writing.

## 5. Reuse, pins, checks and stop receipt

Reuse R39's independently reviewed bounded source-supplier result only for its
actual Code-Call/IF premise account. R40 adds the q-specific partial derivation
and recursive-result inversion; it does not promote that prior report to a
complete Application derivation. Reuse the selected synthesis A/Parameter
rules and the IF registered-cycle construction in their actual scope. Reject
R38's unadopted `Delta_R=Gamma_q` as a source premise. R36's candidate
definitional extension remains conditional on an authentic parent context.
The historical apply/step Gen-Call-0/G_call slice supplies neither a
loop/helper instance nor an output binder: its displayed existential binds
`F_c,e`, not `E_c,A_c`. No old O0/O1 failure is restored as a current blocker.
The R39 native artifact's Capture expansion is not reused as typed propagation.

All directly pinned R40 and retained R39 revision-2 table entries matched
their frozen SHA-256 values before derivation. Direct dependencies used here:

| Input | SHA-256 | Author/provenance |
| --- | --- | --- |
| `tasks/agent-loop/sprints/application-result-formation-20261018-r40.md` | `a1ca3da89e79c7722f2f4e4a228086db360f0279ea1ee7e31ae6b970315eaa45` | Luna, frozen revision 1 |
| `tasks/agent-loop/sprints/original-call-introduction-result-consumer-20261018-r39-rev2.md` | `0b62297eebb50e716257228f767cfc36c7194d0d39ea7c1f7ada13428ab52dc5` | Luna, frozen revision 2 |
| `notes/progress/2026-10-18-r39-review-receipt.md` | `6169082ba0552c52a6ebbe71cd2caa65f7e91da48bbe9c0d8c88f0d35bc6db0b` | Luna receipt of independent bounded reviews |
| `notes/theory/2026-10-18-original-call-introduction-r39.md` | `7d4d914d111b78802517e40349d7a576f55a19399da8b85d6c53d9a3371337f5` | `/root/r39_proof_source_owner` |
| `notes/theory/2026-10-18-apply-scope-publication-r36.md` | `43edea46d93a8b7eac6a68e6544aa34cc36797c59e232fd31599d8eec15ef5a9` | `/root/r36_proof`, candidate |
| `notes/theory/2026-10-18-call-result-owner-r38.md` | `63ba5b3fe053b8ced790f089ab0a6defcf554b440114b94a9f901cec3176af92` | `/root/r38_call_result_proof`, proposal |
| `notes/progress/2026-10-18-r38-candidate-review-closeout.md` | `8ed59d6013f0be42e3f3609dd45fe4db37d9897dc7fec6d1b7790d1cb1f58050` | Luna; proposal-only acceptance |
| `notes/design/2026-10-02-source-result-synthesis-choice.md` | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` | User selection A; primary drafting and recorded review |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` | Primary; scoped source-synthesis reviews; wider core Draft |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` | Researcher; recorded independent repaired review |
| `notes/theory/2026-10-07-call-input-construction-proof.md` | `f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6` | Original producer UNKNOWN; recorded construction review |
| `notes/theory/2026-10-07-owned-call-contribution-construction.md` | `ead206bff341c82993acbaecda25ae1d3a760397796bbbbb53ba3ef917a53fb1` | Original producer UNKNOWN; selected reviewed construction |
| `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` | Original producer UNKNOWN; selected reviewed construction |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` | Primary selection; recorded independent reviews |
| `notes/design/2026-10-07-original-call-formation-definition.md` | `4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f` | User adoption; primary record and independent reviews |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` | Original producer UNKNOWN; bounded apply/step review |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` | User decision and recorded review |
| `crates/yu-solver/src/candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` | Existing read-only worktree input; authors UNKNOWN |
| `crates/yu-solver/src/candidate_call.rs` | `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479` | Existing read-only worktree input; authors UNKNOWN |
| `crates/yu-solver/tests/candidate_local_self_recursion.rs` | `47ced76fe8f0f136c42802b2376ca09f7cadec0fc8e5b1b3d4c6acc7bc613e55` | Existing fixture; authors UNKNOWN; read only |

Checks: static source/rule reads, q-specific rule specialization and inversion,
read-only SHA-256 verification. No test, Cargo/build, CLI, executable probe,
proof checker, semantic acceptance check or independent review ran. Complete
q formation/all arm instantiation, original local semantic laws at this
specimen, source/native commutation, either CopyScope, Generalize/two-frame
lift, arbitrary-W fiber equality and FK1 remain unestablished. Ordinary
generation, accumulation, propagation, levels, extrusion, qualifying intrusion
and generalization are preserved; no withdrawn bypass is introduced.

Resources: 1200-second Sol/high grant charged in full by Luna; no renewal,
refund or Astra work. Actual CPU/RSS and complete launch-to-stop wall time
were not measured and remain UNKNOWN. No heavy process, generated file,
scratch path or descendant. Only this artifact and the exact leased handoff
are new paths. Existing dirty worktree files were read only and preserved.

**Writer stop receipt:** this revision is frozen upon its hash-bearing inbox
submission. This worker then stops writes on both exact leased paths, has no
descendants/unresolved descendant leases, and awaits Luna's intake without
claiming RUNNING. No certification is claimed; independent review belongs to
Luna. Parent OPEN, candidate pending review/integration.

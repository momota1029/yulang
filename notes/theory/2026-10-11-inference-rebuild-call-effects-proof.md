# Complete Call and contextual effects in the inference rebuild

Status: frozen unreviewed research note; relative constructor derivations and
bounded source correspondence; no parent-theorem closure or design authority.
Date: 2026-10-11
Baseline: `d8c097e1f810fb26a8cf1936aa97059f6948bf32`,
`research/simple-sub-intrusion`.
Exclusive lease: this file only. Leaf; no delegation, code, tests or Git mutation.

## Frozen objective, quantifiers and sources

The original obligation remains sound and natural Simple-sub inference with
required principal schemes for every supported resolved Yulang program, its
original binders/scopes, recursive uses, annotations and complete Calls. This
packet addresses complete Call and contextual effects inside that algorithm.
It does not restrict sources to Name/Name Calls, returning arguments, finite
executions, source-generated alternatives, one effect family or scalar ports.

For each actual Call, keep the original dependent index whole:

```text
Idx(e) = (B,X,xi,Delta_e;
          d_f,A_f,R_f,u_f,u_x,c,u,U_e,beta,p0,p_out(c),ElimOrigin)
xi=(nu,K,D), beta=(d_f,R_f), U_e=F_c.
```

`u_f`, `u_x`, checking `u`, source Call `c`, immediate invocation position
`p0` and complete output leg `p_out(c)` retain their original meanings and
remain distinct. Local dependent `U_e` stays in `Delta_e`; outer imports keep
their original capture provenance. One assignment acts on the entire tuple.

The semantic quantifiers range over every legal original joint assignment,
every independently typed compatible punctured context, every admitted whole
carrier, every retained actual decomposition `Act(v,U,r)`, every complete or
pending observation, and every admitted Response/raw Resume/FutureUse
development at its current world. Function realization must work at the same
actual provider returned by the callee. A diverging carrier retains all finite
prefixes, including the initial prefix; Return is not an admission condition.
Contributions and source incidence are fixed before observations:
`exists c_e,a_e. forall z in F_C(X;xi). Cover(a_e,z;X)`, when the independent
constructor premises hold. Reversing this order and choosing a witness per
observation is not the required statement.

Governing sections, read at the pinned baseline:

- Top-level inference principles §§1–5 and Evaluation/Authority: native
  generation, accumulation, propagation, levels, extrusion/intrusion and
  generalization; no speculative typing search; necessary abnormal safety.
- `2026-10-07-original-call-formation-definition.md` §§2–4,6: exact telescope,
  OSig-Demand/OC-CallEff and full receiver-root interpretation.
- `2026-10-08-contextual-function-membership-definition.md` §§2–4: same actual
  provider, complete independent challenges, pending/future behavior.
- `2026-10-07-complete-call-contribution-definition.md` §§2–5: complete
  operation, evidence fibers, conditional accounting and selected attachment.
- `2026-10-08-call-source-interface-definition.md` §§2–4: declaration/use
  incidence, whole carrier hole, returned-provider/future maps, original arms.
- Annotation hygiene §§1,3–4; residual-lineage Selected policy; contextual
  attachment/admission §§3–4 and §3.1: source-owned authority, ordered contexts,
  attachment set identity and separate residual-constructor lineage.
- `2026-10-10-call-reify-construction-direction.md`, Scope/Required next
  construction: retained whole argument and suspension attachment; its
  original registry premise is not discharged by approval.

The 2026-10-10 original Call-effect typing clause **candidate** is Draft;
it is not an adopted comparison rule. Old carrier acceleration and exact
failure restoration are not imported as redesign premises. The top-level
principles govern normal suspension and necessary abnormal safety. Frozen
packet 1, `2026-10-11-simple-sub-rebuilt-core-proof.md`, supplies the native
store/level/extrusion derivations; this note neither duplicates nor promotes
them. Simple-sub reference `Typer.scala:48–83,106–126,134–203` at
`9bae772624c23b52a93c1b226157e16898b4d9db` supplies pure generation and
variance, without Yulang complete Call or contextual-effect semantics.

## One correlated four-port semantic interface

Write the native Function skeleton as `Fn(A,E_arg,E_inv,R)` with relative
variance `(-,-,+,+)`. Its semantic interface is one dependent relation, not
four independently inhabited sets:

```text
I_F(Idx;eta) = {(whole challenge, argument value/computation,
                 argument effects, complete invocation effects,
                 result value/provider, returned future interface,
                 ordered phase/history, live worlds, hard constraints,
                 original arm, complete witness)}.
```

The four ports are projections of this shared fiber, together with their
dependency maps. `E_inv` is the complete invocation position, including entry,
body, designated consumers and invocation return. It is distinct from callee
evaluation effects, bare body effects and a returned value's latent effects.
Invocation effects and the whole source Call effect also differ: a complete
Call includes the preceding callee computation.

This is notation for the adopted interfaces, not a new semantic carrier or
second solver. Generation must retain/construct the actual dependent relation
and its source indices while it is unsolved. Native bounds accumulate its
constraints; propagation traverses its actual ports and contextual obligations.
It need not prove complete Call typing at generation time. Solving scalar
comparisons alone supplies no missing relation witness.

**Correlation obstruction.** If a relation contains only four-tuples `0000`
and `1111`, every port projection contains both bits. Their Cartesian product
also admits `0101`, which has no joint witness. This elementary mathematical
falsifier proves marginal acceptance is insufficient. It is not a
source-qualified counterexample or a claim that four-port terms cannot retain
correlation when their actual constraint owner does so.

## Relative clauses already derivable

**1. Same-provider elimination.** Given the adopted complete Function
membership of the exact decorated value and an independently formed complete
challenge, eliminate membership at the retained `Act(v,U,r)`. Its acceptance
clause supplies actual-U acceptance of the same whole carrier at that
challenge's live event. Its observation clause covers every actual complete
or pending U observation and admitted future development at the same indices.
No second provider, receipt or live authority is constructed. If a valid
whole-interface comparison supplies `D_F subseteq D_A` and
`forall d in D_F. P_A(d) subseteq P_F(d)`, composition with A realization
derives F realization pointwise on the identical challenge/witness. This
reuses the reviewed relative input theorem §3.2; it proves no scalar solver
receipt implements those inclusions.

**2. Authentic complete-operation wrapper.** Given authentic `Q_e` and
independent complete C0, the selected `C-Call` fixes
`c_e=CallContract(Q_e;Idx)` before choosing challenge or observation.
`CallMem(Q_e,h,y,d)` retains the exact original whole-operation witness `d`;
elimination returns `d`. Introduction/elimination compose to identities at
the full evidence fiber, before observation projection. This reuses the
selected C1-Call derivation. It neither establishes C0 nor manufactures Q_e
from arbitrary typed endpoints.

**3. Pending suffix preservation.** Unfold the adopted structural operation:

```text
EvalCall(Q_e,h) = CalleeRef_e(h) >>= S_h
S_h(actual_f,C1) = ExecuteCallable(actual_f,WholeArgRef_e(h),C1).
Request(q,C,k_f) >>= S_h
  = Request(q,C,(response,C'). k_f(response,C') >>= S_h).
```

The callee-pending suffix retains the unreached argument/receiver operation.
Once the callee returns, use that actual provider and current C1. At Value
entry, entry/receipt precede Force of the whole argument. An argument-pending
request retains rebind/body/native delimiters/designated consumer/invocation
return as its ordered suffix; resumption does not replay receipt. Retained
computation entry binds the same carrier without this entry Force. Return
retains the actual result provider; its later latent uses are future
interfaces, not execution at return. These are direct Bind equations in the
selected complete operation, relative to the genuine original operation and
world-action premises. An independently declared whole-Call arm retains its
own witness and need not follow the structural callee Bind or have a source
execution anchor.

**4. Selected static root calculation.** For an actually emitted Gen-Call-0
record, OSig-Demand defines `Inv(Id(U_e),U_e)` and OC-CallEff retains exactly
that root at `e.p0,e.u,e.c,e.beta,e.Delta_e,e.ElimOrigin`. Its interpretation
is the complete receiver operation by the adopted definition. The calculation
does not produce source ownership, C0, attachment, a profile or an execution
receipt. A returned Function's latent position cannot replace the immediate
root even if erased endpoints coincide.

These are relative derivations from selected definitions and their genuine
premises. No raw-source inference theorem, exhaustive semantic model or new
independent review is claimed for this packet.

## Source-to-operation bridge and first missing supplier

At the pinned baseline the actual source constructors provide the following:

| Owner and locator | Retained fact | Consumer / exact gap |
| --- | --- | --- |
| HIR `module/local_source.rs:107–142` | Resolved Name, Apply children, Lambda parameter/body, annotation and scopes | Apply is a source node, not a complete operation certificate. |
| `candidate_source.rs:189–243,394–411,445–461` | Formal registrations/name incidence, exact Apply occurrence and callee/argument/result/effect positions, lambda body/parameter | `Action::Candidate` / `Action::Lambda` drive native construction; no complete Gen-Call-0 telescope is emitted here. |
| `candidate_call.rs:15–57,85–124` | Formal native root, source operands, checking cause and native interface; explicit pending suppliers | Registered positive row is not the jointly scoped complete Function contract; pending enums list missing inputs rather than construct them. |
| `shadow_apply.rs:1304–1399` | Validates source/recipe incidence; creates negative four-port demand, invocation row and NativeInterface; calls `constrain_live_value` | This supplies real scalar generation. No complete whole-carrier/provider/history/future relation is established by it. |
| Source theory `2026-10-06-source-call-generation-construction.md` §§4.2–4.4 | Abstract selected-source Gen-Call-0 construction and immediate root/origin schema | This is a mathematical source instance, not proof that the Rust constructor emits the same dependent record for every source. |

The **first missing supplier** is at original source Call/formal construction:
produce the same jointly scoped complete Function demand and actual original
Call relation, with the whole Gen-Call-0 telescope and its lexical/checking
exposure/origin maps, while retaining the independent whole carrier and actual
callee-result provider/future interfaces. Four-port native terms and occurrence
identity do not establish that supplier. The existence of an unsolved
generated dependent constraint is what must be shown; requiring every
constraint to be solved immediately would change ordinary Simple-sub.

The precise requested bridge is therefore `Gen_source(e) -> retained
Idx(e),demand(e),Q_e,whole interface constraints`, with constructors and
consumers at the actual source owner, before observation and before successful
comparison. Local OSig-Demand/OC-CallEff can then be applied to that retained
record. This statement assumes none of its desired outputs. No arbitrary
relation is cast into Q_e and no new all-Call registry prerequisite is added
to elementary inference. Missing original registry/Reify source construction
remains a supplier on the adopted route; a new compiler representation must
preserve its complete meaning rather than pretend approval supplied it.

## Contextual effects: authentic identity versus dormant execution

An attachment identity is one set at one exact annotation occurrence, with
resolved members and member ordinals. Symbolic variables remain connected.
Contravariant concrete `[E]` permits function-local subtraction at that
position; covariant `[E]` permits concrete E. Neither allowance nor equal
nominal support is a contribution-removal license. Residual identity is its
constructor lineage, even when source rows or current residual keys become
equal. Every applicable current/future lower must reach every retained recipe;
source-to-head/gamma feedback and exact gamma-to-tail projections remain live.

| Actual owner / consumer at baseline | Established static evidence | Missing executable bridge |
| --- | --- | --- |
| `candidate_effect.rs:733–780,1447–1573` | View retains owner, source position, resolved atom set and tail; composed annotation variance/scope enters `AttachmentSource` | Negative concrete rows explicitly return an availability error at 1515–1517; this is not a semantics-preserving implementation of local subtraction. |
| `candidate_context.rs:2174–2200` | `source_weight` allocates one attachment set with member ordinals and scope/polarity | `SourceUnitPush` is dormant; its private detached adapter emits no live context/relation/bound. |
| `candidate_effect.rs:864–955` | Contribution allocation keeps resolved effect, origin and fresh instance; Support expands members/tail; Allowance checks members and routes remaining flow to its tail | This establishes the bounded existing positive/checking mechanism, not authentic negative subtraction or complete handler output. |
| `candidate_context.rs:146–201` | Empty bundle and inferred-entry origin are distinct from executable entry certificates; context syntax retains ordered replay/swap/both | Inert incidence is not authorization for `BothFromRight`; a context constructor field alone does not prove its source producer or execution. |
| `candidate_context.rs:2409–2428,2613–2704,2911–2993` | Bound-to-relation links, bounded zero-word filter consumer and ordered lower/upper fiber replay exist | `discharge_residuals` stores a post-filter ContextId; it is not the selected lineage-owned concrete gamma ResidualRecipe. Stored ReplayRecipe dependencies are not proof of such residual production/activation. |

The corresponding first effect obstruction is the absent *live producer and
consumer* for the negative concrete annotation's attachment-local subtraction
and lineage-owned residual/gamma, including future-lower fan-out and reverse
feedback. Metadata and a detached exact word evaluator leave that premise
untouched. This static account makes no claim that all candidate contexts are
unsupported, or that source arithmetic proves actual worklist divergence.

For a purely indexed statement, transporting a whole attachment/recipe record
through one map preserves its independent identity coordinates if the map
retains them. That is a proposed construction invariant, not an established
source fact or proof for parent/copy equality. Packet 1's equality premise
remains open. Row equality must activate newly combined bounds/recipes and
cannot erase separate lineages or grant annotation authority elsewhere.

## Stop, checks, runtime and commit packet

Method: one bounded static pass; apply selected constructor elimination and
Bind equations, then inspect actual native source/effect owners. Falsifiers
are missing shared telescope fields, substitution splitting one witness into
portwise choices, changing the actual returned provider, erasing a pending
suffix, or removing a sibling contribution/recipe solely by endpoint/support
equality. No execution or model enumeration ran. The exact construction gaps
above are the stop condition; no equivalent reconstruction attempt follows.

Economy audit: retained registration, occurrence, attachment and lineage
facts are D when their actual owners already know them; authentic complete
Call typing, hygiene and publication are A; ordinary Call inference and
required principal generalization are B. Owner retention removes D only.
It does not discharge A/B or authorize a source restriction.

Commands: `cat`/`sed`/`rg` on the named sources; read-only `git rev-parse HEAD`
and `git status --short`; `sha256sum` for dependencies. HEAD matched the pin.
No compiler, Cargo, Oracle, tests, benchmark, executable probe, Git mutation or
child launch. At most two parallel lightweight read commands; no heavyweight
processes or measurement samples. Whole-task CPU/RAM/wall time were not
instrumented. Requested routing is normal Sol/high; role defaults are those
read in packet 1. Effective runtime model/effort metadata remains unknown;
no Astra or hot reload claim. Source and semantic coverage stops at the stated
suppliers. Independent review is pending.

New direct dependency SHA-256 values (packet 1 retains shared-input hashes):

```text
complete Call definition 4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e
Function membership     0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0
original Call formation 4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f
Call source interface   20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c
Call Reify direction    850a6a035d0e4b6ad3be761205d24c51b4b894fcc5e795c4dc30415e529c5a30
attachment design       717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc
semantic input theorem  fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a
Call contribution proof ead206bff341c82993acbaecda25ae1d3a760397796bbbbb53ba3ef917a53fb1
source generation       6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073
candidate_context.rs    4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987
candidate_effect.rs     ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df
local_source.rs         906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed
frozen packet 1         4180f06f9168faefae97ec88233657ff6dc7b33434753a9054f6a8be9791e8fb
```

Exact changed path: `notes/theory/2026-10-11-inference-rebuild-call-effects-proof.md`.
Baseline SHA: `d8c097e1f810fb26a8cf1936aa97059f6948bf32`.
Changed dependency hashes: no changes made by this worker; primary rechecks
the recorded snapshot before integration. Review status: unreviewed; parent
Call/effect/inference theorem OPEN. Checks already run: static source/pin/hash
inspection above. Writes stop at handoff.
Proposed message: `research: localize complete Call and contextual effect suppliers`.
Shared-record deltas left to primary/curator: retain the selected relative
clauses; record exact complete-demand/Q_e and live subtraction/residual
supplier gaps; promote no source/production or parent proof status.
One next action: construct the source-owned jointly scoped complete Call
constraint at its actual generation owner, with authentic operation and whole
carrier/future interface outputs, before scheduling its downstream proof.

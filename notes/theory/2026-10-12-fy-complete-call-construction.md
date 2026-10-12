# The candidate's recursive `f y`: complete Call construction boundary

Date: 2026-10-12
Status: frozen, unreviewed bounded source derivation attempt; parent complete Call and intrusion A/B gates OPEN
Baseline: `3310ab0e4724fc666786fdc8dfdd6dd70c810196`, `research/simple-sub-intrusion`
Producer: prover-equivalent generic leaf `/root/fy_complete_call_bridge`; no delegation
Exclusive lease: this file only
Authority: existing selected source/Call definitions; no new semantic decision or implementation authority
Budget: one static derivation, at most 30 minutes; no executable inference

## 1. Frozen claim and result

The target is the **actual innermost source Call** `f y` in this candidate:

```yulang
my answer = {
  my f x = {
    my g y = { my drop z = y; drop (f y) };
    my first: int = g 0;
    g ()
  };
  f
}
```

Construct its original source-rule judgment, with the actual recursive callee
provider/root, whole argument, current world, receipt, Value entry, body,
designated consumers, invocation return, complete result and future interfaces.
The requested derivation must retain every independent admitted challenge,
finite prefix, compatible history and future development at the original
binders. A divergent invocation needs no fabricated Return. Descriptor choices
and proof strategies stay at their owning type/description/event scopes; they
cannot be selected after a challenge to make this one Call succeed.

The parent claim still ranges over all admitted programs and lawful uses in the
original supported envelope, preserving complete Call, effects, soundness,
required principality and normal inference progress. This one Call cannot close
that universal claim, even if its complete derivation is later supplied.

**Result:** no complete local derivation is established. The first semantic
input unavailable from the selected rules is the genuine hereditary binding
and joint-world introduction of the **actual recursive f closure** at the
g-body event. Source Generalize L4 requires its owning recursive introduction;
it does not provide that introduction for this nested body. The selected
two-closure introduction is for `my f x=g; my g y=f`, not this program.
Consequently the Name/Return callee premise cannot yet be discharged.

This is an absent construction input in the inspected selected subsystem,
not a proof of source rejection, unsatisfiability, impossibility of a future
derivation, or an intrusion counterexample. In particular the Call does not
reach a proved fixed/template conclusion for extrusion-created C. The missing
evidence is semantic recursive introduction, not a request to reinstate a
withdrawn registry prerequisite or solve constraints at generation time.

## 2. Governing sources and scopes

Read the [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
and [Source Generalize selection](../design/2026-10-08-source-generalize-definition.md)
§§2–3, which selects [construction](2026-10-08-source-generalize-definition-and-proof.md)
§§3–5. Its L1–L5 remain genuine local-law premises. Relevant Call sources are
the [original formation definition](../design/2026-10-07-original-call-formation-definition.md),
[Gen-Call-0](../progress/2026-10-06-source-call-generation-construction.md#42-generate-the-initial-typed-address-through-call),
[Call-input proof](2026-10-07-call-input-construction-proof.md) §§3–4,
[source-interface definition](../design/2026-10-08-call-source-interface-definition.md)
and [Theorem IF](2026-10-08-call-source-interface-construction.md) §§3–6.
The actual semantic input consumers are [contextual Function membership](../design/2026-10-08-contextual-function-membership-definition.md),
[input realization](2026-10-08-call-semantic-input-realization.md) §§2–6,
[pure-read result](../design/2026-10-08-pure-read-call-result-constructor.md)
and [complete Call contributions](../design/2026-10-07-complete-call-contribution-definition.md)
§2. The [native recursive interface](../design/2026-10-08-native-recursive-interface-definition.md)
and [captured closure selection](../design/2026-10-08-captured-closure-constructor-definition.md)
establish their exact cases, with broader recursive introduction still separate.

The [committed candidate audit](../progress/2026-10-12-intrusion-admitted-two-use-witness.md)
supplies static lowering correspondence, conditional on a recovery-free CST;
no parser or runtime observation is added here. Its resolved lexical graph has
f as an enclosing local under answer, g inside f's body, and drop inside g's
body. The callee Name resolves to f's original local root; y resolves to g's
formal, and drop's body captures that same y. Neither Name is a polymorphic
instantiation at this occurrence. In particular f is still an active recursive
initializer in the candidate source constructor.

Preserve these separate scopes:

| Field | Original owner/scope retained |
| --- | --- |
| Actual f provider/root | f's outer local recursive introduction under answer; never a provider chosen from a demand shape |
| f formal x description | f's parameter typing scope, before its invocation challenge |
| Actual g closure | g's local initialization in an f-body invocation; its captured references and world belong to that event |
| g formal y description | g's parameter typing scope, before g's invocation challenge |
| y's actual value/provider | actual g entry Return/rebind in the current g invocation |
| drop closure and z description | drop's local initialization and parameter typing scope inside g; its y capture is the same binding |
| Inner Call and whole carrier | g-body Call occurrence c, after drop initialization; captured lexical y, not the formal z or a fresh y witness |
| Receipt/body/return witnesses | this f invocation below the inner Call's actual event and original challenge |
| Request/resume/future witnesses | their own later compatible events and actual live configurations |

The native inference levels are f=2, g and `f y`=3, drop=4, with publication
boundaries f=1, g=2 and drop=3. These are level facts from
`candidate_source.rs`; they do not establish a joint original world or decide
which logical witnesses are Shared, ViewLogic or EventProof. In particular an
actual g closure created within an f-body event cannot be replaced by the
fixed sibling g closure of the selected bare recursive-pair theorem.

## 3. Static rule instances and their exact missing inputs

Write E_e for the source telescope at c, r_f for the original f root,
A_f for its declared value endpoint, A_y for the one y declaration,
and xi=(nu,K,D) for the entire shared original package. A_f and A_y are
symbolic endpoints here, not membership proofs. Let sigma_f retain the outer
f declaration scope and Delta_e retain all actual inner dependencies.

The following is a **partial static instantiation**, recording what the
selected constructors would generate from their authentic input records.
It is not a complete source judgment and does not claim those missing original
records are already emitted by the native candidate.

1. **Name/Result children.** Given the original binding registrations and
   actual resolve/capture edges, Data-Name selects f's same binding certificate
   and y's same ValueBind certificate. Code-Result gives

   ```text
   q_f : Code(E_e, Name f, Comp(empty,A_f))
   q_y : Code(E_e, Name y, Comp(empty,A_y)).
   ```

   The equations mean pure lookup/Return of those same values. They do not
   force a latent result or establish hereditary membership. The actual
   recursive reference stays monomorphic at r_f.

2. **Gen-Call-0.** Given the actual original singleton Call and the original
   declared Value interfaces just used, its selected schema forms

   ```text
   R_f : original inferred-contract root at (component,d_f,A_f,sigma_f)
   F_c : dependent complete Function demand at R_f and Delta_e
   beta=(d_f,R_f)
   p0=(beta,call.effect)
   p_out(c) : original complete-invocation output address
   ElimOrigin(c,u_f,d_f,R_f,p0,p_out(c)).
   ```

   OSig-Demand and OC-CallEff then yield
   `outEff_orig(F_c)=Inv(Id(F_c),F_c)` and its actual typed Call-effect
   occurrence on this **whole** record. These are static positions/incidences;
   no receipt, result safety or satisfiable assignment follows. The native
   candidate has no observed original e_c with this inventory.

3. **Whole argument.** Given this Call's genuine registered
   `ReifyOrigin(o_y,Name y,r_arg,Comp(empty,A_y),Delta_e,incidences)`,
   Carrier-Delay forms

   ```text
   t_y=Delay(Return(lookup(the same y)),the original lexical references)
   J_y=the complete original carrier interface at r_arg.
   ```

   This represents the whole actual operand. It adds no source wrapper,
   receipt or execution. J_y includes inert formation and all designated
   one-layer execution/future obligations. `A_y` alone is not J_y.

4. **Code-Call and complete frame.** The genuine Application constructor must
   own the original checking origins

   ```text
   VIncl-origin(A_f,F_c)
   WholeArgCompatible-origin(J_y,CarrierContract(F_c))
   original complete result Comp(E_c,A_c), result port o_c,
   Suffix_c(U_f), and any distinct result obligation.
   ```

   Bare Gen-Call-0 does not supply these origins; Call-input §3.4 says so
   explicitly. Theorem IF can retain them, the actual original producer
   declaration and all original alternatives in FrameCall. Its finite-cycle
   construction registers interfaces and emits reference slots without
   unfolding recursive bodies. It proves static formation, not recursive
   validity, actual-provider acceptance or truth of the checking clauses.

Thus original static registration/port records, original checking origins and
semantic evidence are distinct inputs. Selected source schemas specify their
owners; an HIR local identity does not supply all three. This partial inventory
does not mistake a remaining compiler supplier for an absent mathematical
definition: Theorem IF already defines the full contextual placement when
its authentic original constructor inputs are supplied.

## 4. First unavailable semantic premise

Now attempt the actual source Name/Return rule, rather than just its static
Code-Result record. Original input realization §4.2 requires

```text
ReturnMem_A_f(Return(v_f,r_f,C_e,w_e)) iff
  JointWF(C_e,w_e)
  and ValueMem_A_f(v_f,r_f,e)
  and the original result/provider/root/world incidences.
```

Lemma W restricts a **previously valid hereditary binding** to the actual
callee-return event; it cannot create v_f's validity from registration. The
required binding certificate must cover the f closure's complete invocation
for every independently admitted challenge and compatible development,
including its recursive calls and actual nested local initialization worlds.
It must be installed jointly with the original world and retained f/capture
incidences. The actual provider decomposition `Act(v_f,U_f,r_f)` is preserved,
with U_f's original role and Value entry, not reconstructed from F_c.

The selected Source Generalize rules give the relevant owner records
`MemberEntry`, `Live` and `Internal`, and require one simultaneous original
member/world introduction. L4 explicitly demands its genuine evidence;
the records are outputs of that owning rule, not axioms validating this body.
Generalize's SRC/GS/GC induction assumes L4 locally. Closing the symbolic
program cannot establish the absent L4 instance, and a recursive equation
edge cannot by itself justify the hereditary interpretation used by Name.

The exact selected positive pair returns the opposite closure without calling
it and introduces two fixed declared value holes. This candidate's f instead
initializes g under its invocation, checks `g 0`, and contains the recursive
Apply `f y` in g. The registered roots, body rule instances, closure allocation
scopes and description frames differ. The selected native recursive definition
§4 explicitly leaves general recursive initializers separate. The selected
captured-step introduction likewise takes captured f validity from an already
typed outer entry; applying it here would assume the missing f certificate.

There is consequently no justified application of those exact introduction
theorems to this actual f. A new constructive instance of the owning general
recursive introduction law, or an established theorem covering this exact
nested construction, is needed. This report does not assert that no such
instance can be proved. It stops before using unproved f validity to derive
the whole carrier, actual receiver acceptance or complete result.

The y/Drop/current-world fields must also be valid on this same telescope.
Value-entry Return/rebind can supply y membership from an independently
admitted g challenge; it cannot choose y's endpoint after observing that
argument. A latent body containing this Call must be justified uniformly
even when no completed outer evaluation is available. No Return from the
recursive `f y` or execution of the later `g ()` is assumed here.

## 5. Complete obligations retained beyond the stop

These are unproved residuals, not additional hypotheses silently used to
finish the derivation:

| Original obligation | Existing selected owner and exact remaining input |
| --- | --- |
| Callee provider and current-world validity | Source Generalize L4, recursive introduction; actual hereditary f binding and JointWF at the g-body event, identified above |
| Actual source e_c and all original coordinates | Gen-Call-0/Application; one authentic whole original record, not separate native fields |
| Whole y carrier | Reify/Carrier-Delay and Lemma D; genuine reify license/scope and persistent y certificate; original WholeArgCompatible checking truth |
| Same-callable checking | original pointwise VIncl; an accepted whole source assignment/certificate, not merely its constraint-origin record |
| Receiver dispatch and receipt preconditions | Theorem R and contextual Function membership; same actual returned U_f, independent punctured context and complete checked challenge at the same C_e,w_e |
| Complete entry/body/consumer/invocation return | U_f's original complete contract; receipt then Force of t_y, actual x Return/rebind, f body and its designated consumers, invocation return; never body/invocation port equality |
| Complete result and future fields | Theorem IF plus actual result constructor; for this structural immutable-read route, selected ReadInvoke supplies an identity synthesis case **if its prerequisites hold**; unrelated existing result descriptors need their genuine bridge |
| Every original non-source alternative | complete Call/C0 and L1,L5; own whole-tuple typing, hard guards, changed/output provider, admission and future laws; no invented source anchor and no deleted W/Z arm |
| Effects and later history | original entry/callee/receiver effects, raw pending suffix and later live world/authority; no receipt replay or back-protection of provider occurrences |

For the selected ReadInvoke case the required result is the complete staged
`ReadInvoke(F_c,D_c,IF_e)`, including prefixes before Delay/challenge formation,
receiver observations after entry, output-dependent futures and all hard
guards. A native result value row is not an identification with this descriptor.
The selected definition avoids inventing another result-checking premise for
its own identity case; it does not prove this candidate has that result
construction or discharge its environment and alternative premises.

The scoped target quantifies over every independently admitted actual event
and challenge in the original domains, every genuine actual-provider
decomposition, all finite complete/pending/administrative developments, and
their compatible continuations/futures. Description choices precede the
appropriate challenges, EventProof strategies depend only on their preceding
inputs, and all ports share the original xi, assignment, provider and world.
No universal claim is reduced to returning executions or this carrier's pure
source diagonal. Complete invocation can carry argument-entry effects even
when the Name argument itself is pure.

## 6. Native Simple-sub correspondence and exclusions

The original Scala Typer's `typeLetRhs` installs an open monomorphic recursive
variable, `Lam` introduces its formal at the current level, and `App` generates
`f_ty <: Function(a_ty,res)`. Instantiation of a SimpleType returns that same
type. For this subterm it therefore explains the value demand
`o_f <: Function(A_y,R)` and the level-sensitive extrusion that may follow.
Typer has no Yulang receipt/world/complete carrier/future contract and supplies
none of the missing semantic premises above. No Scala run or full-program
native typing is claimed; its source language does not supply this Yulang
Unit/annotation program verbatim.

The current Y3 candidate source gives the active f Name an `Action::Link` to
its initializer endpoint and uses y's actual parameter endpoint. Apply owns
one negative four-port demand

```text
callee+ <: Function(argument+,argument_effect+,invocation_effect-,result-)
callee_effect+ <: application_effect-
invocation_effect+ <: application_effect-.
```

These describe native generation/transport, not original complete Call typing.
`CandidateSourceCall::observe` checks authentic LocalSource occurrences,
scope ownership and port kinds against its native demand. The f callee is
a resolved local, so the lexical formal-callee supplier trio does not apply.
`PendingCallConstruction::suppliers` nevertheless retains OriginalGenCall0,
ArgumentReifyAndWholeCarrier and ReceiverDispatchAndCompleteResultFutureInterfaces
unconditionally. The native registered-root accessor is for the separate
formal route and gives no original complete f provider certificate here.

Neither satisfying these native projected equations nor HIR resolution
establishes the actual original assignment, carrier admission, recursive
world or complete result interface. No conclusion about extrusion-created C,
its source declaration, fixed/template placement or equality transport is
drawn. No compiler code, acceptance restriction, annotation rule, production
cutover or parent-gate status changes.

## 7. Frozen verification, runtime and integration packet

Checks: bounded `cat`, `sed`, `rg`, read-only `git rev-parse HEAD` and
`git branch --show-current`, SHA-256 source snapshots, and one hand derivation
of the static rule instances and first failed semantic premise. Early broad
captures truncated; the decisive L1–L5, Name/Return/Delay, R, IF finite-cycle,
recursive-selection and ReadInvoke sections were reread in bounded captures.
No tests, builds, parsing, runtime/Oracle/solver execution, exhaustive search,
performance measurement or Git mutation occurred. Zero inference samples,
zero heavy processes; lightweight read-only shell processes only. Exact
reasoning wall time, CPU/RSS and process peak were not instrumented.

Requested routing: prover-equivalent generic leaf under the supplied Sol/high
fallback policy. Observed worker identity: `/root/fy_complete_call_bridge`.
Effective runtime model/effort metadata: unknown; configuration defaults are
not execution evidence. No custom `prover` execution or independent review is
claimed. The yulang-proofs skill/role contract was read and followed under the
primary's explicit no-delegation packet.

Dependency snapshot; none changed by this producer:

```text
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389 notes/design/2026-10-11-yulang-inference-top-level-principles.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38 notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 notes/theory/2026-10-08-source-generalize-definition-and-proof.md
4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f notes/design/2026-10-07-original-call-formation-definition.md
6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073 notes/progress/2026-10-06-source-call-generation-construction.md
f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6 notes/theory/2026-10-07-call-input-construction-proof.md
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c notes/design/2026-10-08-call-source-interface-definition.md
278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98 notes/theory/2026-10-08-call-source-interface-construction.md
0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0 notes/design/2026-10-08-contextual-function-membership-definition.md
fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a notes/theory/2026-10-08-call-semantic-input-realization.md
a9f833556a7e7c361c5b602c982de96b78663a77099999206bdb7bda6da67903 notes/design/2026-10-08-native-recursive-interface-definition.md
6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd notes/design/2026-10-08-captured-closure-constructor-definition.md
8d1eb7ecea3e63d7ba0ae091dc673f3321e52fc0e31c5d824bdf4f1656b99488 notes/design/2026-10-08-pure-read-call-result-constructor.md
4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e notes/design/2026-10-07-complete-call-contribution-definition.md
1084618662cf885991f83e3d41a901d0d429531bb742a1c0c2f91b8a998ec0ef notes/progress/2026-10-12-intrusion-admitted-two-use-witness.md
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35 crates/yu-solver/src/candidate_call.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49 crates/yu-solver/src/candidate_source.rs
cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411 crates/yu-solver/src/shadow_apply.rs
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9 /home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala
```

Commit packet:

- Exact leased path: `notes/theory/2026-10-12-fy-complete-call-construction.md`.
- Baseline SHA: `3310ab0e4724fc666786fdc8dfdd6dd70c810196`.
- Claim/review: frozen unreviewed partial static derivation and original
  recursive-introduction obstruction; no theorem or counterexample promotion.
- Checks: static reads/derivation, dependency snapshot and leased-file integrity;
  no executable verification authorized or performed.
- Proposed checkpoint message: `research: isolate recursive f input in complete fy Call derivation`.
- Shared-record delta left to primary: keep complete Call/intrusion gates OPEN;
  record L4's actual nested recursive f binding/world introduction as the first
  semantic admission dependency, distinct from the native pending compiler
  suppliers and later extrusion-copy source realization. No task, design,
  index, question, code or configuration path changed.
- Next action: construct or obtain that exact recursive introduction instance
  with the original f-body/g-allocation/event telescopes; reuse the already
  selected Name/Delay/IF/ReadInvoke rules once its input is established.

Writes stop at handoff. The primary must revalidate dependencies and obtain
fresh independent review before accepting any gate-status implication.

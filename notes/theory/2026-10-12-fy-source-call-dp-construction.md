# Recursive f-y: native construction and the first complete-check judgment

Date: 2026-10-12
Status: reviewed research; bounded constructor derivation obstruction; parent gates OPEN
Parent D/P, Source Generalize L3-at-c/L4, complete Call and inference: OPEN
Baseline: `5cb4ba6f9cc8fa65d347c3b53b6d4e6e5196d02f`
Branch: `research/simple-sub-intrusion`
Producer: leaf `/root/fy_source_call_dp_construction`; no delegation
Exclusive output: this file; no implementation or definition authority
Method: instantiate the native four-port construction, then try the original
complete checking rule at its actual operands and original telescopes
Budget: static inspection and hand derivation only; zero tests/builds/probes
Review: `compiler_referee` `/root/fy_call_construction_review`; no blocking or
major findings; one minor Gen-Call-0 wording correction repaired in `849e417a7`
by the primary; effective model/effort unknown.

## 1. Frozen claim and scope

The unchanged source is the source in
[the prior finite-check packet](2026-10-12-application-c-finite-check-proof.md#1-frozen-objective-quantifiers-and-exclusions):

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

Fix its resolved graph, original binder tree, `xi=(nu,K,D)`, outer
initialization event b, and one entire original assignment/strategy. Retain
f's actual endpoint A_f, root r_f, value v_f and **each** actual decomposition
`Act(v_f,U_f,r_f)`. I_x is U_f's actual whole-carrier entry interface. F_c is
the original complete checked demand at the inner `c = f y`; J_y is the
whole original Name-y carrier, not the formal value endpoint A_y.

The required result is an authentic finite original checking derivation k_c
with the following actions at every original c event e:

```text
(D) forall d in D_F_c(e).
      the SAME complete d belongs to D_A_f(e).
(P) forall d in D_F_c(e), forall o in P_A_f[S](d).
      the SAME decorated o belongs to P_F_c[S](d).
```

S is the candidate relation of
[the direct postfixedness attempt](2026-10-12-nested-recursive-f-postfixedness-proof.md#3-candidate-relation-with-the-holes-and-dependencies-exposed).
D is independent of S; P must follow by the actual checking constructors,
including genuine nonpositive equality/domain children. Ordinary recursive
f membership and the parent conclusion `H_f subset Phi(S).V` are not inputs.

Quantifiers retain every independently admitted complete carrier filling,
actual provider decomposition, zero-step/administrative/pending/complete
observation, compatible future demand and finite history. A complete d
retains its whole carrier, live world/configuration, context, typed receipt
and path preconditions, incidences, entry/body/consumer/invocation-return
ports, all shared evidence and hard guards. No marginal witnesses are chosen.

A_x is declared before f's challenge. A_y is below the actual enclosing
f-body dependencies and before g's challenge. A_z is below the actual
g-body construction dependencies and before drop's challenge. A later
EventProof depends only on its preceding inputs. ViewLogic stays in its
original description region. Shared fields and aliases retain one instance.
g[a] and drop[a,d] are actual event-indexed allocations, not fixed siblings
of f. The original c on the source diagonal is inside drop's argument Force,
before z rebind, and retains the unfinished drop suffix. This diagonal does
not restrict D's carrier quantifier.

Excluded: endpoint-shape identification, successful-query or stored-edge
axioms, diagonal-only checking, a no-Return proof, changed source domains,
weaker ordinary inference, invented adapters, new reconstruction semantics,
or assumptions of the missing D/P children. Independent primitive, guard,
annotation, license, context/action and W/Z cases remain genuine obligations.

**Result.** The native construction has the correct four variance directions,
including a real entry-effect port distinct from the body effect. It does
not emit the original complete carrier-interface interpretation needed to
apply the first domain rule below. The selected original schemas also leave
that interpretation as independent input rather than defining it from these
four ports. Section 4 locates the exact failed judgment before any use of
ordinary f membership. This is a bounded construction obstruction, not
impossibility, source rejection, or a refutation of the parent theorem.

## 2. Governing sources and evidence boundary

The governing definitions are the following exact sections, not index status:

| Source | Governing section / use |
| --- | --- |
| [Source Generalize selection](../design/2026-10-08-source-generalize-definition.md) | §§2–3 select the original rules; retain genuine L1–L5 |
| [Source Generalize construction](2026-10-08-source-generalize-definition-and-proof.md) | §2 L3/L4; §3.1 Parameter/Lambda/Call; §3.2(1–4) finite checks; §3.3 Desc/Check/ViewLogic/EventProof; §4 explicit local clauses |
| [Contextual membership selection](../design/2026-10-08-contextual-function-membership-definition.md) | §2 independent complete admission/observation interfaces; §3 immutable/positive cases |
| [Input realization](2026-10-08-call-semantic-input-realization.md) | §2 complete challenge/ActualAdm; §3.1–3.2 complete Function meaning; §4.2–4.3 Return/Delay |
| [Call input construction](2026-10-07-call-input-construction-proof.md) | §§3.1–3.4 actual origins, Entry-Value, Lambda and Code-Call/Check_c |
| [Complete closure selection](../design/2026-10-08-captured-closure-constructor-definition.md) and [construction](2026-10-08-captured-call-closure-introduction.md) | selection §§2–4; construction §§3–4 complete Strict and raw source prefixes |
| [Original Call formation](../design/2026-10-07-original-call-formation-definition.md) | §§2–4 OSig-Demand/OC-CallEff project a supplied complete F_c, not its admission proof |
| [Original source generation](../progress/2026-10-06-source-call-generation-construction.md) | §§4.2–4.4 original demand/root/elimination address; §5 operand checking meanings |
| [Top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md) | §§1,3–5 native inference, proof-derived implementation and necessary safety |

Prior reductions and audits were read as negative route information, not as
proof premises: the [finite-check note](2026-10-12-application-c-finite-check-proof.md),
[source bridge](../progress/2026-10-12-application-c-source-bridge.md),
[f-y inventory](2026-10-12-fy-complete-call-construction.md),
[nested introduction audit](2026-10-12-nested-recursive-l4-proof.md), and
[postfixedness attempt](2026-10-12-nested-recursive-f-postfixedness-proof.md).
The packet's short name `nested-f-postfixedness-proof.md` has no separate
located artifact; the full named postfixedness artifact above was used.

The source bridge supplies a conditional recovery-free CST/LocalSource trace.
This packet does not turn that into a parse or acceptance observation. Static
constructor statements below concern that named route with resources and
feature admission available. No solver execution or complete replay is assumed
to have occurred. The original Scala Typer is used only for its native
operations; it has no Yulang carrier, effect, receipt or future interpretation.

## 3. Native finite construction at the actual recursive operands

### 3.1 Owners and finite emission tree

Use native symbols distinct from the original complete interfaces: o for
f's active initializer row, n for c's callee Name row, X/Y/Z for the formal
value rows, R for c's result, and B_f for f's body result row. E_y and E_n
are the Name-y and Name-f evaluation effect rows. Q_c is c's fresh complete
invocation-effect demand row. E_c is c's application-effect row. E_x is f's
fresh entry-effect row and Q_f its fresh invocation-effect row; E_body_f is
the body computation effect. These symbols do not name I_x, J_y, F_c or xi.

`candidate_source.rs:250–328,369–410,445–473` retains f's active initializer
through the g body. Name f emits `Action::Link(o,n)` rather than a published
instantiation; Name y points to the actual Y recipe. Bare Name effects have
both bottom-lower and empty-upper constraints. Lambda recipes preserve the
formal/body/result/effect incidences. The actual source schedule executes
Link, Candidate and Lambda actions at `:664–683`.

The complete finite **native emission** tree at the central seam is:

```text
Local Name f while f active         Parameter Name y
--------------------------         -----------------
Link(o,n), Name effects             argument row Y, E_y
                 \                 /
                  actual Apply(c) recipe
                  ----------------------
        n <: Fn-(Y+, E_y+, Q_c-, R-)
        E_n <: E_c; Q_c <: E_c

formal x row X, original f body result/effect recipe B_f,E_body_f
----------------------------------------------------------------
Lambda(f): allocate E_x,Q_f at f's formal level
           E_x <: Q_f; E_body_f <: Q_f
           Fn+(X-, E_x-, Q_f+, B_f+) <: o
```

`shadow_apply.rs:1308–1402` checks the actual recipe incidence, constructs
that negative Function, records NativeInterface and invokes
`constrain_live_value`. Its following effect path sends callee and invocation
effects to E_c. `lib.rs:11233–11367` constructs the displayed positive
Function and sends both entry and body effects to Q_f. The inferred-entry
evidence retained there concerns this native entry-effect edge; it is not an
original whole-carrier admission proof. The distinct E_x/Q_f/body ports are
kept even for unused x. No body/invocation equality is used.

### 3.2 Polar extrusion and the four dispatch children

The source levels are o/X at 2 and Y/c at 3. The scalar native operations
carry a younger demand toward older o through the Name link. When that
structured demand is inserted at o, negative extrusion to level 2 keeps its
four fields in one operation-local polar memo. Write their images as
C, L, M, D respectively. For a younger row the positive and negative cases
give the following directions:

```text
Y <: C       E_y <: L       M <: Q_c       D <: R
o <: Fn-(C+, L+, M-, D-)                       [level 2]
```

If an endpoint already meets the target level its image is itself; these
names are not assertions that four distinct allocations must occur. The
copy operation retains its actual parent/polarity/target and traverses
the selected bounds. It does not retarget resolved f/y references or assign
new Value-reference incidences to a copied row.

Exact owners: `candidate_extrusion.rs:75–145` memoizes rows before bounds,
retains parent metadata and inserts the one-sided link; `:210–254` flips
the argument and argument-effect polarities together, preserving both output
polarities. `lib.rs:12415–12452` rewrites a structured bound using the
receiving variable's level. `candidate_extrusion.rs:808–835` inserts native
value bounds and calls the replay consumer, rather than solving each source
constraint at generation time.

For the actual positive/negative Function pair, the dispatch equation is:

```text
Fn+(X-, E_x-, Q_f+, B_f+) <: Fn-(C+, L+, M-, D-)
----------------------------------------------------------------
C <: X       L <: E_x       Q_f <: M       B_f <: D
```

These are exactly the four `FunctionField` children at
`lib.rs:12490–12549`. The child expressions contain neither a complete d
nor its carrier/context/receipt/future fields. Combining the native arrows
as mathematical constraint consequences gives

```text
Y <: X; E_y <: E_x; Q_f <: Q_c; B_f <: R.
```

This is a finite native derivation with the right directions. It is not a
claim that this run activated, acknowledged or fully replayed every edge.
Actual context transport and Function child admission/enqueue stages are
separate consumers (`lib.rs:12200–12305`). Nor does the displayed mathematical
composition authorize composition of successful concrete Function queries.

The original Scala `Typer.scala:48–83,106–125,134–155` independently explains
the value part: recursive monomorphic installation, `App` demand, opposite
bound replay, Function contravariance/covariance, and polar level extrusion.
It supplies no interpretation for the other whole-call coordinates. The
finite four-port tree above is read from the Y3 owners, not imported from
the Scala two-port Function or executed on a rewritten source.

### 3.3 What the surrounding g/drop scopes actually add

drop's body Name y uses the same Y after g entry rebind. Its native positive
Function has argument Z, captured result Y, its own entry effect and its own
invocation effect. Publication at boundary 3 and subsequent use can freshen
Z above that boundary; Y at level 3 remains the captured row. At
`drop (f y)`, Group preserves c's result/effect and Apply uses that whole
argument computation's projected R/E_c ports. This connects R to the fresh
drop formal and sends drop's returned Y toward g's body result. It does
not make Y the inner whole carrier or replace y by z.

g is published at boundary 2; its two later uses are separate Local routes.
`candidate_scheme.rs:1320–1382` stores root/boundary, captures the native
graph and prepares a fresh use at the use level. `g 0`, first's int target,
and `g ()` retain their respective application/annotation constraints.
They are neither a rerun of initialization nor independent choices for
aliased Shared/world fields. The [earlier two-use trace](../progress/2026-10-12-intrusion-admitted-two-use-witness.md)
§§2–5 supplies the detailed conditional lowering; no equality or SCC
qualification conclusion from that trace is assumed here.

These surrounding arrows do not introduce the arbitrary carrier tau of D.
The actual returned y is bound only after the actual g argument Return,
whereas tau is bound by **each independent F_c challenge**. A proof about
that returned y may be used on the source diagonal. It cannot stand in for
a strategy on all tau, and moving its witness above g's entry changes the
original telescope. No no-Return argument is used to omit the latent
first/final checks, drop entry, initial prefixes or compatible futures.

## 4. Attempted finite original check tree and the first failed judgment

### 4.1 Entry and Call require more than the native ports

The selected Parameter rule introduces `Desc(q_x,Value,sigma_x,Delta_x)`
and X at its original type scope. The actual Entry-Value schema in
Call-input construction §3.2 additionally requires:

```text
Capture(E,L_f,E_cap; actual edges)
ParameterOrigin(L_f,x,Value(A_x),r_x)
the original received-carrier port and DESIGNATED ENTRY VIEW
the original receipt/rebind ports
---------------------------------------------------------- Entry-Value
Receive; Receipt_f; Force_entry; Rebind(x) at those ports
```

The capitalized input is not supplied by the declaration of a value variable.
Its semantic interpretation is I_x, including inert formation, designated
execution, response/raw-continuation/future fields and original entry guards.
Strict §3.1 takes that entire I as input. It does not define I from the pair
of a native value row and an effect row.

Likewise Gen-Call-0 introduces the dependent **complete** scoped F_c variable;
its interpretation and admission law remain unsupplied here. OSig-Demand and
OC-CallEff retain and project its full invocation root. They do not define
CarrierContract(F_c) from `Fn-(Y,E_y,Q_c,R)`. Code-Call §3.4 retains
VIncl/WholeArgCompatible origins; it expressly contains no truth of those
relations. Source Generalize §4 generates the original local evidence
clauses, not an interpretation of missing operands by shape.

At the executable boundary, `candidate_call.rs:30–58` defines NativeInterface
with callee, argument, callee/argument/application effects, result, demand,
invocation effect and its row. These are Term/row fields, not original
complete-interface or local checking derivations. `:217–243` leaves
OriginalGenCall0, ArgumentReifyAndWholeCarrier and
ReceiverDispatchAndCompleteResultFutureInterfaces pending for this Local
callee as well. Thus the native finite diagram has an authentic emission
owner, but its original domain proof is not an output of that owner.

This is the first unavailable constructor/interpretation judgment:

```text
At c's ORIGINAL joint telescope and full interfaces,
interpret the emitted contravariant argument/entry-effect construction
as an original STRUCTURAL WHOLE-CARRIER domain derivation
from CarrierContract(F_c) to actual I_x,
with the original context/receipt/path guard action and A_f challenge fields.
```

This notation describes a missing instance of Source Generalize §3.2(4),
not a proposed new predicate or runtime layer. Neither member membership
nor the desired domain inclusion is its admissible input. The missing
construction must first identify those actual full interfaces using their
own source entry/Call records, then give their finite local proof children.

### 4.2 Exact rule tree attempted at one arbitrary complete challenge

Introduce arbitrary `d : D_F_c(e)` at the original challenge binder; set
tau to **that** d's whole carrier. Input-realization §2 projects its
checked carrier admission and its original complete contextual fields.
For the strict original entry/challenge route, the attempted tree is:

```text
d : D_F_c(e)
------------- independent complete challenge elimination
a_F : Acc(CarrierContract(F_c); tau,C_e,w_e,eta0,xi)
g_F : checked original context/path/receipt fields of this SAME d

native children Y <: C <: X and E_y <: L <: E_x
??? authentic complete carrier-interface / structural domain child
-----------------------------------------------------------------
a_x : Acc(I_x; tau,C_e,w_e,eta0,xi)
g_x : actual U_f receipt/path/context fields at this SAME event
??? remaining original A_f complete challenge fields
-----------------------------------------------------------------
d : D_A_f(e)                                      [required D]

??? actual S-indexed observation constructor children at these ports
-----------------------------------------------------------------
o : P_A_f[S](d)  ->  same o : P_F_c[S](d)          [required P]
-----------------------------------------------------------------
k_c : complete original Function check(A_f,F_c)   [not derived]
```

The first `???` is a failed application, not an oracle leaf. Even granting
the native arrows' strongest ordinary value/effect semantic interpretation
would supply only projected value/effect implication. Applying structural
checking to **whole carriers** still needs the original carrier constructor
at both operands, its formation/license and execution clauses, and the
typed dependent context/guard children. No selected schema equates those
full operands to a two-field pair. The ordinary X/Y parameter declarations
and g's actual y Return are not evidence at that arbitrary tau binder.

This identifies a precise missing judgment earlier than applying Theorem F:
the local structural domain child has no established complete-interface
instantiation. This is not the previous conditional calculation
`CarrierContract(U_f)=I_x => ActualAdm`; it attempts the rule that would have
to create its admission premise, using all four native constructor children.

### 4.3 A discriminator for the unsupported native-only implication

The gap can be checked without choosing new source semantics. The native
four-child inequalities use only value/effect operands. Add
the supplied challenge projection `a_F`. In that **projected formula
language**, interpret its carrier admission predicate as true on tau while
interpreting the distinct actual I_x admission predicate as false on tau.
Give the operands of those four inequalities the same value interpretation
and their effect operands the same empty-effect interpretation. Those four
inequalities and a_F remain true, and a_x is false. Preserve the same tau,
event and provider; no alternate witness is used.

Thus the first domain child is not a logical consequence of the native
four inequalities plus checked admission alone. This is a small logical
discriminator for that proposed implication, **not** an original-model or
source-qualified counterexample: it does not instantiate the missing
entry/Call interface law, all surrounding annotation constraints, complete
P, independent W/Z laws or f's L4 introduction. A full original construction
could constrain those admission predicates and invalidate this completion.
It would then be the required new evidence, rather than something already
proved by the native diagram. No claim that actual source guards fail follows.

### 4.4 P cannot be completed from the remaining two native children

The native output children `Q_f <: M <: Q_c` and `B_f <: D <: R` are
covariant at their native ports. They do not instantiate the original
observation constructors for initial receipt, entry Force, body/consumer
suspension, typed response/raw continuation, complete invocation return or
output-dependent future providers. Source Generalize §3.2(4) permits genuine
constructor congruence and finite recursive equation pairing, but requires
the actual equations and nonpositive domain/equality children.

In particular B_f is the native body result, whereas R is c's application
result. Complete Strict and ReadInvoke interfaces include entry and consumer
ports and their pending suffixes. A correct covariant native result edge
does not identify those interfaces. Original P proof children at S must
preserve the observation's same decorated value/world/provider and all its
licensed dependencies. Positive lifting of a native value edge to S.V is
not a selected original checking constructor. The ordinary Theorem F/R/E
route additionally needs ordinary f membership; it does not discharge this
relative P child. No P equality or omission of future cases is concluded.

## 5. Obstruction ownership and obligation-economy disposition

Two earlier methods reached this seam: exact pair/Step constructor fitting
and event-indexed postfixedness with ordinary endpoint checking. The prior
finite-check note left the same admission child unsupplied. The required
economy audit was therefore applied **before** this native-construction pass:

- A/B remains: original complete receiver admission, recursive checking and
  natural inference cannot be retired as optional characterization.
- Parameter owns the value declaration; Lambda/Entry owns I_x and its actual
  received-carrier/designated-view/guard operands; Application owns F_c and
  the complete local check. Installation owns the separate parent L4 law.
- Native owners really know the four polarized edges and their parent/copy
  provenance. They do not thereby know the semantic complete carrier law.
  Retaining those edges is useful evidence but does not discharge that law.
- The constructional remedy under consideration must attach the original
  full carrier/check evidence **where its semantic owner constructs it**.
  Reconstructing it from solved endpoints or adding another relation that
  assumes D/P would be reconstruction debt. No such remedy is adopted here.

This pass answers the concrete question about recursive f entry and actual
g/drop scope: they produce the necessary native projected directions and
keep the right resolved operands, but the selected constructor inventory
does not derive their required whole-carrier/context interpretation or
S-indexed observation children. That is a bounded missing local law/instance,
not proof of inability of native Simple-sub or rejection of this program.

**One next action:** the primary assigns the original Entry/Call semantic
constructor owner the specific structural argument-domain instance above:
authenticate actual I_x and CarrierContract(F_c), including their full
formation/execution/guard fields, and construct the domain child directly
from the actual contravariant native construction at the original telescope.
Its complete checking tree must also supply P's actual S-indexed children.
Until that evidence exists, another endpoint reduction, assumed-transition
checker or renamed coalgebra should not be counted as progress. D/P and the
parent theorem remain OPEN.

## 6. Verification, resource use and runtime

Checks performed: bounded `cat`, `sed`, `rg` static source/rule reads; hand
instantiation of the native four-port emission/extrusion/dispatch diagram;
the finite failed original checking tree; and SHA-256 dependency snapshots.
Leased-file whitespace/fence/local-link checks passed; initial/final
dependency hashes were identical. This is artifact integrity, not proof
checking or independent review.
No parsing, solver execution, tests, builds, numerical probes or performance
experiments occurred. Zero inference samples and zero heavy processes;
at most four initial concurrent lightweight read processes. CPU/RSS and
exact elapsed reasoning time were not instrumented.

I initially ran read-only `git rev-parse HEAD`, `git branch --show-current`
and `git status --short` before applying the packet's no-Git boundary. They
reported the supplied baseline/branch and an unrelated pending question
directory. This boundary mistake was reported to the primary. No Git
mutation or subsequent Git command occurred, and that directory was untouched.
No other specialist was contacted or launched; no external recipient or
user decision was requested. Only this exact leased file was written.

Requested routing: ordinary Sol/high prover leaf. Observed identity:
`/root/fy_source_call_dp_construction`, with the supplied prover contract.
Effective runtime model/effort metadata: **unknown**. `.codex/config.toml`
registers prover and defaults subagents to gpt-6.1-sol/high; prover's role
file omits both pins and the callable schema includes prover. These are
configuration/schema facts, not proof that an override or hot reload ran.
No Astra escalation or self-certification is claimed. The yulang-proofs
skill was applied within the primary's explicit leaf-only scope.

Unverified: exact-byte parse/production source reachability, source admission,
actual complete entry/demand emission and interpretation, activation/replay
completion, D/P, other guard/primitive/annotation/W/Z laws, all parent L4
clauses and background embedding, effects/hygiene, qualifying intrusion,
generalization, soundness, required principality, and production cutover.

Dependency snapshot (revalidate at integration; the Scala path is external
to this Git repository):

```text
2f84356158426711bf81f099ca99748fa320d2bbc52876a08a73fcdaabc25d2c notes/theory/2026-10-12-application-c-finite-check-proof.md
ee6cb83fcb1dac503cc69f78d2249d9614712b3f741b897423b816408ec5058e notes/progress/2026-10-12-application-c-source-bridge.md
73810fef85c264e02a179b8630d4c392fdc0f5369123cb1a4cbe7cfecb2eccb2 notes/theory/2026-10-12-nested-recursive-f-postfixedness-proof.md
657ccdf993aca04085de6857520d05bd26f207e5cf04146dcd98f39465c83540 notes/theory/2026-10-12-nested-recursive-l4-proof.md
3bcc290f0fab01f08272d83c358f491df377da46f2022412c176184533d9f872 notes/theory/2026-10-12-fy-complete-call-construction.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38 notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 notes/theory/2026-10-08-source-generalize-definition-and-proof.md
0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0 notes/design/2026-10-08-contextual-function-membership-definition.md
fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a notes/theory/2026-10-08-call-semantic-input-realization.md
6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd notes/design/2026-10-08-captured-closure-constructor-definition.md
0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f notes/theory/2026-10-08-captured-call-closure-introduction.md
f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6 notes/theory/2026-10-07-call-input-construction-proof.md
4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f notes/design/2026-10-07-original-call-formation-definition.md
6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073 notes/progress/2026-10-06-source-call-generation-construction.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389 notes/design/2026-10-11-yulang-inference-top-level-principles.md
653861f60a148cbb1fcddf71b6426f58124f7fe9fbe353be2e2b8ea2ed86d768 notes/progress/2026-10-12-intrusion-admitted-two-use-witness.md
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49 crates/yu-solver/src/candidate_source.rs
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35 crates/yu-solver/src/candidate_call.rs
cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411 crates/yu-solver/src/shadow_apply.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94 crates/yu-solver/src/lib.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0 crates/yu-solver/src/candidate_extrusion.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1 crates/yu-solver/src/candidate_scheme.rs
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9 /home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala
```

## Commit packet

- Exact leased path: `notes/theory/2026-10-12-fy-source-call-dp-construction.md`.
- Baseline SHA: `5cb4ba6f9cc8fa65d347c3b53b6d4e6e5196d02f`.
- Changed dependency hashes: none; initial/final snapshot comparison passed.
  No dependency file was written.
- Claim/review: reviewed bounded native construction and original
  finite-derivation obstruction; one minor wording correction repaired by the
  primary; no theorem or parent-gate promotion.
- Checks already run: static constructor/rule inspection, hand four-port
  derivation and failed original tree, dependency snapshot and leased-file
  integrity; zero executable compiler checks.
- Proposed checkpoint message: `research: locate native fy to complete carrier checking seam`.
- Shared-record deltas for primary/curator: record the four native variance
  chains as static constructor evidence, and the original whole-carrier
  structural-domain instance as the first missing judgment. Preserve P's
  original observation/recursive/nonpositive children and keep D/P, L3-at-c,
  L4, complete Call, inference and production OPEN. No shared record or
  authoritative definition changed.

Writes stop at handoff. Independent review and integration remain primary-owned.

# Active-root helper: source registration and Call construction frontier

Date: 2026-10-13
Status: frozen unreviewed bounded constructor audit; no source theorem, semantic adoption or implementation authority
Baseline: `f44d4e660d7eb1cf43d9cf863fb4fe0a834a8778`
Prior shared-C review/task checkpoint: `0e3532ead` (primary-supplied provenance)
Reference: `9bae772624c23b52a93c1b226157e16898b4d9db`
Exclusive output lease: this file; proof leaf, no delegation
Method/budget: one static constructor/inversion pass; no implementation, builds, tests or inference experiments
Classification: existing authority; no compiler behavior change; internal cross-layer research; cold static reads

## 1. Frozen statement, inputs and outcome

Use exactly

```text
let rec f = lambda x.
  let g = lambda y. (lambda z. y) (f y)
  in {a = succ (g 0), b = g true}
in f
```

Keep the recursive binder f, nonrecursive binder g, all three Lambda binders
x/y/z, both record fields and all five Apps. No source normalization removes
the ignored recursive Call, changes a result provider or supplies a new
checking boundary. The approved operation qualifies the actual G/F extrusion
occurrence and equates its retained signed pairs; description freshening
creates no new extrusion event or Value-reference edge.

The requested bridge must construct, from actual source registration and
App/Call/extrusion owners, an authentic g publication with its complete source
program and original binder tree. For every finite lawful joint client
derivation at this publication, its independent g frames must preserve one
active monomorphic f root and the actual native operand incidences, including
the approved C=B equality. Actual providers, initializations, worlds,
receipts, witnesses, attachments, resumptions and residual lineages retain
their original scopes and dependencies. Required conclusion: source-derived
registration, operand interpretation and allocation into both actual g-use
frames; no independently assumed K_g, complete Q_c, C telescope, equality
placement or frame map.

Hypotheses are the selected local source laws L1–L5 **at their stated scopes**,
the approved root-reference/occurrence decisions, and the fixed source and
native history. L1–L5 are conditions on genuine source derivations, not an
assertion that this source already satisfies them. The native scalar history
does not supply a complete Yulang Call derivation. The requested universal
soundness/principality conclusions are not hypotheses. No independent choice
of marginal witnesses, fresh C_i, supported-source restriction or alternative
meaning of equality is allowed.

**Outcome:** no requested source-qualified derivation follows from the
inspected constructors. There is a more precise frontier than “Name f is
unavailable”: registered-root reference and static capture of an active f are
supported. The unavailable application is construction of the g publication's
complete dependency records and source telescopes for that imported open
relation and the actual App/extrusion/equality clause. The existing Call and
Generalize rules consume those inputs; neither synthesizes their missing
native-to-source interpretation. Section 4 gives the minimal tree exposing
that distinction. This is a bounded characterization of supplied constructors,
not a proof that no lawful future definition can exist or that this source is
rejected. The original parent gate remains OPEN.

## 2. Exact governing sections

| Source | Governing scope used |
| --- | --- |
| [Source Generalize selection](../design/2026-10-08-source-generalize-definition.md) §§2–4 | Selects construction §§3–5; complete original source programs and scopes; local laws remain premises |
| [Generalize construction/proof](2026-10-08-source-generalize-definition-and-proof.md) §2 L1–L5; §§3.1,3.3–3.4,4,5.1–5.3,6–7.0 | Parameter/Name/Bind/Call/recursive grammar; typed owning records; Build; publication-indexed walk; whole-frame allocation; open recursive grammar versus actual L4 closure |
| [Local self-recursion](../design/2026-10-10-local-self-recursive-binding.md), Selected source behavior; Proposed source-to-solver seam; Required invariants | Nested active f reference uses one open monomorphic root, installation follows initializer formation |
| [Native recursive interface](../design/2026-10-08-native-recursive-interface-definition.md) §§1,4 | Selected simultaneous two-closure pair; general recursive initializers remain independent |
| [Call input construction](2026-10-07-call-input-construction-proof.md) §§3–3.4 | Binding certificate and Capture-Lambda are static interfaces; Code-Call requires authentic Application/check/reify origins and complete suffix |
| [Source Call interface definition](../design/2026-10-08-call-source-interface-definition.md) §§2–4, selecting [IF construction](2026-10-08-call-source-interface-construction.md) §§2,3.2,4–6 | Preallocated declared interfaces and finite monomorphic cycles; IF-Insert/IF-Use retain supplied whole clauses and substitutions |
| [Original Call formation](../design/2026-10-07-original-call-formation-definition.md) §§1,3–4,6 | OSig-Demand/OC-CallEff on already emitted Gen-Call-0; do not assert generation for all Apps |
| [Occurrence qualification](../design/2026-10-12-intrusion-value-type-association.md), Approved extrusion-event qualification; Definition-root origin; Qualification | Actual occurrence, G/F endpoints and all produced pairs; no permanent owner inferred from a type ID |
| [Parent/copy decision](../design/2026-10-10-parent-copy-scc-intrusion.md), Selected operation; Definition-root Value ownership | Equality affects solving/later use; root incidences are explicit source references |
| [Copied-row ownership](../design/2026-10-12-value-reference-copied-row-ownership.md), Decision; Scope | Type copying does not copy or retarget Value incidences |
| [Inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md) §§1–5 | Native generation, bounds, propagation, extrusion and generalization; preserve ordinary behavior |

The prior [nested allocation derivation](2026-10-13-nested-live-root-generalization-derivation.md)
§§3–7 supplies the reviewed native shared-C calculation. The reviewed
[representation obstruction](../progress/2026-10-13-shared-c-source-bridge-falsification.md)
§§3–5 remains conditional on endpoint/equality correspondence. The
[Call-owner inversion](2026-10-12-fg-call-c-endpoint-construction.md) §§3–5,7
already distinguishes supplied complete Call clauses from native scalar
generation. This packet attacks their construction input, rather than
repeating the scalar contradiction.

## 3. Original source tree and scopes

Use c1–c5 only as occurrence names, not new source binders:

```text
LetRec(f,
  Lambda(x,
    Let(g,
      Lambda(y,
        App_c2(Lambda(z, Name(y)), App_c1(Name(f), Name(y)))),
      Record(a = App_c4(Name(succ), App_c3(Name(g), Int(0))),
             b = App_c5(Name(g), Name(true))))),
  Name(f))
```

All resolved Names retain their original targets. At f's publication the
definition-root rule retains F→G from c3/c5; at g's definition it retains
G→F from c1. These justify G/F SCC qualification for an authentic occurrence;
the Value cycle does not supply a source validating component or telescope.

The source type/event order is:

```text
recursive f registration; sigma_x (x description before f challenge)
  h_x: actual f invocation, receipt/Force_x/Return-rebind x
    g formation/publication p_g(h_x)
      sigma_y: y description before g challenge
        h_y: actual g invocation, receipt/Force_y/Return-rebind y
          Lambda z formation captures the same rebound y
            sigma_z: z description before its own challenge h_z
              h_z: receipt/Force_z/Return-rebind z; body Return(y)
          c2: inert whole argument is Delay(code(c1))
            c1: Name f; inert Delay(Name y); actual f receiver/suffix
    after g publication: c3 (first independent g use), c4 (succ consumer),
                         c5 (second independent g use), record return
f installation/publication; final Name f
```

The displayed h_z region specifies the wrapper's source entry. Its designated
Force consumes c2's delayed c1 argument before rebinding z; c1 is not a
source expression in the wrapper's body. These are source interfaces, not a
claim that recursive execution returns or reaches every subsequent event.
Pending c3/c4 prefixes retain their complete record/suffix obligations.

Parameter supplies an ordinary pre-challenge declaration when registration
and its genuine telescope are supplied. Thus
`Desc(K_g,q_y,Value,sigma_y,Delta_y)` is the **required conditional output**,
not an established K_g registration for this program. The lexical order of
sigma_y is fixed above; the complete Delta_y and the source placement of
native C/D must still come from actual owning introductions. Numeric native
levels are not these dependent telescopes.

## 4. Minimal constructor tree and first unavailable bridge

### 4.1 The active f reference has a static route

Call-input §3 defines a binding certificate as the declared interface/root,
not semantic membership. Capture-Lambda restricts the actual dependency-closed
free-binding graph and retains its imported certificate and sharing. IF
§3.2 exposes a registered root's declared telescope before clause formation;
§§5–6 permit preallocated recursive roots and finite monomorphic cycles.
Consequently, conditional on authentic registration/telescope inputs:

```text
reg_f: one registered open root o; actual Resolve(u_f,f)
  -> Capture-Lambda / ImportRestriction retains the same root/interface
  -> Name(E_c1,u_f) selects that registered interface
  -> Data-Name; Code-Result yields code(Name f)
  -> IF-Use retains its actual scoped reference, without a new f instance
```

Local self-recursion independently fixes the monomorphic open-root behavior.
An open recursive source proof grammar may reference f before hereditary L4
introduction is closed (Generalize §§3.4,6). Therefore absence of a **completed**
f semantic certificate does not prohibit this static reference or force eager
constraint solving. Conversely, this static derivation does not discharge L4
for the actual recursive body.

### 4.2 What is missing when the body is assembled

Keep every child in the tree:

```text
Parameter y; registered/captured Name f and Name y
  [authentic Application_c1, whole Reify/check origins, complete suffix]
  --------------------------------------------------------------- Code-Call c1
  code(f y) with whole carrier, receiver, result/effect/future interface
  [source interpretation of actual native App/extrusion e and C=B,D=R]
  --------------------------------------------------------------- MISSING BRIDGE
  same complete clause, actual e/G/F/pairs and original binder incidences

Parameter z; capture same rebound y; Return(y) -> Lambda z
  + complete code(c1) and c2's authentic Application/check/suffix -> Call c2
  -> Lambda y -> Bind's actual g Return/rebind/publication p_g(h_x)
  [actual component/records for imported still-open f relation and that clause]
  --------------------------------------------------------------- MISSING RECORD
  (p_g, authentic K_g, T_g, complete N_g, root, owning dependency records)
  -> Source Generalize §5.1 fixed walk -> §5.2 allocation
  -> independent g frames i0 at c3 and i1 at c5; c4's succ consumer
  -> record return -> Lambda x -> actual L4 f introduction -> final Name f
```

The bracketed Application input is an inherited complete-Call formation
premise. Even if supplied hypothetically, the next missing bridge remains:
Code-Call consumes its authentic complete F_c1, checking origins and result
suffix; it has no rule deriving their relation to
`o <: Function(B,R)`, its extrusion operands and the qualified equality.
OSig-Demand/OC-CallEff read already emitted records. IF-Insert places an actual
typed clause; IF-Use requires its actual whole scoped substitution. Neither
turns a polar memo/type bound into a substitution on carrier/world/license/
receipt/result/future fields. The first unavailable **native-to-source** rule
application is therefore at c1, before g's completed body/publication.

The second bracket is the corresponding Generalize input frontier. Its walk
is indexed by actual p,K; it cannot infer K_g from the Value SCC. Its records
cover own registered Live/Internal relation edges and installed external
Mono/Established contracts. Here f is active and uninstalled, and no inspected
owning application supplies how g's relation retains that open f tuple and
the actual Call/equality clause at publication. Static import admissibility
does not classify this dependency for the publication walk. This is missing
construction evidence, not a prohibition on active capture.

Do not infer that a particular tag is the sole possible future solution.
Even hypothesizing `Internal(K_f,f)` retained through the import does not
derive the actual g component, C's original incidence or equality transport.
Hypothesizing `Internal(K_g,f)` requires a registration output not established
by sequential source binding; hypothesizing Established requires an installed
contract not present at this cut. The simultaneous pair and rebound-formal
examples of §5.3 do not provide either application. They have respectively
actual joint registration and an actual installed formal contract.

### 4.3 Why the whole-frame theorem cannot fill the leaf

Given an authentic N_g/T_g and classification, Build preserves its complete
clauses and §5.2 deterministically translates their existing operands.
For illustration only, **if** that input declares one shared incidence c and
a frame-eligible B and places c=B as an active complete source clause, its two
new events retain c=B_0 and c=B_1. SRC-J then reasons about one strategy on
that entire joined tree. This is conditional rule elimination, not the
missing constructor. No allocation rule infers the condition from C's native
level or shared storage in f's bounds.

The base-event-only equality, per-frame equality and their activation timing
cannot be chosen here. EventProof may vary certificates of shared actual
operands; it does not replace an equality operand. Source closure cannot
discard c1 because the wrapper ignores its returned value. A quotient C↦B
does not supply the absent original telescope or complete clause action.

## 5. Native Scala and current Rust: separate established outputs

The original Scala owners are `Typer.scala:48–55,62–83,106–159,166–207`:
recursive f has root o at level 1; g's B/Z/R/S are level 2; c1 generates
`o <: Function(B,R)` and negative extrusion creates C/D at level 1 with
`B <: C`, `D <: R`, `o <: Function(C,D)`. c2 generates `R <: Z`, `B <: S`.
Publication is `PolymorphicType(1,Function(B,S))`. Each use freshens above 1
with one coherent map, hence B/S have independent images while C is literally
shared. The reference has no intrusion operation. It establishes the native
map on this graph, not a Yulang source telescope or complete Call meaning.

| Actual current owner | Retained output and limit |
| --- | --- |
| `yu-hir/src/module/local_source.rs:329–372,636–657` | Parameterized local initializer temporarily retains its binder identity; Names retain resolution. This inspected carrier does not establish an exact end-to-end route for the displayed Lambda-valued let source. |
| `candidate_source.rs:245–325,375–411,660–686` | Active initializer lookup emits Link, not local freshening; Apply retains actual child endpoints/source occurrence and a candidate recipe. Apply owner is `source.definition_root()`, not an emitted local G/F occurrence certificate. |
| `candidate_scheme.rs:1320–1386` | Installation retains local id/root/boundary; later local use captures that graph and prepares a fresh use. No Source Generalize record/telescope is emitted by these installers. |
| `shadow_apply.rs:1308–1420` | Recipe integrity is checked, four-port native demand is created, NativeInterface retained, provenance admitted, and `constrain_live_value` actually invoked. This is activation of candidate native constraints, not complete source Call generation. |
| `candidate_call.rs:15–59,88–126,152–258` | Formal/Name/Apply records retain source and native coordinates; pending supplier API separately requires original Gen-Call-0, whole argument and complete receiver/result/future interfaces. |
| `candidate_extrusion.rs:21–25,89–126`; `candidate_intrusion.rs:23–28,171–222` | Copy creation retains parent/polarity/target, before bound traversal. Parent has no occurrence identity, G/F Values or original source telescope. |
| `candidate_intrusion.rs:360–487` | SCC graph is built from type/effect bounds and Function ports and compares canonical parent/copy rows. This does not implement the approved Value-reference occurrence test. |

These real producers support a natural retained-evidence owner. They do not
prove that an authentic Generalize source registration or equality clause is
already emitted. No runtime rejection, whole-compiler absence or exact source
admission claim follows from field inspection. No stored constraint is treated
as proof of its complete source replay: the native admission call above is
traced explicitly, while source/equality replay remains unverified.

## 6. Economy audit, coverage and next action

The prior allocation derivation and representation falsification already left
this premise untouched. Under compiler-engineering's economy rule, the parent
preservation/principality obligation stays A/B. Recovering the publication
dependency, actual native-demand operands and their source scopes from IDs,
numeric levels or solved bounds is D reconstruction debt. The constructors
already know the active root, exact Apply children and generated polar pairs;
an authentic retained output belongs at those owners. Retention alone would
not prove its complete semantic interpretation. Another scalar assignment,
new tag census, model layer or reclassification would not discharge this
premise.

One next action for the primary's source-construction owner: establish the
actual g publication input by a named registration/Call rule application
retaining the imported open f relation and the c1 App/extrusion/equality
clause at its full original telescope; prove its operand action commutes with
the unchanged native freshening map, then apply the existing Generalize walk.
If that application yields the conditional shared-C obstruction, return the
source-qualified contradiction to the existing authority path. Dependent
implementation and parent closure remain OPEN. No third equivalent proof
variant is recommended.

Checks: bounded cat/sed/rg owner reads; manual source constructor substitution
and inversion; read-only Git status/revision, direct dependency-byte comparison
to baseline and SHA-256. Broad combined captures initially truncated; decisive
constructor windows were reread narrowly. One guessed `candidate_value.rs`
path and absent top-level `spec/` search produced no evidence. Zero builds,
tests, inference runs, probes, benchmarks, measurement samples, heavy
processes, children or Git mutations. Initial independent read batches used at
most four short shell processes concurrently; later owner reads/hash operations
were sequential. No exact CPU/RSS/wall-time measurement was recorded.
Rules and yulang-proofs skill were read; the leaf performed no delegation.
Configured ordinary prover routing is Sol/high with unpinned role keys;
actual requested launch settings and observed model/effort metadata are
unknown to this leaf. No Astra assignment ran in this packet.

Unverified: complete source admission and primitive/entry declaration maps,
authentic Application/Q_c construction, the missing source interpretation and
publication records, actual equality activation/complete replay, original L4,
all-source soundness, required principality, effects/hygiene, future/lifecycle
coverage, termination, production correspondence and F5 replacement.
Independent review is pending and primary-owned. Writes stop at handoff.

## 7. Frozen dependency hashes and commit packet

All following repository inputs byte-match the pinned baseline. No dependency
was changed by this worker. Reference HEAD and Typer.scala hash were inspected
separately; reference execution was not run.

```text
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38 notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 notes/theory/2026-10-08-source-generalize-definition-and-proof.md
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895 notes/design/2026-10-10-local-self-recursive-binding.md
a9f833556a7e7c361c5b602c982de96b78663a77099999206bdb7bda6da67903 notes/design/2026-10-08-native-recursive-interface-definition.md
4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f notes/design/2026-10-07-original-call-formation-definition.md
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c notes/design/2026-10-08-call-source-interface-definition.md
f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6 notes/theory/2026-10-07-call-input-construction-proof.md
278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98 notes/theory/2026-10-08-call-source-interface-construction.md
28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775 notes/design/2026-10-12-intrusion-value-type-association.md
6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b notes/design/2026-10-10-parent-copy-scc-intrusion.md
7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd notes/design/2026-10-12-value-reference-copied-row-ownership.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389 notes/design/2026-10-11-yulang-inference-top-level-principles.md
f72404c661736ee9e0b6226dfc471724795836510c7aa3a0582d209be47f8dd9 notes/theory/2026-10-13-nested-live-root-generalization-derivation.md
75764f0d3cc7d3b9a2a0e7a9d79eb3b74a4c02eb1bb9b320c26a96ba80dee41b notes/progress/2026-10-13-shared-c-source-bridge-falsification.md
eb5ca0a72d2ec274f3c27ad1f50fb9211ec1ba8d5c45b803843e22b286bb2200 notes/theory/2026-10-12-fg-call-c-endpoint-construction.md
897a7bc108349d9ba8eec905f4490e564f54c71d8df11d7b72ad25016452d6ee notes/theory/2026-10-11-adopted-invoke-precall-construction.md
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed crates/yu-hir/src/module/local_source.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49 crates/yu-solver/src/candidate_source.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1 crates/yu-solver/src/candidate_scheme.rs
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35 crates/yu-solver/src/candidate_call.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0 crates/yu-solver/src/candidate_extrusion.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0 crates/yu-solver/src/candidate_intrusion.rs
cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411 crates/yu-solver/src/shadow_apply.rs
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9 reference Typer.scala
```

- Exact leased path: `notes/theory/2026-10-13-active-root-call-source-construction.md`.
- Baseline SHA: `f44d4e660d7eb1cf43d9cf863fb4fe0a834a8778`; changed dependency hashes: none.
- Claim/review status: bounded constructor characterization; unreviewed producer output, no source theorem or parent closure.
- Checks already run: static tree/inversion/owner reads, baseline/dependency equality and hashes; no builds/tests/probes.
- Proposed checkpoint message: `research: locate active-root helper Call registration frontier`.
- Shared-record deltas left for primary/curator: distinguish admissible static active-root reference from missing complete g publication/Call telescope and equality transport; retain source admission, preservation/principality and original parent gates OPEN. No shared task, theory map, design index or authority file edited.

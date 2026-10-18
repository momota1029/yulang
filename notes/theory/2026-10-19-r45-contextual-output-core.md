# R45: contextual output construction stops at the Application introduction

Status: **candidate source-rule audit and exact obstruction; not a reviewed theorem**.
Parent: unchanged full inference/evaluator theorem and original Simple-sub A/B,
**OPEN, 0 → 0**. Contract: `application-output-derivation-20261019-r45`, revision 1,
SHA-256 `e8e6460eb19500383d71cc6b6b217f294ae8acbf3bfedb48b6beab5ff8457c77`.
Source baseline: `6bf4236c8`; `c3b764578` contains the subsequent frozen contract.
Author: `/root/r45_contextual_core`; no coauthors or descendants.

## 1. Actual result and parent application

The contextual-metavariable construction does not supply an Application output
owner from the pinned rules. Its declaration needs exactly the missing source
introduction and dependency telescope. The first blocked output judgment is:

```text
independent resolved operand derivations at q; original source registration
  ⊢ IntroOut_q : Desc(C_q,rho_A,ValueDescription,sigma_A,D_q)
```

`IntroOut_q` is a name for the missing evidence, not an added source rule.
The evidence must identify the actual introduction, its source component,
original type scope, and exact ordered free dependencies before the first
output-indexed Call header. No instance of that evidence is constructed here.
This is a bounded non-applicability finding about the selected sources; it is
neither a global nonexistence theorem nor a counterexample to an accepted q
typing. Confidence is high in the displayed premise inversion, and UNKNOWN
for whether some additional authoritative source supplies the missing owner.

Applied to the parent, the reviewed Generalize theorem cannot yet be instantiated
at this output declaration, and Code-Call/interface formation cannot be used to
generate the declaration they consume. The original missing premise remains
open. This attempt changes the method from R44's context-inclusion argument to
rule inversion and explicit substitution; it does not claim another conditional
theorem has reduced or closed the parent. The next responsible owner is Luna's
Application source-rule authority lane. Another rearrangement of the same
consumer premises will not discharge this introduction.

All original accepted source cases, independently admitted challenges, joint
client predicates, provider-indexed futures, independent incoming frames and
aliases remain required. F1 and FK1 remain separate obligations. No local
frame action here establishes the foreign-continuation quantifier.

## 2. Stage 1: source construction and the first unsupported owner

The target is the helper body in the selected source:

```yu
my outer = { my loop x = { my direct = loop x; my helper y = loop y; my first = helper x; my second = helper x; helper x }; loop }
```

Write `q = Application(Name(loop),Name(y))`. The direct `loop x`, the helper
invocations, their invocation results and the loop body's final result remain
different occurrences. A syntactic name does not select an owner class.

The pinned Code-Call input construction §§3–3.1 gives a real way to derive
operand code *when* the registered bindings and resolution/capture evidence
are provided:

```text
Name(E,loop) = (b_loop,edge_loop), b_loop.interface = I_loop
  => Data(E,name loop,I_loop; b_loop,edge_loop)
Name(E,y) = (b_y,edge_y), b_y.interface = I_y
  => Data(E,name y,I_y; b_y,edge_y).
```

Its `Code-Result` requires the original result port for a Value interface;
its `Code-Consumer` requires the actual designated port and ConsumerOrigin
for a Computation interface. The typed core §6 gives an unannotated parameter
`y` a Value entry and a fresh parameter endpoint at its original parameter
scope. It does not give the Application a parameter declaration. Generalize
§3.3 supplies Live/Internal at an actual recursive registration and retains
the original certificate through a resolved Name; it does not authorize
reclassifying a capture by spelling or treating it as a new publication.

The selected documents do not enumerate q's complete concrete registration,
capture and port records. The displayed derivations are rule instances with
those explicit unresolved inputs, not a claim to have constructed their full
q certificates. Granting independently supplied operand certificates still
does not close the output-owner step below. Thus the obstruction does not
depend on silently choosing a component partition or weakening an operand.

| Pinned source rule | What it actually supplies | Why it does not introduce this output |
| --- | --- | --- |
| Typed core §6 Application row | `Computation(E_call,A_call)` and `reify(call(n_f,n_a))`; symbolic endpoints constrained by complete invocation | It supplies the result role and translation, with existing invocation premises; no `Desc` owner/free-dependency constructor is specified there. |
| Code-Call §3.4 | Code and Check from child code, actual Application origins, whole-argument reification, compatibility origins and suffix ports | `Comp(E_c,A_c)` and original result port `o_c` occur above the rule's line. |
| Source-interface construction §§2,4–6 | Complete contextual frame and insertion/use incidences, including generic return/future fields | Authentic original `Q_e`, original result/check origins and independently typed declarations are inputs. |
| Generalize §3.3 and §4 Build | An endpoint record from Parameter, written hole or another independently specified inference introduction; clauses from actual source constructors | Build allocates one declaration per *actual* introduction. “Another independently specified” is an obligation to supply a rule, not an Application rule itself. |
| Source-role elaboration §4 | Finite producer/consumer template sites | It explicitly leaves a finished inference-rule set and omitted consumer/result facts open. |

Neither Parameter nor annotation-hole formation applies to the whole `loop y`
occurrence by constructor shape. No other pinned rule specifies its new
output introduction. Reading a symbolic `A_call` in a rule conclusion is
insufficient to derive its owning source record. Interface insertion cannot
be inverted to produce the independent declaration being inserted.

## 3. Explicit substitutions expose the missing premise

This section uses contextual metavariables only as proof notation. It adds no
language rule or compiler representation. Let an ordered telescope be

```text
D_q = (d_1:S_1, ..., d_n:S_n[d_1,...,d_(n-1)]).
```

To write an output metavariable and its occurrence one needs:

```text
meta declaration: M_q : [D_q] ValueDescription
typed substitution: theta : Gamma_(sigma_A) => D_q
occurrence: M_q[theta] : ValueDescription
```

Here the substitution direction means that each `d_j` is mapped to a term
in the available source prefix with type `S_j` after the preceding images.
For source inclusion those images must be the actual retained source entries,
with their owners, order and predecessor edges. One must additionally provide
the authentic `Desc` introduction authorizing `M_q` and its declared `D_q`.
Well-formedness of Gamma supplies neither that authorization nor that telescope.
Writing the meta declaration into a metalanguage environment assumes those
missing data; it does not derive them from Name/Name operand code.

There are three distinct tasks: determine `D_q` from the owning introduction;
prove its typed inclusion at `sigma_A`; later substitute into Call headers.
R44's identity map established only the second task for a guessed full context.
Taking `D_q := []` also guesses the first task. Taking free variables of a
later solution or of completed `Q_q` reverses the required dependency order.
Even free variables of the sort `ValueDescription` cannot determine a
contextual unknown's allowed dependency telescope.

**Minimal falsifier of the proposed shortcut, not a source-q counterexample.**
Consider a well-formed prefix with one independent Boolean challenge `h` and
a description sort containing distinct `a0,a1`. Both meta declarations
`M0 : [] ValueDescription` and `M1 : [h:Bool] ValueDescription` are well sorted.
Both admit the constant assignment `a0`; the second also admits the strategy
`h ↦ if h then a1 else a0`. Neither the common sort, context availability nor
the existence of that constant solution distinguishes the declaration
telescopes. Conversely, choosing the full prefix introduces a strategy argument
that choosing the empty telescope does not. This small metalanguage example
falsifies deriving exact source dependencies solely from those weak facts.
It establishes no actual Boolean challenge or differing accepted typing at q.
An owner might independently forbid or require such a dependency; that is the
precise missing evidence.

The concrete falsifier for this audit is a pinned independently specified
Application rule, instantiated at Name(loop)/Name(y), that emits the actual
`Desc`, exact `D_q` and typed inclusion without consuming q's output-indexed
headers, `Q_q`, solved state or a successful query. That evidence would make
the current bounded obstruction obsolete. A renamed metavariable declaration
without its source introduction would not.

## 4. Downstream obligations retained at the stop boundary

The packet stops at the unsupported owner. Stages 2 and 3 were not executed.
The following are exact blocked consumers, not claimed derivations.

| Consumer | Required construction still missing at q |
| --- | --- |
| Application effect / Code-Call | Independently form `E_q`, its source origin and scope; retain distinct callee, whole-argument, entry/body/consumer and complete invocation effects. Supply `o_q`, actual `VIncl-origin` and `WholeArgCompatible-origin`, and `Suffix_q(U)` at the actual provider. No effect-row union is substituted. |
| `FrameCall(q,Q_q)` | Callee and whole carrier; actual callee Return/provider/current C1; receiver role, receipt, entry and designated consumer; complete Return/provider/current C2; that provider's latent/future interface. All indexed headers need their actual prior declarations. |
| Callee and receiver pending arms | Original raw handle, response and resumed current world, ordered suspended tails. Callee pending does not assert a receiver receipt. Receiver resumption does not repeat receipt. Value entry retains Force/rebind; retained entry retains its different entry rule. |
| W, Z, local and nested alternatives | Every original clause, guard, license, substitution and binder position. W's changed provider needs its own admission/future evidence. Z has its own whole-Call or local insertion. Nested futures use their actual provider slots. No predecessor witness/provider transfer by equal descriptions. |
| Generalize §§5.1–5.2 | A concrete publication/component/root and its complete typed edge graph, including `D_q`, before retain/fix and allocation can select any q action. |

The exact requested two-frame/alias maps therefore remain uninstantiated.
The historical allocation rules specify their *form*, once their inputs are
constructed: for independent frame indices i and j, an eligible Desc occurrence
has images `(i,rho_A)` and `(j,rho_A)` at translated original scopes; a fixed
Desc references its original anchor instead. Which case holds for q is unknown.
For an alias a of frame i, `route(a)=i`, so every declaration and binder image
must be the same as i's, without a new opening. No equation identifies i with j.

The maps must also preserve original Established/OneShot/Intrinsic anchors and
the one Shared binder; allocate ViewLogic per incoming description frame;
route Event/EventField by actual event keys; and allocate EventProof with both
frame and actual-event incidence while sharing its runtime operands. The
required dependency square is entrywise

```text
image_i(theta_q(d)) = theta_(q,i)(image_i(d))  for every actual d in D_q,
```

with its dependent types and original scope positions, and the analogous square
for j and its shared alias routing for a. This displays the unfilled certificate
obligation; it is not a constructed copy pair or a fresh conditional theorem.
There is no map to certify until `D_q` and the retain/fix result are known.
Arbitrary joint W constraints still apply to both frames in one shared client
tree. These obligations cannot discharge F1 or FK1 by assertion.

## 5. Source/native evidence and mutual TODO

No native bytes were inspected. The pinned R42/R44 boundary documents record
the path `ConstraintBatch::emit_candidate_source` → Apply source input → native
admission/`NativeInterface` → typed `FunctionField::Result` →
`Preserve`/`Dependency::FunctionPort` → Context/Dispatch, with Generalize and
extrusion copies needing the same source certificate. This is documentary
evidence only. It neither authenticates present constructors nor proves that
they emit the missing output owner. The typed core's `V/X`, Normalize and
ExecuteCallable equations retain their derivation-indexed scope. R44's rev2
evaluator corollary is usable only after its seven independent premises.

**TODO R45-CORE-OWNER (Luna/source authority).** For the unchanged parent, supply
the missing independent q output-introduction judgment above, or authorize a
new source-rule decision with its preservation obligations. Required inputs
are q's actual registrations, resolved operand/port records, original cursor,
component and owner-specific dependency construction. Proposed output is an
exact typed owner certificate and acyclic introduction derivation, on paths
Luna assigns later. The falsifier is any dependency taken from a later Call
header/provider, a fabricated introduction class, or dependence reconstructed
from solver success. This request grants no lease or semantic permission.

**TODO R45-CORE-CONSUMERS (Luna/independent Sol intake).** Compare this source-rule
inversion with the independent source attack. If it finds the authentic owner,
Luna can issue the concrete effect/all-arms/two-frame continuation. If it finds
the same gap, change the input/authority owner rather than dispatching another
equivalent conditional proof. The R42 source/native certificate gate remains
`NO_SAFE_CODE_SLICE`; the minimal future implementation TODO is to preserve
an approved typed output-owner certificate through the named actual consumers
and copies, with wrong-occurrence, missing/reordered-dependency, provider-swap
and alias-freshening as exact falsifiers. No production edit is authorized.

## 6. Reuse, hashes, checks and stop receipt

Reused within their actual premises: source Generalize ownership/allocation;
Code-Call's explicit input rule; complete source-interface insertion and use;
typed-core result-role/translation; R44 rev2's conditional evaluator statement.
Rejected as formation evidence: R44's `D_q := Gamma_q`, its unfinished q proof,
and its JOF draft. No withdrawn bypass or historical failure is promoted.
Simple-sub generation, accumulation, propagation, variable levels, extrusion,
qualifying intrusion and generalization retain all their obligations.

All following bytes were hashed locally and match R45's pins (R44 draft/proof
hashes match its adjudication). Author information is taken only from the read
documents: R44 artifacts are Luna `/root`; Generalize records a researcher;
typed-core and role elaboration record primary with architect contributions;
Code-Call records researcher repair and primary review disposition;
source-interface construction's individual producer identity is UNKNOWN.
Historical reviewers are not reviewers of this artifact.

| Dependency | SHA-256 |
| --- | --- |
| R44 contract | `8a9cdf31c8ce33feb30673a7cb91c099173ecd1da44e37e76b27d951960a91d8` |
| R44 adjudication | `4e29ef28ad7cdec80a2c195e8bbac09b07fb4ff15c3ff4ca11834ffba010c0aa` |
| R44 scope audit | `172eb876bb50d8439a996cb411af537eb3f526e4dfc951c5fb996b666eb0e9cc` |
| R44 evaluator rev2 | `bb7aff3ed064b7118861f8da67df2d69bd0392c783df7e4864d1a811b112d3ee` |
| Source Generalize | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| Typed-computation core | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| Code-Call input construction | `f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6` |
| Call source-interface construction | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| R44 implementation boundary | `5478d92e69688b26b0b2e6e0564df1efa5d06ef98aeaed5dd222110be4603a21` |
| R42 implementation gate | `855c07f2a6de1e156209f91c7c9f9ea2169369feb0381edb63ddeceb013c1758` |
| Source-computation role elaboration | `9a230eb023698666f4c3e518a527009d6915e65f658b230e6da6a29914ca3abb` |
| Rejected R44 JOF draft | `af9765c72edb19ef7c888e0c6751518ba3a1ccf79c5c99d7297796c1346d84fb` |
| Rejected R44 formation attempt | `a06c546be1204eb16bf81f3c45a3aca6f05db148cc00ea9e3f2fd971e62b0c12` |

Checks: bounded textual rule-premise inspection and SHA-256 inventory. No
compiler execution, tests, build, Cargo, external lookup, Git, nested CLI,
production/source edits or descendant processes. No mathematical checker or
independent review ran for this artifact. The Boolean example is a hand
argument about contextual declarations, not an executable source experiment.
The proof authority is the selected rules under their documented premises;
no transitive historical theorem was imported as an additional source rule.

One substantive stage used; the first unsupported owner triggers the stop
condition before stages 2–3. Budget: 300 active seconds, no renewal; requested
model/effort Astra/medium, observed effective model/effort UNKNOWN. Runtime CPU,
RSS and exact active duration UNKNOWN; wall-clock receipts and conservative
charge are in the single handoff. Only this artifact and
`tasks/agent-loop/inbox/20261019-r45-core.md` are new/written; no scratch paths.
This artifact freezes when its byte hash is entered in that handoff. The
assignment ends after the handoff freeze; no waiting worker or continuing
proof process is claimed. Parent and production remain OPEN; fresh independent
review and Luna intake are pending.

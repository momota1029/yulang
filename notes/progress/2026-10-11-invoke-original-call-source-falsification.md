# `invoke`: direct original Call derivation and its source lift

Date: 2026-10-11
Baseline: `72de8a8389825b395bc910654aa030ad82a289b0`
Branch: `research/simple-sub-intrusion`
Producer: `/root/invoke_original_call_source_falsification`; researcher leaf
Status: unreviewed bounded source audit and finite derivation; frozen on submission
Exclusive lease: this note only
Parent complete source / Call / soundness / principality gates: OPEN
Semantic adoption, implementation authority and independent certification: none

## Objective, method and result

Attack the proposed alternate method for `my invoke f = f 1`: directly use the
original Simple-sub abstraction/application rules rather than reconstructing
this formal's complete received-view/receipt/Force/rebind map. This is a source
spine and judgment comparison, not a repeat of the preceding constructor search.

**Result:** actual LocalSource preserves a direct term projection to
`lambda f. f 1`. That term has an ordinary Fig.3 declarative typing derivation
without any receipt map. This disproves a blanket claim that a formal map is
needed merely to type the projected ordinary term. It does not provide a lift
back to the original complete Yulang source judgment. The first missing edge
in this method is exactly that lift at Lambda/Call: Yulang's chosen source
rules have entry and complete invocation premises that the upstream rules
neither express nor discharge. No authentic source counterexample to such a
lift was obtained; no nonexistence or impossibility claim is made.

The exact map representation in the earlier notes is not proved necessary to
every possible complete proof. A different proof may retain equivalent source
entry/transport evidence directly. The present source audit establishes where
such a proof must connect to the selected meaning, rather than making a
particular proof-record spelling mandatory.

## Authority, scope and direct dependencies

Governing policy: top-level inference principles §§1–5 and Evaluation;
`design-authority.md`, Authority order and Natural compiler behavior;
`compiler-engineering.md`, Natural compiler behavior and Deterministic Simple-sub;
`research-lab.md`, One semantic baseline and Evidence quality;
`git-concurrency.md`, Disjoint-file mode and Research-only checkpoint.

Accepted source decisions: charter §§16–18,21,24. Every call reifies its whole
argument inertly; an unannotated Value formal forces once inside the same
invocation and rebinds its result; body usage cannot revise that role; result
synthesis forwards a computation interface. Section 24 supersedes universal
handler classification, while retaining §16's invocation/entry mechanics.
No new receiver role, no-effects restriction, mandatory annotation, source
restriction or language meaning is introduced.

The Authoritative source Generalize definition §§2–4 selects the independent
source constructor/checking schemas in its construction §§3.1–3.3. Their local
laws L1–L5 remain independent premises. The typed core remains Draft outside
its selected source premises; §§2–4 describe the derivation-indexed core,
§6 the selected roles/results, and §9 the complete invocation distinction.
The ordinary machine §3 and source-role §10 supply the selected operational
expansion, not automatic source typing or full raw-source adequacy.

Frozen predecessors are the assigned value-projection, entry-law,
actual-formal-interface, and formal-map-falsification notes. Their scalar
projection and localized construction limits are retained; their missing
constructor inventory is not rerun. The original reference is
`/home/momota1029/rust/simple-sub-reference` at
`9bae772624c23b52a93c1b226157e16898b4d9db`; the original paper is the permanent
local PDF listed in the hash manifest below. Fig.3, printed p.4, and
`Typer.scala:59–77,110–117` are the decisive independent ordinary rules.
The already reviewed import note §§2–5 records the published theorem's
non-let-polymorphic scope and incomplete proof sketches. Those exclusions
are respected here.

## Actual constructor correspondence and source cases

Fix the actual source occurrences `L,d_f,u_f,a,c`: Lambda, unannotated formal,
resolved body Name, literal `1`, and Apply. There are no imports, annotations,
local bindings, handlers, operations or recursive uses in this single source.
The incoming caller/provider/history domains of the parent are not narrowed
by that syntax observation.

| Case | Actual source construction | Direct ordinary image |
| --- | --- | --- |
| Definition/formal | `local_source.rs:257–322` receives the actual owner-qualified parameter, installs its lexical binding before constructing the body, and gives the body Parameter scope. | One binder, not an independently instantiated `f`. Top-level publication is outside this derivation. |
| Name | `local_source.rs:636–658` uses lexical resolution; `candidate_source.rs:213–216` uses the parameter endpoint and `:368–381` emits pure lookup effects. | `Var(f)` under the same monomorphic binder. Pure lookup says nothing about received argument execution. |
| Integer | `local_source.rs:660–665` retains the literal text; `candidate_source.rs:336–350` emits both Int value bounds and pure evaluation. | `Lit(1)` and T-Lit. Literal row elimination is additional to effect erasure. |
| Apply | `local_source.rs:553–574` retains distinct callee/argument children; `candidate_source.rs:394–413` retains both endpoints and the actual call occurrence; `shadow_apply.rs:1334–1401` constructs the four-port demand. | `App(Var(f),Lit(1))`; its ordinary value demand is `alpha <= Int -> beta` after the already established scalar interpretation. |
| Lambda/result | `candidate_source.rs:445–459` retains formal/body endpoints; `lib.rs:11233–11369` constructs the Function and entry/body-to-invocation constraints. | `Lam(f,App(...))`, ordinary root `alpha -> beta`; the received/entry/invocation children are omitted by this image. |
| Consumer | `candidate_source.rs:632–675` executes scheduled actions and advances after success; `candidate_call.rs:375–438` rejoins authentic Lambda/Name/formal incidence. | Real source incidence survives; this does not turn pending original Call suppliers into discharged typing premises. |

The recursive structural term map on this exact spine is
`e(Name(d_f))=Var(f)`, `e(Integer(1))=Lit(1)`,
`e(Apply(callee,arg))=App(e(callee),e(arg))`, and
`e(Lambda(d_f,body))=Lam(f,e(body))`.
Capture-avoiding fresh naming uses the actual lexical handle. It does not
identify different providers, views or roots. Thus `e(L)=lambda f. f 1`
is source-directed, without a supplied synthetic graph.

This is a source syntax correspondence. The established value-projection note
§§2–5 separately explains the actual extra literal/Lambda/definition rows:
its exact effect-only generation identity is false, while its scalar
interpretation has the ordinary demand. Those facts are not re-proved here.

## Finite ordinary derivation and algorithm order

Let `A,B` be ordinary Fig.3 types with `A <= Int -> B`. Under
`Gamma={f:A}`, T-Var gives `Gamma |- f:A`; T-Sub gives
`Gamma |- f:Int -> B`; T-Lit gives `Gamma |- 1:Int`.
T-App concludes `Gamma |- f 1:B`, and T-Abs concludes
`|- lambda f. f 1:A -> B`. Taking `A=alpha intersect (Int -> beta)`
is the familiar unconstrained ordinary presentation. This is a finite
conditional derivation with the explicit subtype premise, not Yulang
principality or full source acceptance.

Independently, upstream `Typer.scala:59–77` constructs the same ordinary
constraint: Lam allocates a fresh monomorphic parameter, installs it while
inferring the body, and returns Function(parameter,body_type); App infers
callee then argument, constrains `f_type <= Function(a_type,res)`, and returns
`res`; Lit returns Int directly. Here `res` is allocated lazily for App,
so the relevant constraint is `alpha <= Int -> beta`. Function comparison
at `:110–117` reverses the argument comparison and preserves the result.
The reference does not use receipt, provider, guard, Force or rebind fields.

This is *typing traversal order*. It is not evidence that the upstream
algorithm evaluates either source expression at runtime, nor that Yulang
may move Force before receiver activation. The original Fig.3 T-App judgment
contains no operational scheduling premise. No runtime preservation theorem
is inferred from the Scala recursion order.

## Discriminator: the omitted judgment, rather than a false ordinary rule

For the actual selected Yulang spine, typed-core §6:333–410 gives

```text
P_f = Value(A_f)
Gamma(f) = Value(A_f)                 after entry rebind
I_1 = Value(Int)
I_(f 1) = Computation(E_call,A_call)
Result(I_(f 1)) = Comp(E_call,A_call)
I_L = Value(Fun(P_f,Comp(E_call,A_call)))
```

The body's `E_call` is symbolic. The literal's purity and Name lookup's purity
do not establish a pure invocation of arbitrary admitted `f`. Independently,
typed-core §9:912–996 distinguishes whole `J_arg`, rebound body `J_body`, and
complete `J_call`. Its rule includes receipt before entry Force, actual
same-result/current-state rebind, body, return, and every pending suffix.
The source-Generalize construction §3.1:128–164 requires these in its Lambda
and Call schemas before Build preserves their clauses.

Erasing the computation/evidence coordinates gives the ordinary judgment
above. Inverting this erasure is not another application of T-App/T-Abs:
neither rule names those coordinates, generates their original binders, or
establishes their laws for the independently admitted carrier challenges.
The typed core §2 explicitly lists typed Flow/receipt, profiles and joint
`nu,K,D` in its derivation input; §4's realization theorem assumes that input.
It supplies no inverse from an ordinary arrow judgment. Conversely, this
missing inverse does not refute the scalar derivation or prove that a direct
complete proof is impossible.

The Authoritative complete-Call contribution definition §2 explicitly keeps
independent complete C0: `C-Call` consumes the authentic original operation
and its complete typing rather than manufacturing them from a value arrow.
The authoritative contextual Function membership definition §§1–2 selects
Call-semantic-input realization §§2–4. For the actual body call, its §3.1
requires `ActualAdm(v,U,d)` for every independently admitted complete challenge
and each actual provider decomposition, plus all complete/pending/future
observations. Section 2:111–145 distinguishes challenge assembly from actual
admission: `ActualAdm` projects acceptance of the same whole carrier and the
actual receipt/typed-path/context preconditions; it does not perform receipt.
Neither the ordinary demand `alpha <= Int -> beta` nor a pure literal supplies
that semantic action by itself.

For this exact source, Call-input construction §§3.2–3.4 specializes the
static entry rule to `E_body=ValueBind(Empty,d_f,r_f,A_f,entry/rebind origin)`:
no lexical captures exist. `Data-Name`/`Code-Result` then operate under that
same binding. The semantic Name inversion in §6 requires the valid joint
telescope family of §5.1; its persistent value membership does not follow
from lexical IDs. The retained entry-law note §3.3 supplies a conditional
ValueBind elimination after actual entry Return, requiring the same whole
carrier certificate, received typed paths/current guards, and actual rebind
map. At Request it retains the pending suffix and leaves its complete body
Call typing open. Thus the chosen full Call does require these extra source
facts at the actual ordinary binder; it does not require a new separate raw
ViewInlet test or successful observation as a challenge precondition.

The actual source constructors inspected above supply resolved incidence,
parameter/native endpoint sharing and four-port constraints. Their private
consumer explicitly lists `ActualFormalIntroductionRoute`,
`ArgumentReifyAndWholeCarrier`, and
`ReceiverDispatchAndCompleteResultFutureInterfaces` as pending
(`candidate_call.rs:78–90`); `shadow_apply.rs:1–50` retains source/application/
whole-provider/entry/complete-Function premises as unresolved. This is
bounded current-artifact evidence, not an absence theorem about all possible
proofs. This lane does not repeat the prior map inventory, run a test-only
receipt evaluator, or treat that evaluator as an independent source oracle.

The precise unclosed premise of the bypass is:

```text
Lift_Source(L,d_f,u_f,a,c):
from actual source incidence and the ordinary projected derivation,
construct the independently legal full Yulang Lambda/Call derivation
with its original received/entry/body/result/return interfaces and scopes,
for the parent's original carriers, providers, guards and histories.
```

This is an obligation name, not a new rule, successful-Q predicate or added
semantic relation. The lifted derivation must establish the selected entry
and source transport facts; it need not use the earlier note's particular
formal-map representation. Supplying only the projected subtype premise
leaves this conclusion unproved.

A minimal structural failed inference is already this exact three-node body
spine plus its Lambda: applying upstream T-App concludes `f 1:B`, whereas the
Yulang source owner needs the complete `Comp(E_call,A_call)` interface and
its selected consumer. This is a judgment mismatch, not an independently
accepted Yulang counterexample. No extra term, named operation, restricted
provider or hypothetical no-effects assumption is needed to localize it.

## Evidence quality, checks, resources and unverified scope

Method: direct actual-source/spine audit and original-rule comparison. The
independent ordinary source is the original paper/reference, not a checker
encoding the candidate Yulang transitions. Both sides share syntax/binder
incidence and ordinary Int/arrow interpretation. Their richer semantics are
not independently equated. There is no executable semantics oracle, model
comparison, seed/range, enumeration, mutation test or acceptance experiment.
No checker's assumed transition rules are promoted to source correctness.

Checks already run: focused `sed`/`rg` reads of the listed constructor,
consumer and governing sections; `pdftotext -f 4 -l 9 ... -` for original
Fig.3; read-only `git rev-parse`, `git status --short -- <lease>`, and byte
comparison against `git show <baseline>:<path>`. The 26 repository direct
inputs and reference Typer bytes matched their pinned revisions before
writing. Broad combined captures sometimes truncated; decisive clauses were
reread in focused slices. No whole-repository absence search is claimed.
The final artifact/dependency integrity check is recorded in the handoff.

Coverage includes every constructor of the exact unannotated Name/Int/Apply/
Lambda target, definition incidence, actual private candidate consumer, the
original typing rules and inference order, and selected full source schemas.
It omits general source constructors, complete typed-port application,
annotations/conversions, arbitrary globals/providers, handlers/operations,
recursive client histories, source rejection/publication, SCC Generalize,
full inference soundness/principality and F5 cutover. Excluding these from
this audit does not exclude them from the original parent theorem.

One lane, one sequential command process at a time, no builds/tests/Cargo/
Oracle, no scratch outputs, no Git mutations, no nested delegation, and only
this note written. The 30-minute wall cap was not exhausted; precise elapsed
wall/CPU and peak RAM were not measured. Dependency comparison used sequential
read-only git subprocesses. Requested/observed model and effort metadata are
unknown in this lane. This is a producer artifact, not independent review
of any coauthored output.

One recommended next action: have the constructive lane state and prove the
full source lift at the actual Lambda/Call owner, retaining the selected
entry/transport evidence directly if that removes reconstruction debt. Use
this ordinary derivation as its scalar subderivation, without interpreting
its success as discharge of complete source premises.

## Frozen dependency hashes

SHA-256 of the pinned/current byte-identical direct inputs at creation;
reference PDF has a recorded local content hash. The primary rechecks before
integration. Changed dependency hashes at creation: none.

```text
3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69 rules/research-lab.md
e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1 rules/design-authority.md
2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6 rules/git-concurrency.md
4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9 rules/compiler-engineering.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389 notes/design/2026-10-11-yulang-inference-top-level-principles.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed notes/design/2026-09-29-scc-intrusion-redesign-charter.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38 notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 notes/theory/2026-10-08-source-generalize-definition-and-proof.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e notes/design/2026-10-02-typed-computation-core-elaboration.md
9a230eb023698666f4c3e518a527009d6915e65f658b230e6da6a29914ca3abb notes/design/2026-10-02-source-computation-role-elaboration.md
ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917 notes/design/2026-10-02-ordinary-computation-semantics-package.md
cd2b84a84d16be8856766f0514a2f400cf224ac95b6e81e42d4a7a875036e113 notes/theory/2026-10-11-parreaux-simple-sub-proof-import.md
f5151f1c75ac0c75350d5ff5ae8e2cdcd976309505d853a64d2f711b36f14158 notes/theory/2026-10-11-invoke-value-projection-proof.md
a4e666d038172d885edbe5f21f5eb2444e858b8b18f4a369ad3be6b4548cc2f3 notes/theory/2026-10-11-invoke-entry-entry-law-proof.md
62b260ccab954b33caf1fa66e7c1e8f84fd55c17faba6bbe6bc2b153a4fe8ffb notes/theory/2026-10-11-invoke-actual-formal-interface-proof.md
53ac51ebf653f2f106b8eeb2a7c9c127fd7c8c2b1c081cc22890d006c0bf29db notes/progress/2026-10-11-invoke-formal-map-falsification.md
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed crates/yu-hir/src/module/local_source.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49 crates/yu-solver/src/candidate_source.rs
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35 crates/yu-solver/src/candidate_call.rs
230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6 crates/yu-solver/src/shadow_apply.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94 crates/yu-solver/src/lib.rs
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9 /home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala
5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698 /home/momota1029/rust/simple-sub-reference-paper.pdf
4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e notes/design/2026-10-07-complete-call-contribution-definition.md
ead206bff341c82993acbaecda25ae1d3a760397796bbbbb53ba3ef917a53fb1 notes/theory/2026-10-07-owned-call-contribution-construction.md
f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6 notes/theory/2026-10-07-call-input-construction-proof.md
0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0 notes/design/2026-10-08-contextual-function-membership-definition.md
fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a notes/theory/2026-10-08-call-semantic-input-realization.md
```

## Commit packet

- Exact leased path: `notes/progress/2026-10-11-invoke-original-call-source-falsification.md`.
- Baseline SHA: `72de8a8389825b395bc910654aa030ad82a289b0`; reference SHA: `9bae772624c23b52a93c1b226157e16898b4d9db`.
- Changed dependency hashes: none at creation; manifest above records the frozen inputs.
- Review status: unreviewed research audit/finite ordinary derivation; frozen on submission; no source-qualified semantic counterexample, impossibility or parent closure claimed.
- Checks already run: narrow original/source-rule reads, exact source-incidence audit, baseline/reference byte checks and lease absence; no tests/builds/probes/Git mutations.
- Proposed one-line checkpoint message: `research: distinguish invoke original term typing from complete source lift`.
- Shared-record deltas left for primary/curator: record the direct ordinary term derivation as a scalar subresult; distinguish the remaining full-source lift from necessity of a particular formal-map representation; retain original complete source/Call/soundness/principality gates OPEN. No shared task/index/authority/theory-status/question-board file changed.

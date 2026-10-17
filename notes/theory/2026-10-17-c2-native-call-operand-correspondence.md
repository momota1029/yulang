# c2 native call operand correspondence

Date: 2026-10-17  
Revision: 1  
Author: `/root/c2_native_call_operand_correspondence`, sole proof author; no descendants  
Status: unreviewed source/native derivation and conditional decomposition lemma  
Sprint: `c2-typed-call-occurrence-correction-20261017`, contract revision 2  
Baseline: `8f012935e`; no implementation or production authority

## Parent and application

The parent remains original FORWARD-FIRST-CALL A/B at c2. Retain
`receive(f : Unit -> alpha+) = let g = f(Unit) in g(Unit)`,
`c2 = Apply(Name(g), a2)`, the original Unit argument a2,
`F2@(sigma2,Delta2)`, `xi=(nu,K,D)`, and complete original `B_in`.
The original theorem and MODEL premises are those in
`2026-10-16-first-call-joint-forward-preservation.md` §§1–2: every original
xi, alpha, A1/E1, actual provider/captures, compatible context, observation,
admitted response/raw Resume/future and resulting Return remains in scope.
That earlier local c1 conclusion requires its independently valid environment,
compatible punctured context and one authentic joint MODEL. It does not provide
model existence, source T, reverse B, or the c2 inlet by itself.

The result here fixes the exact ordinary c2 constraint and removes the alleged
native admission edge from the parent proof. It supplies a constructor/operand
correspondence fact to a future source bridge. It discharges no original F2
introduction, VIEW or CHECK premise. Those gates, F1/FK1 and original A/B stay
OPEN with their original independent quantifiers.

## 1. Constructor premises and identities

Fix the actual retained source expression c2 under
`Scope(receive, Lambda(f, annotation, Bind(g,c1,c2)))`. Let its source root
be o, its expression index i, its exact callee child s = Name(g), and its exact
argument child a = a2. The source root o is the registration's actual
`SourceRootId`; no numeric ID or unrelated root is chosen here.

The source construction claim has the following explicit operational premises:
the accepted candidate construction reaches this Apply branch, endpoint and
level allocations succeed, its recipe is registered with `source_input`, and
`admit_candidate_fact` completes successfully for that recipe. These are the
ordinary constructor success premises, not new restrictions on accepted source.
No execution or whole-source acceptance/reachability theorem is claimed here.
In particular the scoped experimental branch contains its own rejection checks;
this derivation does not prove every route accepts the source.

At `candidate_source.rs:980–1050`, the Apply branch reads the actual callee and
argument indices, retains `CandidateRelation::Apply`, and registers
`ApplySourceInput` with owner o, index i, children s/a, source level, their
value/effect endpoints and c2 result/application-effect endpoints. It sets

```text
q2 = ConstraintOccurrenceId(c2.occurrence, 0)
cause2 = CauseId::for_occurrence(q2)
```

and joins that exact input back to the recipe. `shadow_apply.rs:1560–1580`
checks the registered recipe, occurrence and endpoint identities before using
it. Its native record retains those operands before initial constraint
admission. Successful `candidate_call::observe` (`candidate_call.rs:437–532`)
adds authentication: the same HIR owner resolves i to an Apply with the same s/a;
the checking occurrence matches that expression; the cause is derived from
that checking occurrence; source occurrences and scopes are owned; and the
retained native Function children equal its recorded ports with the checked
kinds/polarities. Observation alone checks occurrence equality, whereas the
constructor establishes slot 0. No general slot-0 property is inferred for
arbitrary forged records.

Thus source identity, native port identity and semantic interface substitution
are distinct. The first two have constructor/observer evidence here. No
semantic map `m_g : IF(g) -> c2` is constructed.

## 2. Actual whole-call relation

Write C = candidate_endpoint(s, Positive), A =
candidate_endpoint(a, Positive), and R = c2 result endpoint at Negative.
In `shadow_apply::admit_candidate_fact` (`shadow_apply.rs:1582–1669`), the
Apply branch constructs the following native Demand:

| Native operand | Kind | Polarity | Owner/source relationship |
| --- | --- | --- | --- |
| C, callee2 | Value | Positive | Exact source callee child s |
| A, argument2 | Value | Positive | Exact source argument child a2 |
| AE, argument effect | Effect | Positive | Actual argument effect row |
| IE, invocation effect | Effect | Negative | Fresh invocation row at the canonical application row level |
| R, result | Value | Negative | Actual c2 result row |
| CE, callee effect | Effect | Positive | Actual callee effect row |
| JE, application effect | Effect | Negative | Actual c2 application effect row |
| N2 = Function(A,AE,IE,R) | Value/Function | Negative | Newly constructed c2 Demand |

For a registered source call the invocation row must exist; the no-graph
fallback using bottom/empty effects does not supply that authenticated record.
The graph-enabled constructor creates IE at the application's existing effect
level. This is a retained level fact, not a new extrusion/generalization rule.

The branch returns `(lower,upper)=(C,N2)` directly. The subsequent code builds
`ConstraintOccurrence {id:q2,cause:cause2,lower:C,upper:N2}`, calls
`store.admit_and_record_provenance`, forms the positive-lower/negative-upper
canonical Value pair and passes it with q2/cause2 to `constrain_live_value`.
Consequently successful construction emits and retains exactly this initial
whole-call Value relation:

```text
callee2+ <= N2-                    at q2 = (c2, slot 0), cause2
arg(N2) = A = argument2+           equality of retained native terms
```

This proves the corrected source-to-native operand correspondence by direct
substitution into the constructor. It does not depend on callee2 already being
a positive Function or on the call comparison succeeding semantically.
The graph-enabled branch separately generates CE+ <= application-effect- at
slot 1 and invocation-effect+ <= application-effect- at slot 2, with each
slot's own occurrence-derived cause (`shadow_apply.rs:1680–1744`). Those
auxiliary effects do not change the slot-0 operands or create admission.

There is no separate initial Apply Value pair `Unit+ <= arg(N2)` in this
branch. Its displayed upper operand would be Positive. The argument port is
populated from the argument endpoint itself, so this is an identity, not a
second typed subtype edge. A source Unit occurrence does not justify replacing
the retained endpoint by a chosen semantic Unit witness.

## 3. Conditional Function child consequence

Assume additionally that an actual retained comparison has lower endpoint a
positive Function P and upper endpoint this negative Function N2, and that
ordinary Function decomposition processes that comparison. This premise may
arise from independently established ordinary propagation; it is not entailed
by merely constructing the positive callee row C. No provider or P is chosen
to make it true.

`lib.rs:12550` obtains both `positive_function_children(lower)` and
`negative_function_children(upper)`. The accessors (`lib.rs:14179–14220`)
require actual Function endpoint tags and read their stored children.
The child table (`lib.rs:12644–12674`) reverses both argument positions and
preserves both result positions. Substituting lower=P and upper=N2 gives:

```text
arg(N2)+       <= arg(P)-
argEffect(N2)+ <= argEffect(P)-
resultEffect(P)+ <= resultEffect(N2)-
result(P)+       <= result(N2)-
```

In particular the requested child is `argument2+ <= arg(P)-`. Every displayed
comparison has a Positive lower and Negative upper. It is an ordinary
contravariant call-check consequence. It is not `argument2+ <= arg(N2)`.
The decomposition records children/diagnostic edges and dispatches them through
its existing work machinery; deriving a child obligation does not prove it is
satisfied, fully processed in a failed/resource-exhausted route, or an F2 guard.
If C remains a row without an actual positive Function comparison, this lemma
has no instance. Ordinary propagation, accumulation, levels, extrusion,
qualifying intrusion and generalization retain their existing rules.

## 4. Reused mathematics and rejected inference

Reuse the prior phase/carrier note's source-graph retention only: erasure of a
local marker keeps the same Scope/Lambda/Bind/Call/Ref nodes and binding edges.
For the supplied Bind equations
`Return(z,C1) >>= S = S(z,C1)` and
`Request(q,C,k) >>= S = Request(q,C,lambda(r,C').k(r,C') >>= S)`,
retaining the same suffix commutes with the same capture-avoiding substitution.
The Request calculation stays under its response/current-state binder and
extends to repeated requests and finite divergent prefixes. It supplies no
foreign-continuation admissibility action or F1/FK1 theorem.

For any already supplied well-formed dependent telescope T and already typed
predicate/witness, identity substitution preserves T and that same witness by
induction over its dependent binders. This does not form T, type an absent
predicate, install IF(g), or select an inlet. Provider, residual and witness
lineages remain distinct; no field is moved above its event binder.

The withdrawn revision-1 `C-AppArg` is not a theorem. Its positive-to-positive
native reading cannot be repaired by identity substitution. Reject its reuse
as an admission rule. The approved inferred Function call-view direction
(`2026-10-05-inferred-function-call-views.md` §2) explicitly requires source
formation independent of pending Q. Neither endpoint shape, successful
comparison nor local slot/cause authenticates original semantic admission.

## 5. Exact remaining premise and owners

No result above constructs IF(g), original F2 clauses/admission, I2 or I2=SAT,
the complete B_in carrier, VIEW or CHECK. This is a statement of the proof's
scope and missing rules, not a semantic impossibility theorem. The whole-call
pair and its possible children contain no established action on every original
(delta,O), world/context, provider, response, raw continuation or future.
Native argument identity therefore cannot close original VIEW. A possible
argument subtype obligation supplies neither original jointly correlated
guards/witnesses nor their introduction; it cannot close original CHECK.

Mutual TODO `C2-SEMANTIC-INLET-OWNER`: Luna/source-admission owner must supply
the actual original F2 and IF(g) formation and comparison-independent admission
judgment from the original source signature/use component. Inputs are original
F2/sigma2/Delta2, xi and all correlated source fields; output is an independently
reviewable typed source rule, not a port equality. Falsifier: any use of pending
Q or a selected provider/witness to manufacture an original guard.

Mutual TODO `C2-CARRIER-VIEW-CHECK`: respective original inlet/consumer owners
must construct the complete B_in action for every original target and prove
actual original clauses with shared witnesses. Falsifier: a missing world,
foreign continuation, response/future case or split provider/lineage. The native
owners audited here are `candidate_source` Apply emission,
`shadow_apply::admit_candidate_fact`, `candidate_call::observe`, and lib's
ordinary Function child dispatch. None is shown to own those semantic rules.
No new source rule, implementation TODO or code evidence is needed to establish
this packet. NO_SAFE_CODE_SLICE: `admit_candidate_fact` and `observe` supply
only native construction/authentication; dependent semantic consumers remain
unestablished. Luna owns the next authority/lease decision and fresh review.

## 6. Frozen dependencies and checks

Contract revision 2 SHA-256:
`56dfb9a7eec800088341b99d659b9fcabacedbe969f8891b31f1784cd166f54e`.
The ten unchanged contract inputs were rehashed and matched. The two source
paths are intentionally versioned outputs of this contract: their predecessor
pins remain historical; Luna's explicit proof dispatch supplies their frozen
revision-2 replacement hashes below. This is not a silent same-revision change.
Source correction author is `/root` (Luna/high requested, observed UNKNOWN).
Prior graph/phase author is the prior proof worker recorded in its handoff;
its results are reused only as delimited above, never independently certified
by this author. Full prior authorship receipts remain in the frozen dependencies.

| Input | Actual SHA-256 used | Relationship to contract |
| --- | --- | --- |
| `notes/progress/2026-10-17-c2-admission-occurrence-phase-review.md` | `35536c07acd17b8531eae9e62f12c7089f712385685812814df2a58c7bea1bf2` | Unchanged pin |
| `tasks/agent-loop/sprints/c2-admission-occurrence-and-phase-rule-20261017.md` | `1b2c953011a2ffbfb7fdc8d0783869b7b85ef2e2a9824e23d284de1417fdf491` | Unchanged pin |
| `notes/design/2026-10-17-c2-admission-occurrence-and-phase-rule.md` | `a78c3b32db064e3e6add46daeb7395703fe453fb6aba74ba9d98ce82ed409d25` | Luna-authorized revision 2; predecessor e835e269207666ba25f03680c80d1c3da32f5da8883598574b344e6d0f78d5d9 |
| `tasks/agent-loop/inbox/20261017-c2-admission-occurrence-and-phase-rule.md` | `3bc79093b819f2de7029b81136bbfed0a3b9ef727acf68cb5c87696b184e9be4` | Luna-authorized revision 2; predecessor 814f3a723664b9a48d81a282efb8c9becaca20ffaae7d0f807b15cf2695b6204 |
| `notes/theory/2026-10-17-c2-admission-phase-and-carrier-laws.md` | `3dc2aee3594ecadbf42a6dee4b52c6767d058cbc5fcca0ee89067fd81f28c865` | Unchanged pin |
| `tasks/agent-loop/inbox/20261017-c2-admission-phase-and-carrier-laws.md` | `cdea6601d58bf41c812209bb48eb385801770d976646b1fd36632d499eaab04f` | Unchanged pin |
| `crates/yu-solver/src/shadow_apply.rs` | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` | Unchanged pin |
| `crates/yu-solver/src/candidate_call.rs` | `cbad9cf51a05343eb7a29ab77aac520891467a8aa4edc3201ea3d91f978984a1` | Unchanged pin |
| `crates/yu-solver/src/candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` | Unchanged pin |
| `crates/yu-solver/src/lib.rs` | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` | Unchanged pin |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` | Unchanged pin |
| `notes/theory/2026-10-16-first-call-joint-forward-preservation.md` | `f71cc442bcccb23f7e6f1aa6221b089abb8c24d1c4ce01fecef37995541c16b6` | Unchanged pin |

Read-only checks: constructor/observer/ordinary decomposition inspection and
all dependency byte hashes. No tests, probes, builds, compiler execution,
runtime execution, Git, semantic edits or production changes. Initial `python`
hash command was unavailable; `python3` completed the byte checks. No scratch
files or descendants. Only the two exact leased output paths were created.
The producer cannot independently certify this derivation or the combined
source/proof result; review and adjudication belong to Luna.

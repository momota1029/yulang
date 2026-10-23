# R348 — extension from K0 source solutions to the actual native state

Status: **frozen producer candidate, revision 1; independent review pending**.
Assignment `R348-K0-END-STATE-LIFT`. Proof-text author:
`/root/r347_k0_end_state_prover`; primary source-check/census author: Luna
`/root`. No descendants. This is a source-based hand derivation, not an
execution observation, independent certification, or production authority.

## 1. Fixed claim and interpretation

The parent remains the original Simple-sub source/native A/B objective, with
its original quantifiers and accepted behavior. The immediate supplier is
the original audit's G/N interface, using exactly R336 rev4, R337 J and
R341's authentic ordinary K0 completed-state premises. In particular, fix
one authentic source s and its **same actual finite successful construction**
ending in S with `NativeComplete₀(s,S)`. Existence of such a completed run is
a premise; neither successful execution nor `unresolved().is_empty()` is its
definition. No termination, model-existence, or runtime-success premise is
inferred from a source name or a successful API receipt.

Use the unchanged preorder on finite Value terms of R336 rev4, including lattice
rules and four-port Function variance, and finite subsets of the fixed Effect
universe Ω. Both pure Effect endpoints denote ∅. The source family is precisely
R341's occurrence-indexed `C_s`. Write `v_e` for e's semantic Value endpoint,
`ε_e` for its collected evaluation-Effect component, `a_λ` for a Lambda's
formal, `i_λ,r_λ` for its entry/returned Effects, and `κ_c` for a call's
invocation Effect. Then the entire family is:

| Authentic source occurrence | Its source inequalities |
| --- | --- |
| Unit/Bool/decoder-valid Integer/String literal e | `Atom(e) ≤ v_e ≤ Atom(e)`; `BottomE ≤ ε_e ≤ EmptyE` |
| Parameter Name e resolving to λ's formal | `v_e` is **the coordinate `a_λ`**; `BottomE ≤ ε_e ≤ EmptyE` |
| Annotation-free simple Value Lambda λx.b | `Fun(a_λ,i_λ,r_λ,v_b) ≤ v_λ`; `i_λ ≤ r_λ`; `ε_b ≤ r_λ`; `BottomE ≤ ε_λ ≤ EmptyE` |
| Apply c=f a | `v_f ≤ Fun(v_a,ε_a,κ_c,v_c)`; `ε_f ≤ ε_c`; `κ_c ≤ ε_c` |
| Else-complete If e | Each condition Value is ≤ Bool; every branch Value is ≤ `v_e`; every condition/branch Effect is ≤ `ε_e` |
| Group e around b | `v_b ≤ v_e`; `ε_b ≤ ε_e` |
| Binding-free Block/StatementBlock e | Final expression's Value is ≤ `v_e`; its Effect and every expression-prefix Effect are ≤ `ε_e` |
| Definition root | `v_body ≤ v_root`; there is **no Definition-root Effect row** |

All conditions, branches, prefixes, binders and calls are quantified. Equal
formulas from different source occurrences remain different inventory entries.
The Name's unused collected Value component is not substituted for its formal.
No equation between body/root Values is inserted. No constraint is added to
`C_s` by this proof.

`H₀(T)` is R341's existing independent interpretation of an actual state T.
It contains the directed physical bounds and the specifically retained work:
pending typed tasks; initial/current/pending/saved processing requests and
their actual relations; live caller/local transfers; unconsumed replay child
slots; and remaining structural children. We use R345's `B,Q,P,R,D` names for
those same components. For an actual bound,

```text
β(owner,Positive,item) = item ≤ owner,
β(owner,Negative,item) = owner ≤ item.
```

An attached owner relation uses its actual `bound_pair`; a live relation uses
its actual task pair. Inactive source receipts, memo entries, completion
stamps, bare relation/dependency IDs, diagnostic edges and acknowledgement IDs
contribute no extra formula. During a transfer the actual Rust local is an
owner, as in the accepted R338–R346 interpretation; there is no fictitious
unowned interval. The proof below covers all these conjuncts, including those
that disappear before S. It does not redefine final H₀ as only the queue or
only the compact output view.

The candidate conclusion is

```text
∀σ∈Assign(D_s). σ ⊨ C_s ⇒
  ∃ρ∈Assign(R_S). π_s(ρ)=σ ∧ ρ ⊨ H₀(S),                    (Lift)
```

with the explicit domains and map below. Combined with R341 retention **under
the same premises**, it gives the contract's projected solution equality.

## 2. Coordinates, exact map, and a total candidate extension

Keep R341's domain `D_s = FV(C_s)` together with the named output endpoints.
This includes rows nested in source Function terms. Descriptions in this table
refer to existing source coordinates; they introduce neither new variables
nor a quotient of them.

| Coordinate of kind | Actual construction image ι |
| --- | --- |
| Collected component of kind k, including Definition Value | Its checked `live_components[position]` with kind k and its dense ordinal |
| Formal `a_λ : Value` | `Value(parameter_live_base + recipe.parameter_position)` for that exact registered binder |
| `i_λ : Effect`, `r_λ : Effect` | The two distinct `fresh_effect_at_level` results of that occurrence's `admit_lambda_fact`; respectively the Function's negative entry and positive return ports |
| `κ_c : Effect` | That Apply recipe's actual fresh invocation row; the same row in the negative demand's return-Effect port and its slot-2 inclusion |

Component initialization allocates separate Value and Effect spaces, incrementing
the matching ordinal for each component (`lib.rs:10344–10398`). Formal Values
start after **all** collected Value components (`10077`, `10385–10398`). Fresh
allocation appends empty bound vectors and does not reuse an ordinal
(`10456–10516`). The source collector fixes component positions and formal
lookup before admissions (`candidate_source.rs:1089–1137`;
`shadow_apply.rs:3656–3670,3925–3940`). `ComponentId` distinguishes occurrence,
kind and Definition root (`lib.rs:393–419`).

The root schedule executes once before capture. Within that schedule each
action advances only after successful return; distinct Lambda/Apply actions
therefore identify distinct successful allocation events
(`candidate_scheme.rs:2829–2905`; `candidate_source.rs:2378–2413`). The
dependency-order builder publishes a node once after visiting it, with a
finished state preventing reinsertion (`candidate_scheme.rs:3039–3132`). K0
has one nonrecursive root and no operator/member/loose-expression roots that
would readmit it. This is an event-identity argument, not an assumption that
occurrence spelling alone identifies an allocation.

Authentic binder identities are the registered HIR parameter identities, not
source spelling; their uniqueness is part of the unchanged ValidK0/source
correspondence premise. Consequently ι is kind-preserving and injective on **distinct coordinates of
D_s**: initial component ordinals are distinct within a sort; formal Values
occupy a disjoint appended range; and each named fresh Effect occupies a new
appended ordinal. The expression-occurrence-to-endpoint lookup is generally
many-to-one: several Names can select the same formal coordinate. It is not
the coordinate map's injectivity claim. No independent Name coordinate is
silently equated with a formal. Equal raw integers from different kinds
remain separate tagged rows.

R336 L0 and R337 J apply to every successful prefix of this same K0 run.
R341 §3's exact endpoint argument then applies unchanged: every live level
is 1; extrusion at target 1 returns each row unchanged, and finite structural
rebuilding returns the original Function when its children are unchanged.
There is no copied-row parent to enter the intrusion pending list or to
reactivate; startup has none. `settle_candidate_intrusion` takes its empty
pending branch (`candidate_intrusion.rs:568–581`), so no forest merge,
generation increment or bound canonicalization occurs. The only merge caller
is the pending-parent loop (`582–595`); its parent creation/reactivation
requires the excluded copied-row occurrences (`304–420`). Root boundary-0
capture does not lower live levels. Thus

```text
μ(r:k) = k(rep_k,S(ι(r).ordinal)) = ι(r).
```

No representative-changing transport theorem is assumed. Extend μ
structurally, preserving atoms, pure endpoints and all four Function ports.
The positive/negative occurrences of a row read one assignment. Finite term
induction gives, for every source term t and any assignment ρ,

```text
⟦t⟧_(ρ∘μ) = ⟦μ(t)⟧_ρ.                                    (Transport)
```

The Function step follows from its four inductive hypotheses and the unchanged
constructor; it does not require unfolding bound incidence cycles. Define
`π_s(ρ) = (ρ∘μ)|D_s`.

Now enumerate **every** actual native inference coordinate by

```text
R_S = {Value(j) | 0 ≤ j < S.bounds.len()}
    ⊎ {Effect(j) | 0 ≤ j < S.effect_bounds.len()},
U_S = R_S \ μ(D_s).
```

For a fixed arbitrary `σ ⊨ C_s`, define a total assignment on this enumeration:

```text
ρσ(μ(r))     = σ(r),                  r∈D_s;
ρσ(Value(j)) = ⊥V,                    Value(j)∈U_S;
ρσ(Effect(j))= ∅,                     Effect(j)∈U_S.          (Extension)
```

Injectivity makes the first line unambiguous; the tagged complement makes the
cases disjoint and exhaustive. In particular `ρσ(μ(i_λ))=σ(i_λ)`,
`ρσ(μ(r_λ))=σ(r_λ)` and `ρσ(μ(κ_c))=σ(κ_c)`, even when those finite effects
are nonempty. Captured graph row indexes, relation IDs, Term handles, operation
slots and stamps are not additional inference variables in the R336/R341
assignment domain. A Term denotes its fixed constructor over rows.

This definition alone is **not** an admissibility proof for the bottom/empty
cases. Section 4 proves that no actual H₀ clause uses U_S. For example, an
unused collected Name Value is in that complement, whereas its semantic formal
and all active Lambda/Apply ports are in μ(D_s).

## 3. Actual source origins and the admission base

Here source generation is audited independently of the desired native
entailment. The exact R341 constructor inventory is also the entire seed
inventory of this run:

| Origin | Occurrence/coordinate check and actual admission |
| --- | --- |
| Literal facts | `candidate_source.rs:1558–1573` emits slots 0/1 for the two Value inequalities and 2/3 for the pure Effect interval, using that literal's component positions |
| Parameter Name facts | The endpoint lookup selects the registered formal (`1131–1137`); slots 1/2 bound **that Name's Effect component**, with no Value edge for its unused component (`1724–1741`) |
| Value Lambda | Creation slots 0/1 are pure (`shadow_apply.rs:3610–3619`). One retained recipe names its formal, semantic body Value and body Effect (`candidate_source.rs:2050–2070`). `lib.rs:11557–11747` allocates i/r, admits Effect slots 3/4, and admits slot 2's positive Function-to-Lambda row |
| Apply | The registered recipe is checked against the exact source input by `same_endpoint`, distinguishing Component from Parameter (`shadow_apply.rs:3946–3965`; `candidate_call.rs:755–762`). `shadow_apply.rs:4085–4158,4167–4270` constructs the exact negative Function demand in slot 0 and the callee/invocation inclusions in slots 1/2 |
| If | Each actual child occurrence's slot 50 supplies its Boolean/branch Value demand and slot 51 its Effect inclusion (`candidate_source.rs:1632–1655`). Else is present; no no-else Unit branch is substituted |
| Group/Block | A Group recipe supplies slots 0/1 at the Group/Block occurrence. Every StatementBlock expression-prefix has its own occurrence's slot-51 Effect inclusion (`2038–2101`; `shadow_apply.rs:4195–4224`) |
| Definition Link | Body's semantic endpoint to the distinct Definition Value component, at the body's slot 30 (`candidate_source.rs:2164,2427–2435`; `candidate_scheme.rs:4778–4789`) |

For Lambda, the ordinary collector enables both candidate Values and graph
Effects and enters `try_new_candidate` (`shadow_apply.rs:1823–1833`). That
initializer calls `start_candidate_graph` (`lib.rs:10436–10441`), whose fresh
graph is published as `Some` (`candidate_scheme.rs:2263–2288`). The actual
candidate mode therefore makes `candidate_graph_enabled()` true
(`lib.rs:13520–13528`). Annotation-free formals are registered as Value;
`initialize_candidate_source_levels` allocates an entry row **only** for
Computation formals (`candidate_source.rs:2250–2285`). That guarded allocation
does not happen here. Later Lambda admission allocates the two required rows
at the formal's level, uses negative i/positive r in the Function, and uses
positive lower/negative upper views in slots 3/4. Default/record-pattern and
Computation-formal branches are absent under the original K0 membership
premise. The non-graph `(empty,body_effect)` fallback is not used as evidence.

For Apply, the allocation at `shadow_apply.rs:4097–4107` is the same κ used
by the demand and slot 2. `NativeInterface` and `DirectionalIntroduction`
store those endpoints as sidecar evidence; they add no H₀ conjunct. Scoped
authentication/transformers are guarded out, as R337 J proves. Structural
Term creation checks all four child kinds/polarities before interning the
**full** node (`term.rs:1230–1270,1390–1407`). Sharing that node does not share
or erase source occurrences and is not an entailment argument.

There is no pre-admission source cache suppression in this family.
`ConstraintBatch::emit` always appends the occurrence and its exact endpoints
(`lib.rs:2146–2164`); `append_source_facts` schedules every appended index
(`candidate_source.rs:2220–2223`). `retain_candidate_relation` appends each
recipe (`shadow_apply.rs:3685–3720`), and Lambda likewise appends its recipe
before scheduling its action. The action dispatcher follows the exact next
action (`candidate_source.rs:2415–2444`). Collected facts, Link, recipes and
Lambda admissions record provenance and enter the typed constraint path on
every successful fresh **or duplicate** store receipt. The Link helper is
`candidate_scheme.rs:4781–4789`; the other owners are
`lib.rs:11481–11527,11557–11747` and `shadow_apply.rs:4167–4270`.

Thus each actual incoming typing formula is exactly μ(q) for its original
q∈C_s, with the actual rows above. Admission has the semantic update
`H_after = H_before ∪ {μ(q)}`, counting its live caller/frame owner. This is
not an assertion of equal solution sets. `σ ⊨ C_s` and Transport prove that
ρσ satisfies that added formula. A duplicate FactId is not used to deduce
prior entailment. Source facts are not enlarged to include propagated tasks.

## 4. Joint support and satisfaction induction

Freeze the actual final row set R_S as a mathematical ambient set. Every
earlier successful prefix uses a subset: initialization/fresh allocation
append rows; the contracted successful path does not roll back/truncate them.
The final map's description of an eventually allocated source coordinate is
legitimate in this proof about an already fixed run; the compiler need not
know future assignments.

For each successful prefix T, jointly prove

```text
supp(H₀(T)) ⊆ μ(D_s),              ρσ ⊨ H₀(T),                (I)
```

including actual local transfer clauses at intermediate publications of
successful operations. Support means the matching tagged row variables in
the **actual formulas**, including Function subterms, not reachability in a
provenance graph. This is induction on the finite chronological constructor
and mutation history, with inner induction on the finite body of each
successful operation. It is not induction on eventual solver termination or
on an acyclic bound graph.

**Base and allocation.** Initialization creates empty bound vectors and no
work, processing or replay formulas. Fresh graph startup is default empty
context/work state. Hence I holds vacuously. Bare row allocation adds no
formula, so preserves I. The only fresh inference allocations reached later
in K0 are Lambda i/r and Apply κ, all named in D_s (§§2–3). Excluded pattern,
FreshUse, annotation and high-extrusion branches cannot supply another
producer. In particular arbitrary rows are not assumed unconstrained:
allocation merely preserves the previously established formula invariant.

**Source steps.** Section 3 supplies the exhaustive actual input list.
Every added μ(q) has support in μ(D_s) by definition, and is true under ρσ
by Transport and σ's satisfaction. Administrative source cursor/depth/source-
support records add no typing formula. This proves I through each source
action, including every intermediate Lambda/Apply admission after its fresh
rows exist. It does not assume that a later physical owner has already been
installed.

**Transfer and context.** `start_typed_drain` retains q in its actual initial
frame, seeds the same task pair, and queues it (`lib.rs:14186–14239`).
Dequeue retains the exact task first in a local and then current; processing
selects that same item's relation (`14289–14366,15166–15173`). R337 J gives
identity contexts, default flow, no Allowance/views/discharge, and
`candidate_context_execute=false`; exact relation/key alignment is checked
by transport/execution (`candidate_context.rs:3767–3826`). Section 2 fixes
representatives and endpoints. These are copies/transfers of an already true
formula with the same support. Saved processing pairs/relations are separate
actual formulas already satisfying I; restoration does not identify them
with the new frame's initial request.

**Owner admission and physical insertion.** For a row task l≤u, the candidate
Value/Effect apply chooses `(lower-row,Negative,upper)` at the level tie, or
`(upper-row,Positive,lower)` / `(lower-row,Negative,upper)` for a nonrow
endpoint (`candidate_extrusion.rs:1115–1176`). In every case β is the exact
current formula. Owner-side attachment can precede append, but the new
relation is exactly `bound_pair(bound)` (`candidate_context.rs:3898–3937`).
The source/readback lemma of R338, reused by R345/R346, checks the complete
key and addressed physical cell (`candidate_extrusion.rs:702–875`). Thus
both the pre-append attachment and physical incidence copy the true current
formula and its support. They do not add the processing parent's different
pair merely because it provided provenance. Identical endpoints need no
bound; the no-row pure Effect pair is ∅⊆∅. No formula is justified by the
word `OwnerEmission` or its receipt.

**Ordinary opposite-bound replay.** The actual producer selects bound keys
`(o,Positive,l)` and `(o,Negative,u)` and forms precisely l≤u
(`candidate_extrusion.rs:1070–1112`). By I the two actual β premises are true
and supported in μ(D_s). Value-preorder or Effect-inclusion transitivity
therefore gives the child's truth, and its endpoint support is a subset of
the two premise supports. Attached fibers, contexts and dependency identities
remain distinct. `begin_replay` constructs that same pair for each selected
ordered fiber; its local child vector, later ReplayOperation, queue item and
frame carry the same formula (`candidate_context.rs:3992–4074,4156–4228`).
R346's reviewed publication/transfer argument accounts for the local owner
between cursor publication and operation insertion. No extra formula is
obtained from a dependency-key hit or `Queued` outcome. I holds for every
child actually generated and every transfer, including multiple distinct
slots whose formulas happen to agree. This use does not claim completeness
of an ungenerated interaction from a test or cache bit.

**Function decomposition.** R345 §A proves, in the unchanged R336 least
preorder, the equivalence

```text
Fun(A,EA,ER,B) ≤ Fun(A',EA',ER',B')
 ⇔ A'≤A ∧ EA'⊆EA ∧ ER⊆ER' ∧ B≤B'.                           (F)
```

Its forward direction follows by four monotone/antitone coordinate maps
and induction on preorder derivations, including intermediate lattice rules;
it is not a newly assumed inversion axiom. Native Function dispatch reads the
actual four children and constructs exactly those four directed tasks
(`lib.rs:16452–16492,14821–14870`), with Argument/ArgumentEffect Swap and
ResultEffect/Result Preserve at their actual FunctionPort relations
(`candidate_context.rs:3505–3568`). The current parent is true by I, so F
proves each child true. Each child's support is contained in the parent's
structural support. The reverse suffix/pending/enqueue stages transfer these
same children (`lib.rs:14953–14990`); parent/current removal adds nothing.
Any later Function descendant repeats this step on an earlier true parent.
It does not acquire the replay parent's two-bound witness by relabeling.

**Cache, diagnostics and retirement.** The typed pair cache is downstream
of occurrence admission and may delete/skip an already active task. Such
deletion cannot falsify I for the remaining theory. This observation proves
only the direction needed in this induction; it does not turn a memo into
proof that a removed formula remains entailed. For the separately needed
retention direction, R341 supplies actual persistent row witnesses; R339/
R345 supply their exact replay/Function/whole-frame cases. The generation
stamp is written before append/decomposition completes, so no argument uses
it as evidence of completion (`candidate_intrusion.rs:423–455`).

Exact memo/receipt/diagnostic updates add no H₀ clause. The Value dispatch's
extreme/reflexive shortcuts and incompatibility diagnostics add no new typing
formula; remaining Function branches are handled above. Tuple/record/variant
and contextual-effect branches have no source or inductive producer in this
K0 carrier, by R337/R345's origin census. Diagnostic witnesses/replay do not
bootstrap another typed source obligation. Removing current/designated,
Function arrays, exact replay acknowledgement slots or a completed frame is
deletion of true clauses. Restoring previous processing reinstalls the exact
saved true clauses, whose support was already covered by I. The actual
terminal driver performs Diagnostics, consumes its owned acknowledgements,
and only then reaches ReturnReady/pop (`lib.rs:14881–14945`); no numeric
completion marker is substituted for that source control flow. R345's
stronger two-inclusion retirement proof remains valid in its own family,
but is not used to disguise a foreign-continuation quantifier here.

**Extrusion/intrusion and remaining producers.** Section 2's exact identity
extrusion and empty pending-parent argument rules out a different row or
rewritten structural task entering the induction. R337 J also rules out
contextual discharge, incoming-Allowance and effect-view producers. The
initial carrier is rows, the four base atoms, pure endpoints and four-port
Functions. Row insertion, replay and Function child selection preserve that
carrier. Hence it cannot reach an excluded structural/operation source
constructor merely because dispatch contains an arm for it. All active
formula constructors are the source, exact owner, replay, structural-child,
and transfer cases just proved. Ordinary metadata/capacity accounting creates
no inference coordinate or typing formula.

This completes the joint induction on the contracted successful history up
to source-drain completion. Both support and satisfaction were established
at their adding constructors, not inferred from the final queue being empty.

## 5. Graph capture, finalization and the actual observation boundary

The ordinary public branch explicitly executes source/SCC schedules, field
tails, then `finish_candidate` (`shadow_apply.rs:1922–1932`); the private
`run_candidate` wrapper has the same order (`lib.rs:10672–10691`). Candidate
graph-plan scheduling executes the Definition source before root capture
(`candidate_scheme.rs:2829–2905`). K0 has no module uses, local bindings,
operators, members or field-tail/role constructors, so the incoming-use,
member and operator-provider branches create no additional work. In candidate
source mode the post-capture incoming-use branch is explicitly skipped
(`2956–2969`). The contracted single Definition has no separate loose or
Expression-root schedule that readmits its source actions.

Root capture's `Capture` contains `session: &InferenceSession`
(`candidate_scheme.rs:1591–1611`). Its row/node/bound expansion writes a
separate `Graph`; live row/bound vectors and levels are read through that
immutable session (`2520–2827`). Captured local row indexes do not allocate
new live inference rows. Publishing the graph updates graph storage,
accounting and active-root metadata (`2905–2960`), not the H₀ conjunction.
The empty K0 role/field obligations stay empty because none of the Section 3
sources or Section 4 propagators creates those descriptors.

Specifically, field-tail processing collects active and captured descriptors
(`candidate_scheme.rs:3406–3504`). All are empty here under that established
K0 condition, so its pending/deferred loops have no item to dispatch. Its
terminal `refresh_candidate_field_tail_captures(...,[])` call does not sneak
in a new solve: stored Definition graphs have no field obligations and the
refresh loop's empty-obligation/no-residual guard skips them
(`3740–3780,3813–3823`); remaining residual/local update loops are empty.
No unproved claim about nonempty field-tail finalization is imported.

At the candidate finish boundary, `finalization` is None and the active
field-tail guard must pass (`lib.rs:10680–10691`). Let S be the actual live
state immediately before `finish_observations`, with R341's independent
`NativeComplete₀` premise retained. All changes since the last source drain
therefore preserve I. The output routine reads direct bounds to construct
its limited `SolvedProjection` (`19807–19879`) and consumes the session; this
proof neither interprets that compact view as H₀ nor proves its equivalence
to source solutions or a whole-language certificate.

Thus at S,

```text
supp(H₀(S)) ⊆ μ(D_s)   and   ρσ ⊨ H₀(S).
```

Every native complement coordinate in the exhaustive R_S enumeration is
absent from all actual final clauses. Only **after this result** do the
bottom/empty choices in Extension become justified. Source-supported latent
effects retain σ exactly. All assigned Value terms and Effect sets are finite;
the new complement witnesses are finite too. No solution of a cyclic graph
was manufactured by unfolding it or by presuming its reifiability.

## 6. Both inclusions and application to the original supplier

For arbitrary σ satisfying C_s, Extension is total, and injectivity gives
`π_s(ρσ)=σ`; Sections 3–5 prove `ρσ ⊨ H₀(S)`. This proves Lift.

Conversely fix any `ρ ⊨ H₀(S)` in the original R336 assignment carrier.
R341's reviewed retention theorem applies to this same authentic K0
construction, completed-state predicate and μ. Its exact physical witnesses
and Transport give `π_s(ρ) ⊨ C_s`. We reuse **only** that direction, without
deriving it from the present deletion argument. Hence the candidate result is

```text
π_s(Sol_R_S(H₀(S))) = Sol_D_s(C_s).
```

This supplies the previously missing native-extension premise at the bounded
N/G end-state interface: for any supplied C_s solution, an exact native
solution with the same source/output assignments is now constructed for this
actual completed state. R336 D1/G-sound and R337 J still give the independent
source judgment under their original premises; R341 still gives its unchanged
four-premise S0 implication. The new direction supplies no missing source
typing-to-C_s completeness derivation, no completed state from source alone,
and no model from conflict freedom. W, Z, general G-completeness and full N
therefore remain separate obligations.

F1/FK1, foreign continuations, representative-changing paths, FreshUse/export
witness transport, complete Calls and whole-language source forms are not
covered by this actual K0 origin induction. The newest TeX's packet H,
world-indexed V/C meaning, language Y_H, principal package, Q1–Q8, BuildLocal,
certificate construction/processing completeness, original A/B and production
are not conclusions of this candidate.

## 7. Evidence status, residual work and falsifiers

No exact missing premise or source-qualified counterexample was found inside
the stated bounded claim. The new mathematical/source correspondence remains
a **producer candidate** until Luna's fresh non-contributor review and
adjudication. Neither this proof author nor the complementary census author
can independently certify their combined result.

Reused within actual premises: R336 rev4 algebra/L0/source coordinates; R337
successful-prefix J; R341's accepted retention/map; R345's reviewed F and
ordinary transition/origin evidence; R346's reviewed ordinary replay-local/
operation/queue/frame ownership. R338/R339 are used only through those frozen
reviewed dependencies' stated owner/replay results. R347 supplies pinned
source inventories and its explicit OPEN outcome, **not** a proof or a time
grant. Its informal support sketch is not a premise of this derivation.
Rejected arguments include purity of all latent Effects, identifying unused
Name Values with formals, arbitrary complement assignments without Section 4,
entailment from cache/FactId/stamp/Term sharing/OwnerEmission, and projection
equality inferred from compact output or green tests.

`R348-REVIEW-1` — Luna owns fresh isolated review of these frozen bytes and
the pinned primary source check/censuses. Challenge the exact source/input
inventory, one-pass auxiliary allocations, coordinate injectivity versus Name
aliasing, graph-enabled Lambda branch, chronological support/truth induction,
and the actual empty-obligation finish path. A missing active formula owner
or a reachable excluded constructor is a source-boundary finding, not yet a
compiler defect. A semantic falsifier requires authentic s,S, a finite
`σ ⊨ C_s`, and failure of **every** allowed extension with this exact
projection. Under the support lemma, a final clause falsified by Extension
already supplies that valuation separation; a hypothetical unreachable state
or an unsatisfiable σ does not.

`R348-N-G-RESIDUAL` — Luna retains original full N/G and A/B. Apply only an
accepted Lift to the bounded end-state extension premise; keep source-typing
completeness, termination/model existence and every independent continuation
quantifier OPEN. Any next packet must name its first source/consumer premise
and retain the original domain/quantifiers. This TODO grants no new output,
semantics, budget or production right.

`R348-IMPLEMENTATION` — `NO_SAFE_CODE_SLICE`. The actual admission/dispatch
owners (`shadow_apply.rs`, `lib.rs`) and root-capture/empty-finalization owner
(`candidate_scheme.rs`) were inspected. No source-qualified defect or need
for executable instrumentation was established. If review finds a missing
formula/coordinate, Luna owns a minimal provisional evidence packet at that
exact constructor/consumer with the authentic valuation/owner falsifier above;
no compiler change is authorized by this note.

## 8. Frozen dependencies, provenance and checks

Source/theorem baseline: `f1536e5515e8a38c484d0ada5dbd308dcdc6a543`.
Launch/current snapshot: `03b660e15d19a7e2439388889be170b3380b7b2a`.
Luna confirmed the intervening changes are R348 research/metadata only and no
solver source changed. These commit labels are primary-supplied metadata;
the worker performed no Git operation. All ten actual source hashes matched.

| Direct frozen input | SHA-256 |
| --- | --- |
| R348 contract rev1 | `b40044fe20570f9c92049f469d9cbf8407c09099ae33fbf7781155250ffdcba2` |
| R348 primary source check | `61ff50a919ff37f58bf098b87d4044d24cc63f230591e5fa91fb105e8d948829` |
| Original audit | `b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895` |
| Governing TeX | `28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65` |
| R336 rev4 proof | `4bcbe71ec9f2372baca884e3db737c16fc19ad2a51103965ade5ca4c2ecf4973` |
| R337 J | `e14b8125a505c3001021396b8c6e949e3b0a58f61ecf2785f915dbdde65dfc62` |
| R341 proof / census / accepted outcome | `f8607d11c417734c1a7fb5aafe1af7ca78a587c5f5e7189c8cf3dcbc2064343f` / `729c224785d42ee3577351e6a001668fe97a17fb2323aa532f52bbc8a1be0eeb` / `7e5a5905a49335cf7c314da6fd33e800a9552109b638ee5914b050f2b20602bc` |
| R345 proof / census / accepted outcome | `85f8def9fe6e3c07b249c279d14976a428cf15c2d3eba089dbc4f5770e16f8df` / `065fbcd824caa394c4b297159d1ea08925829ad7c608c2814a16e96a9df3126b` / `a8b9b75d41be900060d7ba593bb77aaec738a67674654b6c823e92fac18ac8ce` |
| R346 contract / proof / census / accepted outcome | `7f2419fa4d589ec6bb7d8af769a3eeb94f5361332483321328a06c2558327391` / `f21a15eac621216366338ceeb454aec868554668a6cc4b8da903aa79d9d2fc7d` / `1179312d8230616a0ac5cda45a1c29f08012bba9327f2f3601bb3179cfb5fdfd` / `25748200d206c375a2e450aff688f692a4bfc5537ef7ba3fdc953423006b6512` |
| R347 rev2 contract / census / Lambda supplement / OPEN outcome | `3ff5884ffefb9dca31f5433b68af56f3c6f172feab2284c1c80235dbfbe7ac5b` / `f40856702e43bcf4b990e980bee841292b792c372c7ba99dea1c6ea10b87eb7f` / `157edb3eb6588d3b18e53d9376b5e4a4c9a522d27d9d63bf3a215b374949d3d6` / `f6018a214668b4002e8db97fbe6905294c49939f8f069417227947e4686db21f` |
| `candidate_source.rs` | `0dc798e48e70505093e52b31b2569e3b2d8ff1dee663095176aaf547ccb3289b` |
| `lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `candidate_context.rs` | `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5` |
| `candidate_effect.rs` | `d156fdbf0300387a5aa036053a2cc7eeb6312a803aaf38838e30dd2731ca4945` |
| `candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `candidate_call.rs` | `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f` |

Historical proof authors: R336 primary `/root` with algebra producer
`/root/r336_k0_algebra_prover`; R337 `/root/r337_k0_context_prover`; R341
`/root/r341_k0_source_retention_prover`; R345
`/root/r345_k0_initial_drain_prover`; R346 `/root/r346_k0_replay_prover`.
Primary censuses/outcomes are Luna-authored. Individual original audit/TeX
and compiler-source authors are UNKNOWN. Historical author/review receipts
are reused metadata, not newly authenticated reviewer execution.

Checks: direct source reading, manual derivation and SHA-256 comparisons.
No tests, builds, Cargo, executable probes, compiler/expectation edits, Git,
external contact, descendants or scratch paths. The only new paths are this
proof and `tasks/agent-loop/inbox/20261023-r348-k0-lift-prover.md`.
The handoff carries the proof's frozen byte hash and exact writer-stop clock.

Requested role/model/effort: prover / `gpt-6.1-sol` / high. Actual worker
identity `/root/r347_k0_end_state_prover` is retained from the earlier stopped
identity, but this is a **new R348 assignment**. Effective model/effort and
child runtime session ID are UNKNOWN. Primary session label supplied by Luna:
`01a165ee-0212-7af3-8c99-1c1efcf367fe`; it is not claimed as an observed child
session. Exact grant start `2026-10-23 10:26:23 UTC`; fixed expiry
`2026-10-23 11:16:23 UTC`; active-work acknowledgement `10:26:37 UTC`.
The full 3000-second grant is charged, with no renewal/carryover or R347 budget
transfer. Writer stops at the frozen handoff; no work continues during review.

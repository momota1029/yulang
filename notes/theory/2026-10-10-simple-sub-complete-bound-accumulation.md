# Complete Call bounds: finite same-value saturation with exact witness retention

Date: 2026-10-09 (task date; source filenames include later research dates)
Baseline supplied by primary: `b2894cb6b7b64f0d47e64a0a85a183d11ac6742a`
Status: independently reviewed finite research theorem; no semantic adoption
Scope: finite same-index complete inclusion constraints; actual same-level row-only Simple-sub bridge
Review: [independent mathematics and specification review](../progress/2026-10-10-simple-sub-complete-bound-review.md)
Claim class: constructive finite algorithm, exact residual factorization, actual row-only bridge and complete path-proof discovery
Production routing / public grammar / F5 cutover: unchanged

## 1. Result

**There is a complete-constraint-safe Simple-sub accumulation fragment.** Treat each complete descriptor endpoint as an opaque, correctly scoped semantic operand. An emitted `VIncl(A_f,F_c)` is an ordinary variable upper bound on unknown `A_f`; collecting that edge requires no satisfying assignment, returned provider, actual role, or proof that `f` is already callable. Lower/upper propagation through a shared flexible endpoint is sound because `VIncl` is pointwise inclusion of the **same decorated value**, including its actual provider, world, incidence and all retained alternatives.

The algorithm below terminates on any finite presented graph. It gives an exact residual presentation with projection/reconstruction maps preserving the **entire original dependent witness tuple**, rather than merely satisfiability. Every derived edge has a deterministic derivation referencing the original proof slots. No original proof choice is replaced with a composite proof. A comparison of two nonvariable complete Function operands stops decomposition locally and remains a residual edge. This STOP result is neither rejection nor satisfiability failure.

The sound fragment does **not** justify ordinary scalar Function-child decomposition of every semantic `VIncl(F,G)`. Contextual Function membership alone does not make domain inclusion a necessary consequence of same-value membership inclusion. Genuine complete Function *checking constructor evidence*, when present, does expose full domain and observation inclusion; those may be projected soundly. WholeArg stays opaque unless its actual rule supplies a destructor or a separately proved supplier. No original `CallMem`, full source coherence, successful Direct, registry supplier or L adoption is assumed.

## 2. Sources and authority boundaries

The direct semantic premises are:

1. `notes/design/2026-10-08-contextual-function-membership-definition.md`, §2, and its selected proof `notes/theory/2026-10-08-call-semantic-input-realization.md`, §§2–3.2: `VIncl` acts pointwise on identical decorated values. Function membership quantifies over every retained actual decomposition and every independently admitted complete challenge; acceptance and all complete/pending/future observations are required at that same provider and live event. A printed Function skeleton is not the complete interface.
2. `notes/design/2026-10-07-complete-call-contribution-definition.md`, §§2–4: complete original Call and W/Z alternatives retain their own operation, evidence, independent declarations, provider/world and future interfaces; membership is not source accounting and does not prove C0.
3. `notes/theory/2026-10-08-source-generalize-definition-and-proof.md`, §3.2 (selected by `notes/design/2026-10-08-source-generalize-definition.md`): logical semantic inclusion composition is allowed. Complete Function checking has actual domain/observation subproofs, and these inclusions are conclusions of the finite local checking tree. This does not say every true semantic inclusion has that proof grammar.
4. `notes/progress/2026-10-06-source-call-generation-construction.md`, §5: the complete Call relation retains `WF_Dec`, same-value `VIncl`, existing independent `WholeArgCompatible`, dependent result inclusion, `TypedCallCert_Dec`, roles and source records. Generation requires no satisfiability.

`notes/theory/2026-10-10-literal-emission-pipeline-proof.md`, §§3.5,4.1,9–10, has a useful explicit ordered **L** telescope, but its concrete registry/image/argument/result/emission choices are UNADOPTED. Its `WholeArgCompatible_L` is explicitly new, not an expansion of original WholeArg. The q3 approval mentioned in the assignment is design approval only; it is not exact L/raw-registry adoption.

The independent mathematical fragment is an accumulation algorithm and a conservative view of existing evidence. It makes no new source-acceptance decision and selects no compiler implementation. Any genuinely new checking constructor discussed below is a candidate requiring adoption, not an inferred extension of an opaque old predicate.

## 3. Fixed semantic and scope setup

Fix a finite ordered source/component telescope `T`, with its actual nested rigid and dependent proof binders. An assignment `eta` is scope-respecting in the original sense; siblings of equal depth remain distinct binders. Retain the whole original witness family `R_T(eta)`. It can include, without modification:

- original `xi=(nu,K,D)` and complete descriptor/domain WF;
- actual `WF_Dec`, `WholeArgCompatible`, image/result checking and their proof dependencies;
- every original complete operation/provider/role/entry/world/receipt/profile/license field;
- callee-pending, receiver-pending and future-use interfaces and ordered suffixes;
- every W/Z alternative and all original declaration and nonexecution evidence;
- complete Call certificates, source origins and all actual scope/reference maps.

No positivity, nonemptiness, decidability, product factorization, source-generation property or proof irrelevance of `R_T` is assumed. `R_T(eta)` may be empty.

A node is an actual endpoint **reference at one declared comparison context and full membership-family index**. Here `sigma` includes the exact original `xi=(nu,K,D)`, complete membership-family arguments, actual scope/substitution and event-family binder telescope; it is not a numeric level or bare source occurrence. Its key includes the declaration/binder reference, sort, actual scope inclusion and this complete indexed comparison context. The same written `A_f` at `xi1` and `xi2` does not authorize a common pivot. Composition requires literal identity (or independently supplied genuine typed equality) of the intermediate complete membership type at the same original scope. No common world/join, weakening or transport is derived from endpoint equality. Compound complete descriptors are finite presented references; their internal semantic witness domains can be infinite. An outer parameter referenced in an inner Call has its actual outer declaration and inner reference map; the inner edge is not hoisted to the outer declaration scope.

A V-edge occurrence `i` retains `(s_i,t_i,context_i,origin_i,e_i)`, with `e_i` the corresponding original proof slot. Let

`I_sigma(S,T) = forall z in DecVal_sigma. Mem_S(z) -> Mem_T(z)`.

Here `z` is the identical full decorated tuple throughout: value, retained actual decomposition evidence, root, original assignment, current event/world/incidence and hereditary obligations. `I` does not inspect a successful concrete query. Original `VIncl` evidence provides this semantic action; original evidence can contain more fields than this action, and all of those remain in `R_T`.

Composition at one identical indexed domain is defined on actions by

`compose(p,q)(z,m) = q(z,p(z,m))`.

A composition certificate is a logical derived view, not necessarily an inhabitant of every opaque original *source proof grammar*. A solver must not cast it into an original source-specific atom whose complete evidence constructor has not been supplied.

## 4. The finite accumulation algorithm

For each actual comparison context `sigma`, let `N_sigma` be its finite presented node references. No constructor children or new structural nodes are created in this algorithm. Cross-context propagation is absent unless an already supplied lawful whole-map certificate explicitly gives a correctly indexed edge in the destination context.

Maintain:

- the complete immutable original tuple/telescope `T,R_T` and every original edge occurrence;
- a set `Seen_sigma` of ordered endpoint pairs, used only for scheduling;
- `Lower_sigma(x)` and `Upper_sigma(x)` for each flexible node reference `x`;
- for each scheduled derived pair, one finite derivation DAG over exact original edge occurrences;
- residual complete edges and original predicates unchanged.

Original duplicate occurrences and their separate proof slots remain even when their endpoint pair has already been scheduled. The scheduling set is not the semantic evidence store.

Pseudocode:

```text
seed: enqueue every original VIncl occurrence with its exact occurrence reference

while queue is nonempty:
  pop (s,t,derivation) at its actual context sigma
  retain the occurrence/derivation as a deterministic view
  if (s,t) was already scheduled:
    continue scheduling work; do not delete an original occurrence/proof
  mark (s,t) scheduled

  if t is a flexible node x:
    add (s,derivation) to Lower_sigma(x)
    for every existing (u,du) in Upper_sigma(x):
      enqueue (s,u,Compose(derivation,du))

  if s is a flexible node x:
    add (t,derivation) to Upper_sigma(x)
    for every existing (l,dl) in Lower_sigma(x):
      enqueue (l,t,Compose(dl,derivation))

  if neither endpoint is flexible:
    retain (s,t) as a complete residual comparison; STOP decomposition here
```

A flexible/flexible edge is registered in both lists. A self-edge can be retained and scheduled once; it does not imply endpoint equality or merge evidence. No occurs check, Function head inspection, concrete successful comparison, satisfiability query or provider selection occurs. Optionally one may schedule reflexive derived action views, but that adds no useful original proof and is unnecessary here.

For an explicit finite operational bound, use one stored representative DAG per scheduled pair. Keep every original occurrence separately. A newly scheduled pair scans finite opposite lists; at most `sum_sigma |N_sigma|^2` pairs are scheduled and all scans are finite. This gives a finite executable algorithm; a simple implementation has polynomial bookkeeping in this fixed node universe. No timing or production resource-limit claim is made.

## 5. Theorem BOUND: sound saturation and exact full residual factorization

### Statement

For the setup in §3 and algorithm in §4:

**B1.** The algorithm terminates, even with flexible cycles and complete Function endpoints.

**B2.** Every scheduled derived edge is entailed, as a same-decorated-value semantic action, by original VIncl edge proofs at its exact comparison context. It leaves actual providers, worlds, challenge domains and original incidences unchanged.

**B3.** Let `View(eta,w)` be the deterministic evaluated bound/derivation record for `w:R_T(eta)`. Define the transformed family by the actual record constructor

`R_T^bound(eta) = { BoundRecord(w, View(eta,w)) | w:R_T(eta) }`.

The second field is a **computed view**, not an independently quantified proof choice. There are exact maps

`extend(w)=BoundRecord(w,View(eta,w))`

`erase(BoundRecord(w,View(eta,w)))=w`

with both composites the identity by constructor/projection computation. Thus the complete original witness fiber and transformed fiber are exactly represented, including proof-dependent later fields. This is stronger than a Boolean satisfiability equivalence.

**B4.** The resulting bound graph is a principal residual presentation in the following precise, limited sense: every original scope-respecting assignment and full witness factors uniquely through `extend`; every transformed witness restricts to that original assignment/witness; no endpoint assignment or original proof choice is selected, equated or lost. This is **not** a most-general closed substitution theorem, maximum semantic characterization, general inference principality or source-generalization theorem.

### Proof

For B1, scheduling increases a subset of the finite ordered pairs and processes each pair once. Every enqueue comes from two finite lists and creates no new endpoint. Duplicate scheduling is discarded as bookkeeping. A flexible cycle can cause only already-present pairs, not new syntax or repeated unfolding. Nonflexible complete Function pairs terminate their own processing by STOP. Consequently the total queue production is finite.

For B2, induct on derivation DAG construction. An original leaf invokes the action supplied by that exact original VIncl slot. For `Compose(p,q)` at flexible pivot `x`, both premises use the same `Mem_x(z)` and identical indexed decorated tuple domain. If `p(z,m):Mem_x(z)`, then `q(z,p(z,m))` has the desired target membership. There is no existential elimination/reselection of a provider, world or proof-dependent port. All actual decomposition alternatives carried by membership are covered by the action's universal argument. This proves the derived inclusion. For later compatible events, the same reasoning applies using the original lawful restriction action; no saved world or activation is restored. Cross-scope composition has not been asserted.

For B3, the original tuple is literally the first field of the transformed record. Its later dependent fields, such as an output image indexed by `e_f,e_a`, still reference those exact original proofs; no field is retargeted to a transitive derived proof. Evaluation of the finite derivation DAG is deterministic from that tuple's original inclusion actions. `erase(extend(w))=w` by projection, with its complete evidence unchanged. Conversely every transformed record is by definition a constructor record with the computed second field, so extending its first projection computes that same record. This uses no proof irrelevance or quotient. It is not the claim that arbitrary inhabitant choices of added `VIncl` proof slots are unique.

For B4, the maps are defined separately at each unchanged `eta`, and therefore their assignment projections are the identity. Applying these maps under the original rigid and dependent binder order gives the same strategy dependencies; an inner solution does not acquire an outer witness choice. In a nested `Pi/Sigma` telescope, the computed view is added only inside that entire unchanged telescope after all original dependencies it uses. This is pointwise dependent record extension, never flattening nested quantifiers into a Cartesian tuple. Arbitrary full residual predicates are preserved because their arguments are unchanged. No assumption that they are monotone in endpoint substitutions is used. This proves the stated exact factorization. QED.

### Why an ordinary conjoined proof-slot implementation is weaker

If the transformed family were instead `Sigma w:R_T. Sigma q:I(s,t). ...`, every derived edge could acquire independent proof alternatives. Its projection would still preserve original satisfiability when a composition extension exists, but there need not be an inverse on the entire witness fiber. If later constraints used `q` instead of original `e_f`, even satisfiability equivalence could fail. BOUND deliberately uses computed derived views while preserving each original binder and choice.

### Why this is genuine bound accumulation

A processed `A_f <= F_c`, with both declared flexible, records `F_c` in `Upper(A_f)` and `A_f` in `Lower(F_c)`. Adding a later source edge `L <= A_f` propagates `L <= F_c`; adding `F_c <= U` propagates `A_f <= U` and then `L <= U`. All are ordinary lower/upper bound-store operations with explicit derivations. None asks whether the formal already has a Function provider.

When a derived edge reaches two complete Function descriptors, processing stops and records the whole residual. The bound store still accumulated its variable edges. A future separately certified solver slice may handle that pair; BOUND does not pretend that its scalar children already supply the complete comparison.

## 6. What full Function evidence legitimately projects

There are three different objects, with different eliminations:

1. **Semantic `VIncl(A,F)`** yields a map on all same decorated value members. It composes by BOUND. It does not generally yield `D_F subseteq D_A`.
2. **Actual complete Function checking-constructor evidence** includes independently proved whole maps `D_F -> D_A` and `P_A(d) -> P_F(d)` for each checked challenge, in the genuine local grammar. These are available by its constructor destructor, where that constructor is actually present. They can construct same-value VIncl through contextual precongruence. They are not a completeness theorem for all original VIncl evidence.
3. **Function membership of one actual value/provider** gives actual acceptance and all observations at each admitted challenge. It does not compare arbitrary A/F descriptor domains or declare raw ViewInlet necessary.

### Theorem PROJ: finite necessary support edges from genuine whole maps

Suppose case 2 supplies an actual full domain map `j:D_F -> D_A`, preserving the entire underlying challenge tuple, and the genuine same-whole-observation inclusion action `k_d:P_A(d) -> P_F(d)` for each `d:D_F`. The common carrier is the unchanged original whole observation tuple. In particular every observation projection used below satisfies `rho_d(k_d(z)) = rho_d(z)`; this is the whole-tuple preservation supplied by the selected checking constructor, not a property of an arbitrary typed map. Let `pi` be any finite chosen well-typed coordinate projection on the actual common challenge sort. Define support, with proof choices retained in its presentation, by

`Support_pi(D) = { a | exists d:D, pi(d)=a }`.

Then

`Support_pi(D_F) subseteq Support_pi(D_A)`.

For each identical `d:D_F`, any genuine common well-typed observation projection `rho_d` similarly gives

`Support_rho(P_A(d)) subseteq Support_rho(P_F(d))`.

**Proof.** Map the retained witness `(d,eq)` to `(j(d),eq)` using the whole-tuple preservation equation. The observation proof maps `(z,eq)` to `(k_d(z),eq)` at the same challenge. Every choice remains in the source fiber; the result is a necessary projection action, not a quotient of the original tuple. QED.

A finite selection of such support edges is safe as computed derived views under BOUND, with full constructor evidence retained. The observation edges remain under their `d` binder. They cannot be hoisted into an unconditional scalar `result(A) <= result(F)` without a genuine scope/universal-support theorem. Defining new support aliases in a compiler is a new representation choice; this theorem does not claim those aliases already exist in original endpoint sorts.

To obtain familiar scalar contravariant/covariant child bounds, one additionally needs actual interpretation equations equating these support families to the written child endpoint memberships, at the identical scopes. Those equations are substantive complete descriptor/projection laws. A printed `Function(A,B)` shape does not provide them.

## 7. Effective proof construction, not certificate recognition

Define the finite proof language at each fixed complete index `sigma`:

```text
Refl(s)                     : I_sigma(s,s)
Original(i)                 : I_sigma(source(i),target(i))
Compose(p:s->x,q:x->t)       : I_sigma(s,t).
```

`Original(i)` is a reference to an original unsolved inclusion proof slot,
not a chosen inhabitant. Its later evaluation uses that very original proof.
A composition is allowed only at the identical complete intermediate
membership type. The language contains no Function-child decomposition,
provider change, new admission, cast, or arbitrary local predicate solver.

**Theorem PATH (terminating complete proof discovery).** For any finite
presented graph in one such index and endpoints `s,t`, breadth-first search
on its retained original directed edges, taking the empty path when `s=t`,
decides whether a proof in this language exists. On a positive answer it
constructs a finite proof DAG. On a negative answer no proof in this language
exists. This is not a claim that `I_sigma(s,t)` is semantically false.

**Proof.** Search marks each of the finitely many nodes once, scans each
outgoing edge finitely, and records one predecessor edge at first discovery.
The predecessor chain has strictly decreasing discovery times, so it
terminates at `s`. Reading its original occurrence labels constructs a proof
by repeated Compose; the empty chain gives Refl. Conversely induction on a
proof gives a path: Original gives its stored edge, Refl the empty path,
and Compose concatenates its two paths. Every reachable node is visited by
finite breadth-first search, by induction on path length. Hence a negative
answer excludes every proof in this precise grammar. The two directions
prove decision and evidence construction, not only recognition. QED.

The chosen path is a computed derived view. It does not select or erase any
original proof alternative. Cycles require neither unfolding an infinite
proof nor solving semantic predicates; the finite graph suffices. Strongly
connected nodes remain distinct original endpoint/evidence identities.

## 8. Scope of scalar projection

PROJ supplies necessary support edges from an actual complete checking
constructor. It does not require that every semantically true Function
inclusion decompose into scalar child inclusions. That stronger converse is
not added as an implementation prerequisite. For a source-generated rule
that already emits independently justified scalar inequalities, the existing
scalar solver can process those inequalities directly. The missing task at a
particular producer is its own exact rule correspondence, not an all-model
characterization. BOUND and ROW therefore preserve undecomposed complete
comparisons and all original residuals while allowing independently justified
scalar work in its separate domain.

## 9. Exact application to the unknown formal in `my invoke f = f 1`

The selected Parameter rule introduces `A_f` before the invocation challenge.
The selected Original-ResultLiteral formation supplies the bounded literal
Data/Result port when its original local inputs are present; its original
Code-Result does not solve `f`. These facts do not by themselves supply a
complete original literal emission. For a genuinely formed Call upper-use
constraint `VIncl(A_f,F_c)` at its actual scope, the new result is that no
further role resolution or satisfiability premise is needed to **enter** the
bound store:

`Upper_at_Call(A_f) contains F_c`.

There need be no lower bound yet. An empty lower list causes no propagation or query. No step solves `A_f`, selects `U`, asserts actual receipt, distinguishes Value/retained/operation role, fabricates a callable, or checks satisfiability.

The same component keeps `WF_Dec(F_c)`, the genuine whole argument relation, dependent complete result relation and every complete certificate/policy/suffix field at its original binders. The source direction's complete relation can therefore be represented as one bound-store edge plus an unchanged complete residual, with exact full witness factorization by BOUND. The existing generation theorem is conditional on its genuine emitted rule inputs; BOUND does not manufacture those inputs for a literal whose exact original emission has not been supplied.

For the L candidate, the same result applies *conditionally to that explicitly defined L telescope*. Its `e_out` still depends on the original `e_f,e_a`, and its final certificate still depends on all original proof choices. This is not L adoption or an original-emission bridge.

Neither the literal `1` nor its printed `Comp(empty,Int)` justifies automatically inserting `Int <= scalarArgument(F_c)`. Original WholeArg is independently interpreted and currently lacks a general exact destructor. In L, even its explicit image law quantifies over admitted target challenges and matched whole carriers; it yields a support condition only at those actual matched witnesses, not arbitrary raw events or an unconditionally inhabited target domain. Obtaining a scalar integer-domain edge requires the real scalar projection/supplier law, preserving admission and full contextual correlations. No such law is used by BOUND.

An actual full Function-check constructor elsewhere may expose its real D/P subproofs and qualify for PROJ. Ordinary pure structural Function decomposition is safe only in a separately certified scalar slice, whose exact semantics/projection interpretation has been proved. It must not consume an arbitrary complete Function pair based on its printed head.

## 10. Theorem ROW: actual same-level variable-only storage bridge

The following closes a concrete seam of the **existing code**, rather than assuming a general lifecycle adapter. Its mathematical relation is complete VIncl; rows are only injective scheduling names, not scalar descriptor interpretations.

### Exact envelope

Fix one complete membership-family index `sigma` as in §3 and one arbitrary numeric row level `ell`. Allocate a distinct row for each finite original complete endpoint reference using the actual `fresh_value_at_level(ell)`. Its code initializes empty `VariableBounds`, stores `ell`, and returns the next unique row ordinal. Retain the injection `row <-> (sigma, original endpoint reference)` and **every** original complete declaration/evidence occurrence in an immutable external arena. Fixed complete descriptor anchors may be represented by scheduling rows, but are not assigned flexible semantic variables; the inverse map retains this distinction.

Use a dedicated row-only arena/session slice with initially empty exact nonvariable bounds and no inherited cross-family row edges or memos. Issue only `ValueRow(i) <= ValueRow(j)` tasks for original complete VIncl edges. No constants, scalar Function nodes, effects, generalization, instantiation, routing, semantic endpoint substitution or publication operation is issued. No direct row method is permitted to mutate the external semantic arena. All original evidence occurrences, including duplicates, remain there even if the pair cache stores one copy.

For multiple independent `sigma` fibers, inject them into disjoint row sets and issue no edge across sets. The one-fiber theorem does not require such simultaneous execution.

Actual code dependencies read: `ValueEndpointKey`, `fresh_value_at_level`, `constrain_live`, `apply_value_task`, `positive_function_children`, `negative_function_children`, `incompatible_value_shapes`, and the `ValueRow` arm of `extrude`, in `crates/yu-solver/src/lib.rs`. No patch or executable run was made.

### Statement

Subject to successful existing fallible identity/capacity operations, after a finite list of these row-only tasks:

**R1.** Every injected row still has level `ell`; every exact nonvariable bound list remains empty. No Function children or structural comparison were scheduled.

**R2.** The code's direct upper graph contains exactly the distinct submitted directed pairs, and its direct lower graph contains their reverse incidence lists. The pair memo suppresses repeated storage of a submitted pair; it does not remove an original complete evidence occurrence from the external arena.

**R3.** A finite path in that graph at this exact index gives a constructive derived full semantic inclusion action, composed from selected retained original edge occurrences. Finite reachability plus a predecessor/path certificate discovers every consequence whose derivation consists only of such same-index path composition. It is not completeness for all true semantic VIncl statements.

**R4.** Taking the actual row graph/cache as a deterministic view of the retained original edge occurrence list, with requested path views evaluated from the original proof slots, has the exact full residual projection/reconstruction maps of B3. Unknown `A_f -> F_c` can therefore be stored by the actual kernel before formal-role or satisfiability resolution.

### Proof

Induct on successful submitted tasks. Initially fresh allocation gives all rows level `ell`, empty exact nonvariable lists and unique ordinals.

For a row/row pair, `incompatible_value_shapes` returns `None` because the lower endpoint is not an Int/Function/Bottom constructor. Neither shortcut BottomPositive/TopNegative applies. Both Function-child accessors return `None` on ValueRow. The fallback's atom/row and row/atom guards exclude row/row, so they perform no pre-branch extrusion.

If the pair was already memoized, `constrain_live` skips it without reapplying storage. Otherwise it records a value pair memo with no direct diagnostic witness, then invokes `apply_value_task`. In that branch `minimum = min(ell,ell)=ell`. Each `extrude_value_endpoint` passes its row to `extrude`. The actual ValueRow loop tests `value_levels[index] <= target_level`; here this is `ell <= ell`, so it immediately continues before writing a level, traversing bounds or marking that row. Extrusion generation/stack bookkeeping can change, but no level or semantic field does. The independent fallible stack reservation/generation guard can still fail; this is an infrastructure availability outcome, not semantic unsatisfiability.

Next the branch appends `i` to `direct_lower_rows[j]` and `j` to `direct_upper_rows[i]`. Its two replay loops scan `exact_non_variable_lowers[i]` and `exact_non_variable_uppers[j]`, both empty by the induction invariant. They enqueue nothing. Thus this task has no generated structural or atom work. Diagnostic completion/replay consumes the newly recorded memo without any direct incompatibility witness; it does not inspect the external complete declarations. This proves R1 and R2 for distinct tasks and preserves them for duplicates.

For R3, a graph path `i0 -> i1 -> ... -> ik` has an original submitted occurrence for each edge. Inverse injection returns exact endpoint references at the same `sigma`. Choose a deterministic occurrence (for example earliest source-list occurrence) only for the derived path view; all alternatives remain in the original tuple. Induction on path length uses the same-value composition proof of B2. A finite breadth/depth traversal records a predecessor for each newly visited row, stops after at most the finite number of rows, and reconstructs the finite path to each reachable target. Conversely every path-composition derivation has a graph path by concatenating its two premise paths, so it is found. There is no requirement that the core itself eagerly allocate all transitive row pairs.

For R4, graph/cache construction from the fixed original submitted pair order is deterministic at the semantic storage level, and path certificates are deterministic views. Keep the entire original assignment and proof telescope as the first field; attach graph/cache references as the computed second field. Erasure returns the entire first field, including original proof-dependent result images, certificates, worlds and W/Z evidence. Reconstruction recomputes the same view; no unknown complete endpoint assignment or proof choice is made. Original nested Pi/Sigma scope stays untouched. This is B3 applied to the actual storage seam. QED.

This theorem certifies the named **same-level, row-only, pre-generalization seam**, not the complete compiler's acceptance or lifecycle. The injection/external arena are an explicit proposed wrapper representation; the theorem proves what actual existing core methods do for its finite input envelope, rather than claiming the wrapper is already implemented or adopted. Resource/identity failures stay the code's original availability outcomes. Generalization is excluded because fresh rows currently have `non_generic=false`; permitting it would require a separate fixed-anchor and binder-preservation theorem. Unequal numeric levels, actual nonvariable atoms and cross-scope transport are also outside ROW.

The eager algorithm in §4 remains a separate algorithm specification. ROW's direct graph with finite requested reachability certificates realizes the same safe semantic consequence fragment without materializing every row/row transitive pair. For `A_f -> F_c`, fresh same-level rows and one submitted direct edge suffice; no path search, role inspection, Function child decomposition or satisfying semantic witness is needed merely to store the edge.

## 11. Exact closed fragment and review targets

Proposed theorem name: **FINITE_COMPLETE_VINCL_BOUND_ACCUMULATION**.

Exact claim: finite correctly indexed same-value VIncl variable propagation admits a terminating bound-store algorithm and an exact full-witness conservative view, with original dependent residual retained and opaque nonvariable comparisons stopped locally.

Direct premises: finite presented node/context universe; genuine semantic action from each original VIncl slot; identical indexed decorated-tuple domain at a variable pivot; unchanged original residual telescope; computed derived view rather than independent replacement proof slots.

No assumptions: CallMem inhabitance, solved Direct, all-source emission/coherence, concrete Function-query transitivity, scalar/full membership equality, provider identity quotient, source-generated W/Z, principal closed substitution, satisfiability or unknown formal role resolution.

Independent review should attack: (i) same variable declaration used through distinct scope-reference maps; (ii) original duplicate edge choices with proof-dependent result predicates; (iii) flexible cycles and pair scheduling; (iv) accidental insertion of independently chosen derived proof slots; (v) an attempted scalar Function decomposition before the complete proof/supplier laws exist.

The independently formed original Name/Name Call constraint is an existing
source-generated instance of this bound subsystem. The literal `invoke`
source experiment additionally constructs the actual retained HIR scalar
graph, with the explicit limitations of its test module. Neither instance
converts the bound subsystem theorem into complete Call inference. In
particular, missing original declaration signatures cannot be replaced by
unsolved proof holes of unspecified types. Existing well-formed types may
have unsolved witness slots; absence of their inhabitants is not a static
formation failure. Complete literal emission, exact registry interpretation,
whole Call solving and ordinary publication are outside the closed fragment.

## 12. Verification boundary

The mathematical proofs use the selected same-value inclusion interpretation,
finite graph induction, explicit computed proof terms and the actual row-only
code branches identified in ROW. They do not assume a joint solution or a
completed Call certificate. The accompanying test-only adapter exercises the
real `InferenceSession` on deferred scalar Function constraints and actual
retained HIR. Scalar tests are implementation evidence for that narrower
service, not an independent oracle for complete Call semantics. Review,
executed commands, frozen hashes and exact integration scope are recorded in
the companion progress review record after adjudication.

The proposed wrapper representation and general complete-constraint runtime
are not production implementations. Canonical DAG statuses are not changed
by this fragment theorem. Neither original `CallMem/C0` nor general JOINT_DEC
nor transformed `invoke` public export is claimed closed.

# Complete Call-position and source-occurrence construction

Date: 2026-10-07
Status: Reviewed; original review history below, selected §10 cases now adopted
Baseline: `b540c04df0e0cce554f2d02f3c7fbb22a9fc1102`
Affected-dependency revalidation: `701213b631361811c0c3c9d8c9ec4db2a475570b`
Scope: a conservative, fully specified static constructor completion for H_eff
       and OC-CallEff; exact approved nested source instance
Claim class: conservative construction theorem; not legacy-original O0 closure
Original review's semantic, implementation, and production authority: none; later limited adoption below
Reviewed-by: independent compiler-referee and spec-auditor; fresh compiler-referee delta pass
Review and integration: [exact scopes and findings](../progress/2026-10-07-call-construction-proof-review.md)

**Adoption update.** At `2026-10-07T22:09:13+09:00` the user approved §10's
two formation cases and §10.1 root interpretation as the governing missing
original definitions on actual emitted Gen-Call-0 records. The
[Authoritative definition](../design/2026-10-07-original-call-formation-definition.md)
records that exact choice; the independently reviewed
[O0-selected proof](2026-10-07-adopted-call-formation-o0.md) supplies local
original typed incidence and its exact consumer use. The original proof below
is preserved: its former unadopted/proposed wording describes the pre-approval
state, and §9 still governs comparisons with a separately fixed interpretation.
Fresh-family conservativity is not repurposed as an old-family identity proof.
No whole original domain, downstream gate or production authority is added.

## 1. Result

A complete constructor package exists without assuming a source/signature map,
original Call-occurrence typing, seed truth, successful comparison, receipt,
execution, or a satisfying Function description. The package independently
constructs signature-position derivations from a scoped Function frame, and
constructs one Call-effect occurrence for every emitted Gen-Call-0 record
in the frozen input graph. Its construction on that graph and record inventory
is total and unique up to coherent alpha renaming. An old Call without such
a record retains its old node and child evidence, adding no local occurrence.
Record availability is not inferred from Call shape; general source generation
of that inventory remains open. Erasing its new static evidence gives exactly
the existing generated relation and executable skeleton, including their unsatisfiable cases.

This is a proved **conservative completion package**, not a proof that its
new constructors already belong to a fixed, independently interpreted
`EffPosition_sig,orig` or original source-occurrence relation. These are three
different claims:

| Interpretation situation | Result here |
| --- | --- |
| Fresh auxiliary position/occurrence sorts over the old theory | Total construction, uniqueness, and model/solution/execution conservativity are proved. |
| Independently fixed original sorts/relations | A precisely stated compatibility test remains; the universal property does not discharge it. |
| Genuinely unspecified original Call-position/occurrence clauses | The package supplies complete proposed clauses and their construction proof. Adopting them would complete those clauses rather than prove an old unspecified judgment. |

Unlike a supplied-map theorem, this construction has no correspondence above
the line. Unlike an interface with an opaque H_eff premise, every position
constructor, occurrence constructor, recursive-reference case, and erasure
case is defined below. The unresolved legacy interpretation is not concealed
in its scope, well-formedness, or conservativity claim. In particular the
root-tag calculation proves syntactic designation and coherence, not the
independent original signature realization law added in the minimal-clause
note §7; that law remains open (§4.4). Section 10.1 additionally completes
the exact root's semantic interpretation in the genuinely unspecified
proposed fragment and proves its realization equation there. Compatibility
with an independently fixed original interpretation is a separate open claim.

The source is

```text
my apply f = { my step x = f x; step }
```

The package closes its prospective static constructor case. It establishes no
O1 owner/slot, C0 whole-carrier compatibility, C1 contribution, J0 joint
coverage, complete profile, or independent admission result. No existing DAG
gate is promoted by this producer artifact.

## 2. Frozen inputs and binding requirements

The [Function-view Authority](../design/2026-10-05-inferred-function-call-views.md)
§2 requires one shared source contract, typed paths and source scope,
comparison-independent formation, and one original `xi=(nu,K,D)`. Its §5.1
explicitly leaves the constructing judgments to subsequent work. Its §1.1
separates source annotations, public schemes, and internal evidence-rich views.
The present package addresses that internal static layer only.

The [nested-block Authority](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§2 fixes sequential binding, inert return of `step`, and capture of the same
outer `f`. The approved structural term is

```text
lambda(f,
  bind(step,
    result(lambda(x,
      call(result(name f), result(name x)))),
    result(name step)))
```

The [typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
§6 constructs source interface/result skeletons and registers ordinary
parameters. Its §9 distinguishes received carrier, body/result, and complete
invocation; complete invocation includes actual entry and the designated
consumer. The [typed-boundary account](../design/2026-10-02-typed-boundary-realization-draft.md)
§6 distinguishes `call.effect` from `result.latent.effect` and describes
structural typed paths, including recursive references. Neither document
supplies the missing original source-occurrence clause.

The [reviewed Gen-Call-0 construction](../progress/2026-10-06-source-call-generation-construction.md)
§§4.2–4.4 supplies the dependent source record `e_c`, original root, upper
checking occurrence, source address `p0`, and separate `ElimOrigin` leg to
`p_out(c)`. It also supplies a complete **Function demand variable** `F_c`.
Declaring a variable with this sort is not proving that its value/callable
constraint has a solution. The construction below consumes the declared sort
of the demand, not `WF_Dec` truth or a solved callee value.

The [minimal-clause note](../progress/2026-10-07-original-call-output-minimal-clause.md)
§2 fixes `U_c:=F_c`, the actual local dependency context `Delta_c`, and the
independence condition for H_eff. Its §7, added between the baseline and
`701213b`, fixes the two-head candidate to exactly `rho_c=demand(e_c)` and
`q_c=inv_eff(rho_c)` and retains an independent original realization law.
Sections 4.4 and 10 record this package's exact correspondence and remaining
interpretation obligation. The [architecture audit](../design/2026-10-07-successor-production-proof-architecture.md)
§8 requires a complete original-sort construction/coherence packet rather
than another conditional transport theorem. The [candidate source-introduction
contract](../design/2026-10-07-original-call-source-introduction-contract.md)
remains non-authoritative and retains the downstream obligations.

These source records and skeletons are frozen inputs, not independently
verified compiler output. The finite input graph explicitly carries its
existing emitted Gen-Call-0 record inventory, with original construction
order and Call incidences. The reviewed generator supplies the named-formal
singleton record above. It does not supply records for every generic ordinary
core Call. The package decorates whatever records were actually emitted; it
neither constructs missing generic records nor selects a new source
restriction. Any independent semantic premises of the old record generator
remain old premises. No implementation representation or acceptance by current
production HIR is claimed.

## 3. Base theory, contexts, and what counts as evidence

Let `T0` be the existing symbolic source-generation and operational theory on
this input. It contains the resolved source tree, registered endpoints and
Function demand variables, binder/dependency tree, generated predicates, and
existing executable-core translation, together with the frozen inventory of
actually emitted Gen-Call-0 records. No old predicate is redefined.

Write a context `Delta` as the actual ordered binder/dependency context of a
source demand. A declaration is available in `Delta` if its original scope is
an ancestor of the demand scope and its dependency substitution is legal.
Availability is a resolved scope fact. It says nothing about a semantic
predicate being true. Every `nu,K,D` occurrence below denotes the same original
joint tuple, under the same binders as in `T0`.

There are two different levels of typing:

1. **Symbolic declared sorts.** A generated `U:FunctionDemand` is a symbolic
   variable for a complete Function description. It has that declared sort
   before any assignment satisfies the generated relations.
2. **Independent semantic membership/formation.** A realization must satisfy
   the existing descriptor, carrier, provider, and Call laws. This is not
   inferred from the symbolic declared sort.

The new static position and occurrence judgments are dependent on the first
level. A proposed original-sort completion may identify them with the
corresponding original static judgments, as specified in §10. It cannot thereby
prove membership, receipt, observation, or admission at the second level.

The new judgments are **set-indexed dependent families**; their fibers may
be empty. Constructors are total functions on their displayed well-typed
input domains, and eliminators are total on constructed terms in their
displayed domains. No eliminator is required on an empty fiber. The model
claims use this family semantics, with no axiom that every new fiber or new
first-order sort is nonempty; they do not invoke ordinary many-sorted FOL
nonemptiness conventions for these families.

No metatheoretic constructor below allocates an effect-row coordinate, source
variable, runtime carrier, boundary, or source existential. A position is an
address derivation with a sort and provenance. Its interpretation may later
select an existing descriptor interface; it is not that interface's denotation.

## 4. Independent signature-position algebra

### 4.1 Signature frames

A *signature frame* is a finite, scoped interface graph `G` whose declarations
are already present in the symbolic interface skeleton. Nodes have declared
kinds. The kinds needed here are

```text
Val                       opaque or structurally registered value interface
Fun                       complete Function-demand/interface frame
Comp                      registered computation-data/interface frame
```

Each `Fun` node has distinguished ports

```text
arg       : whole received carrier interface
inv       : complete immediate invocation computation interface
result    : returned value interface
```

Each `Comp` node has ports `run` and `result`. A structural value node may
have its already registered immutable component edges. An opaque value node
has no decomposing edge. Registered recursive references point to existing
nodes; they do not unfold a definition. Missing unknown descendants are not
invented. No new source forms, union decomposition rule, or complete profile
inventory is selected by this graph.

For a demand variable `U:FunctionDemand` whose descendants are still unknown,
its frame has one `Fun` node for `U`, an opaque carrier interface, and an opaque
result interface. Its distinguished `inv` port is present independently of
those descendants. This is a declaration-level frame, not a replacement for
an independently well-formed complete descriptor. If more structure is later
registered, the already present invocation port is retained.

The frame constructor does not read `e_c`, `p0`, `p_out(c)`, `beta`, or source
Call-occurrence typing. It is uniformly available for any scoped
`FunctionDemand` declaration, including one not introduced at this source
Call. Thus no desired correspondence is inside H_eff's input.

The label `inv` names the existing complete `ExecuteCallable` interface from
typed-core §§3,9. It does not define that relation, equate it with a body row,
or assert a runtime invocation occurs. The frame also keeps `result` distinct;
this distinction is required even if effect endpoints later have equal values.

### 4.2 Typed finite walks

Define `Walk_G(r,t)` inductively, where `r` is a registered interface root and
`t` an endpoint node/port:

```text
Id(r)                       : Walk_G(r,r)
Step(w,edge)                : Walk_G(r,t')
    when w : Walk_G(r,t) and edge is a registered directed edge t -> t'
```

Edges retain their original component/port tags, interface indices, and scope.
The `arg`, `inv`, and `result` tags are distinct constructors; so are `run`
and computation `result`. Following a recursive reference is an ordinary
registered `Step`. A path is a finite derivation even when the graph has a
cycle. Different tagged paths are not identified by endpoint equality.

This accounts for recursive signatures without an assumption that their
unfolding terminates: path checking recurses on the finite path derivation,
not on the graph. The package never enumerates all finite walks of a cyclic
graph. Its immediate position constructor needs only the empty walk.

### 4.3 Effect-position constructors

The complete inductive definition for this package's effect positions is

```text
Inv(w,U) : EffSig_plus(G,r)
    when w : Walk_G(r,U) and U is a declared Fun node

Run(w,T) : EffSig_plus(G,r)
    when w : Walk_G(r,T) and T is a declared Comp node
```

`Inv(w,U)` selects `U.inv.effect`; `Run(w,T)` selects `T.run.effect`. Effect
positions reached under structural components or latent returned values use
the corresponding finite walk followed by one of these two constructors.
There is no constructor giving an effect position to an opaque value merely
because some assignment makes its erased shape latent. This is a declared
path inventory, not an exhaustive claim about every original profile/path.

Value/interface positions needed to state the walks are just registered
nodes reached by `Walk`. The graph's other existing position families remain
unchanged. No `Flow`, owner, contribution, grant, or observed-event constructor
is added here.

For the independent `Fun` frame of `U`, define

```text
q(U) := Inv(Id(U),U)
H_eff_plus(U;Delta) := the frame, EffSig_plus family, and q(U)'s derivation
```

This is a **definition with an explicit derivation**, not an H_eff assumption.
Its formation reads only the scoped declaration of `U` and the fixed signature
frame clauses. `q(U)` has the complete-invocation effect sort by the `Inv`
rule. It is distinct from every position whose walk begins with `result`,
including `result.latent.effect`.

### Theorem 1: signature formation and immediate-position uniqueness

For every well-scoped symbolic `U:FunctionDemand`, `H_eff_plus(U;Delta)` is
total and contains exactly one root immediate-invocation position. It is
independent of all source-occurrence addresses and of truth of generated
constraints. Path checking for any supplied finite derivation terminates.

**Proof.** The frame rule registers the distinguished `inv` port for a `Fun`
declaration without inspecting descendants. `Id(U)` is a walk by its nullary
rule and `Inv(Id(U),U)` is an effect position by `Inv`. A root immediate
position has empty walk and terminal constructor `Inv`, so inversion gives
this same term. `Run` requires a `Comp` declaration and cannot be that position;
nonempty walks are not empty walks. Scope formation follows from the declared
availability of `U` in `Delta`. No step uses source `p0` or any semantic
predicate. Finite-walk checking strictly decreases its derivation length at
`Step`. Cycles in `G` do not change that measure. QED.

Uniqueness here concerns the distinguished immediate position, not all paths
to the same graph node and not solutions for `U`. The theorem applies when the
old generated relation is empty.

### 4.4 Exact demand projection and original realization boundary

For every emitted Gen-Call-0 record `e`, let `rho_e=demand(e)` be the
projection retaining `U_e`, `B,X,xi,Delta_e`, `d_f,A_f,R_f,c` and their original
scope/dependency incidences. It contains no `p0` correspondence, original
occurrence-typing witness, comparison result, or execution. This projection
uses frozen record fields; it is not a construction of a missing record.
Define

```text
inv_eff_plus(rho_e) := q(U_e) = Inv(Id(U_e),U_e)
```

Here `q(U_e)` abbreviates its full dependent fiber at the indices retained by
`rho_e`. Its descriptor is exactly `U_e`, its root/provider is the retained
`R_f/(d_f,A_f)`, and its scope is the actual `Delta_e`. Its designation is the
root immediate complete invocation, excluding every result-latent path.
This is the exact distinguished projection required by minimal-clause §7;
there is no choice of an arbitrary other effect position at this head.
The signature construction still reads only the demand declaration and these
indices, never the desired source correspondence.

**Original semantic realization remains unproved.** The governing typed-core
§9 gives the complete `ExecuteCallable` relational image, including entry,
body, designated consumers and native-return delimiters. Typed-boundary §6
fixes supplied signature descriptors and typed correspondences. Neither gives
an independent evaluator of this symbolic position constructor in the
original signature family. Consequently the present proof establishes
syntactic formation/designation and legal whole-tuple substitution, but not

```text
interpret(theta,inv_eff(rho_e))
  = completeInvocationEffectPosition(interpret(theta,U_e))
```

for every legal original assignment in the same `(X,xi)`. Defining the left
side by the right side here would select an interpretation, not prove the
law in an independently fixed original interpretation. Theorem 1's tag
inversion, Theorem 6's syntactic naturality, and Theorem 7's proposed typed
constructor do not discharge it. The original evaluator and its root-projection
law are still required by §9 before claiming the upstream original O0 target.
Section 10.1 instead supplies an explicit new semantic root interpretation
for the genuinely unspecified-fragment proposal, with its own realization
proof. That definition is not an evaluator already supplied by Authority.

## 5. The source-occurrence algebra and its algorithm

### 5.1 Original source indices are not quotient keys

For every emitted Gen-Call-0 record `e`, retain the complete dependent index

```text
Idx(e) = (B,X,xi,Delta_e;
          d_f,A_f,R_f,u_f,u_x,c,u,U_e,beta,p0,p_out(c),ElimOrigin)
```

All these fields are already generated or resolved. In particular `u` is the
original upper-checking occurrence. The source-address field `p0` may be
shared through a stable `beta`; that does not merge different checking
occurrences or Call constructors. Equality of numeric labels or type endpoints
is never a typing rule. Dependent equality of indices is used only after the
entire corresponding source record has been established.

Define the new Call-occurrence family by this sole constructor:

```text
e : emitted GenCall0(Idx(e)) in the frozen inventory
rho_e = demand(e)
q(U_e) = inv_eff_plus(rho_e) : EffSig_plus(Frame(U_e),U_e)
--------------------------------------------------------- CallEff_plus
a(e) : CallOccurrence_plus(Idx(e); q(U_e))
```

The constructor's eliminators are defined by pattern matching:

```text
sig(a(e))             = q(U_e)
src(a(e))             = e.p0
upper(a(e))           = e.u
call(a(e))            = e.c
staticRoot(a(e))      = (e.d_f,e.R_f) = e.beta
sourceScope(a(e))     = e.Delta_e
sourceOrigin(a(e))    = e's complete resolved/generated dependent record
invocationLeg(a(e))   = e.ElimOrigin, retaining e.p_out(c)
```

Define `Incidence_plus(a(e))` to be the dependent *constructor certificate*
for these projections, with its source leg to `p0` and separate elimination
leg to `p_out(c)`. Its formation rule is elimination of `CallEff_plus`, not
an independent Boolean atom conjoined to old constraints. Forgetting this
certificate gives `{(q(U_e),e.p0)}`; the construction produces the certificate
before forgetting it.

The signature family does not mention this occurrence family. No constructor
in §4 uses `CallEff_plus`, so there is no mutual or recursive H_eff assumption.
A particular `e` constructs an occurrence at the original upper view, not at
an existing lower/provider view.

### 5.2 Source traversal

Let `Generate0(D)` name the frozen finite source-generator derivation graph
with emitted relation `Phi_D` **and its existing emitted inventory `E_D`**.
This is input data, not a total generic record-generation algorithm proved
here. Each record has its actual Call origin and complete old dependent
fields; `E_D(c)` is its finite ordered subinventory at Call `c`, possibly
empty. Well-scoped input means the existing graph and the records it actually
carries are well-scoped. It does not mean every Call has a Gen-Call-0 record.
The known named-formal singleton is included with its emitted record.
Define `Decorate(D)` by recursion on the finite construction, copying `E_D`
verbatim and adding only these outputs:

| Existing constructor | Added position/occurrence output |
| --- | --- |
| Literal | Empty Call-occurrence sequence; registered interface references retained. |
| Name | Empty local sequence; retains its exact resolved declaration/import reference, without creating a new Call or seed. |
| Result | Child sequence retained; returning a callable creates no `CallEff_plus`. |
| Lambda | Register/reuse its interface frame; traverse its finite body derivation once, retaining body scope and captures. No body execution occurs. |
| Operation declaration | Register/reuse its declared callable frame; empty local Call sequence. This is not an operation invocation. |
| Reify / explicit inert introduction | Child static sequence retained; no force or runtime occurrence is added. |
| Eliminate at a previously designated non-Call computation port | Child sequence retained; register its already designated path if present. Adds no Call occurrence. Its source typing remains an old premise. |
| Bind | Ordered concatenation of child sequences, in their original binder scopes; retains the old shared result/rebind witnesses and suffix unchanged. |
| Call | Concatenate child evidence and retain the unchanged old Call. For every emitted record `e` in `E_D(c)`, construct `H_eff_plus(U_e;Delta_e)` by §4 and append `a(e)` in the existing record order. If `E_D(c)` is empty, append no local occurrence. |
| Registered recursive reference | Retain the reference; no recursive descent through its target. The target definition is traversed once as a finite registered definition. |

The exact nested source needs Literal/Name/Result/Lambda/Bind/Call only. The
other rows define evidence traversal on finite old graphs in the already
described ordinary core envelope with the supplied emitted inventory. They
do not assert that ordinary core shapes emit Gen-Call-0 records, extend
raw-source acceptance, or remove old typing/annotation or record-generation
semantic premises. All-source record construction/inference remains open. Handlers or other constructors not in that envelope
may carry an unchanged independent subderivation, but no general elaboration
case for them is claimed here.

Frame registration is memoized by declared interface-node identity and scope;
consistent reuse references the same frame. The exact immediate-position
construction is constant-size per emitted Gen-Call-0 record and does not
inspect or enumerate all latent paths. Static sequences may equivalently be stored as a shared finite
graph; concatenation is a mathematical description, not a selected data layout.

### Theorem 2: total source construction and coherence

For every finite well-scoped input `Generate0(D)` in this envelope carrying
its frozen emitted inventory, `Decorate` is total and yields one
`CallEff_plus` derivation for every emitted Gen-Call-0 record. It adds no local
Call-effect derivation at an old Call with empty `E_D(c)`, inert return, Name,
Lambda execution boundary, or non-Call computation elimination. Its output is
unique up to one coherent alpha renaming of all old and new indices. This
is decoration totality on the given input, not all-source generation totality.

**Proof.** Order source definitions by the finite registered construction and
within each definition use its finite derivation-tree size. Recursive
references are terminal, so the measure decreases at every visited child.
The non-Call rows copy old operands and uniquely concatenate the inductively
constructed outputs. Lambda preserves scope and visits the finite body once;
return/reify retain the child's static graph without adding an execution. In
the Call row, first use the fixed finite list `E_D(c)`. For each emitted
record `e` on that list, its old FunctionDemand declaration is in its actual
`Delta_e`. Theorem 1 yields `q(U_e)` uniquely, and the sole `CallEff_plus`
constructor yields `a(e)`. An empty list leaves the old Call and child outputs
unchanged. No record is inferred or synthesized from Call shape. There is no
new premise search, comparison, truth test, or original occurrence typing;
old generator premises remain part of the input. Inverting that row of any
decoration obeying these equations gives the same child outputs and the same
ordered `a(e)` terms for exactly the supplied inventory. Non-Call rows cannot
add `a(e)` because they have no such constructor case. A coherent freshening of old labels determines freshening of all their
dependent new terms; no additional independent fresh labels are required.
Induction proves totality and uniqueness. QED.

This construction does not test consistency to choose its inventory. Every
emitted Gen-Call-0 record receives the same constructor evidence even when
`Phi_D` is inconsistent. A Call with no such emitted record is retained as
an old Call; absence of a new local occurrence says nothing about its
consistency, acceptance, or original semantics.

## 6. Conservativity: precise theorem and proof

### 6.1 Erasure and reconstruction

Define `Forget` to delete the §4–§5 auxiliary frame/position/occurrence
derivations, retaining the entire original source graph, `e` records,
predicates `Phi_D`, binder tree, `xi`, and executable skeleton. On each
constructor it is the identity on old operands.

Then

```text
Forget(Decorate(D)) = Generate0(D)
Decorate(Forget(E)) = E
```

for canonical decorations `E` satisfying the algorithm's computation
equations. The second statement is not true of arbitrary enlarged occurrence
inventories with additional independently licensed paths or records; it is
claimed only for this new canonical evidence, not for the original semantic
witness domain.

**Proof.** Every non-Call row adds no old data and copies its old node. The
Call row adds `q(U_e)` and `a(e)` for every emitted record, adds nothing local
when there is none, and does not modify the old Call, inventory or predicates.
Erasing this addition recovers that row. Conversely, Theorems 1–2 uniquely
reconstruct exactly the erased auxiliary derivations. Induction over the
constructor table gives both equations. QED.

### Theorem 3: exact old solution-set preservation

At every original scope and for every assignment/strategy `s` of the old
joint coordinates, including old evidence and locally scoped witnesses,

```text
s satisfies Phi_D
  iff
s with its canonical static decoration satisfies the extended presentation.
```

The extended presentation contains the same `Phi_D`; its new sort equations
are interpreted by §§4–§5. Projection to old strategies and canonical
extension are inverse. This holds also for an empty old solution set.

**Proof.** Extension changes no old conjunct, binder, alternative, or
coordinate. The new derivations are total functions of the symbolic source
record and frame declarations by Theorems 1–2; they add no independently
chosen witness and no condition on `s`. Thus every old satisfying strategy
extends. Forgetting an extended satisfying strategy preserves every old
conjunct with its original witness and scope. Uniqueness of the decoration
makes the two operations inverse. Nothing is prenexed or solved during this
argument. QED.

The theorem is exact for the existing `Phi_D`. It is **not** an assertion that
`Phi_D` already has all original source semantic clauses, or that adding
future owner/admission clauses cannot restrict its solutions.

### Theorem 4: conservative fresh-sort extension of T0

Under the set-indexed dependent-family semantics of §3, every model of `T0`
has an expansion interpreting these new static families and computation
equations, with identical old sorts, old functions, old predicates, and old
truth values. No assumption that all new first-order sorts are nonempty is
made. Consequently the fresh-sort extension has no new
consequence expressed wholly in the old language.

**Proof.** Fix an arbitrary old model `M`. Interpret a new graph/frame object
as the finite symbolic declaration graph paired with its original scope
indices. Interpret positions as the finite derivation trees of §4; interpret
source Call-occurrences as the finite constructor terms of §5 indexed by
the frozen emitted inventory of already present symbolic records. These are
separate set-indexed families, so old carrier members are neither added nor
removed. Their eliminators are the defined total pattern matches on actual
constructed terms. Fibers with no derivation are empty, including occurrence
fibers for recordless Calls; every emitted Gen-Call-0 record has its
constructed term. No operation requires an element of an empty fiber. No existence of an old satisfying
assignment is needed to form these symbolic terms. All equations hold by
construction, while every old equation/predicate is interpreted exactly as
in `M`. If an old-language sentence were a new consequence, a countermodel
in `T0` would expand to a countermodel of the extension, contradiction. QED.

This proof concerns fresh sorts. It cannot be silently reused when
`CallOccurrence_orig` is an already fixed old sort or relation. In that case
a required fiber could lack a suitable element, a fixed eliminator could have
a different value, or an old exhaustive-domain axiom could forbid adding an
element. Section 9 states that boundary exactly.

### Theorem 5: preservation of old observable execution

Erasure gives the identical executable-core graph, initial old configuration,
transition operands, and existing metadata. Therefore execution observations
and accepted old generated strategies coincide on the old operational theory,
including prefixes, returned latent providers, and future uses covered by
that theory.

**Proof.** Static additions occur only in the evidence derivation and no new
instruction or runtime field is installed. Every old initial configuration is
literally unchanged. At each old transition the operand/state tuple is the
same, hence its old target configurations and observations are the same.
Induction on finite transitions proves equality of every finite execution
prefix. Stored old code/providers and raw resumptions are the same operands,
so the induction restarts unchanged at each old future-use configuration.
No step invokes a new static eliminator as a dynamic permission. QED.

This is a reduct identity theorem, not an independently proved source/runtime
adequacy theorem. If an eventual implementation makes original occurrence
facts govern new slot/profile/admission behavior, that larger semantic use
requires its own independent proof. The old operational behavior cannot be
claimed conservative merely because this auxiliary proof was conservative.

## 7. Scope, substitution, and exact-source calculation

A legal uniform map `theta` acts on the entire original binder graph,
declarations, endpoints, `xi`, dependency incidences, source tags, and `e`
records at once. It fixes captured/rigid imports where required. It induces

```text
theta(Id(U))          = Id(theta U)
theta(Step(w,edge))   = Step(theta w,theta edge)
theta(Inv(w,U))       = Inv(theta w,theta U)
theta(Run(w,T))       = Run(theta w,theta T)
theta(a(e))           = a(theta e).
```

### Theorem 6: naturality and preservation without scope hoisting

For every such legal map,

```text
theta(q(U))       = q(theta U)
theta(Decorate(D)) = Decorate(theta D)
Forget(theta E)   = theta(Forget E).
```

Every dependent projection of `a(e)` commutes with that same map.

**Proof.** The first equality unfolds `q` to `Inv(Id(U),U)`. Walk/effect
formation commutes by induction on finite derivations because `theta`
preserves registered tags and their declared sorts. The source table commutes
constructor by constructor: Name uses the mapped environment; Lambda/Bind
use the mapped original scopes; Call uses the mapped emitted inventory,
each mapped whole record and the first equality. The empty-inventory case
retains mapped child evidence and the old Call; recursive references remain mapped registered references.
Projection commutation follows by unfolding the single `a(e)` pattern match,
not by reconstructing an occurrence from endpoint equality. Erasure removes
the same auxiliary fields on each side. QED.

A noninjective endpoint substitution can preserve declared tags and still
identify old type endpoints. It does not identify tagged occurrence paths or
source occurrences. An alpha renaming of eligible source identities is
injective on those identities. Reflection by an inverse is asserted only for
such renamings on their image. Arbitrary graft/hiding soundness and completed
source generalization are not derived merely from these equations.

For the exact source:

1. The outer parameter registration gives `d_f,A_f,R_f` at `sigma_apply`.
2. The local Lambda creates `d_x,A_x` at `sigma_step`. The captured Name `u_f`
   imports the same outer `d_f,A_f,R_f`; it does not freshen that provider.
3. The inner Call generates `e_c` and its complete Function demand
   `U_c=F_c` in the actual `Delta_c`, which contains the imports and any local
   dependencies, including `A_x` where required.
4. The signature frame uses that locally scoped demand declaration. It gives
   `rho_c=demand(e_c)` and exactly
   `q_c=inv_eff_plus(rho_c)=Inv(Id(U_c),U_c)`, retaining the original
   root/provider indices without moving `U_c` to `sigma_apply`.
5. `a(e_c)` has the original upper `u`, source `p0`, stable `beta`, and separate
   `p_out(c)` elimination leg by its defined projections.
6. The Bind and final `result(name step)` retain this static occurrence and
   return the closure inertly; they create no second Call occurrence.

This is a full calculation of the proposed O0 constructor case. The source
binder `f` is shared; the locally dependent demand is not hoisted with it.
No `A_x`, provider, `K`, `D`, or local witness is selected afresh per port.
This calculation uses the actual singleton emitted record and supplies no
missing generic Call record or original semantic realization law (§4.4).

## 8. Universal property, and exactly what it does not prove

The package is an initial dependent constructor algebra for its new static
fragment. A target algebra consists of independently given target frame,
walk, effect-position, and Call-occurrence sorts with interpretations of the
constructors and the same computation equations. A target interpretation must
preserve original indices and declared sorts, not just endpoint labels.

There is exactly one constructor-preserving interpretation into any such
target algebra, on the package-generated fragment.

**Proof.** Interpret `Id`, then each `Step`, by recursion on finite walks;
interpret `Inv` and `Run` by their target operations. Interpret `a(e)` by the
target Call constructor using the already interpreted `q(U_e)`. This defines
a total map on every finite term. Any constructor-preserving map must take
the same value on nullary terms and, inductively, on composite terms. The
projection equations hold by the target's stated constructor equations. QED.

The theorem supplies no target algebra. In particular it does not construct
an operation returning an element of a preexisting original occurrence fiber.
It is also not a representation-isomorphism theorem onto the complete target
sort: a target may contain other independent positions/occurrences, distinct
licensed alternatives, or extra equalities. There is no claim that original
paths, slots, contributions, licenses, or `I_orig(X)` equal this initial image.

## 9. Exact legacy-original compatibility test

Suppose an independent original interpretation `L` is already fixed. Let its
signature and occurrence families, eliminators, and interpretation of complete
invocation be fixed before inspecting this package. The necessary and
sufficient *local extension condition* is the following restricted model of
the constructor signature:

- **Signature case.** For every scoped declared Function frame used by the
  package, `L` has the mandatory immediate complete-invocation effect position.
  Its formation depends on that frame, not the source `p0` map. It respects the
  registered structural/recursive path clauses on the paths actually used.
  Its semantic port is the complete existing invocation interface, retaining
  entry/consumer/native-return distinctions; no body-only interpretation is
  substituted. In particular the independent evaluator must establish the
  exact realization equation of §4.4 for `rho_e=demand(e)` and
  `q_e=inv_eff(rho_e)` at every emitted record; designation alone is
  insufficient.
- **Source case.** For every emitted dependent Gen-Call-0 record, `L`'s Call
  introduction interprets `a(e)` in its **original typed occurrence family**,
  with the projections, upper origin, scope, and separate elimination leg of
  §5. The premise is that original introduction rule, not an untyped endpoint
  pair, numeric identity, or relation inferred from a successful `Q`.

Necessity follows by applying a putative constructor-preserving interpretation
to `q(U)` and `a(e)` and reading their eliminators. Sufficiency follows by the
finite-recursion proof in §8 restricted to these supplied original rules.
No condition on unused original paths or owner/contribution/license domains
is needed for this local constructor interpretation. No surjectivity is
needed or asserted.

This is the smallest interface **relative to this displayed constructor
signature**, in the exact sense that it asks for interpretations of its
operations and laws only. It is not a claim of a representation-independent
minimum axiom basis. The source case contains the legacy O0 introduction
content and remains unresolved if that rule is absent. Calling it a model,
coherence condition, or naturality law does not solve it. Neither the universal
property nor Theorems 3–5 prove it.

If uniqueness in an existing original sort is desired, one additionally needs
uniqueness of these original constructor results up to the original proof
quotient. The package's syntactic uniqueness alone cannot identify distinct
original witnesses. This additional uniqueness is not needed to exhibit one
O0 occurrence, and is not imposed on the entire original witness domain.

## 10. Proposed completion clauses and adoption boundary

If these original static clauses are genuinely unspecified, the following
is a complete candidate completion on the selected fragment. The `orig` names
in this section are **proposed**, not facts about the current theory.

### H_eff completion

Interpret a scoped complete Function-demand/interface declaration by its
independent signature frame as in §4.1. Define the original static
signature-position judgments on this frame by finite registered walks,
`Inv`, and `Run` as in §§4.2–4.3. Define the immediate call-effect projection by

```text
rho : scoped complete Function-demand declaration with its original indices
U := descriptor(rho)
------------------------------------------------------------- Sig-CallEff
inv_eff_orig(rho) := Inv(Id(U),U)
                    : EffPosition_sig,orig(U;B,X,xi,Delta)
outEff_orig(U) := inv_eff_orig(rho)  [at this same dependent fiber].
```

Here `Sig-CallEff` implements the proposed `OSig-Demand` head of
minimal-clause §7 in the term-algebra completion. Its input retains that
head's root/provider and actual scope/dependencies. Section 10.1 completes
its proposed semantic root evaluation. It does not provide an evaluator in
an independently fixed original signature family or prove that family's
realization law (§4.4).

This judgment is about the static signature of a declared complete Function
interface, not semantic descriptor membership of any unconstrained assigned
value. The complete-invocation label refers to the existing full Call
interface; its observation, admission, provider, and execution relations are
left unchanged. Other independently defined original position clauses are
retained; this fragment supplies neither exhaustive profile membership nor
an all-path inversion theorem for those other clauses.

### 10.1 Proposed semantic interpretation of the exact root

For the **genuinely unspecified** signature fragment, define its semantic
root family explicitly as follows. Work over the unchanged, independently
interpreted old domain of complete Function descriptions and its existing
complete invocation interface interpretation from typed-core §§3,9. For an
object `d` of that domain at the same original `(X,xi,Delta)`, write
`J_call(d;xi)` for that existing full relational interface: actual entry,
body, designated consumers, native-return delimiters and the complete
executing view with their unchanged admitted dependencies. This uses the old
invocation interpretation as semantic data; it neither constructs the old
descriptor/admission domain nor asserts a satisfying source assignment or
an execution of `d`. The payload is the whole parameterized old relational
interface over its unchanged admitted joint inputs, not one selected trace or
source-body effect. The construction is uniform over any independently fixed
old interpretation of those descriptors and complete invocation interfaces;
it makes no new common-model existence claim. It is not an old signature-position judgment `H_eff`.

Independently of source positions, occurrences, comparison and `p0`, define
`SemFrame_call(d)` to have a Function root named `d` and a distinguished
`inv` port carrying exactly `J_call(d;xi)`. Retain the same original root,
provider, scope and dependency indices as the demand declaration. Define
its new root-position fiber to be the singleton

```text
RootEff_new(d) = { Inv_sem(Id_sem(d),d) }
interface(Inv_sem(Id_sem(d),d)) := J_call(d;xi)
completeInvocationEffectPosition_new(d) := Inv_sem(Id_sem(d),d).
```

These are definitions of fresh semantic position objects over existing
interface data. The `inv` tag remains distinct from body, native return and
result-latent tags even if some interface endpoints happen to have equal
values. No unknown descendant or existing original position is identified
with this root. The root is formed for every object in the old interpreted
complete-description domain; the existence of an assignment into that
domain, or truth of `WF_Dec`, is not obtained from its symbolic formation.

For any legal original sorted assignment `theta` at the unchanged joint
indices with `d=interpret_old(theta,U)`, define the **new** root evaluation
by the following two clauses:

```text
interpret_new(theta,Id(U)) := Id_sem(d)
interpret_new(theta,Inv(Id(U),U)) := Inv_sem(Id_sem(d),d).
```

They specify the exact root case, not an evaluator for every original
signature path or an adoption of new runtime semantics. The dependency
indices are interpreted together by the same `theta`; the captured
root/provider and locally dependent `U` are never separated or hoisted.
For `rho=demand(e)` the root equation in this proposed interpretation is

```text
interpret_new(theta,inv_eff_orig(rho))
  = completeInvocationEffectPosition_new(interpret_old(theta,U)).
```

**Root realization proof.** By `Sig-CallEff`, `inv_eff_orig(rho)` is exactly
`Inv(Id(U),U)` in the fiber indexed by `rho`. Let
`d=interpret_old(theta,U)`. The two displayed evaluation clauses take it to
`Inv_sem(Id_sem(d),d)`. By the independently source-free definition of
`SemFrame_call(d)` this is its complete-invocation effect position, whose
interface is exactly the old `J_call(d;xi)`. Unfolding
`completeInvocationEffectPosition_new(d)` gives the right side. Every
index on both sides is the interpretation of the same demand tuple. No
source-address correspondence, successful comparison, receipt, execution
or original `H_eff` was used. This proves the equation for every legal sorted
assignment in its stated domain, including assignments that fail the
additional generated source constraints. If there are no such assignments,
it makes no existence claim. QED.

Thus the proposal includes a fully interpreted **local root** completion,
with a semantic projection proof in its newly defined position family. It
still does not prove the upstream equation into an independently fixed
original position family: a bridge must show that the original evaluator
and original complete-invocation position agree with this new interpretation.
That bridge is §9's compatibility condition and remains open. No original
slot, profile, contribution, owner, license, `I_orig(X)`, admission or
Option 2 domain is redefined. The full old invocation interface is retained
as data, so this root definition neither restricts source acceptance nor
selects a new complete-call denotation.

### OC-CallEff completion

Interpret the source elimination case uniformly by

```text
e : emitted Gen-Call-0 record at original dependent indices
rho_e = demand(e)
q_e = inv_eff_orig(rho_e) = outEff_orig(U_e)
-------------------------------------------------------------- OC-CallEff
CallEff_orig(e) : original typed Call-effect occurrence
                 at (U_e,q_e; beta,u,p0,c;Delta_e)
```

The eight eliminators are exactly the equations of §5.1, including
`invocationLeg=ElimOrigin` to `p_out(c)`. The constructor is indexed by the
whole original dependent record. It creates no runtime `Flow` or receipt,
owner, grant, license, contributor, original witness `a in I_orig(X)`, row
equality, or new satisfying source strategy. Inherited provider protection
and the upper seed remain unchanged inputs for their later independent rules.

These clauses contain no `TypedOutputCorrespondence` premise. Their result
includes the dependent incidence proof, and its erasure is the one-port map
`kappa`. The proof of their total construction and coherence is Theorems 1–2
and 6, now using these specified constructors. Their conservation of the
previous symbolic relation and executable reduct is Theorems 3–5.

Adopting a completion at previously unspecified static sorts is different
from extending fixed old predicates. If the latter applies, §9 is mandatory
and the clauses cannot be adopted as a proof shortcut. If an old consumer
uses these sorts to determine admission/profile/solution membership, showing
that its interpretation remains unchanged is a separate comparison theorem;
the fresh-sort conservativity proof is insufficient for that consumer.

No manual proof annotations or source restrictions occur. Calls without an
emitted Gen-Call-0 record retain their old derivation and child evidence;
this clause does not generate a missing record or alter their source
acceptance. Users receive no new language mode. The completion is a
formalization of a source-constructor responsibility, not a permission to weaken any current supported behavior.

### Theorem 7: O0 in the explicitly completed static fragment

Let `T_call` be the proposed fragment with the two formation cases just
specified, keeping every separate original semantic judgment and its domain
outside this definition. For every emitted Gen-Call-0 record `e` in the
frozen inventory of a finite well-scoped §5.2 input graph,
one can construct

```text
kappa_e : original typed correspondence
          (U_e,outEff_orig(U_e)) -> e.p0
          at the original (B,X,xi,Delta_e; beta,u,c),
```

with the separate retained `ElimOrigin` leg to `p_out(c)`. The construction is
total on these generated records, including records in inconsistent generated
relations. It is uniform in the source, independent of comparison success,
and coherent under the legal whole-tuple maps of §7. Its exact signature root
also has the proposed semantic realization equation of §10.1 under every legal sorted assignment in that interpretation's domain.
No source/signature correspondence or independently granted H_eff is a premise
of this theorem. The old emitted record and its declaration are explicit frozen source inputs;
this theorem does not prove that all ordinary source Calls emit such a record.

**Proof.** Invert the actual Gen-Call-0 construction of `e`. Its emitted
Function demand `U_e` is declared in `Delta_e` with the original dependent
indices; no successful interpretation is concluded from that declaration.
Project `rho_e=demand(e)` and apply `Sig-CallEff` to construct exactly
`q_e=inv_eff_orig(rho_e)=Inv(Id(U_e),U_e)` at that same context. Apply the
specified `OC-CallEff` formation case to `e` and this exact projection; an
arbitrary latent effect position cannot satisfy this head. Its dependent
source/signature eliminators give the typed incidence certificate `kappa_e`, and its invocation-leg eliminator
returns the original `ElimOrigin`. These are the computation rules of the
declared original constructor, not an inference from equal endpoint labels.
The two rule applications are total without testing `Phi_D` or Q. Theorem 2
applies them at every emitted record, including the single inner Call of §7;
Theorem 6 proves coherence by acting once on their entire dependent indices.
Theorems 3–5 give preservation of the old symbolic/executable reduct for the
specified conservative representation. For the proposed semantic root, §10.1
evaluates this exact `q_e` at the assigned complete description and proves its
full-invocation root equation by the supplied evaluation definitions, without
using `kappa_e` or `p0`. This constructs the stated conclusion.
QED.

Theorem 7 is a complete theorem **of this explicitly proposed formalization**.
It is not a derivation of the previously unspecified original judgment from
unchanged prior rules, and it does not remove §9's requirement if an original
interpretation is fixed independently. It proves neither the completeness of
all original position families nor any O1/C0/C1/J0 or production property.
Its rule-adoption boundary remains visible rather than being moved above the
line as an assumed typed-certificate theorem. The upstream §7 realization
law in an independently fixed original family remains open: the O0 conclusion and semantic root equation here are fully
constructed in the proposed `T_call` interpretation, while compatibility of
that root evaluation with the independent original semantic family still
requires §9. All-source record inference also remains open; neither gap is closed by this prospective constructor proof.

## 11. Does current Authority force this interpretation?

Authority fixes substantial parts of the clause: the source occurrence is the
actual resolved Call, the contract/root is shared, formation is independent
of `Q`, scope and joint dependencies are retained, and the approved ordinary
source meaning returns `step` inertly. The typed core's already selected
complete invocation semantics fixes which computation the immediate port
names. `call.effect` cannot be replaced by body effect, native return, or a
latent result descendant while retaining those specifications.

Authority does **not** already supply a complete inductive original
signature-position/occurrence judgment. Function views §2 says the exact
constructing judgments remain open; §5.1 expressly requires them as the next
gate. The nested-block addendum §3 selects no new call-view registration rule.
The typed core's source/result and direction constructions retain independent
typed-path/descriptor inputs. Thus these texts do not prove that every original
interpretation is isomorphic to the present term algebra. They do not specify
all additional original paths, derivation quotients, or independently licensed
alternatives, and the present package cannot determine those by initiality.

The minimal-clause §7 continuation makes the exact demand/root head fixed
for this proof attack and expressly retains the original realization law.
The inspected sources provide complete invocation meaning and supplied typed
paths, but no independent original signature evaluation proving that law.
The syntactic term algebra cannot fill that semantic gap by relabeling its
root projection. Section 10.1 therefore explicitly defines a new semantic
root interpretation for the unspecified-fragment proposal and proves its
local equation; that proposal does not establish the missing independent
original bridge.

The constructor choice therefore remains a **formal specification/adoption
step** if it completes an unspecified clause. No pair of complete,
Authority-consistent interpretations with different approved observable or
principal behavior has been produced. A missing formal definition alone does
not demonstrate a genuine new observable language choice or justify asking
the user to choose singleton slots, arbitrary latent protection, or a new
admission policy. Review and the ordinary authority gate remain necessary for
adoption. Publishing the reviewed construction needs no additional approval.
Selecting these definitions as the governing original judgments does require
an explicit scoped decision; it would not itself prove compatibility with an
independently fixed older interpretation or conservation of its consumers.
The [integration record](../progress/2026-10-07-call-construction-proof-review.md)
separates that definition-selection question from an unproved claim that a
different observable language behavior must be chosen.

## 12. Verification, freeze, and handoff

Producer proof method: explicit finite constructor definitions, constructor inversion,
induction on finite walks/source derivations, model expansion, and identity
of old relations/transition operands. No Python probe, Cargo run, Oracle run,
performance sample, production mutation, Git mutation, or subagent was used by
the proof producers.
The permitted one bounded probe budget remains entirely unused. A finite
enumerator would only test these defined constructor equations, so it would
not discriminate the unresolved original interpretation.

Affected-dependency repair: inspected the exact
`git diff b540c04..701213b -- notes/progress/2026-10-07-original-call-output-minimal-clause.md tasks/current.md`.
The added §7 fixes the exact demand/root head already used syntactically here;
its independent original semantic realization obligation remains explicit in
§§4.4,9–11. Section 10.1 adds the exact root's proposed semantic interpretation
and an evaluation-by-definition proof, distinct from that original bridge.
The §5.2 inventory repair, empty-fiber domain conventions, exact root
interpretation and eight-eliminator count received a fresh independent
compiler-referee delta review with no findings. The primary accepted the
initial compiler-referee/spec-auditor reports and that delta report; the one
accepted major finding about generic Call coverage is closed within the
corrected supplied-inventory scope. The review certifies these stated
theorems, not original O0 closure. See the linked review record for frozen
hashes and the exact review boundary.

Dependency hashes below identify inspected source bytes. The primary
revalidated all nine against the frozen review snapshot and the later
`fd190fa6bff0a10908c0e6888182260da98145ef` integration baseline, whose delta
adds a solver test only. Other agents' unfinished artifacts are not premises.
Shared task, theory-map and design-index navigation is synchronized by the
primary. The canonical DAG is unchanged because no original gate is closed.

```text
114b136deb274695fbfd991494c1f8e864ecff1ce5f43c4f6dee06dd09e3485b  notes/design/2026-10-07-successor-production-proof-architecture.md
0b883c273bf5ce7e413cf18463cc12b6383e1ebd3a4a917c3af8b77b683136a4  notes/progress/2026-10-07-original-call-output-minimal-clause.md
7c725904d12996c05bf6fbdceb81ee1e5e300af542fc0ecd9fc556d0fad02fa6  notes/design/2026-10-07-original-call-source-introduction-contract.md
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1  notes/design/2026-10-05-inferred-function-call-views.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e  notes/design/2026-10-02-typed-computation-core-elaboration.md
6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073  notes/progress/2026-10-06-source-call-generation-construction.md
750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0  notes/design/2026-10-06-nested-block-function-source-realization-addendum.md
1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb  notes/design/2026-10-02-typed-boundary-realization-draft.md
fc459dfac03693f426dea575585a0d20d7a075f8c7ac27be9fd2e67a150466c1  notes/progress/2026-10-06-directional-joint-source-judgment.md
```

The minimal-clause baseline hash was
`7fd661c3046e90bf5a9391e1afb9c1e3cd9f7fe3ee5bf7832e22a4c4f86bc85c`;
the displayed replacement is the inspected `701213b` version including §7.
Other displayed dependency hashes retain their original source provenance;
no claim is made that the minimal-clause bytes were unchanged.

Reviewed integration scope:

- Mathematical output: this file; primary review and navigation records are separate.
- Baseline: `b540c04df0e0cce554f2d02f3c7fbb22a9fc1102`.
- Claim: completed conservative constructor package; existing-original bridge
  and adoption unresolved; no original O0 or downstream closure claim.
- Proposed message: `research: construct scoped Call-position and occurrence completion`.
- Gate boundary: retain ORIGINAL_ASSOC OPEN-SEMANTIC; record this package
  as a completed conservative construction with an explicit definition-selection
  candidate and original-sort compatibility condition, without promoting
  owner/contribution/profile/admission gates.

# Typed-boundary realization: scope choices and finite adapters

Date: 2026-10-02
Status: Draft; source scope choices pending; no implementation authority
Scope: completion of boundary relevance and structural Function/Thunk adapters
Approved-by: none
Drafted-by: primary with scoped-boundary and adapter-construction architect inputs
Reviewed-by: compiler_referee and spec_auditor package reviews, 2026-10-02; no blocking/major findings; minor Boolean-equality wording clarified by primary
Supersedes: none

## 1. Remaining definitions, not another effect mechanism

`2026-10-02-source-realization-and-symbolic-basis.md` isolates two source
definitions needed to instantiate the finite presentation: effective callback
relevance and effective general adaptation. This package advances both without
changing selected behavior. Boundary scope still needs the two source choices
in §2; a finite structural adapter construction is proved in §§3–5.

The unchanged requirements are: an explicit concrete callback contract governs
both direct requests and caller-owned requests exposed by `Force` in its
complete `CallView`; hidden origin cannot veto that contract; receiver/handler
expiry ends authority; escaped values retain latent behavior and symbolic
`K,D`; raw shallow resumption uses current state outside the selected handler.
Oracle routing does not define any rule here.

The adapter result is a structural operational subtheorem, not a new supported
source envelope. It does not supply source typing, all conversions, arbitrary
unknown-shape instantiation, or the missing component interaction theorem.

## 2. Why the selected scope rules do not uniquely define relevance

A declared callback boundary can be represented by
`b=(receiver activation, callback slot, typed contract)` and a typed view of
the callback value. Entering that view covers argument adaptation, the call,
result adaptation and demanded forces. Nested computation preserves enclosing
view instances; requests record the applicable instances independently of
origin. Candidate testing filters them using the *current* active receiver
and handler occurrences. This realizes the selected cases for explicit
callback uses, but does not determine every value-transport case.

### Handler territory through a captured environment

Consider this semantic scenario, not an executed Oracle fixture:

```text
outer handler h0 handles E
receiver r receives caller callback f
r defines helper g capturing f in its lexical environment
g installs its own handler hg for E, then calls f
hg has no concrete capture contract for f
```

The source description distinguishes `r` and `g` activations. An enclosing
grant to a handler owned by `r` does not by itself grant authority to `hg`.
That does not yet determine whether `hg` has *ordinary* eligibility:

| Interpretation | Treatment of `hg` |
|---|---|
| Only declared argument boundaries determine territory | No `g` callback argument boundary is crossed; `hg` may handle ordinarily |
| Callback value transport preserves protection across environment/store paths while the receiver is active | Capturing `f` does not remove its receiving-side protection; `hg` needs an applicable local concrete contract and otherwise forwards |

The second is the proposed direction for avoiding capture merely by changing
an argument into a lexical capture. It requires one general typed-value
transport/handler-territory rule. Wrapping every callable environment value
would be unjustified: ordinary local closures and direct operation values
must not become protected callback inputs merely because they are callable.
Nor may an enclosing grant be copied into a new helper grant by family equality.

### Latent values after the complete CallView returns

Suppose a callback returns an unexecuted thunk or closure, and the receiver
executes that returned value after the callback's complete `CallView` has
returned but before the receiver activation ends. This differs from the
already-selected case of a force *inside* result adaptation.

| Interpretation | Later latent execution while receiver remains active |
|---|---|
| Execution-view scope | The completed callback view adds no boundary at this later entry; current ordinary boundaries determine eligibility |
| Typed-value scope | The returned value retains the typed boundary reference; later entry consults that contract while its receiver is still active |

Both retain latent effects and `K,D`, and both remove the old receiver's
authority/mask after its activation ends. They can differ before expiry; for
example, an absent/wildcard contract does not authorize a receiver handler
under the second interpretation, whereas the first can permit ordinary
handling outside the former view. The exact effect depth/typed result path
to which a contract applies must be part of the common value-boundary rule;
this comparison does not authorize copying one effect annotation onto every
nested latent result.

These alternatives agree with the selected direct/Force-in-view, nested
preservation, and post-expiry rules but leave different remaining cases.
The tables are source-choice discriminators, not complete alternative calculi
with established soundness/principality.
An async user question presents both decisions. No reply or elapsed time is
approval. The proposed direction is transport through both paths with
activation-scoped lifetime; adoption and its complete rule/proof are pending.
This is a semantic blocker for that definition, not a class-3 finiteness
counterexample. Independent structural adapter work below does not depend on
choosing either interpretation.

## 3. A finite structural adapter kernel

### Fixed-shape graph and explicit equivalence candidate

Let `T` be a finite rooted graph of constructor nodes:

```text
Atom(a)                 a ∈ {Unit, Bool, Int}
Fun(argument, result)
Thunk(effectLabel, result)
```

Every reference targets another node. Recursive edges refer directly to
constructor nodes; there are no constructor-free alias cycles. The three
atoms are rigid tags, not variables whose assignment can change them into a
function or thunk. The finite effect labels retain their symbolic family
endpoints and constraints; ground effect arguments need not be finite.

For this operational kernel define `≈g` as graph bisimilarity respecting
constructor/atom tags and exact symbolic effect-label identity. Start with
all pairs and repeatedly delete pairs whose tags/labels disagree or whose
required child pair is absent. At most `|T|²` pairs are deleted, so this is
effective even for recursive graphs. The final relation is a bisimulation;
every bisimulation is retained by induction over deletions, hence it is the
greatest one. No type solver or concrete materialization is hidden here.

This is an explicit *candidate* for the structural subtheorem, not a selection
of the successor's general boundary equivalence `≈`. Distinct symbolic effect
labels can denote equal effects under some `ν`; `≈g` need not identify them.
The theorem interprets the displayed source equations using `≈g`. A bridge
to a different selected equivalence requires its own preservation argument.

### Pair graph construction

For an ordered source/target pair `(s,t)`, insert a placeholder in a memo table
*before* following children. Fill it according to this priority table:

| Condition | Descriptor | Child pairs |
|---|---|---|
| `s ≈g t` | `Id` | none |
| `s=Thunk(E,a)`, `t` not Thunk | `ForceThen(d)` | `(a,t)` |
| `s` not Thunk, `t=Thunk(F,b)` | `DelayThen(d)` | `(s,b)` |
| `s=Thunk(E,a)`, `t=Thunk(F,b)` | `ThunkMap(d)` | `(a,b)` |
| `s=Fun(a,b)`, `t=Fun(c,d)` | `FunctionMap(darg,dres)` | `(c,a)`, `(b,d)` |
| otherwise | uncovered pair | none |

After the identity case the three thunk cases are disjoint. Each pair is
processed once; back edges reuse its placeholder. For any finite set of roots,
at most `|T|²` descriptors with at most two child references each are needed.
No recursive source type or adapter is expanded into a tree.

An uncovered reachable pair means this kernel supplies no operational
realization for that root. It is not a successor `ill-typed` diagnostic,
does not establish absence of another source conversion, and does not publish
a partially realized root. The graph is a research construction, not a
compiler API or resource-limit decision.

## 4. Operational interpretation and proof

Use the existing state-threaded `Return`, bind, `Force`, source `Delay` and
source `Call` operations. `RunD(d,v,C)` denotes descriptor execution with
current source configuration `C`:

```text
Id(v)                = Return(v)
ForceThen(d)(v)       = Force(v) >>= (λx. RunD(d,x))
DelayThen(d)(v)       = Return(Delay(RunD(d,v)))
ThunkMap(d)(v)        = Return(Delay(Force(v) >>= (λx. RunD(d,x))))
FunctionMap(da,dr)(f) = Return(FunctionView(f,da,dr))

Apply(FunctionView(f,da,dr),x) =
  RunD(da,x) >>= (λy. Call(f,y) >>= (λz. RunD(dr,z)))
```

Omitted `C` arguments are threaded by bind exactly as in the adequacy package.
`Delay` and `FunctionView` store the input value and child descriptor IDs;
they do not execute child conversions at construction. They retain source
lexical references and whatever boundary lineage the ultimately selected
source value-transport rule requires. They do not capture mutable-store
contents. Function application/resumption later uses the actual current store.

The view is an administrative realization of the complete source `CallView`;
it does not install a fresh receiver/handler or manufacture capture authority.
`Id` eliminates only value-conversion work. The surrounding typed-boundary
entry/exit and explicit annotation contract are still executed by the source
rule, even when source and target value shapes coincide. The type graph does
not identify an omitted annotation with an explicit capture contract merely
because their inferred effect labels agree.
If source boundary semantics surrounds that view with a scope, the same scope
surrounds argument conversion, underlying call, result conversion and all
demanded forces on both sides. This policy is a shared parameter, not a
hidden implementation of the pending §2 decision. The theorem below assumes
the same source `Delay`/value-lineage behavior on both sides and does not
certify its still-pending finite realization.

**Theorem (finite operational realization).** For every covered root pair
and input value/configuration of the corresponding source shape, descriptor
execution simulates the structural source adaptation equations with `≈g`,
preserving returns, request prefixes, latent future calls/forces, current
state and raw resumption behavior. It emits the same requests as those
equations; it performs no row subtraction.

Proof: relate every reachable `(s,t)` source adaptation command to its memoized
descriptor, and relate suspended binds by their corresponding suffix stacks.
Unfolding one command chooses the same priority-table case. `Id` returns the
same value. `ForceThen` invokes the same source force and appends related
child conversions. `DelayThen` and `ThunkMap` return related latent values;
on each future force they execute the same source operations before entering
the related child. `FunctionMap` returns related views; every application
uses the contravariant argument pair, the same underlying call and the
covariant result pair. The stateful bind lifting lemma composes these matches,
including every typed admissible resumption. All symbolic endpoint references,
request origins and still-live `K,D` are transported by those same source
operations under one `ν`.

For recursive pairs the relation contains all memoized pairs at once.
Descriptor recursion either returns a latent value/view or executes an actual
source force before its child; function children are entered only upon source
application. There is no descriptor-only cycle that repeatedly expands type
aliases. More explicitly, matching command configurations count each source
force/call entry and each adaptation-clause unfolding as a step; each
descriptor clause has the same corresponding operational step. Thus an
infinite chain of forced computations is matched by an infinite source
execution, not declared convergent by memoization. Induction covers finite
prefixes, and the simultaneous command relation covers unbounded execution.
The argument never requires recursive syntax to be unfolded in advance.

This is an operational simulation, not a proof that a proposed conversion
satisfies its target type/effect contract. In particular the delayed target
must cover the whole source force plus result adaptation. The complete
interface/certificate must validate that condition using the common source
relation; neither a `ThunkMap` tag nor equal family heads proves it.

## 5. Consequences and remaining source bridge

### Symbolic label-equality extension

For fixed constructor graphs one can also construct a symbolic structural
equivalence candidate without materializing family arguments. Add the finite
set of label-equality predicates for encountered thunk-label pairs to `PΩ`.
Represent formulas by truth tables in the finite Boolean algebra of the
finite-presentation package, rather than raw syntactic expression trees.
For pairs `s,t`, define the operator in that algebra:

```text
F(X)_s,t = false                                  mismatched constructors/atoms
         = true                                   identical rigid atoms
         = X_arg(s),arg(t) ∧ X_res(s),res(t)       two Function nodes
         = LabelEq_s,t ∧ X_res(s),res(t)           two Thunk nodes
Eq = νX. F(X)
```

Here `νX` denotes greatest fixed point, not the type assignment `ν`. Iterate
from all true formulas. At each Boolean valuation at most `|T|²` pair entries
can be removed; therefore the vector stabilizes after at most `|T|²` rounds.
Evaluation under any realizing assignment commutes with each iteration, so
the result is exactly greatest structural bisimilarity with that assignment's
label equality. Unrealisable Boolean cells assert nothing about a source
assignment.

Replace each descriptor's identity-first decision by a finite guard
`if Eq_s,t then Id else structural-case`. Allocate the descriptor before its
children as before; each pair still has bounded descriptor size. This gives
a symbolic generator and the same operational simulation if the source
selects this structural meaning for `≈`. Guard evaluation/realizability still
needs the underlying type theory. Neither version is selected here as the
general source equivalence. Equal labels do not identify callback boundary
ownership, event identities, annotation forms, or `K,D` endpoints.

### Source bridge

The graph construction gives a concrete finite family of adapter code labels
and bounded wrapper records for the earlier `Ω` machine: a child descriptor
is a graph pointer, not an unbounded host function. Finite symbolic endpoint
queries remain attached to the original pairs. Allocation of another runtime
wrapper creates no new type endpoint. This discharges the operational
adapter-descriptor premise for this fixed-shape kernel, conditional only on
the already explicit source primitives/value-lineage policy.

It does not discharge these broader obligations:

- deriving finite resolved shapes, admitted conversions and force positions
  from source inference; an unknown type endpoint whose `ν` may be a thunk
  cannot be treated as a rigid atom to obtain this theorem;
- proving that general source `≈`, other data/value conversions, and all
  recursive typing cases agree with or extend this kernel;
- defining the §2 source territory/latent transport rules and proving their
  finite realization, including invocation re-entry;
- a uniform modular future-interaction presentation and the source
  typing/acceptance bridge, then lifecycle and implementation gates.

No source envelope is narrowed and no acceptance difference is approved.
This constructive finite recursive adapter graph is a component of the
Milestone-3 route, not a complete finite successor or a class-3 result.

For the first gap, `(α,Unit)` is a concrete obstruction to *this fixed-shape
construction*: assigning `α=Unit`, `α=Thunk(E,Unit)`, and an arbitrarily deep
nest of such thunks demands identity, one force, and repeated forces. The
endpoint name remaining `α` does not make its outer constructor fixed.
Pair memoization over the given source nodes alone does not supply those
different payload nodes. This does not prove impossibility of a finite
parametric descriptor interpreter or richer symbolic presentation, and does
not justify rejecting such source uses. Its resolution belongs to the
source elaboration/representation bridge.

# Source generation and guarded permission for recursive name-return uses

Date: 2026-10-06
Status: frozen conditional research derivation; compiler-reviewed, one MINOR repaired and delta-reviewed
Baseline: `b784f48d10f92a74d43c9ef5542fb9e712be9310` (supplied by primary)
Exclusive lease: this file only
Method: constructive candidate source judgments and static production-path closure
Implementation authority: none

## Objective and governing premises

Attempt to derive the source permission law `(L)` for an incoming use of
either member of

```text
my f x = g
my g y = f
```

The governing selected decisions are the redesign charter §§20, 22–23.
Section 20 gives essential existential request opening and distinguishes its
hidden request binders from equality-kernel existential inference variables.
Section 22 guards every derived comparison involving an introduced
existential; §23 puts levels on variables rather than constructors. These
sections select neither the classification of this pure scheme's fresh row
nor a complete source admissibility judgment. No new user decision is used.

Other inputs are the candidate pure typing note, “Semantic fragment”; the
candidate SCC note, “Recursive group generation” and “Graph scheme and use”;
the reviewed recursive-group adequacy note, “Declarative group rule” and
“Generation relation”; the reviewed member bridge H1–H4; the reviewed
production crosswalk, “Source and endpoint reconstruction”; the reviewed
pure production reduction, “Exact named scheme and incoming-use reduction”
and “Symbolic effect elimination”; and the reviewed contextual valuation
note P1–P4, `(I)` and `(L)`, together with the reviewed installed-graph E
invariant. F5 §§7–9 and 23 are legacy comparison material under the charter,
not selected successor source meaning.

Keep three quantifications distinct:

1. A scheme's recursive binder `R` is a closed storage/binder category with a
   restored bound; it is distinct from its `Q` category.
2. The production use creates one fresh solver row for the repeated `R`
   ordinal. Writing `∃d∈D` for its carrier assignment in H4 is mathematical
   projection, and does not classify that row as a §22 source existential.
3. Section 20's hidden request binder is opened to a fresh rigid proof name
   when checking an operation arm. No operation/request/arm occurs in the
   source examined here. This proves absence of that introduction event,
   without deciding the source status of category 2.

The primary's accepted boundaries remain fixed: candidate `RecGroup` is
not intended Yulang authority; the regular-tree carrier remains unselected;
successful general concrete comparisons do not supply a transitive preorder.
No question bundle was read or used as new authority.

## Construct the binding and member-use judgments

Use the candidate pure preorder and complete Function law, precisely H1–H2
of the member bridge. There are no free outer anchors. The candidate recursive
environment is

```text
Ξ_G = {f ↦ s_f, g ↦ s_g}.
```

The Name and Lambda rules give, with distinct fresh parameters `a,b`,

```text
Ξ_G[x↦a] ⊢ g ⇓ (s_g, ∅)
Ξ_G       ⊢ λx.g ⇓ (Fun(a,s_g), ∅)

Ξ_G[y↦b] ⊢ f ⇓ (s_f, ∅)
Ξ_G       ⊢ λy.f ⇓ (Fun(b,s_f), ∅).
```

The two definition boundaries therefore give exactly

```text
C_G = {
  Fun(a,s_g) ≤ s_f, Fun(a,s_g) ≤ r_f,
  Fun(b,s_f) ≤ s_g, Fun(b,s_f) ≤ r_g
}.
```

The corresponding declarative premises are
`Γ[f:S_f,g:S_g,x:A] ⊢ g:S_g` and its symmetric counterpart,
followed by Lambda and the two inequalities per member in `RecGroup`.
All six coordinates are SCC-created; the reviewed adequacy theorem applies
to this candidate rule with its all-local partition. It does not assert
production identity correspondence or any existential-level classification.

For a separately observed external use `u` of `f`, the existing candidate
“Graph scheme and use” text prescribes an injective freshening `θ_u` of all
six locals, followed by the root observation. Expressing that text as a
judgment, rather than adding a different scheme semantics, gives

```text
Σ(f)=H_f
────────────────────────────────────────────────── candidate member use
Σ ⊢ use_u(f) ⇓ (θ_u(r_f), θ_u(C_G))

Use_f(U) ⇔ ∃ν_u : θ_u(L_G)→D.
                 Sat(θ_u(C_G),ν_u) ∧ ν_u(θ_u(r_f))≤U.
```

The fresh range is disjoint from the caller. The caller assignment and any
caller constraints remain fixed. This use judgment contains no source scope
context, existential introduction category, introduction level, or per-task
guard premise. In particular, the candidate monomorphic Name rule alone
does not instantiate a scheme: its conclusion is `(Ξ(f),∅)`. The external
use rule above comes from the separate candidate graph-scheme text.

Under H1–H4 the reviewed member bridge derives

```text
∀U∈D. Use_f(U) ⇔ ∃d∈D. F²(d)≤d ∧ F²(d)≤U,
F(t)=Fun(Top,t).
```

For a fixed production witness `d`, its reverse construction gives a
concrete candidate use witness, rather than assuming source existence:

```text
a=b=Top; s_g=F(d); s_f=r_f=F²(d); r_g=F³(d).
```

The f self/export obligations are reflexive. The g obligations follow from
`F²(d)≤d` by monotonicity, giving `F³(d)≤F(d)`; the selected root is below
`U` by the predicate obligation. Symmetry gives the g use. This constructs
the candidate graph witness but still supplies no source permission labels.

## A source-produced target envelope smaller than P2

Define a **syntactic production envelope**, not a selected semantic support
class:

```text
G plus m bare bindings `my h_i = d_i`,
m finite, d_i∈{f,g}, every h_i distinct from f,g and the other h_j;
no other items, annotations, imported anchors, requests, handlers or uses of h_i.
```

Assume normal parsing/association and name resolution with no recovery,
valid session ownership, and successful completed allocations/transitions.
For the per-use observation require `m≥1`. This class uses real accepted
lowering branches: `yu-hir/src/module.rs:1155` wraps a parameterized binding
in Lambda, while `:1402–1470` accepts a direct identifier atom. Collection
at `yu-solver/src/lib.rs:1008` admits a bare resolved-name binding, and
`:1032` admits the parameterized bodies of G. This is static branch
characterization; no new compilation was executed.

For an alias `h_i`, `emit_resolved_binding_name` (`:1513`) creates its body
occurrence value row `cu_i`, its pure effect bounds, and, with a definition
root supplied, the direct fact

```text
cu_i ≤ R_hi.                                                (alias)
```

The use record (`:1120–1135`) targets the closed scheme of `d_i`, retains
this exact `cu_i`, and fixes `use_level=1`. It does not allocate a replacement
consuming row. `run` (`:9731`) admits all collected facts before executing
the SCC plan; `admit_all_collected_facts` (`:10447`) admits the Lambda
recipes in that pass. `execute_scc_plan_inner` (`:12968` onward) completes
internal G uses and finalizes G before its incoming use calls (`:13963`).

Before that incoming call, the alias portion of the inventory is exactly:

* `cu_i` has direct upper neighbor `R_hi`, no exact lower or upper;
* `R_hi` has direct lower neighbor `cu_i`, no exact lower or upper;
* no use of `h_i` adds another neighbor or an upper on `R_hi`;
* no collected value fact in this source has a negative Function endpoint.

Other aliases have distinct rows. Internal G facts connect only G's roots,
body rows and parameters; they have no path to these alias rows before the
incoming routes. Existing completion and generalization scratch do not
change this alias inventory. The narrowed trace below ends at completion of
one incoming route, before later alias generalization/publication.

The audited scheme of each `d_i` is

```text
Q=[]; R=[r0]; predicate=L=PureFun(Top,PureFun(Top,r0));
R0.lower=L; R0.upper=Top.
```

`instantiate_and_route_closed_inner` (`:14527`) produces one fresh row `ρ_i`
and the three root comparisons, in order:

```text
L_i <: ρ_i       ρ_i <: Top−       L_i <: cu_i,
L_i=P₀(Top−,P₀(Top−,ρ_i+)).
```

### Exact value replay closure for that alias

This is an owner-path induction, not an assumed checker transition system:

1. The fresh row is empty. `L_i <: ρ_i` installs its structural lower;
   the row has no upper or direct upper neighbor to replay.
2. `ρ_i <: Top−` is terminal in `constrain_live` (`:11105` vicinity) and
   installs no upper.
3. `L_i <: cu_i` installs the lower. The non-variable/row branch of
   `apply_value_task` (`:12174–12234`) replays it against direct upper
   neighbor `R_hi`, producing exactly `L_i <: R_hi`.
4. That comparison stores a lower on `R_hi`. The receiving row has no
   exact or direct upper, so no further value comparison is generated.

Duplicate memo entries can suppress an operation already certified, but
create no additional comparison shape. Thus the only new value pair shapes
are the three roots and this one replay. There is no Function/Function
pair, no structural decomposition, and no derived `ρ_i <: v` pair in this
envelope. Other aliases do not change that conclusion. Fixed pure effect
facts from collection are separate Bottom/Empty/row comparisons; this
incoming substitution allocates no effect row, and its Function terms are
stored as bounds without decomposing their pure effect leaves.

The contextual example `cu≤N₀(A0,N₀(A1,v))`, yielding `ρ≤v`, is important
for P2 but cannot be supplied by this alias-only generator. This restriction
comes from actual source owners rather than discarding a possible replay
from an arbitrary caller inventory. It gives no completeness result for
application targets, annotation targets or all of P2.

Every row here has level one under the reviewed H3 producer invariant.
Extrusion visits the Function syntax, reaches `ρ_i`, and skips that row at
equal target level. No level changes. E justifies the already-aged skip in
the more general owner-reachable graph; no new heterogeneous-level probe
is needed for this specialized trace.

## Guard classification and a conditional permission derivation

Section 20 classifies **none** of the events above as a request opening:
the source and the lowering/collection branches have no request package or
arm elimination. Every internal reference is monomorphic in the candidate
SCC. The external `R` substitution is observed solver allocation, not a
`Pack_s`/unpack operation. This establishes absence of §20 introductions in
this particular source trace.

It does **not** establish that every fresh source/solver variable lacks an
introduced-existential classification for §22. The candidate source rules
assign all graph variables over D and provide no introduction judgments.
The production row metadata (`yu-solver/src/lib.rs:749`) records
`Collected/Fresh` origin and `non_generic`, but no declared §22 introduction
classification. F5's `Q/R` partition describes legacy generalization and
restoration, not the selected successor classification.

For precision, define a permission-only interface without choosing which
source variables are existentials. A hypothetical source derivation supplies
a context Δ with an introduction classification and level for each relevant
variable. Let `Guard_Δ(q)` be the selected §22 guard judgment for one
comparison; in the absence of any introduced existential it is vacuous. Let
`Orig_p(Δ)` certify that Δ comes from the source binding/use derivation p,
including classification of the occurrence rows and the fresh `R` instance.
This is proof data, not a proposal for a new IR token.

For the actual comparison history H before this use and the finite added
history T proved above, define the **guard component** of admissibility:

```text
A_alloc^G(Δ) = Orig_p(Δ) ∧ ∀q∈H. Guard_Δ(q)
A_final^G(Δ) = Orig_p(Δ) ∧ ∀q∈H++T. Guard_Δ(q).
```

These are definitions of a separated guard component, not definitions of
the full source `A_alloc(σ,d)` and `A_final(σ,d)` requested by `(L)`.
Carrier/source witness requirements and any other admissibility obligations
must also be supplied by an actual source rule.

**Conditional theorem, exact premise O.** Suppose a source origin rule for
the closed alias envelope derives `Orig_p(Δ)` and classifies every collected
row and the fresh constrained `R` instance as carrying no §22 introduced
existential. Then `A_alloc^G(Δ) iff A_final^G(Δ)` for every completed
incoming trace in this envelope.

Proof: O classifies the collected target/root rows and the current fresh
constrained `ρ_i` as carrying no guarded existential. The rooted value
operations and the single replay create no further variable identity or
existential introduction; every operand and dependency of a comparison in T
is one of those rows, `ρ_i`, Top, or the fixed Function syntax. Their origins
are retained. The examined owners change no level in this envelope.
Consequently every `Guard_Δ(q)` in T is vacuous. Existing H and its guard
obligations are retained, including obligations concerning any earlier alias
instances in Δ; O does not classify those instances. Appending T adds only
true conjuncts. This proves both directions without assuming `(L)` itself.

The candidate source graph witness constructed earlier is also preserved
pointwise by the reviewed contextual `(I)`. If an eventual source judgment
defines full admission from that graph witness plus this guard component,
with no other changing permission obligations, the same pointwise argument
proves its full `(L)` in the alias envelope. That last correspondence is an
additional unproved source premise. It is not selected by defining a guard
component here. Consequently the actual source `A_alloc/A_final` remain
undefined in the current inputs; this note does not claim their theorem.

O is narrower and more testable than “unchanged levels imply unchanged
permissions”: it asks which source rule labels **each** allocated variable,
and the trace induction proves that every initial and replay comparison is
then covered. No new choice about the language is made by assuming O.

### Why all-one H3 alone cannot replace O

Level equality is not existential classification. Under §22, if one endpoint
of a derived variable/variable comparison is an introduced existential at
level one and the other variable is at level one, that comparison meets the
forbidden `<= introduction level` condition. Unchanged levels would preserve
this rejection condition, rather than discharge it. Whether a structural
bound involving an existential triggers another guard before its variable
comparisons remains part of §23's coverage task; no constructor-level rule
is supplied here.

Even when no row is aged, final admission can acquire the guards of **new**
comparisons. H3 proves equality of level metadata across states; it proves
neither truth of these new guard obligations nor the source status of their
operands. For this alias trace the new comparisons are known exactly, but O
is still needed to classify them. For broader P2 caller inventories the
classification must also cover replayed row pairs such as `ρ≤v`.

## Smallest missing source generation rule and stop condition

The first missing seam is a source origin premise on the external member-use
rule, and on the ordinary allocations supplying its caller rows:

```text
Δ; Σ ⊢ use_u(f) ⇒ (fresh ρ, constrained instance, cu,
                    classification/introduction information)
```

For the candidate graph judgment this must accompany `θ_u`; for production
it must accompany the closed R-bound substitution. It must state whether
the instance row is a §22 introduced existential, how its relevant level is
assigned, and how the already allocated occurrence/caller rows are classified.
The complete source rule must then make guard judgments available for the
two structural bound insertions, the terminal upper and the alias replay.
If it gives O, the conditional induction above closes the guard component
for this narrow envelope. If it gives an existential classification instead,
the structural/variable guard clauses must actually be applied; neither H4's
mathematical `∃` nor H3's all-one levels decides the result.

This is the smallest missing rule **for this derivation**, not a claim that
one annotation alone closes all source adequacy. Full source member
realization, any additional admissibility conditions, and carrier selection
still require their own correspondence. Candidate binding and use syntax
currently cannot produce the required origin premise, so no approved source
class or full permission theorem has been proved. A larger toy carrier or a
checker taking O as input would leave that same premise untouched.

Recommended next action: the primary should obtain or derive the exact
source allocation/member-use origin rule for this closed alias envelope,
including the classification of constrained R instantiation. Feed that rule
to this four-pair trace before extending to negative Function callers.

## Independence, coverage and resources

This combines static reads of actual source owners with a constructive
derivation in the explicitly candidate source calculus. The candidate
preorder, Function law and row interpretation are shared with H1–H4/P1;
they are not an independent source-semantics oracle. The production-path
closure independently identifies which comparison shapes the narrow source
generates. The permission theorem assumes O explicitly; neither that owner
closure nor any checker based on it proves O.

Coverage is symbolic over every finite number m of the specified bare aliases,
either selected member, and all fixed shared caller assignments satisfying
the contextual relation. There is no bounded executable characterization,
seed/range, mutation run or search. No test, build, probe, formatter, Git
command or subprocess concurrency was used. Initial broad captures were
truncated; the used source seams were reread with narrow `sed` ranges.

Failure/omission conditions include recovery, ambiguous/unresolved names,
extra consumers of aliases, external anchors, annotations/applications,
negative Function uppers, non-pure effects, unowned/injected inventories,
interleaving, failed allocation/reservation, rollback, incomplete memo
certificates and observations during a transition. Later alias generalization,
diagnostic completeness, module publication, full source adequacy, selected
target meaning, principal inference and runtime behavior remain unverified.

Resources: one lightweight shell process at a time; only `cat`, bounded
`rg`/`sed`, SHA-256 reads and the leased-file write/check. CPU/RSS were not
measured. No heavy process or compute search budget was consumed. The primary
supplied baseline verification; this worker did not inspect Git refs/index.

## Frozen dependency snapshot

SHA-256 hashes, rechecked at freeze:

| Dependency | SHA-256 |
|---|---|
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/progress/2026-09-30-intrusion-pure-source-typing-rules.md` | `beb998aabe285ed026a04cddb90055a6ea579c463457a4f1639e1e6ffc019a73` |
| `notes/progress/2026-09-30-intrusion-scc-constraint-scheme-rules.md` | `78d3a34508b7771701044b7b66d423ed0e7278cb52c9f9f368734bfb524cbdda` |
| `notes/progress/2026-09-30-intrusion-pure-recursive-group-adequacy.md` | `6227dc1875602c26d6aa7b1a8fbb15f981bc8a78e50f647339cdab3849640d99` |
| `notes/progress/2026-10-06-rec-name-return-member-scheme-bridge.md` | `fea42929e591c160d8a92edcb4f103254fb2726feef0be58ca747fb7075cf84e` |
| `notes/progress/2026-10-06-rec-name-return-production-crosswalk.md` | `e9fdd07b254e262312175771ba86c514db568434b4211107803446e5ff78c70f` |
| `notes/progress/2026-10-06-rec-name-return-purefun-production-reduction.md` | `f4ee1f71bea24c1150c90a274b41bc8fb9f8c2059c797c500a245fd4003f9779` |
| `notes/progress/2026-10-06-live-row-contextual-valuation-attempt.md` | `f7351170386a2b832ccd5bfccec32ad46fab3c7ab6bf42b9387ea39f1ecae53b` |
| `notes/progress/2026-10-06-rec-name-return-level-permission-constructive-attempt.md` | `4f162399344ddce70262f3fcd39a2fecb91df75eb98c4a29dad1d5e14ac11758` |
| `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md` | `781d719ef6ddd458908b61b7b95f49e4c6abec9ffed79595af5fe1e201caac83` |
| `crates/yu-hir/src/module.rs` | `ed92636de471b4d424a274f3509673c68761d9fa24fa06f07c9afc3bb3b9b7a5` |
| `crates/yu-solver/src/lib.rs` | `a2103c6735d7a4efad00231f973544dda59d42219dbf83439fffc17889168e59` |

## Commit packet

* Exact leased path: `notes/progress/2026-10-06-rec-name-return-source-guard-derivation-attempt.md`.
* Baseline: `b784f48d10f92a74d43c9ef5542fb9e712be9310`, supplied by primary.
* Dependency changes: none observed in the direct dependency hash recheck.
* Claim/review status: compiler-referee found no BLOCKING or major issue and
  one MINOR quantifier overstatement; the repair was delta-reviewed PASS.
  Candidate source derivation, static alias-target closure and conditional
  guard-component theorem only. Full `(L)`/source realization remain open; no
  authority promotion.
* Checks already run: narrow rule/source reads, repeated dependency SHA-256
  equality, leased-note text/read integrity. No tests/builds/probes or Git.
* Proposed commit message: `research: derive alias-target guard seam for recursive member uses`.
* Shared-record deltas intentionally left for primary/curator: record the
  alias-only target envelope and four value pair shapes as static evidence;
  retain full `(L)` as open, narrowed to the source allocation/member-use
  classification premise plus full admissibility correspondence. No edits to
  tasks, theory maps, INDEX, authority or question-board paths.

Writing stops at submission for frozen review.

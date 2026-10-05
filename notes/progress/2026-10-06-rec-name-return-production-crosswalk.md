# Mutually recursive name-return endpoint crosswalk

Date: 2026-10-06
Status: reviewed research correspondence and conditional derivation
Baseline: `ab0d91ec50750087326df50a7232d4fb92d22094`
Branch inspected: `research/simple-sub-intrusion`
Write lease: this file only
Implementation authority: none

## Objective and governing premises

Reconstruct the current production endpoints for the narrow source fragment

```yulang
my f x = g;
my g y = f
```

and compare them with the reviewed conditional `RecGroup` graph. The external
expression `f 1` is considered separately below. This is one production
correspondence subcase, not an SCC correctness or intended-source theorem.

The exact candidate clauses used are “Semantic fragment” and “Correspondence
theorem for this fragment” in
`2026-09-30-intrusion-pure-source-typing-rules.md`; “Recursive group generation”
and “Graph scheme and use” in
`2026-09-30-intrusion-scc-constraint-scheme-rules.md`; and “Declarative group
rule,” “Generation relation,” and “Adequacy theorem” in
`2026-09-30-intrusion-pure-recursive-group-adequacy.md`. The corrected Apply
direction is `callee ≤ Fun(argument,result)`.

The redesign charter §§1–4 makes current F5 comparison material and keeps
successor implementation behind a separate approval gate. The primary's
accepted boundary is retained: the candidate `RecGroup` rule is not intended
Yulang authority, and the pure transitive preorder is an explicit premise.
Successful concrete endpoint comparisons are not silently treated as that
preorder. No question draft supplies any premise here.

## Source and endpoint reconstruction

The reconstruction follows the owners, independently of the candidate graph.
It is a static control-flow derivation, not a newly executed source trace.
Assume parsing/association succeeds without recovery, the module has unique
`f`/`g` definitions, and allocation is available.

1. `yu-hir/src/module.rs:803` builds the complete namespace before lowering
   bodies. Its root loop at `:817` creates one `DefinitionRootId` per admitted
   binding. `plain_binding_header` at `:1471` admits the identifier plus one
   identifier parameter. Thus the two distinct definition IDs produce distinct
   roots; the forward reference from `f` to `g` is not unresolved merely because
   `g` comes later.
2. `lower_plan` at `:1155` creates `HirParameterId(root,0)` for each parameter,
   allocates a separate body occurrence at `:1167`, and wraps that body in one
   `ResolvedExpr::Lambda` at `:1199`. `lower_simple_chain` at `:1402` accepts
   direct name atoms. At `:1443`, `g` in `f` resolves to the module definition
   `g`, and `f` in `g` resolves to `f`; neither is its local parameter.
3. `ConstraintBatch::collect` at `yu-solver/src/lib.rs:876` registers one
   root component per binding. Both lambda body statuses are Complete
   (`:934`). The lambda branch at `:1032` creates one parameter recipe per
   member, invokes `emit_lambda`, and records a pending use at the body name
   occurrence. The completed definition table resolves both uses at `:1087`.
   The frozen records retain `target_root_component` and
   `use_value_component` (`:1115`). The plan is built once at `:1225`.
4. `emit_lambda` at `:1557` takes the module-name-body branch, which calls
   `emit_resolved_binding_name(body,None)` at `:1592`. That creates a fresh
   body value component and body effect component, with two effect bounds;
   the `None` argument adds no body-value-to-own-root alias edge. Each lambda
   gets a separate effect component with two bounds and one `LambdaRecipe`.
5. `InferenceSession::try_new` at `:9177` assigns a distinct live row to each
   collected value component (`:9480`) and then each parameter (`:9517`).
   `admit_lambda_fact` at `:10539` constructs a positive Function term from
   the negative parameter port, negative empty argument-effect port, positive
   body-effect port, and positive body-value port. It adds exactly that term
   below the member's definition root at `:10563`.
6. The two opposite resolved definition uses place the members in one SCC.
   Before member generalization, `execute_scc_plan` consumes its internal use
   list at `:12978`. `route_internal_inner` at `:13990` selects the target's
   **definition root**, and adds its value-row lower to the consuming body's
   value-row upper. This path uses no closed-scheme instantiation.

Use the following symbolic names; distinct letters denote distinct allocated
rows, not an assertion about distinct solved values.

| Production object | Name in this derivation |
|---|---|
| `DefinitionValue(root_f)`, `DefinitionValue(root_g)` | `R_f`, `R_g` |
| live parameter recipe rows for `x`, `y` | `a`, `b` |
| value rows of body names `g`, `f` | `v_f`, `v_g` |
| body effect rows | `e_f`, `e_g` |
| lambda construction effect rows | `l_f`, `l_g` |

The initial recipe inventory has four collected value components, four
collected effect components, and two extra parameter value rows. The lambda
occurrences have effect components but no separate value component; their
Function terms provide their value endpoints. There is no independently
allocated `s_f` or `s_g` recursive self endpoint in these clauses.

Writing `F⁺` only as notation for the actual four-port positive Function term,
the admitted source/route facts are:

```text
F⁺(a⁻, Empty⁻, e_f⁺, v_f⁺) <: R_f
F⁺(b⁻, Empty⁻, e_g⁺, v_g⁺) <: R_g
R_g <: v_f                         internal f-body use of g
R_f <: v_g                         internal g-body use of f

EffectBottom⁺ <: e_f <: Empty⁻
EffectBottom⁺ <: e_g <: Empty⁻
EffectBottom⁺ <: l_f <: Empty⁻
EffectBottom⁺ <: l_g <: Empty⁻
```

There are eight collected effect facts, two session-admitted Function facts,
and two internal-route value facts. These are generator/route facts, not an
exhaustive enumeration of later solver replay or generalization work.

## Candidate graph and the exact missing correspondence

Candidate Name generation under `Ξ_G(f)=s_f`, `Ξ_G(g)=s_g` allocates no body
value endpoint. Lambda generation and the two RecGroup obligations give:

```text
Fun(a,s_g) ≤ s_f       Fun(a,s_g) ≤ r_f
Fun(b,s_f) ≤ s_g       Fun(b,s_f) ≤ r_g
```

All six candidate identities `a,b,s_f,s_g,r_f,r_g` are group-local, with no
outer anchors in this source. Crucially, equal cardinality with the six
production value rows does not establish an adequate identity map: production
`v_f,v_g` are consumer body rows receiving lower bounds from roots. They do not
receive the member Function lower bounds directly.

The directly observed production internal provider is `R_g`/`R_f`, the same
root receiving that member's Function fact. Production preserves distinct
member roots and shared live internal routing, but this does not reconstruct
the candidate's separate self/export pair. Mapping `s_d` and `r_d` both to
`R_d` is an identification, not injective endpoint renaming.

There is also an injective syntactic map `s_f↦v_g`, `s_g↦v_f`,
`r_f↦R_f`, `r_g↦R_g`, fixing `a,b`. Under that map the production projection
is exactly the candidate graph **plus** `r_f ≤ s_f`, `r_g ≤ s_g`: the two
candidate self lower bounds follow transitively through these added root
edges, while the candidate root bounds are present directly. Thus reusing
the opposite body rows as self endpoints still adds obligations that the
declarative rule does not require. Either map needs a preservation argument;
the allocation count alone supplies neither.

Here is the strongest simple algebraic crosswalk available without interpreting
the concrete solver as source semantics. Assume:

* H1: interpret the **syntactic value projection** of the four production
  value facts in a fixed transitive preorder `D`; one positive/negative row
  denotes one assigned `D` value, and the projected Function obeys the pure
  Function law. This interpretation is a candidate assumption, not a proved
  denotation of the coupled production Function/effect facts.
* H2: no additional obligations are included in this projected relation;
  parameter and body rows are freely assigned over `D`.

Under H1–H2 the projection is

```text
Fun(a,v_f) ≤ R_f       R_g ≤ v_f
Fun(b,v_g) ≤ R_g       R_f ≤ v_g.
```

Existentially eliminating `v_f,v_g` yields **exactly**

```text
Fun(a,R_g) ≤ R_f
Fun(b,R_f) ≤ R_g.
```

Forwards, covariance gives `Fun(a,R_g) ≤ Fun(a,v_f) ≤ R_f`, and similarly
for `g`. Backwards, choose `v_f=R_g`, `v_g=R_f`. Thus this projected relation
is the candidate RecGroup relation restricted to `s_f=r_f=R_f` and
`s_g=r_g=R_g`. It is a subset of the candidate's joint exposed-root relation.
Equality with the unrestricted candidate relation requires an additional
identification-preservation proof. The reviewed RecGroup adequacy theorem
does not supply that proof.

## Compact conditional separator

This is an algebraic witness against a universal claim that self/export
identification preserves the joint root relation. It is not a production
acceptance counterexample. In addition to H1, assume a carrier with least
`Bottom`, greatest `Top`, distinguished `Int`, and a regular value `Z` such
that `Z=Fun(Bottom,Z)` and `Top ≰ Z`. For example, the regular structural
Function domain with extrema and its coinductive variance preorder supports
these assumptions. The abstract preorder premise alone does not require `Z`.

Choose:

```text
a=Int, b=Bottom, s_f=s_g=Z
r_f=Fun(Int,Top), r_g=Z.
```

The candidate accepts this joint assignment: `Fun(Int,Z) ≤ Z` follows from
`Bottom ≤ Int` and reflexivity of `Z`; `Fun(Int,Z) ≤ Fun(Int,Top)` follows
from `Z ≤ Top`; both `g` bounds are `Z ≤ Z`.

The identified projection cannot realize the same joint exposed roots.
Its `g` obligation would require

```text
Fun(b,Fun(Int,Top)) ≤ Z = Fun(Bottom,Z),
```

which by the Function law requires `Fun(Int,Top) ≤ Z`, hence `Top ≤ Z`,
contradicting the hypothesis. This failure holds for every production choice
of `b`, since the result requirement is unchanged.

This uses the assigned two-member name-return pattern and a single regular
back-reference. No exhaustive minimization search was performed. It separates
the **joint root vector**, not the separately existentially projected `f`
root: allowing a different `r_g`, for example `Top`, can remove the obstruction.
It therefore does not establish different acceptance of a program that only
uses `f`.

## External `f 1`: logical query only

Current `ResolvedExpr` has no Apply variant (`yu-hir/src/module.rs:426`).
`direct_atom` in `yu-hir/src/lib.rs:175` requires one integer/name atom, and
`lower_simple_chain` at `module.rs:1419` rejects a chain without that atom or
without a child-free `HirExpr::Value`. Thus `f 1` is outside the admitted HIR
envelope: a direct-root occurrence is retained as Error with
`UnsupportedExpression` by `lower_direct_root_expression` at `:1259`.
Placing it in a binding RHS likewise fails through `lower_body` at `:1374`.
No production Apply constraint or external Function-call trace is claimed.

In the candidate graph, one external use of `f` takes a fresh renamed copy of
**all** group-local identities and constraints, fixes the empty outer-anchor
environment, and adds `r_f^u ≤ Fun(Int,w)` for fresh `w`. This is the corrected
Apply direction. The separator assignment above extends to that logical
query with `w=Top`, by reflexivity of `Fun(Int,Top)`.

For a logical query over production's projected current roots, add
`R_f ≤ Fun(Int,w)` to the identified graph. This is deliberately not the
production incoming route: `route_incoming_inner` at `yu-solver/src/lib.rs:14877`
reads a finalized scheme before instantiating it. The selected joint-root
assignment remains impossible, but satisfiability or acceptance of `f 1`
does not follow from this comparison. Actual production generalization,
scheme projection, and incoming instantiation have not been reconstructed.

## Evidence independence, coverage, and limits

The production endpoint inventory comes from HIR/collector/admission/route
control flow, not from a checker that implements the candidate RecGroup rule.
The candidate equations come independently from the named declarative clauses.
Their algebraic comparison still shares H1's preorder and Function law. This
separation establishes a mismatch in raw endpoint ownership; it does not
validate the candidate source rule or the denotation of concrete polarized
rows. Frozen Oracle behavior was not consulted or executed.

Coverage is exactly two error-free one-parameter lambdas with module-name
bodies and their two internal uses, plus source rejection ownership for one
application. There are no seeds, enumerated ranges, executable probes, or
executed mutations. The separator attacks the shortcut “identify self and
export roots”; it is not evidence against other representations. Dropping the
other member's obligations could hide its joint-root failure and is not part
of the comparison.

Omitted: effects denotation/full bound inclusion, concrete comparison
transitivity, replay completeness, current final schemes, independent member
root-marginal equality, incoming Function use, runtime behavior, nested lets,
member-specific boundaries, and general SCC adequacy. The static source claim
fails if parser recovery, duplicate definitions, changed lowering owners,
missing target endpoints, or allocation failure intervene. The algebraic
theorem fails without H1–H2; the separator requires `Z` and `Top ≰ Z`.

Recommended next action: independently review the endpoint crosswalk and the
diagonal-projection derivation, then specify the intended member observation
(joint exposed roots or an individual root lens) before attempting the
remaining identification-preservation bridge. No production change is proposed.

## Independent review

`compiler_referee` reviewed the complete endpoint reconstruction, equations,
conditional elimination, separator, and claim limits against the production
owners, candidate rules, F4/F5 clauses, and redesign charter. The reviewer
found no blocking, major, or minor findings. This review does not establish
concrete solver denotation, finalized schemes, intended Yulang semantics, or
final acceptance correspondence.

## Snapshot, verification, and commit packet

Direct dependency SHA-256 hashes, unchanged against the pinned baseline:

```text
6227dc1875602c26d6aa7b1a8fbb15f981bc8a78e50f647339cdab3849640d99  notes/progress/2026-09-30-intrusion-pure-recursive-group-adequacy.md
beb998aabe285ed026a04cddb90055a6ea579c463457a4f1639e1e6ffc019a73  notes/progress/2026-09-30-intrusion-pure-source-typing-rules.md
78d3a34508b7771701044b7b66d423ed0e7278cb52c9f9f368734bfb524cbdda  notes/progress/2026-09-30-intrusion-scc-constraint-scheme-rules.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed  notes/design/2026-09-29-scc-intrusion-redesign-charter.md
ed92636de471b4d424a274f3509673c68761d9fa24fa06f07c9afc3bb3b9b7a5  crates/yu-hir/src/module.rs
56aafd7d958acdfa3362ffcc7bf3e815d795f455597cf4f8e471194addb04c1b  crates/yu-hir/src/lib.rs
a2103c6735d7a4efad00231f973544dda59d42219dbf83439fffc17889168e59  crates/yu-solver/src/lib.rs
```

Commands/checks: `git rev-parse HEAD`, `git branch --show-current`, narrow
`rg`/`sed` source inspection, `sha256sum` on the dependencies, and
`git diff --quiet ab0d91ec50750087326df50a7232d4fb92d22094 -- <direct dependencies>`
(exit 0). No tests, builds, formatting, searches over models, or Git mutations
ran. Local command execution was lightweight; CPU/RAM/wall-time totals were
not instrumented. No heavyweight process or extra output path was used.

Commit packet:

* Exact leased path: `notes/progress/2026-10-06-rec-name-return-production-crosswalk.md`.
* Baseline SHA: `ab0d91ec50750087326df50a7232d4fb92d22094`.
* Changed dependency hashes: none at production time; hashes above pin the
  required review snapshot.
* Claim/review status: reviewed source correspondence and conditional
  algebraic derivation; no intended-semantic or final-acceptance closure.
* Checks already run: the narrow read/hash/baseline checks above; final note
  scope and whitespace inspection, with no executable verification.
* Proposed one-line commit message: `research: crosswalk recursive name-return production endpoints`.
* Shared-record deltas left for the primary/curator: record the absent separate
  production self endpoints, the conditional diagonal relation, and unsupported
  production Apply; do not promote RecGroup to source authority or claim a
  final-acceptance mismatch. No shared task/index/theory file was edited.

This artifact is frozen for review after submission; subsequent repair requires
the primary to return a specific finding and lease.

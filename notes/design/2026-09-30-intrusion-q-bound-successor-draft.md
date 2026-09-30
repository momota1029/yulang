# Successor draft: retain selected bounds on one-polarity parents

Date: 2026-09-30
Status: Draft; unreviewed; not implementation authority
Scope: proposed successor rule for the pure type-bound projection used by
SCC intrusion
Approved-by: none
Approved-at: none
Reviewed-by: none
Supersedes: none

## Decision under consideration

Do not erase a generalizable variable to `Top` or `Bottom` solely because it
occurs at one polarity when the selected frozen graph has incident bounds on
that variable. Intrude the variable to a per-member boundary parent and retain
the selected incident constraints, including recursive back-edges. A
per-incoming-use instantiation freshens that parent and transports its selected
constraint graph as one unit. Unconstrained one-polarity variables remain
eligible for the Oracle's polarity extreme.

This is a candidate successor rule, not an approved design. It does not select
which bounds are eligible, define boundary levels, settle the full type
carrier, or define effects, roles, diagnostics, or serialization.

## Concrete conflict motivating the rule

For frozen Oracle `a58eefc31`, source `pub f x = x f` has parameter `x` mapped
to `q = TypeVar(2)`, self value `S = TypeVar(1)`, and application result
`V = TypeVar(11)`. Its selected typed graph contains:

```text
q⁻ ≤ Fun(S⁺, V⁺)       BoundRecordId(7), source ApplicationArgument
Fun(q⁻, V⁺) ≤ S⁺       BoundRecordId(4), selected recursive lower
Fun(q⁻, V⁺) ≤ root⁺   selected root lower
```

The Oracle expands q at negative polarity, erases it to `Top`, prunes its
recursive row, and publishes the root argument as `Top`. The exact traces and
run-local identity correspondence are recorded in
`notes/progress/2026-09-30-intrusion-q-finite-bound-cycle-trace.md` and
`notes/progress/2026-09-30-intrusion-source-identity-map.md`.

Work in the pure value-type projection, writing `Fun(A,R)` for the Function
value type and holding the separate effect coordinates fixed. Assume a subtype
preorder with greatest element `Top`, a proper Function constructor
(`Top ≰ Fun(S,V)` for every assignment), and the ordinary contravariant
Function rule:

```text
Fun(A,R) ≤ Fun(A',R') iff A' ≤ A and R ≤ R'
```

The selected q-cycle/root fragment is nonempty: choose `q=Bottom`, `S=Top`,
`V=Bottom`, and root `r=Top`. Now consider `A = Fun(Top,Bottom)`. The erased
scheme relation contains `A` as a generator by assigning its result binder
`Bottom`. The original selected graph cannot generate any root `t ≤ A`:
the selected root edge requires `Fun(q,V) ≤ t`, hence by transitivity
`Fun(q,V) ≤ A`. Function subtyping then requires `Top ≤ q`. Its selected
upper edge also requires `q ≤ Fun(S,V)`. Transitivity would give
`Top ≤ Fun(S,V)`, contradicting properness. Therefore:

```text
A ∈ Pred_erased
A ∉ Pred_selected
```

The conflict is thus not an empty-graph artifact. This is a concrete
principal root-relation mismatch for the traced selected-bound graph under
the stated carrier/order assumptions: polarity-only erasure enlarges the
relation.

The contradiction uses only the necessary value-argument condition of
Function subtyping; additional latent-effect constraints can only further
restrict the source relation. Matching the captured effect coordinates into a
full `Obs_source` witness is part of the still-open source/effect bridge below.

### Scope of this counterexample

The selected application upper is directly traced to source syntax, and the
root's q occurrence and Oracle erasure are traced. The graph-level relational
conflict is established under the stated subtype assumptions. A complete
source-to-denotation theorem still needs to show that the entire effectful
Oracle root view, including subtraction/latent effects and every selected
projection premise, maps to this pure relation without changing the witness.
The example is enough to reject the unconditional *graph rule* “one polarity
implies extreme”; it is not a proof that the full Oracle compiler accepts an
unsound executable program.

## Oracle behavior proposed for removal

Remove this projection behavior from the successor's inference semantics:

> Erase a one-polarity variable with selected incident constraints, replace it
> by the polarity extreme, and discard its now-unreachable recursive row.

The observed Oracle output for this fixture is
`any -> ['a] 'b` with no q recursive bound. Oracle `dump-poly` succeeds for
`pub f x = x f; pub main = f 1`, reports `main : never`, and marks `main` as a
runtime root; `dump-mono` later rejects its `f : int -> unit` instance. The
source-level inference and mono observations are distinct. The proposed
successor preserves the selected bound at inference/use instantiation, so the
invalid use may fail earlier; this is a proposed principality correction, not
a claim of end-to-end Oracle unsoundness.

## Successor semantics to prove

For each member root and boundary, construct the root relation from the
selected bound graph, not from polarity alone. The one-polarity parent remains
an explicit graph identity with its incident selected inequalities. Intrusion
must satisfy all of these before any implementation can claim principality:

1. the parent graph's satisfying assignments correspond to the Oracle source
   bound assignments before projection;
2. the parent graph's `Pred` relation is sound and complete for the root
   relation over every fixed outer environment;
3. each use receives capture-avoiding fresh parents and the same selected
   edges, while preserving outer anchors;
4. SCC recursion remains inequality sharing, never an implicit recursive type
   equation;
5. any later body specialization check is redundant for these selected type
   obligations or is explicitly part of the source observation relation;
6. effects, handler hygiene, role constraints, diagnostic order, and public
   normalization are transported or accounted for by separate proved layers.

The proof obligation is about root principality and per-use behavior; a
pointwise least assignment to every graph vertex is not required.

## Compatibility impact if approved

For fixtures where an erased one-polarity variable has selected bounds, public
inference output can change from an extreme (`any`/`never`) to a constrained
regular graph or an equivalent bounded view. Programs such as `f 1` that
currently pass `dump-poly` and fail `dump-mono` may fail during inference or
use instantiation instead. Diagnostic phase, wording, source attribution,
`dump-poly` output, and downstream API consumers of the old broad scheme can
change. Programs whose one-polarity variables have no selected bounds should
retain the extreme projection. Whether accepted-program sets change outside
the observed fixtures remains unproved and must be measured against the
frozen Oracle after the successor is reviewed.

## Gate

This proposal needs independent semantic review and explicit user approval
before code changes. Current evidence justifies rejecting unconditional
polarity erasure in the candidate graph semantics; it does not yet prove the
full successor's Oracle-capable envelope or authorize implementation.

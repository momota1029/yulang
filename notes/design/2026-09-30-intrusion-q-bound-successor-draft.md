# Successor draft: retain meaningful bounds on one-polarity parents

Date: 2026-09-30
Status: Draft; unreviewed; not implementation authority
Scope: proposed successor rule for the pure type-bound projection used by
SCC intrusion
Approved-by: none
Approved-at: none
Reviewed-by: none
Supersedes: none

## User-approved semantic priority

On 2026-09-30 the user decided that matching Oracle one-polarity q erasure is
not a successor requirement: if erasure loses a meaningful source constraint,
retain that constraint. Compatibility with Oracle inference-stage scheme
formatting and acceptance stage is not required. The target is acceptance of
final well-typed programs. Soundness and principality remain ahead of Oracle
compatibility.

This records that priority decision. The exact parent representation and its
proof obligations below remain a draft, not an approved implementation
contract.

## Proposed successor rule

Do not erase a generalizable variable to `Top` or `Bottom` solely because it
occurs at one polarity when the source constraint graph has meaningful
obligations incident on that variable. Intrude the variable to a per-member
boundary parent and retain those source constraints, including recursive
back-edges. A per-incoming-use instantiation freshens that parent and
transports the retained source constraint graph as one unit. Unconstrained
one-polarity variables may be
projected to a polarity extreme only if a separate preservation proof permits
it; such erasure is not a successor requirement.

The formal criterion for a bound to be meaningful, the successor's source
constraint and edge ownership rules, boundary levels, the full type carrier, effects, roles,
diagnostics, and serialization remain to be specified and proved.

## Concrete conflict motivating the rule

For frozen Oracle `a58eefc31`, source `pub f x = x f` has parameter `x` mapped
to `q = TypeVar(2)`, self value `S = TypeVar(1)`, application result
`V = TypeVar(11)`, wrapper `W`, and public root `R`. The symbolic source
inventory gives:

```text
q ≤ Fun(S, Ea, Stack(C, push(δ)), V)                         // application
Fun(q, Bot, NonSubtract(Be,pop(δ)), NonSubtract(Bv,pop(δ))) ≤ W
W ≤ R
```

The collector also records a q-bearing selected lower at the root and the
recursive edge `Fun(q,V) ≤ S`; those are useful graph evidence but are not
needed for the root exclusion below. The exact source constraints, edge
provenance, and run-local identity correspondence are recorded in
`notes/progress/2026-09-30-intrusion-powerset-carrier-candidate.md`,
`notes/progress/2026-09-30-intrusion-q-finite-bound-cycle-trace.md`, and
`notes/progress/2026-09-30-intrusion-source-identity-map.md`.

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

Now consider `A = Fun(Top,Bottom)`. The erased scheme relation contains `A`
as a generator by assigning its result binder `Bottom`. If a source root
assignment `t` satisfied `t ≤ A`, the source wrapper constraints would give
`Fun(q, ..., ...) ≤ W ≤ t ≤ A`. The Function value-argument condition then
requires `Top ≤ q`. The direct application constraint also requires
`q ≤ Fun(S, ..., V)`. By transitivity this implies
`Top ≤ Fun(S, ..., V)`, contradicting properness. Therefore:

```text
A ∈ Pred_erased
A ∉ Pred_selected
```

This proof uses source-generated wrapper constraints, not only the collector's
selected-root edge. It is a concrete principal root-relation mismatch for the
exact traced source constraints under the stated carrier/order assumptions:
polarity-only erasure enlarges the relation. The q/S incidence fragment is
nonempty with `q=Bottom`, `S=Top`, `V=Bottom`; that assignment is only for the
incidence fragment, not a witness for every source/effect constraint.

The compact recursive upper is `q ≤ q ∩ K(q)`. If `∩` is the meet, then
`q ≤ q ∩ K(q)` iff `q ≤ K(q)`: one direction follows by meet projection, and
the other by the greatest-lower-bound property plus reflexivity `q ≤ q`.
The compact `K(q)` is more structured than one endpoint: the captured upper
contains q and a Function with nested q occurrence. Independently, the
selected source upper record 7 gives the direct obligation
`q ≤ Fun(S,V)` (with its captured effect positions); it is one constraint
that any ordinary satisfying assignment must meet. Substituting `q=Top`
therefore requires `Top ≤ Fun(S,V)`, which fails under the proper-Function
premise. The collector trace records that direct upper as the source
`ApplicationArgument` edge and records q at negative polarity with empty
weights. This does not identify the full compact `K(q)` with only that edge.

The exclusion uses only the necessary value-argument condition of Function
subtyping; additional latent-effect constraints cannot make an unsupported
root enter the source relation. The erased scheme can assign its unconstrained
result/effect binders directly. The full source-to-public observation bridge,
including satisfiability of the complete effect graph and runtime behavior,
remains open.

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
successor preserves the meaningful source bound through generalization and
use instantiation,
so the invalid use may fail earlier. This corrects the inferred root relation;
it is not a claim that Oracle's completed pipeline accepts the invalid program.

## Successor semantics to prove

For each member root and boundary, construct the root relation from the
successor's complete source constraint graph, not from polarity alone. The
one-polarity parent remains an explicit graph identity with its incident
source inequalities. Intrusion
must satisfy all of these before any implementation can claim principality:

1. the parent graph's satisfying assignments correspond to the declarative
   source typing assignments before root projection;
2. the parent graph's `Pred` relation is sound and complete for the root
   relation over every fixed outer environment;
3. each use receives capture-avoiding fresh parents and the corresponding
   source constraints, while preserving outer anchors;
4. SCC recursion remains inequality sharing, never an implicit recursive type
   equation;
5. any later body specialization check is redundant for these source type
   obligations or is explicitly part of the source observation relation;
6. effects, handler hygiene, role constraints, diagnostic order, and public
   normalization are transported or accounted for by separate proved layers.

The proof obligation is about root principality and per-use behavior; a
pointwise least assignment to every graph vertex is not required.

## Compatibility boundary

Oracle inference-stage scheme formatting and the phase where a program is
accepted or rejected are not compatibility requirements. Thus `dump-poly`
changing from `any -> ['a] 'b` or rejecting `f 1` before mono specialization
is an allowed stage-level difference. The acceptance target is every final
well-typed program in the supported envelope remaining accepted by the
completed successor pipeline, with soundness and principality preserved.
Programs such as `f 1` already fail Oracle `dump-mono`, so an earlier rejection
does not reduce final acceptance capability for that fixture. The successor
may retain variables even when their bounds appear irrelevant; removing them
is an optimization, not a compatibility requirement. No claim is made that
the proposed rule preserves the complete final accepted-program set; proving
that is part of the Oracle-capability theorem.

## Gate

The user approved the semantic priority and source-constraint-retention policy
above. Exact eligibility and transport semantics still need independent
semantic review before code changes under the repository design gate. Current
evidence rejects unconditional polarity erasure for this graph; it does not
yet prove the full successor's final-acceptance capability or authorize
implementation.

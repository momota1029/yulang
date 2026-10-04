# Principal scheme acceptance criteria

Status: user-directed acceptance criteria; successor derivation remains open.
Date: 2026-10-04.

The following public schemes are the user's expected principal presentations
for the stated source definitions. They are criteria for the general
constraint-generation, co-occurrence, inequality-solving, and generalization
rules; they are not permission to add per-example special cases.

```text
my id x = x
  id : 'a -> 'a

my zero x = 0
  zero : 'a -> int

my call f x = f x
  call : ('a -> ['b] 'c) -> 'a -> ['b] 'c

my compose f g x = f (g x)
  compose : ('a ['b] -> ['c] 'd)
         -> ('e -> ['b] 'a)
         -> 'e -> ['c] 'd

my twice f x = { f x; f x }
  twice : ('a -> ['b] 'c) -> 'a -> ['b] 'c

my choose cond f g x = if cond: f x else: g x
  choose : bool -> ('a -> ['b] 'c) -> ('a -> ['b] 'c)
         -> 'a -> ['b] 'c

my higher f g x = f g x
  higher : ('a -> ['e] 'b -> ['e] 'c)
         -> 'a -> 'b -> ['e] 'c
```

Value-level dependencies must not be exposed as refinements (`zero` keeps an
unconstrained argument). Effect support is not usage multiplicity (`twice`).
The compose presentation retains `g`'s contribution in the outer allowance;
it does not infer subtraction without witnessed attachment. Branch and staged
call outputs use the displayed shared effect components, but that presentation
does not by itself assert equality of the original source effect expressions.
The successor must derive these presentations from its general rules and
preserve the corresponding solution family.

## Existing production value-skeleton evidence

The current HIR/F5 source-generation audit covers the value projection of the
first two definitions, but not their complete schemes. `id x = x` generates a
positive Function descriptor whose negative argument and positive result both
reference the same live parameter value endpoint. `zero x = 0` generates a
distinct literal endpoint fixed to `Int`, while its parameter remains free in
that value projection. The exact source clauses and regular-witness boundary
are recorded in [the value-skeleton theorem](2026-10-04-production-f5-value-skeleton-selector.md).

This evidence supports the requested value skeletons and confirms that the
literal itself carries no value refinement. It does not prove that the
successor generalizer presents the free `zero` parameter as `'a`, or that the
full coupled Function/effect package preserves either scheme. In particular,
the existing theorem explicitly projects away effect children and disclaims
scheme principality; it cannot certify the full requested principal types.

## Frozen Oracle characterization

Oracle at `a58eefc31e22141574b6f20c6a5748151c6d79f1` confirms the displayed
`call` scheme. Its unannotated composition fixture prints protected subtraction
markers (`#0[Empty]`); the plain displayed form is present with an annotation.
Oracle prediction for `zero` is `any -> int`, not the user-directed successor
criterion, and is not adopted. The supplied same-line `twice` spelling parses
as a root-level separator, so the two-call body above uses a block. No exact
Oracle output was established for that normalized `twice`, `choose`, or
`higher`; lower-level Oracle rules are characterization only.

## Proof boundary

The existing callback B contract remains normative: expected callback context
selects Handler and boundary before body generation, endpoints are independently
synthesized, then one completed Function inequality is checked. The criteria
above are regression conditions for its principal projection and the broader
Function design; they do not establish its production bridge.

No current successor theorem proves that these seven presentations are
principal or that the active Simple-Sub/callback/Function endpoint proposal
preserves them. The open obligation is one compositional solution-preservation
argument across source constraint generation, co-occurrence consolidation,
concrete endpoint resolution, and generalization. In particular, branch or
staged-call effects may share a principal public allowance without treating
successful concrete comparisons as transitive or equating evidence owners.

An independent architect audit checked whether these principal criteria could
close the active Pure-value callback production bridge. They cannot: principal
projection constrains the public solution family, but supplies no inversion of
complete endpoint-bound membership into the `J_arg`, entry/rebind, body,
designated result-consumer, and `J_call` witnesses required by the production
crosswalk. That is an earlier source-to-endpoint realization obligation. The
remaining premise is stated in [the production design §4](../design/2026-10-04-production-callback-endpoint-generation-draft.md)
and [the direct main-gate audit](2026-10-04-direct-main-gate-attacks.md); this
audit establishes neither a source counterexample nor a new semantic choice.

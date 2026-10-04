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

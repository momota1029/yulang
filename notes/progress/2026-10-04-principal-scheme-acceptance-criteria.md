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

The current F5 closed representation has a concrete migration difference for
this case. Its test at `crates/yu-solver/src/lib.rs` around lines 20371–20400
asserts zero quantifiers, a negative `Top` argument, and positive `Int` result
for `my k x = 42`; the F5 scheme draft §§23–24 explicitly classifies this as
negative-only elimination. The user-directed successor criterion instead
requires `'a -> int`. This establishes a difference in public scheme
representation, not semantic equivalence or inequivalence between the two
forms. No theorem currently licenses carrying F5's negative-only elimination
through to the successor.

The generalization proof must therefore explain, by a source-owned rule rather
than a `zero` special case, how a flexible component exposed at a public
Function boundary survives as a quantifier even when its body has no
constraint on it. Internal solver extrema still retain their distinct roles;
the precise successor eligibility/projection rule remains unproved. This is
an additional direct obligation alongside, not a substitute for, the
common-allowance theorem.

The pair `id`/`zero` makes the required generalization criterion precise at
this boundary: both expose the source parameter's value component in the
public Function argument, but only `id` gives that component positive result
incidence. A successor rule based solely on bipolar incidence would quantify
`id` and eliminate `zero`'s negative-only component, contradicting the two
accepted schemes. A source-checkable candidate is to retain a flexible
component as quantifiable when its source owner is a function parameter and
its endpoint is exposed through that definition's public argument port,
independent of body incidence polarity; preserve any attached original
constraints in the scheme predicate. This uses the existing parameter owner
and endpoint path, not a new solver carrier. The candidate still needs proof
that it preserves the full solution family under SCC/environment closure,
instantiation, and generalization; it does not decide how other one-sided
internal components normalize.

The representation itself is not a blocker. Code inspection of
`yu-types::ClosedTypeFinalizer` and the normal F5 scheme-use path confirms that
`Q=[q0]` with the only occurrence `q0` in a negative Function argument can be
finalized and instantiated: finalization validates an in-range negative Q
reference without requiring positive incidence, and each declared Q receives
one fresh value variable that the negative occurrence resolves through the
same substitution. This proves carrier and path capability only. It does not
change F5's current negative-only elimination rule or establish successor
solution preservation/principality. The remaining zero-specific proof point
is therefore the source-owned generalizer's Q eligibility, not a new type
carrier or instantiation mechanism.

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

## Current design cross-check

The active proposal was audited against each acceptance example. The audit found
no counterexample to the requested schemes, but did not establish their
derivation:

| Example | Evidence already available | Unclosed part |
|---|---|---|
| `id` | Production value skeleton points the Function argument and result to the same live parameter endpoint. | Coupled effect interface and principal generalization. |
| `zero` | Production value skeleton leaves the parameter free and fixes the literal result to `Int`. | Successor generalization must expose the free parameter as `'a` without a value refinement; full interface principality. |
| `call` | Frozen Oracle characterizes the displayed scheme; source candidate routes the invocation through the common output port. | Source-to-complete-interface generation and principal factorization. |
| `compose` | The expected scheme and no-unwitnessed-subtraction condition are explicit. | Transport of `g`'s intermediate value through `f`'s argument entry while its effect remains in the outward allowance, with one complete correlated interface. |
| `twice` | Covariant rows are intended to be flat support, so repeated support is not multiplicity. | Preserve both occurrence paths and sequential continuation while proving one principal allowance. |
| `choose` | Branch views may both fit one allowance while remaining unequal (`{Read}` and `{Write}` into `{Read,Write}`). | Source-generated common allowance and its principal factorization; raw equality merging is invalid. |
| `higher` | Function stages and their evidence remain separate in the coupled-interface proposal. | Prove the shared public `e` factors through both stage views while preserving the intermediate returned Function dependency. |

This audit uses the user's schemes as acceptance criteria. Frozen Oracle output is
characterization only. It found no missing carrier: `Rel_C`, shared `ν,K,D`,
source occurrences/incidence, typed paths, existing subtraction evidence, and
generalization remain the required proof vocabulary, but their sufficiency for
the complete principal extension is unverified. The exact open premise is the
source-generated principal common-allowance extension stated below, not another
per-example rule. The cross-check is recorded in
[the contributor-bound proof attempt](2026-10-04-principal-contributor-bound-theorem.md).

## Common-allowance factorization gate

The shared effect variables in these criteria are public common allowances,
not equations identifying the original branch or call-stage endpoints. The
general source rule needed to derive them is still unproved. Its exact form is
a two-way, same-fiber solution-preservation law: every original source solution
must induce the shared-allowance presentation plus retained original
constraints/evidence, and every such presented solution must reconstruct a
permitted original solution under the same `ν,K,D`. Original invocation
endpoints, scopes, occurrence evidence, and concrete inequalities remain
separate; each invocation view is checked directly against the common
allowance.

This law is stronger than collecting support points or taking a row union.
For example, branch endpoints `{Read}` and `{Write}` can both fit an outward
allowance `{Read, Write}`; identifying those endpoints with each other would
lose that assignment. For `higher`, the stage views likewise remain distinct
and retain their dependency on the first-stage result. For `twice`, both
invocation occurrences and sequential continuation behavior remain, although
the public support has no multiplicity. For `compose`, the `g` contribution
must flow through `f`'s argument interface and stay in the outward allowance
unless existing subtraction evidence witnesses its consumption. No successful
concrete comparisons are composed to justify any of these views.

The missing premise is therefore one source-generated complete-interface
factorization preserving the joint solution fiber while presenting these
simultaneous common allowances. The current concrete-compatibility design
leaves co-occurrence consolidation open and makes support-union results
conditional on a source-derived component-combination rule; it does not prove
this factorization. The branch example above refutes raw equality merging, not
common-allowance principal inference itself.

A finite source-output-effect contributor rule has been recorded as a
proof candidate in [the contributor-bound theorem attempt](2026-10-04-principal-contributor-bound-theorem.md).
It keeps intermediate value endpoints and staged Function values separate,
and phrases each candidate contributor as an existing direct endpoint query.
Independent semantic and authority reviews found no authority violation, but
both identified that the candidate still lacks a source-derived contributor
map; total representability and all-view factorization remain unproved. It is
not a derived theorem or implementation authorization.

If the scheme residual retains the complete original constraints and evidence
conjunctively, the two-way projection obligation has a sharper form. Fix an
original fiber `ξ = (ν,K,D)` and its complete solution set `Sξ`. Let `Qξ(s,a)`
mean that allowance `a` is source-expressible, well-scoped, and passes every
required direct invocation comparison for solution `s`, preserving its
dependencies and public observation. Then the retained presentation
`Pξ = {(s,a) | s ∈ Sξ ∧ Qξ(s,a)}` projects back to all original solutions iff

```text
∀s ∈ Sξ. ∃a. Qξ(s,a).
```

The reverse projection is immediate from retaining `s`; the open proof is
total extension by a representable common allowance for every original
solution in the same fiber. This reduction is conditional on retaining the
original solution coordinates/residual. If the scheme omits any of them, a
stronger reconstruction theorem is needed. Support collection alone does not
prove the extension: `a` must be independently defined by source composition,
not by query success, and must respect branch/stage dependencies, both `twice`
invocations, and `compose`'s unwitnessed contribution.

For principal inference, nonempty extension is necessary but insufficient.
The extension must also be principal: for every valid public Function/effect
view `V`, there must be an admissible generalization/instantiation map `m_V`
through which `V` factors from the generated presentation, without
strengthening direct inequality checks or dropping residual dependencies. The
map may depend on `V`; no single substitution is expected to serve every
alternative view. A merely large allowance could preserve all source
solutions while losing principal precision. Thus the exact open theorem is a
**principal common-allowance extension** over every original fiber, including
both total representability and factorization of all valid views; the formula
above isolates only its totality clause.

An independent architect audit checked whether these principal criteria could
close the active Pure-value callback production bridge. They cannot: principal
projection constrains the public solution family, but supplies no inversion of
complete endpoint-bound membership into the `J_arg`, entry/rebind, body,
designated result-consumer, and `J_call` witnesses required by the production
crosswalk. That is an earlier source-to-endpoint realization obligation. The
remaining premise is stated in [the production design §4](../design/2026-10-04-production-callback-endpoint-generation-draft.md)
and [the direct main-gate audit](2026-10-04-direct-main-gate-attacks.md); this
audit establishes neither a source counterexample nor a new semantic choice.

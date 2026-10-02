# Finite row projection with correlated request capacities

Date: 2026-10-02
Status: Draft; research construction; no implementation authority
Scope: exact symbolic row projection including the register quotient's counting predicates
Approved-by: none for a successor row-domain or acceptance choice
Drafted-by: primary with bounded architect analysis
Reviewed-by: compiler_referee and spec_auditor; scoped M3 package review complete
Supersedes: none; extends the eligible projection fragment without changing source semantics

## 1. The specific missing operation

The open-row package constructs pointwise membership constraints and exact
hiding of eligible local row variables. The register quotient additionally
uses `AtLeast(Q,j)`: there are at least `j` distinct unnamed request points
with unary property `Q`. Its row variables cannot use pointwise hiding.
For example, `Y` and its complement cannot independently supply the same
single witness when the constraints require disjoint witnesses in both.

This package constructs exact hiding **including those correlations** when
the unary predicates are built from the existing row-membership grammar,
family heads, named-point equality and row-independent global conditions.
It gives a finite residual formula, with a derived finite bound on its
counting thresholds. It does not normalize general subtype predicates or
complete callback invocation into that grammar.

This is a new successor mathematical construction, not Simple-sub-original
or a frozen Oracle routing rule. Counting is presentation bookkeeping, not
a new source operator. Both finite-row and arbitrary-subset interpretations
are treated; the theorem selects neither as the language's row domain.

## 2. Input and dependency conditions

Fix a finite family partition `U = disjoint union_f U_f` of typed request
points, and one ordinary type/import assignment `nu`. A point retains its
invariant family arguments. Let `N` be the set of distinct interpretations
of finitely many named point terms. Named occurrences may coincide.
The family partition and point terms do not mention rows to be hidden.

For the finite-row construction, each domain has known finite cardinality
`d_f`, or is known infinite, at this assignment. For a usual parameterless
family the domain is one point. An infinite argument domain can supply an
infinite family domain; arity alone is not a proof of that premise. A
symbolic domain-cardinality condition may be retained if not resolved, but
then total satisfiability of that condition remains outside the theorem.
Domain classifications are fixed construction parameters, or finitely
guarded global cases independent of the hidden rows; they are not discovered
by choosing new type assignments per cell. The all-row satisfiability
corollary below needs domain-capacity information in either row interpretation.

Partition row variables into retained `X=(X_1,...,X_r)` and hidden
`Y=(Y_1,...,Y_h)`. An input block has the form

```text
K(nu) and (forall u. Phi(nu,u,X(u),Y(u))) and B(nu,X,Y).
```

`Phi` is a finite Boolean membership circuit. Every point test is a family
head or equality to a named point. Its other coefficients are finite global
predicates independent of `Y`. Row inclusion/equality from the open-row
grammar is a special case. `B` is a finite Boolean combination of:

- memberships of named points in the rows;
- the same global predicates;
- `AtLeast(Q,j)`, for positive finite `j`, counting points outside `N`,
  where `Q` is a unary Boolean circuit over the same point tests and row bits.

Counts that include named points can first be decomposed into the finitely
many named contributions and the unnamed count. Count-dependent conditions
are outer formulas in `B`; they are not coefficients secretly depending on
`Y` inside `Phi` or `Q`. Finite alternatives remain unions of whole blocks.

All occurrences of an eliminated row must be in this joined block. In
particular, it cannot still occur in an invariant family argument, named
point, global coefficient, unjoined type constraint, or live output `K,D`
dependency. This is existential constraint projection, not permission to
erase a source-owned dependency. Shared `nu` is never chosen independently
per point, color, selection or alternative.

## 3. Construct the finite cells

Let `b=max(1, all counting thresholds)`, `D=2^h`, and `L=b D`.
For a fixed assignment to `nu,X`, define the unnamed retained cells

```text
C_(f,c) = {u in U_f minus N | X(u)=c},   c in {0,1}^r
n_(f,c) = cardinality C_(f,c).
```

Within such a cell, equality to every named point is false. Fixing the
finite global predicate values makes every remaining predicate a Boolean
function of the hidden membership vector `d in {0,1}^h`.

Enumerate a table `t_(f,c,d) in {0,...,b}`. Its meaning is the cardinality
of the full cell capped at `b`; `b` means at least `b`, including infinity.
Separately enumerate hidden bits at each **distinct** named point. Enumerate
named equality partitions first, guarded by the corresponding equalities
and disequalities; equal occurrences receive the same hidden bits. Their
retained bits likewise refer to the same actual retained row assignment.

For each table require:

1. `Phi` holds at every named point and every full cell with `t>0`;
2. every atom `AtLeast(Q,j)` is evaluated by summing the capped counts of
   precisely the full cells where `Q` is true, then capping the sum at `b`;
3. the resulting outer formula `B` holds;
4. the table can partition each actual retained cell, as specified below.

For a threshold `j<=b`, summing capped counts has exactly the same threshold
truth as summing actual counts. No individual witness is reused across
different full cells: their row-bit vectors or families differ.

## 4. Exact partition feasibility and the threshold bound

For one finite retained cell of size `n`, write `t_d` for its `D` entries
and `s=sum_d t_d`.

```text
if every t_d < b:     feasible iff n = s
if some t_d = b:      feasible iff n >= s.
```

Necessity follows from disjointness and the exact unsaturated counts.
For sufficiency, allocate `t_d` distinct points to each hidden color. In
the second case place all remaining points into any saturated color.
Its capped count remains `b`. Thus this is an exact partition criterion,
not an independent nonemptiness approximation.

When no entry is saturated, `s <= D(b-1) < L`. Express `n=s` by
`AtLeast(C,s) and not AtLeast(C,s+1)`, interpreting threshold zero as true.
When some entry is saturated, `s<=L`, so `n>=s` needs only threshold `s`.
Consequently **all output thresholds are at most `L=b 2^h`**. In particular,
large finite retained rows are not truncated: the formula preserves exactly
the distinctions relevant to the given input constraints.

### Finite rows

Assume all retained and hidden rows are finite. In an infinite family domain,
every retained cell except `c=0` is finite. The exterior cell `c=0` is infinite,
because finitely many named points and retained rows remove only finitely
many points. Finitely many finite hidden rows likewise leave its `d=0`
subcell infinite. For that exterior cell the exact criterion is simply:

```text
t_(f,0,0) = b.
```

All other `d` entries can be realized by finitely many distinct points,
choosing exactly `t_d` points even when `t_d=b`. The infinite remainder
has hidden vector zero. Step 1 must therefore check `Phi` on that remainder;
it cannot be omitted because there are no positive hidden memberships there.
The outer capacity predicates also see its saturated count.

In a finite family domain every cell is finite, so use the finite partition
criterion. No infinite row is introduced to discharge a finite-support
obligation. Witnesses need not have a uniform size independent of the
retained rows: a constraint `X subset Y` may require all of a large `X`.

### Arbitrary subsets

If all rows may be arbitrary subsets, use the finite partition formula for
every cell, interpreting `n>=s` also for infinite `n`. This remains exact.
An infinite cell cannot be partitioned into finitely many finite unsaturated
cells. If a saturated color exists, assign it the infinite remainder after
allocating the finite prescribed parts. Hidden rows may then be infinite,
as permitted by this interpretation. No special exterior rule is required.

These are two interpretations of the same construction with different
feasibility clauses. They need not admit the same constraints. Neither
silently stands in for the other in a source typing theorem.

## 5. Elimination theorem and principal residual relation

Conjoin the conditions of §§3–4 for a table, its named hidden bits and its
global/named partition case. Take the finite disjunction over these choices.
Keep `K(nu)` and all retained membership/global/partition guards. The result
`Project_Y(R)(nu,X)` uses only retained rows, named equality, the original
global conditions and retained-cell capacity queries up to threshold `L`.

**Theorem.** In either of the declared row interpretations,

```text
Project_Y(R)(nu,X) iff exists admissible Y. R(nu,X,Y).
```

Forward construction from a satisfying `Y` is its actual named bits and
capped full-cell counts. The membership tests and outer capacities agree
by construction. Its finite or infinite partitions satisfy §4, so its
disjunct is true.

Conversely, a true disjunct supplies named hidden bits and feasible tables.
Partition each actual retained cell by §4, and define `Y_i` to contain
exactly the named/unnamed points whose chosen vector has bit `i`. There
are only finitely many cells and colors. In the finite-row interpretation,
finite retained cells contribute finitely, while each infinite exterior
contributes only the finitely chosen nonzero colors. Thus every `Y_i` is
finite. Membership circuits hold at each point; counted predicates have
the specified truth; the outer block holds under the original `nu`.

The resulting relation is the **exact existential residual**, so no more
or fewer retained assignments are admitted. It is principal as a projected
constraint relation in this fragment. It is not a theorem of principal
source types or of safe source let-generalization. It introduces neither
per-request type assignments nor independent marginal projections of `K,D`.

Finite whole-block alternatives distribute through existential hiding;
conjunctions are joined before hiding any common row. Successive projection
remains in the counting language: a retained-cell query is itself a unary
Boolean membership predicate. Thresholds can increase at each stage but
remain finite. Exact projection therefore composes whenever the stated
dependency conditions permit hiding.

## 6. Effectiveness, transport and the remaining source theorem

There are finitely many named partitions, global truth cases, named hidden
bits and count tables. The table bound is
`(b+1)^(|Families| 2^(r+h))` before pruning. This is a finite but unbounded
construction, not a claim of practical inference cost. Known family-domain
cardinalities suffice for the finite-row exterior case.

With no retained rows, unnamed cells are just the family domains minus
the named points. In either row interpretation, their counts are evaluable
when finite domain cardinalities or infinitude are known. Without that
information, retain the residual domain-capacity queries as symbolic global
conditions: for example, `exists Y. AtLeast(Y,2)` may leave `|U minus N|>=2`.
The construction eliminates all row unknowns, but not an unresolved fact
about the domain. Thus row satisfiability is decidable **at a fixed
interpretation of the endpoint/global conditions, named equalities and
required domain-capacity queries**. Deciding arbitrary underlying
type equality/subtyping is not supplied by a finite list of formula names.

Renaming row binders, named terms and invariant type endpoints consistently
commutes with the denotation of projection by the theorem. Substitutions
may merge named points; the guarded partition cases recompute that equality
pattern rather than assuming distinctness survives. Domain and dependency
premises must still hold. This is symbolic transport; no concrete endpoint
materialization is required, and live incidence is not removed by this law.

The register quotient may use this result when its unary queries have the
displayed membership form. Arbitrary unary subtype tests, point constructors,
unjoined count dependencies and full `OpCompat` remain outside it. Its
finite `Q/P` theorem still needs a source interaction abstraction.

In particular, operation-instance ownership does not close complete
invocation checking. An operation arm executing a supplied callback must
establish its actual entry/capture contract and completed result under the
current store, handler order and shared dependencies. Equal regular value
shape plus row inclusion does not justify replacing a concrete capture
contract by a wildcard (typed-computation-core §7). The next source theorem
must construct that invocation simulation and its finite symbolic closure;
renaming it `CIncl` or enumerating operation/arm pairs is insufficient.

This package removes the nonpointwise row-projection obstacle for the
stated predicate fragment. It gives no class-3 impossibility, acceptance
restriction, lifecycle completion, method/role resolution or implementation
approval. Full generalization, fresh instantiation and SCC intrusion still
must preserve the complete chosen presentation, including dependencies
outside the eligible row block.

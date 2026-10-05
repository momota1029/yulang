# Atomic Record projection with joint admission

Date: 2026-10-05
Status: Frozen exploratory finite characterization; independently reviewed with no findings
Assigned baseline: `0ab7620e167f190691a9ec50fde507d039265aa4`
Assigned branch: `research/simple-sub-intrusion`
Implementation authority: none

## Outstanding premise addressed

The active residual-projection gate in `tasks/current.md` and
`notes/theory/inference-theory-map.md` retains original existential witnesses
until source rules define primitive `Guards/Phi/K,D` and their comparison
context transitions. The reviewed
[admission-retraction derivation](2026-10-05-residual-admission-retraction-proof.md)
provides exact visible-query membership only under total, bisimulation-extensional
admission and a same-coordinate one-way transport condition. Its
[source-premise audit](2026-10-05-residual-admission-source-premise-audit.md)
does not derive that condition from current source rules.

This model discriminates the conjunction and original-witness premises in
one atomic Record case. It does not repeat the previous unguarded structural
image enumeration, enlarge its recursive graph bound, or interpret source
admission. The additional predicates below are supplied finite truth tables.
They are synthetic characterizations, not production `Guards`, `Phi`, or
`nu,K,D`. The question board was inspected before this independent lane;
pending Function-inlet and handler-release choices are not needed, and no
question answer was consumed as authority.

## Exact finite range

Required upper bound: `X <= {a:kappa}`, with hidden rigid identities `kappa`
and `lambda`, visible primitive `Int`, and no lower bounds. All selected
fields are mandatory. The complete model universe is the following four
finite source trees, not the entire structural fiber:

| Source index | Original source | Positive projection |
| --- | --- | --- |
| 0 | `{a:kappa}` | `{}` |
| 1 | `{a:kappa,b:kappa}` | `{}` |
| 2 | `{a:kappa,b:lambda}` | `{}` |
| 3 | `{a:kappa,b:Int}` | `{b:Int}` |

Projection uses the positive Record rule of
[scoped structural projection §3](../design/2026-10-03-scoped-structural-projection.md):
hidden atom fields disappear and visible atom fields remain. Source
admissibility uses the supplied atomic fiber from
[open residual factorization §7.1](../design/2026-10-03-open-residual-factorization.md).
There are two visible values and two canonical graft representatives:
`G({}) = source 0` and `G({b:Int}) = source 3`. In this acyclic atomic case
the closed-copy/fresh-root graft reduces to these representatives.

`Omega = {0,1}` is a supplied complete coordinate list. Its elements are
abstract witness tags, not interpreted scope or effect evidence. Four
permission profiles always permit `kappa` and independently permit or deny
`lambda` at each coordinate. Permissions apply to reachable rigid identities
of the original source; primitives need no permission. The experiment
exhausts all 256 possible Guards tables and all 256 possible Phi tables on
the eight original `(source,omega)` pairs, for each of the four profiles:
**262,144 cases**, with no random seed or uncovered shard.

Each source denotes a distinct finite rooted tree, so no representation
identity, sharing, or bisimulation-sensitive predicate is introduced here.
This finite setting supplies total predicates; it cannot establish those
properties for source-generated predicates or unbounded graphs.

## Reference and candidate comparisons

The exact reference is

```text
Image = { A+(T) | exists omega.
                    Perm(T,omega) and Guards(T,omega) and Phi(T,omega) }.
```

The canonical candidate evaluates that same conjunction on `G(V)` with one
coordinate. The sufficient joint retraction premise is checked separately:

```text
Perm(T,omega) and Guards(T,omega) and Phi(T,omega)
  implies Guards(G(A+(T)),omega) and Phi(G(A+(T)),omega).
```

The script also evaluates two mutations: join the independently projected
Guards and Phi relations while keeping `omega`, or first forget `omega`
and then join their visible marginals. Both lose original witnesses; the
second loses their coordinate correlation as well. Reference and candidates
share the supplied finite tables and exact Record projection. This is an
algebraic finite characterization, not independent source validation or an
implementation comparison.

## Results

| Property | Cases |
| --- | ---: |
| Total enumerated | 262,144 |
| Canonical candidate equals exact image | 178,192 |
| Same-coordinate joint retraction holds | 144,400 |
| Canonical equality without that retraction | 33,792 |
| Canonical candidate misses a valid visible value | 83,952 |
| Joining projected predicates with omega retained adds a false value | 33,920 |
| Joining after forgetting omega adds a false value | 72,556 |
| Each factor separately has exact canonical image, but their conjunction does not | 18,656 |

These categories overlap; their counts are not disjoint totals. Every case
with the joint retraction premise has exact canonical membership. The
canonical candidate never adds a value: an admitted canonical source is
already an original witness. Every same-coordinate retraction of each
individual factor implies joint retraction in this universe. Mere exact
canonical membership of each separate marginal is insufficient.

The script minimizes mutation witnesses by the total number of true Guards
and Phi entries, then by permission profile and table masks.

**Original witness loss even with omega retained.** Guards is true only at
`(source 0,0)` and Phi only at `(source 1,0)`. Both project to `({},0)`;
their projected join accepts `{}`. There is no original pair satisfying
both, so the exact image is empty. This uses two true entries, the minimum
needed for both marginals to be nonempty.

**Coordinate loss.** Guards is true only at `(source 0,0)` and Phi only at
`(source 0,1)`. Joining after forgetting `omega` accepts `{}`, while the
same-coordinate projected join and exact reference are empty. This also
uses two true entries and isolates coordinate loss without changing source.

**Separate canonical coverage does not compose.** Guards is true at
`(source 0,0)` and `(source 1,0)`. Phi is true at `(source 0,1)` and
`(source 1,0)`. Each factor's projected image and canonical test individually
accept exactly `{}`. Their conjunction admits `(source 1,0)`, so its exact
image contains `{}`; neither coordinate admits the canonical source under
both factors. This violates the required same-coordinate joint retraction.
It uses four true entries and is minimal under the stated enumeration/rank.

The last witness distinguishes existential marginal coverage from the
reviewed theorem's same-witness premise. It does not refute that theorem.
The 33,792 equality cases without retraction additionally show that this
premise is sufficient and stronger than necessary in the finite universe;
no claim about a universally necessary source premise follows.

## Verification and omissions

One bounded computation passed:

```text
python3 tools/research_atomic_record_joint_admission_20261005.py
```

The sole process enforced 5-second wall/CPU limits and a 256-MiB address-space
limit, exited zero without timeout, and passed all conditional-reduction,
join-inclusion, explicit mutation, and required-hidden-permission assertions.
There were no builds, Cargo commands, broad tests, performance samples, or
additional search processes. Peak memory and timing were not measured.
Narrow trailing-whitespace checks covered only the two leased outputs.

Coverage omits recursion, Functions, visible rigid atoms, further labels,
additional structural bounds, actual scope/context transitions, source
generation, source-defined `K,D`, admission derivations, and global image
nonemptiness or effective inference. A permission forbidding the required
`kappa` eliminates every original witness, independently of projection;
the script checks that boundary separately from its four main profiles.
No theorem status, production carrier, durable semantic choice, or
implementation authority is promoted.

## Frozen dependency and commit packet

The assigned baseline is supplied by the primary; this child performed no
Git operation. Inspected semantic dependencies were hashed and rechecked:

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-03-open-residual-factorization.md` | `02e6e04d1a4eea405442587206e34c653b45405677d653e6bfec37568fee4f43` |
| `notes/design/2026-10-03-scoped-structural-projection.md` | `b1b7e675902820d6e5d4488c656ab11332b4fc2f54dd64e0fa2cd2e5cf5519a0` |
| `notes/progress/2026-10-05-residual-admission-retraction-proof.md` | `40929e3aa0509e357ec9c9f06db6e547362639eb945eb6e4058eb903060a54ef` |
| `notes/progress/2026-10-05-residual-admission-source-premise-audit.md` | `ac69d1696dbe023d0886d15c0bee0e5e21fca5a189ab89b9b79b3c96bc3587fd` |

Shared locator snapshots at the initial read were
`tasks/current.md`: `55f613e7fb6129da93db1e4ff796784479565cee644f57d3f8c61936a3e38c22`
and `notes/theory/inference-theory-map.md`:
`530da33202926e5054097e9a6924041a79db4bc085ed374a12d11c11e0918f41`.
These are navigation inputs, not authority for a new predicate interpretation.

Exact exclusive outputs:

- `tools/research_atomic_record_joint_admission_20261005.py`
- `notes/progress/2026-10-05-atomic-record-joint-admission-model.md`

Research-only finite characterization; independently reviewed by `spec_auditor`
with no findings in the assigned scope. This is not a source theorem or
production conformance claim.
Proposed commit message: `research: discriminate atomic projection joint admission`
Shared tasks, theory maps, design index, question integration, and Git
integration remain deferred to the primary. Recommended delta after
adjudication: preserve the joint original-witness existential; separate
projected marginals and separate existential canonical coverage do not
establish the conditional theorem's same-coordinate admission retraction.

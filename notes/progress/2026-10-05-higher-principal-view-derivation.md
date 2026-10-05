# `higher`: a conditional source-allocation view construction

Date: 2026-10-05
Status: research derivation; conditional instance of the reviewed A-allocation package
Baseline: `a674fcf72f4b10c0d69dc32e75e04e054fc18e53`, `research/simple-sub-intrusion`
Implementation authority: none
Review: compiler_referee and spec_auditor found no BLOCKING/major/minor
findings within the conditional construction and authority/conformance scopes.
Named-view admission, production resolver conformance, and the full principal
gate remain unproved.

## 1. Claim and boundary

The exact user-directed criterion is

```text
my higher f g x = f g x
  higher : ('a -> ['e] 'b -> ['e] 'c)
         -> 'a -> 'b -> ['e] 'c
```

It comes from [the principal-scheme acceptance record](2026-10-04-principal-scheme-acceptance-criteria.md),
including its `higher` row and proof boundary. In particular, `'a` is generic:
the first argument `g` may be Function-valued, but the criterion does not
require it to be a Function. It also does not equate either invocation's
original effect endpoint with the other's.

There is an explicit conditional A-allocation construction for this staged
view. An independently supplied source derivation must retain the first
invocation's actual returned provider, its dependent contract, the original
state/rebind and second-call continuation. Given the reviewed formation,
coverage, aligned-interface and query hypotheses, set only the fresh common
coordinate to the independent public allowance. The resulting use is through
the actual common export and preserves the original joint constraints.

This constructs a witness for a supplied aligned allocation view. It does
not show that the bare printed criterion supplies those hypotheses, prove
value principality, quantify over arbitrary valid Function views, establish
production source generation, or select Function caller-context quantification.
The exact quantifier retained is

```text
forall V in V_alloc,H(S_higher). exists original-scope finite m_V.
```

The governing conditional contracts are [source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§§2, 3.7, 5–7 and 10. [Factor coverage](../design/2026-10-05-source-factor-cover-and-query-preservation.md)
§§2, 5–7 supplies the dependency-preservation test, not a common-component
formation rule. This record instantiates those hypotheses; it adds no new
descriptor constructor or resolution rule.

## 2. Source occurrences, paths and original fiber

Fix the original fiber `xi = (nu,K,D)` and its original binder tree `T`.
Caller/environment coordinates remain the parameters or binders already
present in that tree. No universal caller-context premise is added here.

The mathematical decorated source graph for left-associated `f g x` has
the following administrative shape:

```text
H0 = lambda(f, result(H1))
H1 = lambda(g, result(H2))
H2 = lambda(x,
       bind(r, call(result(name f), result(name g)),
               call(result(name r), result(name x))))
```

Here `r` labels the source-core result/rebind seam of `(f g) x`; it is not
an extra public source parameter. This graph requires the supplied source
correspondence and entry/consumer contracts of the conditional package. It
is not a claim that current HIR lowers the source this way. The first two
wrappers return inert closures. Their output regions are distinct from the
body region of `H2`; the following inventory does not execute latent bodies
when either wrapper is returned.

Use `ArgV`, `ResV` and `Out` only as path notation for value argument, value
result and complete output guarantee. They are not new representation fields.
The relevant public and invocation incidences are:

| Path/occurrence | Original endpoint or operand | Required retained relation |
| --- | --- | --- |
| `H0.ArgV` | `u_f`, with first-stage Function interface `F1` | The actual first provider, its role/entry and full original descriptor constraints. |
| `H0.ResV.ArgV` | `u_g`, value endpoint `v_g` | The same lexical `g` at the first-call argument path; its existing argument comparison/evidence. |
| `H0.ResV.ResV.ArgV` | `u_x`, value endpoint `v_x` | The same lexical `x` at the second-call argument path; its existing argument comparison/evidence. |
| `F1.Out` | Original provider guarantee `B_1` | First-stage guarantee on that whole `u_f`, with its fixed non-coverage envelope. |
| `F1.ResV` | Returned Function interface `F2` | The dependent returned-provider contract of `u_f`; every actual return selects its same provider `r`. |
| `F1.ResV.Out` | Original returned-provider guarantee `B_2` | Latent second-stage guarantee on that returned provider; its future argument and invariants remain fixed. |
| First call `c_1` | Local output `L_1`, return endpoint `v_r` | Full call clause, including receipt, entry, consumer, returns, requests and continuations. |
| Second call `c_2` | Local output `L_2`, return endpoint `v_y` | Full call clause with receiver exactly the `r` delivered by `c_1` and rebind. |
| `H0.ResV.ResV.Out` / body bind | Original source-node output `E_0` | Ordered composition of `c_1` and its suffix `c_2`, retaining current state and sharing. |
| `H0.ResV.ResV.ResV` | `v_y` | The final result of the same second invocation. |

These are incidences rather than endpoint equations. In particular, this
record asserts neither `B_1 = L_1` nor `B_2 = L_2`, and never asserts
`B_1 = B_2 = E_0`. The ordinary value/structural constraints relating
`v_g`, `F1.ArgV`, `v_r`, `F2`, `v_x`, `F2.ArgV` and `v_y` remain intact.
Reading their eventual public shapes as `'a`, `'b` and `'c` does not derive
those shapes or authorize replacing a concrete local comparison with an
equality. The source solution still contains the original comparison evidence.

For an independent view `V`, its endpoint map `rho_V` has one image for
**each source occurrence**: each name occurrence, both calls, their return
ports, the bind and the three wrappers. It maps shared provider references
uniformly and keeps each fixed declaration/annotation equation. The image of
the original body output is a source-local endpoint `E_0^V`. The separate
public allowance is `W_V`; the public-view rule adds coverage and does not
assign `E_0^V := W_V`. The same distinction holds for `B_1^V,B_2^V`.

## 3. The exact returned-provider seam

The decisive dependency is

```text
first Call return(provider r, current configuration C_1)
  -> original typed rebind of that same r
  -> suffix Call(receiver r, whole argument u_x, configuration C_1).
```

The second provider is not reconstructed from a printed `['e]`, from a
projection of the first output, or from an unrelated member of `F2`.
All copies of the provider, its descriptor, typed result path, captures and
operation/authority dependencies refer to the same original witness.

The first call may expose a request before it returns. In that case the
source bind retains the original request and continuation, attaching the
same pending suffix to the resumed computation at the current resumed
configuration. It does not replay receipt or choose a second provider early.
If the first call never returns, no executed second-call witness is required.
The conservative allocation obligation for the second stage nevertheless
remains. The argument uses neither termination nor an inhabited intermediate
result premise.

The scope of `r` is the original return/rebind binder inside the source
constructor, not a new scheme-level existential. A latent output term `B_2`
can participate in the common component only if it is itself legal at the
common binder scope. Its provider-incidence witness may remain under the
original internal binder. A body-local rigid identity occurring freely in
`B_2` cannot be exported by flattening it. If the supplied derivation has
such an identity without a legal retained scoped presentation, §5.1's scope
premise fails and this conditional construction stops there.

## 4. Coverage certificate and active incidence

Use the source-allocation clauses to derive, under the unchanged scoped
environment `Gamma_V`,

```text
Cov(B_1^V, L_1^V)     Cov(B_2^V, L_2^V)
Cov(L_1^V, E_0^V)    Cov(L_2^V, E_0^V)
Cov(E_0^V, W_V).
```

The first line is the Call allocation obligation, including receiver output.
Each full Call certificate must also cover callee evaluation and any
source-required argument/hygiene contribution in that call's output. Such
contributions are not erased because the source names are pure to evaluate
or because an inferred component has the same spelling. The second line is
Bind allocation; it covers the suffix even when unreachable. The last line
is the independent public guarantee view. The coverage DAG therefore derives

```text
Cov(B_1^V,W_V), Cov(B_2^V,W_V), Cov(E_0^V,W_V).
```

This is logical implication among the retained complete-interface allowance
predicates, at one fiber with all their operands. It is not scalar effect
subtyping or composition of successful concrete inequalities.

The exact same-provider formation obligations are:

| Original guarantee | Added common guarantee | Operand identity that must hold |
| --- | --- | --- |
| `Bound_1(B_1,u_f; N_1)` | `Bound_1(e,u_f; N_1)` | Whole first-stage provider, actual role/entry, argument/future domain and all invariant operands of `N_1` agree. |
| `Bound_2(B_2,r; N_2)` | `Bound_2(e,r; N_2)` | Whole returned provider, its original typed path and second-stage future argument/invariants agree at the same return/rebind binder. |
| Original source output bound at `E_0` | Public output allowance `e` | Same complete body observation and original control/provider incidence. |

Both provider pairs occur semantically in the complete parent admission
clauses. Their matching output predicates occur at the same original whole
observations in the membership/guarantee clauses. `Bound_2` is retained with
the source's own conditional/future-use structure; this table does not move
it outside the binder or require a returned provider for a non-returning
history.

For every changed ordinary descriptor occurrence, its actual `DescMem`
clauses must expose the eligible guarantee leaves plus the fixed non-coverage
predicates. An inert provenance reference or an untouched *old* descriptor
predicate cannot certify that decomposition of the *changed* descriptor.
This is the material additional incidence/interpretation premise of §§2 and
5.1. Equality of the printed `e` occurrences supplies none of it.

Although `f` is in the outer Function's argument position, the proof does
not weaken that complete challenge interface by naked Function variance.
It proves equality of the retained admission clauses via same-provider
absorption. Only genuine provider guarantee leaves change; arguments,
roles, entries, consumers and invariants stay fixed under the supplied
kernel alignment. The future argument at `F2.ArgV` remains distinct from
`F1.ArgV`, even when a particular instance gives them equal value types.

## 5. Joint factors: retaining the seam is sufficient

Let `U` be the complete original coordinate inventory at a permitted scope.
For every independently specified relation clause `A`, its factor interface
`E_A` is **all** its free operands. These include source paths, descriptor
and provider identities, original witness/evidence operands, states, saved
continuations, role/entry/consumer and residual dependencies wherever used.
An opaque Call/Bind/descriptor clause remains one whole factor. Its request
and return alternatives cannot be split by forgetting their common operands.

The necessary seam interfaces include at least:

```text
E_Call1: u_f, u_g, B_1, returned contract F2, original entry/consumer,
         initial/current states, return/provider r when returned,
         request/resumption/continuation and local evidence operands;

E_Bind:  original Call1 result/state witness, typed rebind, r,
         current resumed state, ordered suffix Call2 and continuation;

E_Call2: that same r, u_x, B_2, F2's argument/result paths,
         actual second entry/consumer, state and local evidence operands;

E_Inc2:  F1's returned-provider relation, r, F2, B_2,
         original typed path, binder and all dependent provider operands.
```

These lists identify required operands, not an exhaustive production clause
inventory. Any extra operand of the supplied primitive/descriptor predicates
is included in its actual `E_A`. The scope tree is kept unchanged; an internal
binder is not flattened into an outer coordinate to fit this notation.

A sufficient finite factor-cover certificate retains a bag containing

```text
E_Call1 union E_Bind union E_Call2 union E_Inc2,
```

at the original scope where those operands are jointly present. In a
non-returning alternative, retain the opaque whole Bind/Call clause rather
than inventing an `r` coordinate. The certificate is applied pointwise under
the unchanged binders, never by joining bags from incompatible scopes.
Also retain a covering bag for every other complete factor, including admission,
ordinary descriptor membership, fixed value comparisons, abstraction guards
and residual `Phi`. It may retain the entire original joint graph. Then
`Cover(E,B)` holds by construction and reconstruction of projections of
that **same whole relation** is exact. The old `r` has one identity across
all bags. No independent existential elimination of the first and second
stage witnesses is permitted.

For this construction no projection rewrite is needed: A-allocation retains
the full joint graph conjunctively. The factor-cover result explains why
keeping the seam suffices for relation preservation; it does not generate
the common descriptor. Stage-only marginals omitting a whole dependency
factor are uncertified. The fixed XOR/returned-provider obstruction in the
factor-cover note §5 shows why matching all smaller projections cannot
generally repair that omission. It is not a counterexample to `higher` or
to this retained-joint construction.

## 6. Constructing the actual ordinary use

Assume the independent derivation has the preceding source correspondence,
scope/variance/incidence and aligned non-coverage/value-interface certificates.
Assume its complete Option 2 membership grammar has the paired positive
abstractor, hard guard, invariant parameters and unchanged-admission
certificate of source contracts §3.7. Also assume the local complete-query
conformance hypothesis of §5.3. These are the hypotheses for membership in
`V_alloc,H(S_higher)`; the final common query is not a validity premise.

Build one finite `m_V` by whole freshening and legal uniform graft of the
generated constrained graph. Apply `rho_V` to the source-local endpoints
and shared provider references, retaining all original constraints and
the original scope tree. Set only

```text
fresh common effect coordinate e := W_V.
```

Do not set `B_1`, `B_2`, `L_1`, `L_2` or `E_0` to `W_V`.
The source inventory's constructive totality term

```text
e_s = flat{E_0(s), B_1(s), B_2(s)}
```

is a witness, not an imposed equation on all solutions. Any further selected
contributor in the supplied outward inventory is retained in that same flat
template and has its own coverage certificate. `W_V` covers the entire
inventory, so choosing the fresh coordinate as `W_V` is permitted.

The finite query certificate has the following leaves and congruences:

1. Reference the exact original scoped coverage obligations to prove each
   selected bound and `E_0` covered by `W_V`.
2. For admission, use `Absorb` on each retained old/common provider pair,
   including the pair at `r`. Lift with `Eq-C` through the unchanged Call,
   Bind, return/future-use and wrapper clauses. This gives
   `Eq(D_common,D_V)` without changing a challenge or moving its binder.
3. For membership, use the same absorption at retained incidences,
   `Guarantee(E_0,W_V)` at the public output, and the required eligible
   guarantee leaves of each changed ordinary descriptor. Identity leaves
   apply only to actually unchanged non-coverage predicates and operands.
   Lift with the matching positive constructor clauses to get the base and
   hard-envelope `Le` proofs. Pair every declared positive abstraction
   alternative/parameter and guard; §3.7 lifts those proofs to
   `Le(M_common,H,M_V,H)`. Unanchored extras are included, not filtered
   away by demanding a source execution witness.
4. Introduce the one ordinary whole Function query at the actual roots:

```text
Direct(B_common,H(s,W_V), R_V,H(v); this finite proof DAG).
```

There is no query against a substituted hidden old export and no inference
from two other successful queries. Recursive references, if present in a
supplied provider graph, require the same finite registered equation pairing;
the two named call occurrences are not themselves a recursive unfolding rule.

For each public solution `v`, the independent endpoint derivation supplies
the old source witnesses `s` at their original binders. The construction gives

```text
C_V(v) => exists original-scope s,evidence.
  C_G(s) and Link_rhoV(s,v) and Q(s,W_V)
  and Direct(B_common,H(s,W_V), R_V,H(v); evidence).
```

The displayed existential notation abbreviates `T`, not a rearrangement of
its quantifiers. One finite use graph works over the whole public solution
predicate; it does not choose a new source solution separately for every
runtime challenge. Since that use retains `C_V`, projection adds no public
solutions. The two original stage bounds can be unequal throughout: for
example, coverage of `Read` and `Write` by a common `Read,Write` is compatible
with the retained old bounds whenever all the complete-interface premises
hold. That row example alone does not establish those premises.

## 7. The remaining exact obligation for the named criterion

The staged dependency creates no new obstruction **inside** the aligned,
scoped, active allocation class: retaining it permits the explicit
construction above. The unproved implication is

```text
the named expected higher presentation, with its intended complete validity
  => a supplied certificate placing it in V_alloc,H(S_higher).
```

In dependency order, the first unprovided object is the independently
interpreted source-to-complete-interface/endpoint derivation for the named
source, including its original value comparisons, entry/consumer choices
and the conditional returned-provider contract. The printed scheme supplies
no exhaustive ordinary `DescMem`/admission clauses from which to verify that
`Bound_2(B_2,r)` and `Bound_2(e,r)` constrain the same returned provider in
the complete parent admission. Current HIR does not generate these
applications, and no current HIR claim discharges this object.

Even if that source-base certificate is supplied mathematically, the
following independent premises remain to be verified rather than inferred
from the common printed row:

- scope closure of the latent selected component, including hidden free
  dependencies;
- exact fixed non-coverage kernel and future-input alignment under the
  legal whole graft, without assuming a new value-conversion theorem;
- the independent Call/Bind/public coverage derivation for `B_1,B_2,E_0`;
- active changed-descriptor bound-leaf exposure, exhaustive paired Option 2
  abstraction/guard/admission contracts and local whole-query conformance.

This is a definition/certificate gap, not a source counterexample, rejection
criterion, or evidence for a new carrier. Arbitrary valid views may use other
value interfaces, adapters, domains or abstractors; they remain outside the
proved quantifier. Neither complete scheme principality nor the separate
Function caller-context decision is resolved here.

## 8. Verification and handoff

Method: symbolic source/path and finite-certificate construction; no finite
model or checker was needed. No Cargo/build/test run and no measurements.
Deterministic check: `git diff --check -- notes/progress/2026-10-05-higher-principal-view-derivation.md`.
Because this new file is initially untracked, the same whitespace check is
also applied as a no-index diff from `/dev/null` before integration.

Only this record is producer-owned. The primary should report this as a
conditional named-view derivation with explicit envelope-membership residual,
not as closure of `higher` or of the seven-scheme principal gate. Required
task/theory synchronization and Git integration belong to the primary. No
compiler, tests, shared records or question-board files
were changed by this packet.

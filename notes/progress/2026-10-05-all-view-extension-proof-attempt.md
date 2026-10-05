# All-view extension: unequal abstraction grammars and the missing certificate

Date: 2026-10-05
Status: independently reviewed conditional derivation and reduced proof obligation; research only, no implementation authority
Implementation authority: none
Assignment baseline: `659eb05646bb95f10a991bbb9cefdee55721eea1`
Scope: principal-view open gate 5; no unrestricted all-view closure

## 1. Result and boundary

The paired-grammar restriction in A-allocation-abstraction has a constructive
generalization: the common export and target may use different declared
abstraction relations when their actual clauses have finite local inclusion
proofs. The existing registered-positive-recursion and whole Function rules
then construct evidence for the direct query at the actual common export.
No composition of successful concrete queries or general resolver
completeness is used.

This is a conditional extension of the certificate route. It does **not**
establish that a strictly broader class of independently licensed Yulang source
views exists. The missing object for that stronger conclusion is an independently
valid unmatched grammar with the finite local clause proofs described below.
Changing the allowed proof inputs is not itself a source-realization theorem.

The primary's concurrent source audit reports an actual named-returned-identity
example with a nested `ResV` Function path
(`research_function_realization.rs:1431`) and a separate test-only invocation
at line 1651. This is a bounded actual-source frame for the returned-provider
seam. It supplies no source-allocation certificate, production Apply rule or
direct common-root evidence. This worker did not run or independently audit
that experiment; it is not a premise of the grammar theorem below.

The governing inputs are [source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§§3.7, 5.3, 6–7; [coverage and joins](../design/2026-10-05-callback-coverage-and-source-joins.md)
§8; and [certified use](../design/2026-10-04-certified-callback-and-constrained-use.md)
§§5–6. The [higher derivation](2026-10-05-higher-principal-view-derivation.md)
instantiates the paired class; it does not supply the unequal-grammar proof.

## 2. Exact conditional view class

Fix a source component `S`, original binder tree `T`, fiber `xi=(nu,K,D)`,
and an actually designated common presentation `P`. Assume the common
formation/totality and local resolver-conformance hypotheses of source
contracts §§2–5. Its own old/common presentations satisfy the paired grammar
conditions needed by A-extension. This assumption is retained, not derived
from the new target-side simulation.

After one legal whole freshening/graft, the common and view membership grammars
are independently declared, exhaustive grammars on the same whole tuple:

```text
H_i(R_i) = lfp X. F_i(X)
F_i(X)(y) = G_i(y) and (
    R_i(y) or Z_i(y)
    or exists x,z. X(x) and W_i(x,y,z)),       i = P,V.
```

`R_i` is the corresponding source base; `G_i` is its complete hard envelope.
The ordinary descriptor, genuine guarantees, provider paths, authorities,
residuals and their original scopes are all included. All alternatives of
`Z_i,W_i`, including unanchored extras and abstract-provider future uses,
must already have independently valid primitive/formation contracts.
Their mere positivity does not establish independent validity or admission.

Define `V_sim(P,S)` to consist of finite independently checked views satisfying
source contracts §6's source-allocation, endpoint reconstruction,
non-coverage/value-kernel, scope, incidence and retention conditions, together
with the following certificate inputs:

1. Each side has the displayed independently licensed complete grammar and
   the original unchanged-admission certificate. The original source allocation
   derivation supplies the admission `Eq` proof after same-provider absorption.
2. In the same original scoped environment `Gamma`, finite §5.3 proof DAGs give

   ```text
   Le(R_P,R_V), Le(G_P,G_V), Le(Z_P,Z_V), Le(W_P,W_V).
   ```

   Every local proof applies to actual clauses with their full operands. The
   first two proofs are the allocation construction's base/envelope proofs;
   the last two replace the paired-grammar identity premise. They are not bare
   extensional inclusion assertions or an assertion of final query success.
3. One scope-preserving tuple/parameter correspondence applies to every proof.
   The same original source labels, provider incidences and invariant operands
   are used throughout. Any variation in an eligible coverage operand has its
   actual `Guarantee`/`Absorb` derivation. A changed opaque primitive identifier
   has no identity proof merely because both primitives are conservative.
4. The registered root pair and its defining-operator proofs satisfy §5.3's
   positive recursion rule, accounting for every common-side alternative.
   Any recursion already inside `Z_i,W_i` needs its own finite registered
   pairing; semantic inclusions cannot replace those proofs.

This validity class does not use `Direct(B_common,R_V)` as a checking premise.
It is relative to the already stated local resolution-conformance hypothesis,
as A-allocation itself is. Rigid source binders remain external and pointwise
at their original positions; witnesses are never hoisted across them.

## 3. Grammar simulation with finite query evidence

**Lemma.** The four displayed local proof DAGs give a finite §5.3 proof of
`Le(H_P(R_P),H_V(R_V))` at the actual membership roots.

**Semantic derivation.** Translate a finite common-side derivation by its last
alternative. A source leaf uses `R_P <= R_V`; an unanchored leaf uses
`Z_P <= Z_V`; every hard guard uses `G_P <= G_V`. At an abstract step,
translate its predecessor and use `W_P <= W_V` with the same `x,y,z` and
original dependencies. This gives a target derivation at the same whole
tuple. All source and abstraction recursion is positive and membership has
the declared finite-derivation interpretation. Induction on derivation height
covers every finite abstract chain; applying the same final `Pi` preserves
inclusion. No source anchor is required for the `Z` case.

**Certificate derivation.** Pair the two registered membership roots. Under
the permitted recursive hypothesis `X_P <= X_V`, lift the `W` proof and that
hypothesis through conjunction and the unchanged existential image. Lift
the source and extra proofs through their ordered whole-tuple union. Lift
the result and the guard proof through conjunction. Every constructor's
non-child operands and original scope match. This is a finite `Le` proof
between `F_P(X_P)` and `F_V(X_V)`, so the existing registered-recursion rule
discharges the hypothesis and supplies the displayed root proof. The proof
uses exactly the already stated rules; it adds no union-injection,
primitive-inclusion oracle or new resolution rule.

**Conditional extension theorem.** For every fixed `S,P` satisfying the
preceding common contracts,

```text
forall finite V in V_sim(P,S).
  exists one finite admissible use graph m_V.
    forall public assignments v satisfying C_V(v).
      exists original-scope s,a,evidence.
    C_G(s) and Link(s,v) and Q(s,a)
    and Direct(B_common(s,a),R_V(v); evidence).
```

The existential display abbreviates `T`; it is not permission to flatten
alternating binders. `m_V` is one finite retained constraint graph, not a
different source instantiation for each runtime challenge.

**Construction.** Use the independent allocation derivation to reconstruct
the old source solution at each original occurrence. Preserve all fixed
provider bounds and the source-node endpoint `E_out`. Set only the fresh
common allowance `a := W_public`; this public allowance is distinct from
the abstraction relation `W_i`. Source allocation derives each selected
contributor and `E_out` covered by `W_public`, exactly as in A-allocation.
The existing formation/absorption arguments provide `Q` and
`Eq(D_common,P,D_V)` with independent unchanged-admission evidence.
Use the lemma on the actual complete membership roots. Apply the existing
`Function` rule once to that `Eq` and `Le` proof. This gives the final
`Direct` evidence through the designated common export. It is not a query
through a hidden old root and is not inferred from two other successful queries.

Whole copying/grafting retains `C_V`, all source endpoints, local evidence
and the original binder tree. Consequently certified use §5.2 gives

```text
C_V(v) => Ext_P(v),
projection_public Use(P,V) = C_V.
```

## 4. Inclusion in the old class and unresolved strictness

Every paired `V_alloc,H(S)` instance satisfying these common contracts embeds
in `V_sim(P,S)` by identity proofs for its matched `Z,W` clauses. The new
lemma removes literal relation matching as a necessary condition of this
certificate route; it does not prove that matching was necessary for the
unrestricted theorem.

A possible locally checkable unequal pair has

```text
Z_P(y) = N(y) and Bound_j(E,u(y))
Z_V(y) = N(y) and Bound_j(A,u(y)),
```

where `Cov(E,A)` is independently certified and the whole provider, envelope,
typed operands and scopes agree. `Guarantee` and `Le-C` give the required
extra-relation proof even when the coverage operands differ. The same construction
can apply to a `W` relation. This is a conditional proof schema for already
licensed clauses, not a selection of production extras. If the two operands
are classified as coverage-dependent abstraction parameters, this supplies
the parameter-inclusion certificate deferred in source contracts §3.7.

To establish a **strict source-derived enlargement**, one must additionally
exhibit a valid actual source/view pair of this form with a genuinely unmatched
grammar, satisfying the full hard guard and independent admission contracts.
In particular, enlarging an extra's allowed support does not prove the changed
tuple satisfies ordinary `DescMem`, retained provider identity or original
fixed bounds. A guard can absorb the difference and make both roots identical.
The existing supplied source clauses do not decide that licensing/inhabitation
question. Thus this note claims a broader sufficient certificate schema, not
a proved strict enlargement of the actual source-valid view set.

## 5. Why conservative abstraction alone does not supply the missing proof

There is a two-point algebraic obstruction to deriving the new clause proofs
from source allocation and Option 2 extensivity alone. At one fixed scoped
challenge let

```text
whole tuples = {r,z}
R_P = R_V = {r},       G_P = G_V = {r,z},
W_P = W_V = empty,
Z_P = {z},            Z_V = empty.
```

Then `H_P(R_P)={r,z}` and `H_V(R_V)={r}`. Both abstractions contain the same
inhabited source base and obey the displayed complete guard. Their independent
admission can be equal. Nevertheless the common membership is not included
in the target membership. Two tuple points suffice, and one cannot exhibit
this difference with one point and a shared inhabited source base under
extensivity.

This is an algebraic separation of hypotheses, not a source-realized Yulang
counterexample or a proof that any registered adapter fails. It shows why the
existing source allocation proof cannot manufacture `Le(Z_P,Z_V)` for
arbitrary independently conservative grammars. A same-source conservative
target is allowed to omit a common-only abstract extra. If the relevant
primitive relations are opaque and unmatched, §5.3 has no leaf certifying
their inclusion. If actual source contracts license this separation, even
semantic containment would fail for the displayed direct-containment route;
other resolution evidence would require its own independent theorem.

The smallest newly isolated proof input for the unequal-grammar route is
therefore a finite common-to-view alternative simulation at the actual
`Z,W` clauses, plus the unchanged-admission evidence already required.
For arbitrary views with changed value interfaces, entries, domains or
adapters, the original broader missing premises remain; this reduction does
not cover them.

## 6. Frozen dependencies, checks and handoff

Assignment baseline is the pinned commit supplied by the primary. This worker
used filesystem reads only, with no Git operation. The primary must compare
these dependency hashes with the pinned revision before integration:

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-05-callback-coverage-and-source-joins.md` | `77b7550bdf0a610f0fde4266dcf678d028cf72b8cc6bbb3b1dfaf6a99091cf20` |
| `notes/design/2026-10-04-certified-callback-and-constrained-use.md` | `887bc7c0743d2f34608b46ccb8e5ee9b58ea4a39995b93a5aaced764295bae80` |
| `notes/progress/2026-10-05-higher-principal-view-derivation.md` | `4ef07e440d1d06fc1d83827a505104444ea5741712c5e92f0930330ff2a23e1d` |

Checks: source-section comparison, symbolic derivation of all grammar arms,
finite-certificate rule audit, scoped quantifier audit, and exact two-point
set calculation. A lightweight text check checks trailing whitespace and
verifies the listed dependency hashes after writing. These are producer
checks; no independent review is claimed. No builds, tests, executable
experiments, measurements, Git mutations or delegation occurred. At most
one lightweight local process was used at a time; measurement samples zero.

Changed path: only this leased note. Output is frozen for primary review.
Recommended next action: independently audit whether the displayed operator
proof is admitted by §5.3, then seek one independently licensed unequal
`Z/W` source/view pair; do not enlarge model enumeration before that input exists.

## 7. Independent review and repair

The `compiler_referee` reviewed the full frozen derivation and its cited
dependencies. It found no blocking, major or minor issue in the grammar
simulation, scoped quantifiers, common-coordinate choice, or two-point
obstruction. It did not inspect production resolver behavior or certify
source realization.

The `spec_auditor` found one minor notation defect at the projected direct
query: the common-root operand omitted its explicit `(s,a)` instantiation.
The statement now uses `B_common(s,a)`. This repairs notation only; the
construction already described applying the Function rule to that actual
root. The reviewer found no blocking or major conformance issue and confirmed
that strict source-class enlargement, unrestricted all-view principality, and
production resolver conformance remain open.

Primary delta inspection confirms that the correction changes no premises,
proof steps or claim scope. No additional review round is required for this
minor notation repair.

Commit packet: exact leased path
`notes/progress/2026-10-05-all-view-extension-proof-attempt.md`; assignment
baseline above; reviewed conditional research result; dependency hashes
above, with pinned-revision equality delegated to the primary. Proposed
checkpoint message: `research: derive unequal abstraction grammar extension certificates`.
Shared task/theory/index status changes remain primary/curator-owned; any
accepted summary should retain strict source-class enlargement and all-view
principality as open.

Primary integration status: an earlier managed session could not write `.git`,
so its commit attempt failed and left this note untracked. The current session
has writable Git metadata. `tasks/current.md` and
`notes/theory/inference-theory-map.md` have extensive pre-existing concurrent
staged/worktree changes; their record synchronization remains deferred to avoid
mixing scopes. This artifact remains research-only and does not close gate 5.

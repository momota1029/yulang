# Directional protection in active whole relations and downstream gates

Date: 2026-10-06
Baseline: `e12738d4f1452d87883516dfa5b709a4a5c38230`
Status: independently reviewed conditional relational elaboration and gate reduction
Method: checked relational elaboration and primitive-obligation reduction
Implementation/semantic authority: none

## 1. Target and claim boundary

The selected [directional rule](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
constructs an upper-output protection incidence. The earlier local proof
extended a supplied relation by deterministic records and transported predicates
which did not inspect those records. That result alone does not preserve a
source relation whose typing, admission, or handler observation depends on
protection.

This note instantiates the existing checked-rewrite/whole-transport theorem
with the directional rule **inside the active semantic predicates**. It gives:

1. a pointwise inlining/materialization theorem, including semantic consumers
   of the new incidence, shared recursion and original scoped hiding;
2. an exact sufficient leaf obligation for genuine seed/refined source
   preservation, without independently choosing port or use witnesses;
3. explicit implications, and non-implications, for admission, common
   allowance, all-view principality and Option A/2 production containment.

Item 1 is a relational elaboration theorem over independently interpreted
source-rule presentations. It does not claim that such a presentation has
been generated for every Yulang source. Item 2 exposes that remaining source
premise; it does not prove it by defining both sides to be equal. In
particular, an opaque `FormalSeed` predicate is not silently replaced by the
formula below. No full `FVIEW -> SRC`, `PRIN` or `PROD` edge is closed here.

## 2. Sources and inputs

The current user direction and no-backflow case govern their exact scope.
[Inferred call views](../design/2026-10-05-inferred-function-call-views.md)
§§1.1–5 require one source component, distinct source/public/internal layers,
unchanged actual roles and entry, and original joint `xi=(nu,K,D)`; they leave
complete source judgments and role refinement open.

The proof operations are those of
[certified constrained use](../design/2026-10-04-certified-callback-and-constrained-use.md)
§§2–3: whole alpha transport, checked pointwise rewrites, finite recursive
operator equality, and original-scope joint hiding. Its existing admission
qualification is retained. The
[source-contract package](../design/2026-10-05-source-contracts-and-common-allowance.md)
§§2–3 supplies a **conditional** independently interpreted relation grammar;
§§4–7 supplies the conditional common-allowance and allocation-view results.
These packages are reviewed mathematics, not newly authoritative source rules.

Use a resolved source component `S` with original source facts `H`. A fact
names its original component, binder, scope, use, shared root, directed
constraint occurrence and designated effect-position occurrence. `At` is a
source/proof-stage applicability witness, not a record-arrival timestamp.
Where source generation of `At` is unavailable, it remains an explicit input.
Endpoint substitution acts on endpoints, not on the nominal occurrence tags.

At each original scope, define the already selected incidence relation:

```text
Dir_H(k,u,p) iff there exist original d,r,sigma,U such that
    ProtectedVarAt_H(k,d,r,sigma,u)
  & SourceUpperUse_H(u,d,r,U,sigma)
  & p = the designated output-effect occurrence of that U at u.
```

The equality in the last line is an occurrence/address equality in the
source certificate. It is not equality of effect denotations. There is no
lower-edge arm, endpoint-unification arm, pending-query arm, or blanket
result-descendant arm. Inherited profiles are separate inputs and are never
replaced by `Dir_H`.

For finitely presented original facts this is a finite relational join. The
theorems do not assume that arbitrary source inference already enumerates
all relevant facts finitely. Generalized uses need their existing whole
source-origin transport certificate; they do not create a seed at an external
Name merely because its printed occurrence is unannotated.

## 3. DREL-1: active-predicate directional elaboration

Let `E` be an independently interpreted whole-relation presentation at its
original binder tree. Its free tuple contains the whole `xi`, endpoints,
providers, source incidences and any environment/observation coordinates it
actually uses. It may include original lower bounds, actual role/entry,
provider/result packets, and a protection-sensitive semantic kernel
`Typed`, `DescMem`, `OpenInit`, `Path`, `Observe` or `Visible`.

Assume each relevant primitive has an explicit incidence parameter `M`, or
equivalently a declared interpretation of the predicate symbol `Dir`. Keep
the primitive's independently specified meaning unchanged. This is an
interface hypothesis to check, not permission to infer that an unspecified
primitive has the desired meaning.

Construct two presentations:

```text
E_inline:       interpret every Dir occurrence by the source formula Dir_H;

E_materialized: bind M at the same original scope,
                impose M = Dir_H,
                use that same M in every incident primitive of E.
```

`M` is a proof-level relation definition, not a fresh Yulang type or selected
runtime carrier. A local dependent definition stays below every rigid binder
on which it depends and outside all uses sharing it. It is never separately
bound per port, history, capture or query.

**DREL-1.** Under these hypotheses, erasing the definition `M` yields exactly
the complete relation of `E_inline` from `E_materialized`, with the same
original whole witness, and conversely. This covers predicates that actively
inspect protection. It is not restricted to old predicates independent of
`M`.

**Proof.** Fix an arbitrary full assignment at its original scope. The
definition has the unique value `M=Dir_H`, so every primitive sees exactly
the same whole argument tuple and incidence relation on both sides. This
proves each primitive equality, including a primitive with a negative
protection test; no monotonicity in protection is used.

Conjunction preserves the same shared tuple. Union preserves the chosen
original whole alternative. A relational image keeps the same intermediate
witness, before projection. A scoped existential keeps its original witness
inside its original binder; a fixed universal binder is handled pointwise
without changing its range or exchanging quantifiers. Thus structural
induction preserves every nonrecursive clause.

For a recursive block, hold all recursive relation variables arbitrary. The
preceding argument proves equality of the defining operators **pointwise in
those variables**, with all original operands and equations present. They
therefore have the same designated least/finite-derivation interpretation.
No equality of bare recursive equations is substituted for this operator
equality. Every finite recursive membership/history witness translates;
there is no bound on the number of unfoldings of an individual witness.

The extension from an inline witness uses its own `Dir_H` at its own scope.
Erasure of a materialized witness preserves every original conjunct. These
are the two directions. No `xi`, provider or packet is reselected. QED.

This proof is a concrete checked logical rewrite in the certified-transport
inventory, so its alpha/use/hiding consequences retain that inventory's
side conditions. In a use copy, one map moves endpoints, incidences, `K,D`,
and local definitions together and fixes the appropriate imports. A captured
root remains shared according to its original interface. A type-port quotient
does not quotient source occurrences, boundaries, provider identities or
receipts. Hiding an admission-live witness still needs the separate domain
certificate; DREL-1 does not manufacture it.

### Why active predicates matter

For example, take an independently typed request `q`, a supplied exact
observation/receipt path to upper `p`, and current handler configuration `C`.
Its existing visibility predicate may inspect whether `Dir_H(k,u,p)` reaches
that view. `E_inline` and `E_materialized` feed the same incidence to this
predicate and retain its actual path, receiver activity and grant premises.
Their accepted full tuples coincide even if some tuples are rejected because
of protection. The proof does **not** compare that relation to the old one
with protection omitted. It constructs no request, path, receipt, grant, or
live receiver from a static `Dir_H` fact.

## 4. DREL-2: the actual full seed/refined obligation

To promote an elaboration result to the user's full original-source claim,
let the source independently generate `E_seed` and `E_ref`. Write `w` for
the **entire** original internal tuple at `xi`, including inherited evidence;
let `z` denote only additional proof/local coordinates at specified original
scopes. A sufficient primitive obligation is:

```text
for every original scoped xi,w and arbitrary recursive predicate arguments X,

    FormalSeed_S(xi,w;X)
       iff exists_original_scopes z.
              FormalRef_S(xi,w,z;X),
```

with one coherent witness family `z` across every incidence of the same
source formal. To compose this leaf inside arbitrary larger presentations,
all other uses of `z` must be included in this paired leaf/interface, and
the erasure must commute with their original scoped binders. This is joint
extension, not the separate family
`forall port. exists witness_port`.

In addition, every other changed primitive must have the corresponding
whole-tuple equivalence with identical interfaces or a proved original-scope
joint extension. Unchanged primitives use identity. DREL-1 handles the
directional incidence expression once its source applicability is justified.
The certified-transport theorem then carries these actual leaf certificates
through the entire source relation. For recursive operator transport, any
extra `z` must be internal to the paired clause or retained in the explicit
relation correspondence; one cannot identify least fixed points of operators
on different carriers merely from equality of projected final solutions.

This criterion gives coverage and soundness:

```text
every original seed solution extends coherently to a refined solution;
every refined solution erases to an original seed solution;
all original xi, scopes, provider/result evidence and client constraints stay.
```

It does not claim a unique concrete realization `z`. Deterministic static
incidence does not prove uniqueness of dynamic receiver or typed world
witnesses. Nor does a pointwise solution argument permit exchanging
`exists original w. forall challenges` with
`forall challenges. exists w_challenge`.

### What can already be used, and what is missing

The current user decision supplies the `Dir` primitive for certified
source upper exposures, including its negative lower case. An ordinary
unannotated formal's source seed precedes its own body-use exposure in the
logical constructor dependency; processing an existing lower bound first
does not alter that fact. Uniform transport retains such a certificate.

The ordinary-value `NonHandlerFormal` refinement is not a protection-release
rule. Actual callable roles and entry remain independent coordinates.
Nevertheless, proving that the **complete** `FormalSeed`/`FormalRef`
constraints satisfy the displayed equivalence still needs the source rule
for their role-indexed interface and every contribution/realized-profile
predicate they change. The older `Role_0` inverse on a raw non-role domain
does not prove this leaf.

The precise remaining checks are therefore at semantic leaves, not at
conjunction, recursion, renaming or capture-address composition. They include
source applicability for a genuinely later semantic seed; source-certified
realization of the static fragment at a typed receiving boundary; and the
full role-refinement relation, including multiple-use eligibility/aggregation
outside the approved example. This note adopts no answer to those questions.

## 5. Admission and production: exact consequences

**Q independence.** `Dir_H` has no query input. If the source facts,
applicability certificates and primitive meanings are independently generated
without `Q`, replacing inlining by materialization introduces no `Q`
dependency. This is not a proof that an arbitrary supplied `H` was itself
generated independently: proof dependencies count as inputs.

**All-world contexts.** DREL-1 is pointwise over arbitrary original world,
environment, provider and whole-carrier tuples, including tuples never reached
by the current source program. Therefore, if `OpenInit` has an independent
meaning on the approved all-context domain, the transformation preserves that
entire admission relation. It neither derives `OpenInit` nor replaces that
domain by reached calls, returning-Name carriers, or witnessed invocations.
The initial-context gate in the
[admission attempt](2026-10-06-admission-A-exact-candidate-attempt.md) remains.

**Option A/2.** DREL-1 works with every declared production membership
alternative whose whole-tuple primitives are transported as stated. An
alternative need not have a source-constructor witness. In particular the
source-contract §3.7 unanchored `Z` alternative is preserved by the same
primitive substitution if its full envelope and parameters are preserved;
there is no test for membership in `P_ref`.

If an actual/checked pair already satisfies, on the same original tuples,

```text
D_C(xi) subseteq D_A(xi),
forall c in D_C(xi). P_A(c;xi) subseteq P_C(c;xi),
```

and DREL-1 (or actual DREL-2 certificates) transports **both** sides, then
the same two containments hold after transport. This follows by equality of
each paired complete relation, followed by the original inclusion. It does
not derive a missing inclusion, license unexplained root alternatives,
select `W/Z`, or prove that the production generator has the stated grammar.
The `A` in these subscripts is the actual side, not the common-allowance
theorem or the name of the independently typed initial-context gate.

## 6. Common allowance and principality

The directional rule adds source-indexed protection evidence. It does not
show that changing an effect coordinate changes only a guarantee. Thus the
common-allowance hypotheses remain substantive: fixed challenge domains,
legal scopes, active same-provider incidence, retention of old bounds, and
the actual descriptor's `Bound`-leaf decomposition. If a proposed common
coordinate changes profile applicability or admission, the guarantee-only
absorption proof does not apply merely because the row is covariant.

For a component already satisfying those hypotheses, DREL-1 transports the
same original complete solution relation and direct-query predicates. The
existing totality witness and original quantifier order survive:

```text
forall xi. forall s in S_xi. exists a. Q_xi(s,a).
```

Likewise the existing `V_alloc` / paired-abstraction view theorem keeps its
same finite view class, source constraints, designated common export and
whole use map. This preservation introduces no new all-view coverage.
An unrestricted statement

```text
forall independently valid source view V. exists a finite use m_V
through the actual designated export, preserving every public solution
```

still needs independent validity/coverage and direct-query completeness for
views outside those classes. A normalization of protection evidence cannot
infer those facts. Finite effective representation, general residual solving,
source State/world realization and lifecycle equality are also unchanged.

## 7. Verification and review boundary

This artifact is a proof specialization/reduction, with no compiler or Oracle
execution. The checker in the companion research slice may test finite
instances of full active-predicate filtering; those tests cannot supply a
source primitive or prove the universal theorem. The independent
compiler-referee and spec-auditor reviews checked primitive interfaces, shared
witnesses, recursion/operator scope, admission and Option 2 exclusions; neither
reported a finding on this note. The
[review record](2026-10-06-directional-whole-source-review.md) preserves their
scope. This is not full source soundness or principality.

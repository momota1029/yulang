# REC-DESC finite-reflection proof cut

Date: 2026-10-07
Baseline: `636a2c41f`
Status: conditional proof localization; REC-DESC remains OPEN-PROOF
Claim class: exact classical bridge and unresolved premise localization
Semantic authority: none added; no Oracle semantics used

## Result

Three independent read-only attacks localized the recursion-specific gap after
the finite-history invariant FH. A simultaneous induction on finite
interaction derivation size proves local checks for histories under FH's
pointwise local premises. It does not establish ordinary descriptor
membership for an inert returned Function. At `Return(v_g)`, the handle remains
the original `v_g` with its latent contract; the return step neither invokes it
nor proves the independent `DescMem` conjunct.

The exact missing bridge can be stated as finite-failure reflection, provided
its check judgment has exactly the scopes and quantifiers of FH. Fix one actual
provider, its original descriptor, and the original scoped assignment
`(xi,w)`. Let:

- `S(xi,w)` be the independently established static descriptor, role, entry,
  owner, scope and root obligations;
- `Adm(xi,w)` be the independently interpreted, query-independent domain of
  finite admitted interactions, including the initial inlet, responses, use
  of original raw resumptions, and future calls to the actually returned
  handles;
- `L(d;xi,w)` be the complete joint local typing/check judgment on one
  admitted finite decorated history `d`, retaining its original typed
  incidences, current resumed state, pending suffix, provider identities and
  compatible event-local assignments.

The required characterization is:

```text
S(xi,w) and not DescMem(R,v;xi,w)
  => exists d in Adm(xi,w). not L(d;xi,w).
```

FH must establish `L(d;xi,w)` for every member of this exact `Adm` domain.
Under classical logic, the two statements give `DescMem(R,v;xi,w)` by
contradiction. This is a reformulation of the finite-elimination obligation;
it is not an independent proof of reflection or a definition of `DescMem`.

## Quantifier and coverage conditions

The history domain must retain decorated source witnesses and preserve the
original binder order. If the intended FH premise is instead
`forall h. exists e. L(h,e)`, then a reflected failure must negate that whole
judgment, namely `exists h. forall e. not L(h,e)` over the exact authorized
compatible extensions. Merely finding one bad extension,
`exists h,e. not L(h,e)`, does not contradict `forall h. exists e. L(h,e)`.
Neither histories nor their old `(xi,w)` coordinates may be reselected to
obtain a failure.

The reflection proof must account for all ordinary descriptor clauses:

1. Conditions checkable at the root or before any elimination belong in `S`
   or an explicit zero-step check. A provider with no future call cannot have
   an active latent condition silently skipped.
2. An inert `Return` retains the exact actual handle. Immediate return-shape
   conditions must be checked there; remaining latent obligations must be
   witnessed by a query-independent admitted future use of that same handle.
3. The finite witness must start from the independently valid inlet/world and
   remain in the exact all-world admission domain. It cannot require the
   recursive member validity being established.
4. Requests, responses, raw resumptions and later uses retain the original
   operation witness, current resumed state, pending suffix, live activation,
   shared `xi`, and compatible scope-respecting extensions.
5. `DescMem` is one conjunct of complete membership. Reflection for it alone
   does not prove the separate membership relation `M_E`, carrier/world
   clauses, or the simultaneous complete member judgment in `MEMBER_DISCHARGE`.

If local checks contain existential event-local witnesses, reflection must
negate the whole local judgment with its existential scope intact. A
pointwise failing assignment is insufficient when some other authorized,
compatible extension can pass. Conversely, one bad assignment is a valid
failure witness only if FH quantifies over every such decorated assignment.

## Authority and limits

The approved Function-denotation answer selects complete typed observations
with independently interpreted constraints and directs construction from
existing evidence; it leaves exhaustive endpoint and admission rules as proof
work. The approved membership answer preserves Option 2, allowing conservative
extras without source-constructor witnesses. Source contracts §2.2 keeps
`DescMem` independent of source-image membership; §3.5 assumes constructor
typing lemmas; §3.7 includes `DescMem` in its hard guard and assumes
`R subset G`. The positive finite abstraction grammar therefore cannot prove
the missing source-base/descriptor inclusion on its own.

The source-contract clauses reviewed here give operational composition,
independent admission cases, finite source/reference derivations and Return/
Request equations. They do not provide exhaustive ordinary returned-Function
descriptor introduction/inversion clauses or prove finite-failure reflection.
No Authority-consistent countermodel was found; this bounded failure to derive
reflection is not a non-entailment theorem, impossibility result, repository-
wide absence result, or evidence that a user decision is necessary. The
architecture audit found no new question required yet: the next work is to
localize all active clauses of the single independent interpretation and
derive their finite witnesses, while retaining Option A/2 and the actual
recursive providers. If that localization exposes incompatible meanings or
requires a new observable restriction, return only that semantic seam for a
user decision.

No code, tests, builds, Oracle execution, or semantic decision changed. The
gate remains open; source adequacy, principality and production cutover remain
unproved.

## Inputs and review

- `notes/theory/successor-proof-obligations.md`: `SEM_JOINT`, `FH`, `REC-DESC`,
  `MEMBER_DISCHARGE`.
- `notes/progress/2026-10-07-successor-recursive-synthesis.md`: §§2–5.
- `notes/design/2026-10-05-source-contracts-and-common-allowance.md`:
  §§2.2, 3.1–3.7, 10.
- `notes/design/2026-10-02-source-interface-adequacy-theorem.md`: §§2–3.
- Approved answers for production Function denotation (Option A) and bound
  membership (Option 2).
- Bounded independent methods: constructive finite-history induction,
  Authority-constrained counterexample search, source/contract last-rule
  correspondence, and architecture authority adjudication.

Review status: compiler-referee and spec-auditor review complete; neither found
blocking, major or minor findings. This review certifies only the conditional
logical reformulation and authority boundary, not finite reflection, an
exhaustive descriptor interpretation, actual FH premises or complete member
discharge. No gate closure is claimed.

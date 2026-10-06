# I-call-rest: source witness search and finite derivation cut

Date: 2026-10-06
Baseline: `bb45955082ad885ea63687908b8cf852912c99ed`
Status: frozen research checkpoint; independent review pending
Claim class: bounded non-derivability from supplied constructors; conditional provenance lemma
Scope: `I-call-rest` / `N-call` for the exact approved captured-step component
Semantic and implementation authority: none

## 1. Objective and result

Search for a source-valid original introduction at an effect position beyond
the direct Call's immediate complete invocation, or isolate its derivation
obstruction. The exact selected source is:

```text
my apply f = { my step x = f x; step }
```

No such accepted-source witness is supplied by the governing rules. This is
an incomplete source witness search, bounded to this approved component and
the assigned rule interfaces. It does **not** prove that the source has no
additional original position in the completed language. In particular it does
not discharge `N-call`, prove `Slots_original(beta)={p0}`, or settle `I-formal`.

The reduced obstruction is a first-introduction rule at the one Call. Result
transport can carry an independently introduced callee-result profile; its
input introduction cannot be derived from transport, latent type structure,
or complete invocation behavior alone. The cut below identifies where an
attempt to construct that input stops.

## 2. Baseline, authority and retained premises

All semantic reads use the pinned revision, not concurrent live edits.
Direct dependencies and governing sections:

| Dependency | Sections | Pinned Git blob |
| --- | --- | --- |
| [Inferred call views](../design/2026-10-05-inferred-function-call-views.md) | 2–5 | `9493abd55e61dbc59de31f319c2ff9670204069a` |
| [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md) | 2–3, 10 | `1c2b1a579a9cc7a51d98a4fda755838decb96d07` |
| [Typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md) | 6 | `5e0499e43b3dbf04de0bcdb6c0fa5994224d8a87` |
| [Nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md) | 2 | `704048bc866d1638ef8811e2364a25e31c0ebb96` |
| [Formation-rule attempt](2026-10-06-formal-profile-formation-rule-attempt.md) | 3–6 | `960c22c7626b51b8bd8509d71e544b744a7a6b17` |
| [Call construction](2026-10-06-source-call-generation-construction.md) | 3–7 | `2e9879c162d93f6560889f4738bcaab4ac72be6e` |

The addendum fixes sequential local binding, return of the `step` value,
resolution of `f` to the outer formal, and retention of that same capture.
The call-view decision fixes one shared inferred relation, the provisional
fully protected Handler view, its ordinary-value formal refinement, and
annotation-dependent policy. Absence of an annotation fixes full protection
at applicable positions and no annotation removal grant. It does not provide
an exhaustive inventory of those positions. Actual callable roles/entry,
callback B, original scopes, and one joint `xi=(nu,K,D)` remain unchanged.

The reviewed mathematical packages operate on supplied decorated profiles,
typed correspondences and independently interpreted primitives. They are
conditional dependencies, not additional approved raw-source introductions.
Option 2 production observations without source witnesses are permitted; they
do not constitute the original source witness sought here.

## 3. The finite tree and its only supplied Call introduction

The selected structural correspondence has eleven constructor occurrences:

```text
n0 lambda(f,
  n1 bind(step,
    n2 result(n3 lambda(x,
      n4 call(n5 result(n6 name f), n7 result(n8 name x)))),
    n9 result(n10 name step)))
```

There are two Lambda, one Bind, four Result, three Name and one Call nodes.
The final Name returns `step`; it is not a second Call. The captured name and
formal share the original root `R_f`. No annotation, operation, primitive
declaration, reification, or explicit future elimination occurs in this tree.
These are facts about the selected tree, not an exhaustive surface grammar.

At `c=n4`, the reviewed positive constructor supplies:

```text
u_f=n6 -> d_f; u_x=n8 -> d_x; ordinary Value evidence at u_x
NoAnnotation(d_f); original shared R_f,F_c,sigma
---------------------------------------------------------- Gen-Call-0
beta=(d_f,R_f); p0=(beta,call.effect)
ElimOrigin(c,u_f,d_f,R_f,p0,p_out(c))
```

`p_out(c)` is the complete immediate invocation effect address: receipt,
actual entry, body, designated consumer and return, including suspension
suffixes. It is not a body-only row or outward-support observation. This
constructor creates its static address before solving the Function variable.
Its contribution is exactly the known initial seed. It supplies neither an
original result-profile introduction nor an exhaustive negative inversion.

## 4. Provenance descent and the failed result route

**Conditional lemma.** Suppose a finite witness is assembled from explicit
source introductions, the typed-boundary §6 indexed image operation, and
source-contract §3.4 certified whole-scope transformations. Preserve source
tags and original introduction positions throughout. Every output profile
witness then has an input first-introduction witness. If all first
introductions for `beta` in that derivation are `Gen-Call-0`, every such
witness's original position is `p0`.

**Derivation.** For a profile-image step at current target path `p'`, expand:

```text
chi_out(p',b) iff exists i,p. chi_i(p,b) and M_i(p,p').
```

Choose its retained source witness and descend to the premise. Each descent
strictly decreases finite derivation height. At a certified scheme step,
follow its coherent whole-coordinate witness back at the original scope.
At a first introduction, stop. Relocation of the current observation path
does not change the recorded original introduction position. If that leaf
is `Gen-Call-0`, its recorded origin is `p0`. This proves a provenance lemma
for the supplied composition rules; it does not assert that those rules
exhaust original source derivations.

The strongest apparent route to an extra Call position is the multi-input
result rule. It preserves both the actual result packet and the projected
callee-result profile. The latter route has the finite shape:

```text
? original introduction for beta at a callee-result effect position p_r
chi_callee(p_r,b)          ResultMap(p_r,p_later)
------------------------------------------------------ image
chi_returned(p_later,b)
```

The question-mark premise is the cut. The result rule consumes the supplied
callee-result profile; it does not construct the original applicability of
`p_r`. Typed-boundary §6 explicitly states that profiles are supplied by
elaboration. Its ordinary result correspondence removes the result prefix:
`result.latent.effect` can map to `latent.effect`, while `call.effect` does
not map there. Thus the supplied `p0` cannot discharge this cut by changing
its path spelling.

For the other result input, an actual returned provider may carry inherited
profiles. Their original source tags survive the union. An external provider's
profile is not a fresh introduction for this formal's `beta`. Showing a
provider whose value has a latent result is consequently insufficient. The
missing step would be a separately justified original incidence relating
that provider/result source to this Call's own formal contract, with one
joint witness at the same original scope.

Capture/name transport preserves any supplied `f` packet into the private
environment of `step`. Returning `step` transports its public result view;
it does not expose private captures as public signature positions. Neither
route introduces a new original position. A later source-typed Call/Force
may execute an actually returned provider under source-contract §3.3, but
that rule needs its independent typed port/profile. Later observation cannot
retroactively supply the missing first introduction at this Call.

## 5. Exact obstruction and falsifiers

For this assigned Call leaf, the missing independent source interface is:

```text
resolved c=n4 and original d_f,R_f,sigma; one joint xi
independently justified source contract/declaration/result incidence kappa
---------------------------------------------------------------- I-call-rest [unsupplied]
Intro_original(C,c,d_f,R_f,p,kappa;xi)
```

The line describes an obligation, not a proposed adopted rule. `kappa` must
explain why this original contract contributes this position and which
contribution it governs; it cannot be `Applicable_original` renamed, generic
descriptor well-formedness, a latent-path scan, or successful comparison Q.
To prove `N-call`, one also needs independent local inversion of every original
Call introduction into `Gen-Call-0` or a justified `I-call-rest` case, followed
by proof that no extra case applies to this exact source. That inversion is
the missing exhaustiveness premise, rather than a failure to emit unknown
Function constraints.

This bounded obstruction would be falsified by an independently source-typed
original derivation at this Call with `p != p0`, including its introduction
rule, contribution, source identity and jointly scoped premises. Such a
derivation would refute the exact `N-call` claim and provide an extra-position
witness. A complete independent Call introduction/inversion table with only
the immediate case applicable would instead discharge `N-call`. Neither is
provided by the current assigned sources.

A formal-binder introduction independent of the Call is the separate
`I-formal` gate. It could invalidate full singleton while leaving `N-call`
true; this note does not classify or search that gate. Transport that loses
source tags, independently hides joint witnesses, or invents maps from equal
types invalidates the conditional provenance lemma. Infinite/coinductive
introduction derivations require a different descent argument.

## 6. Checks, coverage and resources

Method: manual constructor accounting and finite provenance descent over the
eleven-node approved tree. No checker, executable source experiment, Oracle
run, legacy rule premise, abstract fiber counterexample, invented complete
grammar, compiler build/test, random seed, numeric enumeration or mutation
campaign was used. No source-valid counterexample is claimed.

Oracle independence means no Oracle transition or compatibility observation
supplies a semantic premise. There is no independent validating oracle. The
conditional lemma and the failed construction share the approved source tree
and the supplied decorated transport contracts; therefore neither validates
the missing original introduction rules. Writing a checker with only
`Gen-Call-0` would merely verify that checker's chosen inventory and would not
prove `N-call`.

Read/check commands already run:

```text
cat rules/research-lab.md rules/design-authority.md rules/git-concurrency.md
git rev-parse HEAD
git show bb4595508:<assigned-path> | sed -n '<governing-section-range>p'
git ls-tree bb4595508 <six-direct-dependency-paths>
git diff bb4595508 -- <six-direct-dependency-paths>
test -e notes/progress/2026-10-06-i-call-rest-source-witness-search.md
```

HEAD initially matched the pinned full SHA. The dependency diff was empty;
no direct dependency hash changed. The target did not exist before creation.
Startup context and the governing index locators were read at the baseline.
An initial combined read was truncated; bounded subsequent pinned section
reads supplied the governing material used here. No conclusion depends on an
unread tail of the combined output.

Resource usage: one lightweight shell command at a time during derivation,
with an independent read batch of five short commands for startup context;
no computation/build workers, Cargo processes, or generated logs. No numeric
CPU/RAM/wall-time limit was assigned. Peak memory, aggregate CPU and elapsed
research time were not measured. Search coverage is the one selected tree
and the stated constructor routes; it is not an enumeration of every accepted
Yulang source, ambient world/import, or future client.

Unverified: original Call introduction completeness; implicit formal origins;
complete contribution policy/refinement; actual receipt and liveness;
source/production acceptance; general recursive or multi-use components;
annotation-result source derivation; independently typed full-world admission;
principality, Option A/2 conformance and production implementation.

Recommended next action: supply and independently review the local original
Call-result introduction/inversion clause against this exact tree. Its source
premises must be established before extending the same decorated toy search.
If it selects a new durable language meaning, the primary owns its approval
route. This report establishes no need to reopen an accepted user decision.

## Commit packet

- Exact lease: `notes/progress/2026-10-06-i-call-rest-source-witness-search.md`.
- Baseline: `bb45955082ad885ea63687908b8cf852912c99ed`.
- Changed dependency hashes: none at the dependency check; pinned blobs in §2.
- Claim/review status: frozen bounded obstruction and conditional provenance lemma; independent review pending; no original-profile gate closure or authority.
- Checks already run: pinned section reads, eleven-node constructor accounting, finite witness descent, baseline identity and narrow dependency diff; no tests/builds/Oracle/Git mutations.
- Proposed commit message: `research: localize I-call-rest to original result-profile introduction`.
- Shared-record deltas left to primary/curator: link this bounded obstruction if accepted; retain `I-call-rest`/`N-call` and `I-exhaust` as open; keep the formal-binder lane separate; do not promote full P, source adequacy, principality, admission or implementation status.

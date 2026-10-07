# World import action: incidence substitution does not descend to closed identities

Date: 2026-10-07
Pinned baseline: `4a9d969db09be881bdc0ce6888cc3d651dfc2405`
Branch assigned: `research/simple-sub-intrusion`
Status: frozen research-only producer artifact; compiler-referee reviewed, no findings
Claim classes: conditional structural counterexample, conditional transport
derivation, and exact missing-premise localization
Semantic / implementation authority: none
Exclusive lease: this file only

## Objective and distinct method

Attack the actual semantic open-import action in world/recursive round 3 §3.
The method is an incidence-substitution derivation and a two-reference
obstruction to substitution on closed provider identities. It does not repeat
the prior false-world Boolean valuation, supplier/alias source construction,
or own-member/world dependency cycle. No ORIGINAL_ASSOC premise is attacked.

The result is conditional: if a legal filling can make a hole reference and
an independently rigid reference accidentally coincide, an identity-only
closed representation cannot support the required substitution. Retaining
their original incidences removes this structural obstruction, but does not
prove the independent import/world predicate is stable under that action.
Closed-filled-root validity, even granted at every importer filling, supplies
neither that stability theorem nor a transport of the original witness.

Scalar exporter validity remains insufficient for the importing incidence:
the source contracts take the independent primitive and constructor typing
rules as premises, and supply no scalar import-installation last rule.
This is a bounded audit of the named rules, not repository-wide
nonderivability or an admitted Yulang counterexample.

## Baseline, governing windows and accepted boundaries

Read the following stable inputs at the pinned baseline:

| Input | Exact window and use |
| --- | --- |
| [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md) | §§2.1–2.2: independent primitive meanings, whole-tuple renaming and descriptor typing; §§3.1–3.5: immutable aliases, separate admission, rigid imports and certified uniform graft; §3.7: Option 2 extras; §6.1: allocation validity is a supplied source derivation; §10: production interpretation and arbitrary source coverage remain open. |
| [World/recursive round 3](2026-10-07-world-recursive-rule-round3.md) | §3: distinct source-owned/imported inventories, the open-import-action row, scalar importing-incidence inference, original witness dependence; §§4–5 are retained own-member boundaries, not this attack. |
| [Initial context construction](2026-10-06-initial-context-source-construction.md) | §§3–4.1: one X, formal callable/whole-carrier holes, supplied joint `Imp_Delta`, no closed target membership for a root containing H_f. |
| [Concrete compatibility](../design/2026-10-03-concrete-compatibility-boundary.md) | §8, “Rigid-hole proof schema”, “Conditional open-graph route”, “Step-indexed open-world candidate”: actual versus hypothetical contracts, source-licensed identity graph, independent free-variable worlds and unchanged original witness scopes. |
| [Scalar import attempt](2026-10-08-init-valid-import-realization.md) | “Derivation and first missing rule”, “Conditional extension”: supplier/local constructor rules do not introduce `Imp_Delta` at the importer; alias construction consumes an installed-root premise. |
| [World localization](2026-10-08-init-world-clause-localization.md) | §§3–5: W0 is the independent open-root/import meaning; W1 is one common interpretation; neither is actual realization. |
| [Shortcut audit](2026-10-08-init-world-adversarial-shortcuts.md) | §§2–3: earlier partial Boolean countervaluation and joint-hiding limits, deliberately not reused as this witness. |
| [Approved inlet answer](../../questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md) | Decisions 1–5: all independent compatible punctured contexts, direct callable and whole-carrier holes, independently valid other bindings, no comparison-defined admission, no new complete descriptor meaning. |
| [DAG](../theory/successor-proof-obligations.md) | INIT-WORLD, REF-WORLD, SEM-JOINT and INIT-VALID. There is no separately named IMPORT node in this baseline; imports are operands of those nodes. |
| [Current task](../../tasks/current.md) | Round-3 world summary and recursive/generalized frontier: scalar installation, semantic open action and latent ordinary Return are distinct cuts. |

Rules read: research-lab, design-authority, git-concurrency and
orchestration-budget. The approved quantifier domain, source meaning,
`EnvStore`, `JointWF`, original B_orig/xi and witness binders are unchanged.
No restriction to source-reachable clients, source-bodied imports, or one new
existential witness shared across fillings is proposed.

## One fixed object and two different transport propositions

Fix one original X, B_orig, xi=(nu,K,D), supplied import/root inventory and
old witness family w at its original binders. Let U^H denote its open import
operands: roots, hole references, rigid imported references, captures, raw
handles, suffixes, incidences, current configuration and dependent witnesses.
This is notation for existing operands, not a runtime representation.

For a legal uniform substitution theta on licensed **open incidences**, write
S_theta U^H for its action. Repeated references to the same hole move together;
rigid imported coordinates remain fixed; all dependent predicates/witnesses
move only where their original dependence licenses it. Role, entry, binder
position, xi and retained K/D incidence are preserved. Event-local witness
extensions remain exactly those authorized by the independent clauses.

Two propositions must not be conflated:

1. **Relation image:** applying the generic Renaming/graft interpretation to
   all operands and the relation itself gives a transported relation instance.
2. **Fixed import interpretation:** that transported instance is valid for
   the independently specified import/world clause at the target importing
   incidence and current configuration.

Source contracts §2.1 supplies the meaning of operation 1. It does not prove
operation 2 for an arbitrary independent primitive. For example, the renamed
image of a relation constraining an operand to one rigid declaration is not
automatically that same declaration's relation after changing the operand.
The certified transformations of §3.4 require their legal joint certificates;
calling a change “uniform graft” does not construct such a certificate for
an opaque semantic import. Section 3.5 assumes the local typing lemmas that
would exclude discarded source witnesses. Section 6.1 adds coverage premises,
not an import/world typing constructor.

## Smallest witness against closed-identity substitution

This witness grants an open occurrence action and tests whether a shortcut
can recover it solely by replacing closed provider identities. It does not
assign truth values to `EnvStore` or `JointWF`.

Assume the following **candidate structural envelope**, whose occurrence
forms are licensed by the source/import interfaces but whose actual joint
admission is not constructed here:

- One semantic imported root r retains two dependent reference incidences
  e_H and e_k at its original scope. Their open operands are H_f and one
  independent rigid provider reference k, respectively.
- Two distinguishable provider identities a and b are available in the same
  permitted endpoint/role/entry envelope. The rigid reference denotes a.
- Fillings sigma_a(H_f)=a and sigma_b(H_f)=b are both legal for this envelope.
  No actual membership at T_checked is a premise; if legality would require
  it, this envelope cannot be used as an admitted-domain witness.
- The equality obtained after sigma_a is accidental co-reference, not a
  source/import equation identifying the rigid reference with H_f in U^H.

At the same original r/e_H/e_k incidences, the required reference pairs are

```text
U^H:                         (H_f, k)
sigma_a U^H, with k=a:        (a,   a)
sigma_b U^H, with k=a:        (b,   a)
```

Suppose the shortcut uses one map t on closed provider identities to perform
the second filling from the first, at every occurrence of an identity. At
e_H it requires t(a)=b; at e_k rigidity requires t(a)=a. Since a differs
from b, no such t exists. QED under the four displayed hypotheses.

This is an established elementary obstruction for that structural envelope,
and only a **conditional structural counterexample** for the Yulang gate.
It is not a complete semantic model, a competing language meaning or a
confirmed independently admitted source. The two fillings are instances of
one fixed open X, not unrelated programs or reselected xi/w. Provider
reference equality is used only where supplied by the filling; printed
endpoint equality creates no identity.

Minimality is relative to this shortcut: two reference incidences, one hole,
one rigid reference, two distinguishable identities and two fillings suffice.
With one identity there is no nontrivial replacement; with one incidence the
two requirements cannot conflict; without rigidity or without a changed hole
there is no contradiction. No global minimum Yulang source size is claimed.

An occurrence-aware closed representation retaining the original labels
e_H/e_k can produce (b,a). It has retained part of the open action data and
therefore escapes this particular obstruction. This result is not an
impossibility of every algorithm consuming closed graphs. The precise failed
shortcut is action on closed identities after forgetting occurrence origin.

## Restricted action law and what it would prove

The weakest needed structural information is a supplied action on the
original import incidences and their dependent witnesses, rather than an
identity map inferred from one filled graph. No globally minimal semantic
axiom basis is claimed.

For each substitution theta that the independent contract declares legal,
the still-missing semantic theorem has this restricted signature:

```text
an independent open import certificate at its original importing incidence
the original joint compatibility certificate for the same X/xi/w
the independent legality certificate for theta and its dependent action
-----------------------------------------------------------------------
the corresponding open import certificate at the transported incidence,
on S_theta U^H with transported original-scope evidence,
and the independent importer root-extension obligations on that same tuple.
```

“Corresponding” needs a proved clause-by-clause identification with the fixed
independent import/world interpretation; merely taking the relation image
does not supply it. Root extension must preserve old external incidences and
introduce the new root obligations jointly. It cannot assume completed
validity of those added roots or an own-member target fact as its premise.

This display is a missing theorem interface, not a new rule of the language
or a definition of the open certificate by universal filling success. It
does not assert target membership of an actual filling at T_checked. Open
typing transport uses formal holes and their licensed assumptions. Actual
plugging additionally needs independently valid actual callable/carrier
contracts and the original joint compatibility/domain premises. Checked-to-
actual domain inclusion, current-state transition closure and complete
future-history validity remain separate proofs.

**Conditional derivation.** If the action theorem and importer root-extension
rule above are independently proved for the selected clauses, apply the
incidence action to every dependent reference and local witness together,
identify the resulting relation with the target import-clause instance, and
apply root extension at that actual importing incidence. Then apply the
ordinary Name/Bind preservation rules to the distinct imported/alias binding
records while retaining the same provider reference. The independent scalar
Literal/Bind lemma supplies the supplier premise only. No new witness is
pulled across a universal binder; the action and any authorized extensions
operate at the original binder positions. This proves only those particular
import/alias instances under the named hypotheses.

Even granting pointwise closed validity at every independently legal filling
is weaker as *certificate data*: it states that each filled root has a valid
certificate, but need not give a map from the original certificate and its
dependencies to those certificates. No exchange of `forall` and `exists` is
required for this observation. One may establish a common action by a further
theorem; an independently chosen certificate per filling does not establish
that theorem by itself. The occurrence witness above discriminates one
concrete identity-only proposal even before semantic preservation is tested.

## Exact blocker, coverage and recommended next action

The first semantic blocker remains the independent last rule establishing
`Imp_Delta` and importer root extension at the original importing incidence.
For hole-dependent semantic imports it must additionally expose the licensed
incidence action and prove identification/preservation in the fixed semantic
family. Supplier scalar validity, closed-root validity and generic relation
renaming do not instantiate that last rule. INIT_WORLD/SEM_JOINT own these
premises; INIT_VALID consumes their proved actual instances. No node is closed
or promoted by this artifact.

There is no executable experiment, Oracle call, bounded enumeration or
random seed. Coverage is the two-incidence structural envelope and the named
source windows. Manual mutations are: retain original occurrence labels
(obstruction disappears), drop rigid reference (disappears), keep the same
hole filling (disappears), or declare open H_f=k (sigma_b ceases to be legal).
These mutations test the shortcut assumptions; none tests Yulang admission.

No independent semantic oracle is supplied. The derivation shares the
independent primitive/typing/action hypotheses with its reference semantics;
it cannot validate those premises. Failure conditions include: the actual
independent contract rules out coincident fillings; no second compatible
provider exists; a supposed rigid reference is actually hole-dependent;
or the proposed closed representation retains sufficient incidence data.
Even when the structural obstruction disappears, semantic preservation can
still fail or remain unproved.

No tests, builds, production code, shared records, question bundles, child
agents, interactive questions or Git mutations were used. Read-only Git
baseline/status inspection was used. Reads were bounded and sequential except
for independent source reads batched in the same tool request. Truncated broad
output was followed by narrow operative-window reads. No whole-repository
search or nonderivability claim is made.

The packet specified no numeric resource allowance. This lane used no compute
search/build workers and imposed a 15-minute wall target. Independent source
reads briefly used at most three lightweight shell processes; mutations and
final checks were sequential. Aggregate CPU/RSS and actual total wall time
were not instrumented. Frozen note checks are readback, trailing whitespace,
local links, lease/baseline and direct dependency hashes. Independent review is
pending; producer reread is not independent certification.

Unverified scope: actual admission of the structural envelope; independent
open-import clauses and their joint interpretation; scalar cross-world
installation; whole-world root extension; State/reference/raw continuation
transition realization; recursive own-member discharge; all-world/future
coverage; Generalize, production conformance and principality.

Recommended next action: extract and independently justify one open import
last-rule instance at the importer with explicit incidence/witness action;
do not run a larger identity-only closed-fill probe.

## Commit packet

- Exact lease: `notes/progress/2026-10-07-world-open-import-action-round1.md`.
- Baseline: `4a9d969db09be881bdc0ce6888cc3d651dfc2405`.
- Dependency changes by this worker: none. All ten direct dependency hashes
  match both their recorded bytes and `git show` at the pinned baseline;
  primary revalidates the snapshot before integration. Frozen hashes are below.
- Review status: compiler-referee reviewed, no findings; no authoritative
  clause selection, full theorem closure or implementation claim.
- Checks already run: named source-window audit, lease absence before creation,
  baseline/status inspection, direct SHA-256 comparison to the pinned revision,
  note readback, local-link existence and trailing-whitespace checks. All pass.
- Proposed message: `research: isolate incidence action for open semantic imports`.
- Shared-record deltas intentionally left to primary/curator: optional
  INIT_WORLD/REF_WORLD/INIT_VALID commentary for the closed-identity shortcut
  obstruction and relation-image versus fixed-interpretation distinction;
  retain existing statuses. No tasks, theory map, DAG or index writes.

| Direct dependency | SHA-256 at production |
| --- | --- |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/progress/2026-10-07-world-recursive-rule-round3.md` | `76c43e03b014bdd99252ff2af229998bc369ff1c2623ec812521d8a24b91fb18` |
| `notes/progress/2026-10-08-init-valid-import-realization.md` | `1bc16ed3df5bdd473ddbec901cb31d43178fb44b564591dddb9d5f1d0df3bd8e` |
| `notes/progress/2026-10-08-init-world-clause-localization.md` | `c32cbc26914dbd9c32fed7b0694f83ad72159f55b5415fe44a0d2219a4e9f1b3` |
| `notes/progress/2026-10-08-init-world-adversarial-shortcuts.md` | `a021cc08a8d6c32b64904716dffae676c25f9179fdb14c50d4fcf9d1c4bb68f9` |
| `notes/progress/2026-10-06-initial-context-source-construction.md` | `10e86ed3bac72d91f03c83acf50ed8e8336ab3c3d0df4a90a03cbe4efdc7ef75` |
| `notes/design/2026-10-03-concrete-compatibility-boundary.md` | `5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16` |
| `notes/theory/successor-proof-obligations.md` | `151089a6dccb3078755e3979bdcad092e12ca53f26d80c0864a79d54b73574a3` |
| `questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md` | `9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3` |
| `tasks/current.md` | `225ae38a8b6c6b7b7856bdee7ba768b637c526485687a1a7f344fb1832ec476b` |

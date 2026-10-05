# Source registration: falsification by invariant inversion

Date: 2026-10-06
Status: Frozen research-only necessity audit; independently reviewed with no findings in its bounded documentary scope; no implementation authority
Baseline: `621d24b77453799e01ce46615ccabf5b30af183b`
Branch inspected: `research/simple-sub-intrusion`
Exclusive lease: this file only
Method: backward invariant inversion and minimized structural witnesses

## Objective and bounded result

Test candidate registration shortcuts for the approved `apply f x = f x`
against the retained shared-interface contract. This is distinct from the
prior forward source derivation and its literal/mixed-use trigger audit.

**Result class:** bounded necessary-condition derivation from authoritative
requirements, with conditional recursive-contract obligations. Destructive
per-use identities, disconnected occurrence roles, independently scoped port
witnesses, and removal of the seed/protection relationship fail those
requirements. These are structural failure witnesses, not accepted/rejected
source programs, compiler counterexamples, or principal-scheme theorems.

There is no accepted-source discriminator here that selects declaration-first
versus use-first allocation, existential versus universal role aggregation,
the exact relevant recursive closure, or an early discharge schedule. Those
choices remain open. In particular, a declaration-first root that retains
source uses through references survives this audit. No candidate policy is
selected.

## Baseline, authority and retained dependencies

Governing originals read at the pinned revision:

- `notes/design/2026-10-05-inferred-function-call-views.md` §§1–3,
  including §1.1, and §§4–5 for preservation/gate limits. Its shared source
  contract is Authoritative, while its concrete source judgments are open.
- Integrated `function-call-view-formation/approved-answer.md`, exact a2
  decisions 1–6. Item 1 selects relevant declarations/definitions/uses and,
  when relevant, the recursive component. Items 4–5 select static identities
  and jointly scoped source constraints. Item 6 leaves detailed rules open.
- `notes/design/2026-10-05-source-contracts-and-common-allowance.md`
  §§2.1–2.2,3.1–3.4,10. This is a Reviewed conditional package, not an
  authoritative selection of its decorated source envelope or production
  membership grammar. Its monomorphic preallocated recursive references are
  therefore used only under its explicit hypotheses.
- Prior `call-view-source-rule-derivation-attempt`,
  `function-formal-seed-elimination-derivation`, and
  `annotation-occurrence-profile-bridge` notes dated 2026-10-06. The first
  locates registration before discharge; the second leaves eligibility and
  aggregation open; the third leaves annotation-to-profile mapping open.

The §1.1 distinction between written annotation, inferred public type, and
internal evidence-rich view is retained. Discharging a seed refines internal
inference state; it does not rewrite written syntax, infer an actual callable
role, or enact effect removal. Static `beta` is not a dynamically activated
receiver boundary. Option A/production membership Option 2 and literal B are
unchanged. No pending local answer draft was consumed.

All semantic reads used `git show BASELINE:path`. Current direct dependencies
were byte-compared to those bytes; every comparison passed. HEAD equaled the
baseline at the check. Concurrent modifications in task/design-index/theory
files and the pending answer archive were observed and preserved. Pinned
`tasks/current.md` lines 984–995 were locator context only.

## Inverting the required shared registration

Use these as proof coordinates, not proposed compiler fields:

```text
s,b             original source component and resolved formal binder f
c,a             resolved callee use f and whole argument occurrence x
F_b             shared inferred formal/interface relationship
beta_b,S_b      original static position and Slots(beta_b)
omega_b         annotation presence/absence and original lexical scope
xi=(nu,K,D)     original joint constraints with typed incidences
E_b             source references relating binder, uses, paths and incidences
Seed_b          provisional protected Handler view for this inferred formal
```

An eventual registration representation may store these inline, reference a
source graph, or recover them through certified transformations. The necessary
condition is that the relationship is available and preserved, independently
of pending comparison `Q`; this note does not require a particular tuple
layout or persistent duplicate metadata.

For the approved example, the required conclusions invert to these premises:

1. The callee name must resolve to `b`, and the argument evidence must refer to
   `a`, the ordinary `x` supplied at that call. A fresh type endpoint alone
   cannot prove either lexical incidence. This is the source direction of §2,
   not a derived general eligibility rule.
2. `Seed_b` and the later `NonHandlerFormal` conclusion must concern the same
   inferred relationship `F_b`. They are not competing immutable actual-role
   equations. The approved example requires a connecting inference derivation.
3. Absence of annotation must remain tied to the original contract/profile
   whose effects are fully protected. Non-Handler determination supplies no
   permission to drop that protection, infer an empty row, or remove `io`.
   The annotated `[io]` case has a separate occurrence-specific premise.
4. Original `beta_b`, `S_b`, source scope and correlated `xi` must survive use
   transport. A fresh use may have freshly renamed logical coordinates;
   **uniform freshening of the whole relationship** is allowed. This does not
   require all distinct polymorphic uses to share the same fresh variables.
5. Any relevant definition/use/recursive incidence must belong to the same
   original relation before its whole-tuple constraints are interpreted.
   The word relevant does not supply a graph-closure algorithm or aggregation
   quantifier. Those premises still need concrete source rules.

These are necessity statements conditional only on conformance to the
approved example/formation requirements. They neither construct registration
nor prove that the listed coordinates suffice for a principal result.

## Minimal witnesses against destructive shortcuts

| Candidate mutation | Smallest witness | Exact failure and qualification |
| --- | --- | --- |
| Allocate an unrelated static slot on every use/activation, with no original-slot correspondence | Two transported occurrences/activations of one registered source position: `origin(c1)=origin(c2)=beta_b`, but mutant records only `beta1 != beta2` | Erases the original position identity selected by §2/a2.4. Two occurrences are necessary to expose this split. Fresh dynamic receiver IDs or occurrence copies carrying a certified common origin are permitted; they are different objects. This is a transport obligation, not a claim that an unproved two-call source program is accepted. |
| Retain only declaration endpoints, erasing definition/use references and all means of recovering them | The approved single call `f x`: the retained declaration has fresh endpoints but no `b <- callee(c)` or `c <- argument(a)` incidence | The required ordinary-value cause cannot be connected to this seed on `F_b`. One approved call already suffices. Declaration-first allocation plus subsequent graph-linked constraints is not this mutation and is not falsified. |
| Give each occurrence an isolated role conclusion with no common formal/interface relation | The same approved example's required provisional `Seed_b` and later formal conclusion are emitted at unrelated roots `F_seed` and `F_use` | No inference derivation connects the two views on the shared relationship, contrary to §§1.1,3/a2.2. Local evidence and local temporary variables are allowed if they feed a shared relation through certified correspondence. This witness does not select how multiple use conclusions aggregate. |
| Hide/freshen original constraints independently per port/segment and combine witnesses afterward | One Function relation with two incidences depending on the same original witness `w`; mutant substitutes independently scoped `w1,w2` without a joint correspondence | Violates the explicit joint-scope requirement even before any claimed principal scheme. Two dependent incidences are structurally minimal for exposing a split. Independent choices might happen to coincide in a particular model; that does not provide the original shared relationship. No distinct semantic results or source satisfiability are assumed. |
| Discharge by replacing the provisional view and dropping its connection/protection obligations without preservation proof | One unannotated formal in the approved example: `Seed_b` is removed and final `F_b` has no retained or certified source of its annotation-absence protection | Cannot explain full protection from annotation absence or the required seed-to-final connection. A proved equivalent transformation may remove a provisional representation while preserving its required relation/consequences. The audit rejects information loss, not early scheduling itself. |

The witness counts measure proof coordinates, not syntax size. None assumes a
second accepted application, an eligible literal, mixed Value/Computation use,
a specific actual supplied callable, or a particular principal public type.
No claim is made that distinct internal records must print different schemes.

The joint-witness row is a scoping failure, not a new toy relation exercise.
The authoritative contract itself forbids independent port choices. The
conditional source contract makes the precise proof seam explicit:
conjunction is on the same whole tuple (§2.1), active clauses share their
original binder environment (§2.2), and transport moves `K,D` and incidences
together without independent segment hiding (§3.4). Checking a product of
independent per-port relations would assume away that seam.

## Recursive scope: conditional obligation and exact blocker

The Authoritative clause includes any relevant recursive component but does
not define relevance, recursive registration, role aggregation, or component
closure. The approved nonrecursive `apply` example cannot distinguish those
extensions. No accepted recursive-source pair with stipulated role/effect
outcomes follows from that example alone.

Under the separate decorated-source hypotheses of source-contract §§2.1,3.1,
a recursive name references a registered relation root; recursive references
are monomorphic/preallocated and names retain dependent provider roots.
The smallest structural check is a one-root self-reference:

```text
original graph: r --recursive-name--> r
mutant graph:   r --recursive-name--> fresh unrelated r'
```

If `r'` has no certified root correspondence, the mutant fails that conditional
source contract. One node and one self-edge are minimal for exposing this
failure; no recursive program acceptance, effect solution, or role conclusion
is asserted. A multi-root cycle is unnecessary for this structural test.
Implementations with lazy registration or another certified representation
are not rejected by the Authoritative direction merely because they do not
literally use this conditional package's preallocation mechanism.

Before a complete source-registration rule can use recursive components, it
must separately prove: source-derived membership/closure of the relevant
component; one registered relation for each resolved recursive root; shared
constraints across its incidences before any permitted generalization; and
preservation under the chosen recursive unfolding/transport semantics. This
is a proof checklist. It does not select SCC construction, phase ordering,
fixed-point role polarity, or the discharge quantifier.

## Why this does not establish principality or source rules

No order of completed schemes, complete solution family, or principal
role/profile rule is supplied by the approved direction. Therefore none of
the structural failures above is advertised as a minimized counterexample to
principality. Preserving the shared tuple is necessary; proving it sufficient
would require formation, satisfiability, generalization, role/profile solving
and a principality theorem on a specified solution space.

There is no executable oracle. The authoritative requirements independently
ground the audit; the recursive check shares the conditional package's supplied
decorations and root interpretation. Prior derivations provide context, not an
independent validation of this note. A checker supplied with a registration
or seed-discharge transition would establish consequences of those supplied
rules, not prove their source legitimacy. Mutations above are proof-interface
mutations only; none was executed. Seeds, numerical ranges, randomization,
performance samples and executable search coverage are not applicable.

The precise blocker to a stronger discriminating accepted-source experiment is
missing source judgments for relevant-component closure and role eligibility/
aggregation, plus missing completed solution/principality semantics. Enlarging
the old literal/mixed-use model would leave that same premise untouched. This
lane stops after the invariant inversion rather than constructing another
transition-assuming probe.

## Checks, resources, omissions and next action

Commands were bounded read-only rule/source captures, `git status --short
--branch`, pinned `git show` reads, Python source extraction and dependency
hash/byte comparisons, leased-note creation, and final lease/hash/whitespace
inspection. Some combined output was truncated; the approved answer,
annotation note and source-contract §10 were reread narrowly. All decisive
clauses are in the successfully captured sections. No global absence claim
or complete repository search is made.

Budget used: 10 sequential top-level lightweight command invocations including
creation and final inspection; Python issued sequential read-only `git show`
subprocesses. At most one command/subprocess was active. No builds, tests,
probes, formatter, Git mutation, shared-file write, question-board write,
child agent or interactive question. CPU, peak RAM and elapsed wall time were
not measured; no numeric resource bound is claimed. The leased path was absent
before creation. Dependencies must be revalidated by the primary at integration.

Unverified: accepted-source grammar/typing beyond the approved shape; source
registration sufficiency; alpha/generalization/instantiation proof; recursive
closure/acceptance; role eligibility/aggregation and seed elimination; exact
annotation-to-profile mapping; complete admission and production Option 2
extras; membership/containment; B-equivalent scheduling; solver implementation,
soundness and principality. No production permission is inferred.

Recommended next action: the primary should sketch a source-registration proof
interface that retains resolved incidences, original static/annotation origin,
seed-to-final correspondence and jointly transported constraints; present exact
recursive closure and discharge aggregation as explicit open premises. Apply
these minimal information-loss checks to that interface before choosing a
solver schedule or using the conditional complete-view results.

## Dependency snapshot

Whole-file SHA-256 values at the pinned revision; every listed worktree file
matched its pinned bytes before writing, and was rechecked at freeze.

| Dependency | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/progress/2026-10-06-call-view-source-rule-derivation-attempt.md` | `0009795b060e3bac47d17437f7350f0e45f0bc1eee4131706e04bd4d44624c4d` |
| `notes/progress/2026-10-06-function-formal-seed-elimination-derivation.md` | `e65825e917b7bebee3f3eec2b4c67d5c359903aa4255966f1a8bf53e745ef0fa` |
| `notes/progress/2026-10-06-annotation-occurrence-profile-bridge.md` | `2ace5a896d205d14a75cf90b582802ffc8477800d87e5f1e9da678a369237a46` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-source-registration-falsification.md`.
- Baseline SHA: `621d24b77453799e01ce46615ccabf5b30af183b`.
- Changed dependency hashes: none against the pinned snapshot during this pass;
  snapshot above. Prior notes' historical snapshots are not substituted for
  current pinned bytes. Primary rechecks baseline/dependencies before integration.
- Review status: frozen unreviewed research-only necessity audit and conditional
  recursive obligation; no independent review, theorem closure or implementation
  authority. Writing stops before submission for review.
- Checks already run: governing-clause/prior-result inspection; pinned/worktree
  byte and SHA-256 comparison; lease absence check; final note whitespace/hash
  inspection. No executable semantic checks, tests or builds.
- Proposed one-line commit message: `research: bound source registration information-loss shortcuts`.
- Shared-record deltas intentionally left for primary/curator: link this audit
  as necessary-condition evidence; retain registration sufficiency, component
  closure, aggregation and principality as open. Do not select a rule, close the
  formation gate, relabel the conditional recursive package, or change pending
  question bundles. Task/theory/index/authority files were not modified.

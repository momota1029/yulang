# INIT_WORLD: localization of the independent initial clauses

Date: 2026-10-08 (assignment date)
Baseline: `8a3f7ecbc0aef25fd448593fea1cf8fd5891ddf4`
Branch: `research/simple-sub-intrusion`
Status: frozen research-only conditional schema; compiler-referee reviewed, no findings
Claim class: bounded source-clause localization and conditional derivation
Authority / implementation permission: none
Lease: this note only

## 1. Objective and result

Localize the filling-independent `EnvStore`/`JointWF` part of INIT_WORLD,
retaining the original initial context, semantic imports, both holes, alias
identities, source scopes and `xi=(nu,K,D)`. The method is constructive
factorization of the approved domain requirements and the displayed PCINIT
premises. No execution model, Oracle, solver, build or test is used.

The approved requirements determine what a complete clause package must
preserve. They do **not** determine the concrete interpretation of every
imported/open root or current source world. The package below is sufficient
only relative to explicitly supplied independent local meanings. It does
not define admission as source solutions, source reachability, or Q success.
Its first missing premise is W0: independently interpreted root/world
introduction and compatibility rules that cover hole-dependent roots as
open roots, including semantic imports without source bodies. Neither
PCINIT nor the body/result Function skeleton supplies W0.

“Smallest” here means a factored interface with six obligation classes and
one shared witness; it is not a proved unique or logically minimal complete
semantics. A formula alone cannot select the open rules behind its leaves.

## 2. Exact governing premises

- [Approved inlet answer](../../questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md),
  decision clauses 1–5: all independently typed compatible punctured caller
  contexts at the fixed original interface/`xi`; direct callable and whole
  carrier holes; independently valid other bindings; no circular comparison;
  no universal source-constructor requirement on Option 2 observations.
  Its [receipt](../../questions/2026-10-05-production-function-inlet-context-domain/receipt.md)
  records integration at `28dddc75f`; both files match the pinned baseline.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2.1–2.2: independent local constructor/descriptor/owner meanings, with
  every incident predicate on the same tuple and original binder tree;
  §§3.1–3.4: preserved immutable provider references and four independent
  admission classes; §3.7: Option 2 extras and their admission certificates;
  §§6–10: allocation premises and production boundaries are conditional.
  This is a reviewed conditional package; concrete clauses remain Draft.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §4, “Initial relation and data”: same source descriptors, lexical/capture
  references and typed evidence; introductions preserve store/activity.
  §6: disjoint source tags, syntax-directed entry and source-owned Normalize.
  §9, “Entry is part of the interface” and “One joint law”: whole carrier,
  body result and complete invocation differ; actual role/entry and the
  complete challenge domain are retained. This remains a scoped Draft.
- [Callback delivery](../design/2026-10-03-callback-context-delivery.md)
  §§2–4, Authoritative: B generates endpoints independently after expected
  boundary delivery; actual existing-provider role/entry survives a slot view;
  static profile identity is distinct from dynamic receiver activation.
- [Concrete compatibility](../design/2026-10-03-concrete-compatibility-boundary.md)
  §8, “Rigid-hole proof schema”, “Conditional open-graph route”,
  “Step-indexed open-world candidate” and “Source-state realization boundary”:
  the checked hole is hypothetical; aliases and saved suffixes stay open;
  world construction is not established; no primitive heap mutation or naive
  greatest fixed point is justified; semantic free-variable worlds remain.
- [Initial source construction](2026-10-06-initial-context-source-construction.md)
  §§4.1–4.4,5,8–9: import-world operands and source-owned open generation;
  [profile/admission construction](2026-10-06-source-profile-admission-construction.md)
  §§5–6: five initial factors and four history cases;
  [independent initial attempt](2026-10-06-independent-initial-admission-construction.md)
  §§2–4: concrete prefixes do not discharge profile, inlet or arbitrary world
  validity. These are prior bounded/conditional results, not W0.
- [Obligation DAG](../theory/successor-proof-obligations.md)
  `PCINIT`, `INIT-WORLD`, `ADMISSION-CLAUSES`, `SEM-JOINT`, `INIT-VALID`;
  [current task](../../tasks/current.md), “Priority frontier:
  recursive/generalized source”: clause formation, common interpretation and
  actual source-world realization are distinct gates.

The current directional upper-output/no-backflow decision is preserved as
an original profile premise. No profile inventory, entry role, reference
semantics or recursive interpretation is selected by this note.

## 3. One shared open tuple

Fix the original scope tree `sigma`, original `xi`, and original source
puncture. Write the initial data schematically as

```text
Z = (context roots, imported roots, rho, C0, source identity references,
     original typed incidences/profiles, operation instances,
     active ownership records, raw handles and ordered saved suffixes,
     H_f:T_checked, H_a:I_argument, distinguished port and result path).
```

These are coordinates already required by the initial schema, not new
runtime or solver carriers. A root table displays the identities supplied
by source resolution/import contracts. Equality of endpoint IDs, printed
types or source positions is not a rule creating those identities.

Retain every root and dependent reference required by the original context
and imports, including latent closures, carriers and saved continuations.
No root disappears merely because it is not executed by the current program.
This obligation specifies coverage of the supplied world, not a computable
finite enumeration of every possible semantic world.

Where a source-licensed reference identifies the designated provider with
`H_f`, an alias remains that reference. Hole dependence is an operand of the
open contract, not a static boolean “contains H” tag. A supplied external
root with no source body requires an independent semantic open contract if
it participates in that dependence. A source-only traversal cannot certify it.

All judgments below are at the same original `(sigma,xi,Z)` with their local
witnesses at their original binders. The notation `exists_sigma w` retains
the original binder tree; it does not prenex or separately hide witnesses.

## 4. Conditional formula package

For an independently supplied semantic family `S`, the factored candidate is

```text
IW_S^H(Z;xi) = exists_sigma w.
    Roots_S^H(Z,w)
  & Identity_S^H(Z,w)
  & Incidence_S^H(Z,w)
  & Current_S^H(Z,w)
  & Interfaces_S^H(Z,w)
  & Puncture_S^H(Z,w).
```

Each factor expands to the following obligations. None is a synonym for
“the complete context is already valid.” Superscript `H` records hypothetical
open typing, rather than checked semantic membership of actual fillings.

| Factor | Required operands and checks | Entailed requirement versus missing rule |
| --- | --- | --- |
| `Roots` | Every original ordinary environment/import root has its independently interpreted descriptor/provider contract. Every hole-dependent root has the corresponding **open** contract at its recorded typed incidence; source-owned roots use their original open constructor derivations, semantic imports use their supplied independent semantic clauses. | Other-binding validity and complete root coverage are approved requirements. Literal/Name/Lambda/Delay structural construction is available conditionally. The exhaustive independent open-import/descriptor introduction rules are W0, still OPEN-SEMANTIC. |
| `Identity` | Original lexical/import/capture/alias references and any source-provided reference/state identities agree across all their incidences. Operation instances, raw handles and suffix references sharing an original witness retain it. | Sharing is required by the source/import contracts. Source Name/capture copying gives a structural case. Exact reference/world identity and compatibility rules for arbitrary admitted imports are open; no universal shared-cell model is inferred. |
| `Incidence` | Each retained role, entry, profile, typed path, origin, receipt and authority record belongs to its original provider/use. Original `K,D` and scope predicates remain incident to those same operands. Slot views do not rewrite actual introduction or entry. | This preservation and B ordering are selected. Complete descriptor/path/profile applicability and licensing are separate open inputs; `Slots(beta)` cannot be guessed from a trace or graph shape. |
| `Current` | One actual current configuration: source-compatible activation order, independently justified live owners/receipts, request/response dependency operands where already present, and original raw continuation/suffix. Expired activations supply no live incidence; saved suffixes supply no restored expired grant. | These are constraints on any valid world. Concrete independent initial source-State/general-reference/imported-continuation rules and their joint compatibility remain open. A static slot ID does not supply runtime activation or cell identity. |
| `Interfaces` | The formal whole-carrier/code interface and designated consumer are retained independently of Q; source-owned argument code has its original code certificate when actually supplied. Whole-carrier contract, complete invocation, source body result and public bound remain distinct. | Inert construction and actual receipt-before-entry are selected/scoped constructor facts. Complete carrier/descriptor admissibility is an independent open leaf, not proved by Value entry or a returned Unit trace. Actual argument realization is downstream of the formal open schema. |
| `Puncture` | Exactly the original callable and whole argument holes, original call/slot/port, result/rebind address and ordered surrounding suffix, with hypothetical interfaces. No actual filling is installed and no target `DescMem(T_checked,f)` or pending Q is checked. | Rigid holes and source-owned puncture/entry structure are the retained PCINIT scope. Their semantic validity/inhabitedness and exhaustive production context coverage do not follow. |

The grouping adds no independence between factors. In particular,
`Roots` and `Current` cannot each choose an unrelated store, imported
operation instance or captured provider. A local satisfying assignment to
each factor is weaker than the displayed one-witness conjunction.

For full INIT_WORLD, `S` must cover every admitted initial world of the
approved domain. Source contracts §3.1's immutable envelope supplies a
restricted construction case. Its exclusion of mutable/opaque imports is
not permission to exclude independently admitted general references or
production-only providers from the approved inlet domain.

## 5. Derivation and first missing premise

Assume the following; they are hypotheses, not adopted rules:

```text
W0  An exhaustive independent root/world clause specification covers the
    six classes above, including open hole-dependent semantic imports.
W1  One interpretation S of those clauses and the descriptor/carrier/local
    predicates exists, with their original scopes and shared dependencies.
W2  The displayed local witnesses coexist at one original Z/xi; in particular
    no root/world proof uses actual checked-hole membership or Q success.
W3  The source-owned PCINIT structural certificates use that same S and Z.
```

W0 is clause formation in INIT_WORLD together with its descriptor/admission
interfaces; W1 is the SEM_JOINT interpretation obligation. W2 is an actual
realization hypothesis when applied to a concrete initial world, not evidence
that every formal schema is inhabited. W3 is the retained conditional PCINIT
construction. These labels identify existing cuts, not new DAG nodes.

**Conditional assembly.** Under W0–W3, assemble `w` from the original scoped
local certificates without changing coordinates. Conjoin `Roots` through
`Puncture` at those binders. Projection to the world/environment incidences
gives the independently interpreted initial `EnvStore`/`JointWF` judgments
specified by W0; retaining the context incidences supplies PCINIT's initial
world factor. This is introduction/conjunction/projection in one supplied
meaning. It neither constructs S nor proves W0/W2 from source syntax.

**Filling independence of the open schema.** Its operands include the formal
hole interfaces but no actual tested callable, actual target membership, or
comparison result. Renaming a source-licensed reference transports every
incident coordinate and `w` together; no alias receives a second filling.
When execution later plugs actual fillings, substitution must act uniformly
on those exact open references, captures and saved suffixes. Actual callable
typing uses its actual contract/role/entry. Actual argument/world validity
requires separate independent witnesses. Open-schema assembly proves neither
checked-to-actual domain inclusion nor preservation at `T_checked` after
plugging, nor unchanged state after execution.

**First missing premise.** W0 is not currently instantiated for a
hole-dependent semantic root sharing the initial source world. PCINIT §4.1
supplies `Imp_Delta` only relative to an independent import interpretation
and expressly forbids certifying a closure containing `H_f` as a closed
target member. Source contracts §2.1 takes the independently typed kernel
as input; §2.2 assumes active root clauses. Core §4 transports already
related initial data, and core §9 identifies but does not construct the
whole carrier/domain relation. None gives the required open-import last rule.

W0 is genuinely OPEN-SEMANTIC, but this bounded inspection is not a
repository-wide nonderivability theorem. Even conditionally granting W0
leaves W1, concrete initial-world realization and all-history coverage open.

**Unresolved branches.** An independently admitted acyclic immutable source
root can use the source-owned open constructor route, conditionally on its
descriptor/port leaves. An external production-only root needs its independent
semantic import route. A cyclic alias/capture/state/continuation component
needs a sound joint recursive justification. Positive finite-derivation
membership clauses in source contracts §2.1 do not select a fixed point for
negative Function domains or source-reference worlds. Guarded/step-indexed
interpretation is a candidate proof method; naive greatest-fixed-point
membership, static graph-shapedness and closed-program reachability are not
established alternatives. No pair of complete competing admitted meanings
has been constructed, so no user decision is requested.

## 6. Smallest symbolic discriminator and failure conditions

One existing Name alias suffices to expose checked-membership circularity:

```text
H_f:T_checked                  hypothetical callable root
rho(y) = H_f                   one original source Name alias
OpenName(y,H_f;T_checked)       permitted structural open premise
```

If a proposed initial-world clause treats `y` as an ordinary closed import
and requires `DescMem(T_checked, rho(y))`, then after uniform plugging
`rho(y)=f` that clause is exactly `DescMem(T_checked,f)`. Admission would
assume the membership under test. Removing `y` instead loses the original
source alias. Keeping `y` under the open contract retains the source reference
without asserting actual checked membership. This is a minimized logical
discriminator: one hole and one alias, with no invocation or state update.
It is not an independently admitted Yulang counterexample, a new import
semantics, or a proof that the full open-import rule exists.

Other premise mutations are logical failure checks, not executed tests:

| Mutation | Failure condition |
| --- | --- |
| Independently instantiate roots and world factors | Shared provider/state/operation witnesses need not coexist; violates W2. |
| Admit only roots reachable from current closed source | Omits the approved semantic free-variable/future-context domain. |
| Accept any graph with matching labels or endpoints | Provides neither descriptor typing nor source-licensed world compatibility. |
| Require every imported provider to have a source body | Excludes independently permitted Option 2 roots. |
| Require a return to certify the argument hole | Excludes permitted divergent/suspended whole carriers. |
| Turn a captured suffix into live authority | Revives expired ownership without a current source-world rule. |
| Read `StateSlotId` as shared cell identity | Adds a source-state meaning absent from the governing clauses. |

No enlarged identity trace or equivalent empty-world probe was run. Such a
probe leaves W0 unchanged; the next method must construct the independent
open-import rule or audit a claimed source rule supplying it.

## 7. Checks, resources and omissions

Checks performed: read the three required rules in full; inspect exact
governing sections and prior construction cuts; read the applicable committed
inlet answer/receipt; compare every input named below byte-for-byte with the
pinned Git revision and compute SHA-256; inspect this note's scope. These are
source/dependency checks, not independent review or compiler verification.

Oracle independence: no Oracle behavior or output is used. The derivation
and source packages share W0–W3 and their local contracts; a checker
implementing this formula would establish consistency relative to those
supplied rules, not that the source entails W0. Seeds/ranges: none. Executable
mutations/searches: none. Search coverage is the cited sections only.

Resource envelope: one serial lightweight process at a time, no Cargo,
builds, tests or child agents; <=15-minute assignment budget. No CPU-time or
peak-RSS profiler was run, so those measurements are unknown. No generated
logs, temporary outputs or research checker were written.

Unverified: concrete import/descriptor/carrier clause selection, joint
recursive interpretation, actual initial-world inhabitants, reference/State
source realization, handler/continuation closure, complete production
context coverage, checked-to-actual domain inclusion, soundness/principality,
compiler conformance. Required shared records are left to the primary;
INIT_WORLD, SEM_JOINT and INIT_VALID remain at their current statuses.

Recommended next action: construct or identify the independent open semantic
import introduction for one hole-dependent root sharing a supplied original
world, with explicit descriptor/identity/incidence operands and a justified
recursive branch. Return that rule for authority adjudication before using
it as W0; do not repeat a source-only identity execution probe.

## 8. Frozen dependency snapshot and commit packet

Direct SHA-256 values at the pinned baseline (working bytes matched):

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| `notes/design/2026-10-03-concrete-compatibility-boundary.md` | `5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16` |
| `notes/progress/2026-10-06-initial-context-source-construction.md` | `10e86ed3bac72d91f03c83acf50ed8e8336ab3c3d0df4a90a03cbe4efdc7ef75` |
| `notes/progress/2026-10-06-independent-initial-admission-construction.md` | `4feb8131e9360ba8508b0eace82d882e446433d5b5f75beee402027e4986284f` |
| `notes/progress/2026-10-06-source-profile-admission-construction.md` | `00f9e4e8db427fe97a46bd25245cf235c02d2e38007c5b9bb9088d9b40db8636` |
| `notes/theory/successor-proof-obligations.md` | `1b4d27e80fb8437fc78adde55853cdbd7b5cc0a9e819c7eb3474dc83a09aeeb3` |
| `questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md` | `9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3` |
| `questions/2026-10-05-production-function-inlet-context-domain/receipt.md` | `a952c4588f6020ba1c51f69c623bf12ef695d73fe086496bf6ecdeee37450021` |

Commit packet:

- Exact leased/changed path: `notes/progress/2026-10-08-init-world-clause-localization.md`.
- Baseline SHA: `8a3f7ecbc0aef25fd448593fea1cf8fd5891ddf4`.
- Changed dependency hashes: none observed; recheck against integration HEAD.
- Claim/review status: frozen research-only conditional localization;
  compiler-referee reviewed with no findings; no semantic adoption or gate closure.
- Checks already run: governing-section inspection; committed answer/receipt
  inspection; pinned-input byte comparison and SHA-256 inventory; narrow
  note whitespace/path inspection. No tests/builds/Oracle/Git mutations.
- Proposed commit message: `research: localize independent INIT_WORLD clauses`.
- Shared-record deltas intentionally left for primary/curator:
  add this bounded W0 localization as evidence at INIT_WORLD and reference
  its distinction from SEM_JOINT/INIT_VALID; preserve all gate statuses and
  existing dependencies. Do not edit authority/index/question bundles or
  promote candidate predicates to selected semantics.

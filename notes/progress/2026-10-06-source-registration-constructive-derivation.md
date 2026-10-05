# Source registration: constructive derivation for unannotated `apply`

Date: 2026-10-06
Status: Frozen research-only premise audit; independently reviewed with no findings in its bounded documentary scope; no implementation authority
Baseline: `621d24b77453799e01ce46615ccabf5b30af183b`
Exclusive lease: this file only
Method: forward derivation, stopping at the first missing registration premise

## Objective and claim class

Try to construct the first source registration for `apply f x = f x`: one
shared inferred formal interface, its `beta`/`Slots(beta)`, stable endpoints,
typed source paths, owner/receiver incidence, and original joint `(nu,K,D)`.
Use the approved source direction and the displayed existing rules, without
turning proposed judgment names into rules.

**Result: bounded characterization of the available derivation.** The ordinary
parameter/name rules construct two fresh value endpoints and preserve their
lexical references inside this body. The application rule can generate a
callable constraint at the endpoint for `f`. Neither step constructs the
shared role-indexed contract that gives that endpoint a static slot/profile.
That endpoint-to-contract registration is the first missing premise. Typed
profile/receipt construction, the joint constraint fiber, and the later
provisional-Handler discharge cannot be reached without it.

This refines the earlier registration blocker by separating ordinary endpoint
and source-label allocation from semantic registration. It is not a new
counterexample, an impossibility proof, a principal-inference theorem, or a
completed source rule. The earlier note's proposed `RegisterFormalView` name
is treated only as a description of the open obligation.

## Governing sources and exact premises

The approved direction is [inferred-call-views](../design/2026-10-05-inferred-function-call-views.md)
§§1–3, especially §1.1's distinction between written annotations, inferred
public schemes, and internal views. Its §2 explicitly leaves the exact
construction judgments open. The integrated approved answer
`function-call-view-formation/a2`, items 1, 4–6, independently records the
shared source component, position/contract origin of `beta`, and joint scope.
Item 2 records the example's internal fully protected Handler seed and its
ordinary-value resolution; it supplies a selected result, not a displayed
inference rule deriving the registration.

Additional rules inspected at the pinned baseline:

- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §6, parameter table at lines 335–347; role/receipt caveat at 349–358;
  structural table at 396–405; call constraints at 412–423; coherence and
  substitution qualifications at 444–487. This construction is Draft with
  reviewed conditional results, not an independently approved new semantics.
- Typed core §9, lines 988–996 and 1050–1083: port construction/sign
  propagation operates on a resolved graph with supplied typed profiles and
  correspondences; it preserves original slots rather than creating them.
- [Callback delivery](../design/2026-10-03-callback-context-delivery.md)
  §§1–2.1 and 4: the known instantiated callback contract, `beta`, and original
  profile are inputs. B independently generates literal endpoints; existing
  supplied callable roles and entries remain their actual roles and entries.
- [Source-generated theorem](../design/2026-10-04-source-generated-callback-structural-theorems.md)
  §2.1, lines 71–91: source labels/binders are preallocated, while decorated
  owner/view witnesses are supplied before the query. §2.3, lines 153–165,
  uses already selected static correspondences. §2.6, lines 250–265, requires
  complete typed views/path maps already in the instruction schema. §3 Initial,
  lines 322–353, requires the known slot, typed profile/path, decorated context,
  and joint fiber.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2.1–2.2, lines 79–142: original binder tree, typed kernel and active
  incidences are interpretation hypotheses. §§3.1–3.3, lines 155–222:
  roles, paths, owners, receipts and original shared tuple are source inputs;
  emission/admission inventories retain them.

Line numbers are pinned-baseline locators. The design sections are the
governing references if later unrelated edits move those lines.

## Forward derivation tree

Explicit hypotheses for the available conditional construction:

1. H1: an admitted finite ordinary definition has resolved parameter binders
   `b_f,b_x` and name occurrences `u_f,u_x`; the displayed parameter/name rules
   apply. Raw parsing/resolution is outside this derivation.
2. H2: unknown value endpoints remain symbolic, with consistent fresh naming.
   No known completed Function interface, profile, or typed receipt for `f`
   is supplied by H1 or H2.
3. H3: ordinary applications generate the typed-core §6 call obligations;
   generating an obligation does not certify its premises or solve it.

Let `c` name the body call occurrence. All these identifiers are proof labels,
not new source constructs or proposed runtime objects.

```text
unannotated binder b_f                 unannotated binder b_x
  | core §6 parameter table             | core §6 parameter table
P_f = Value(A_f)                      P_x = Value(A_x)
Gamma(b_f) = Value(A_f)               Gamma(b_x) = Value(A_x)
  | name u_f resolves to b_f            | name u_x resolves to b_x
I_f = Value(A_f), d_f = name b_f      I_x = Value(A_x), d_x = name b_x
  | Result / Normalize                 | Result / Normalize
Result(I_f) = Comp(empty,A_f)         Result(I_x) = Comp(empty,A_x)
n_f = result(d_f)                    n_x = result(d_x)
                 \                  /
                  core §6 application
             I_c = Computation(E_c,A_c)
             d_c = reify(call(n_f,n_x))
             n_c = Normalize(I_c,d_c)
```

The last row generates constraints: identify a callable interface at the
result endpoint `A_f`; relate the **whole** `Result(I_x)` to that interface's
parameter; retain typed path/contract obligations and the complete invocation
relation for symbolic `E_c,A_c`. It does not assert that those obligations
have solutions. In particular `E_c` is not defined as an argument/body row
union, and `A_x` is not asserted equal to a candidate callable input endpoint.

The `P_f,P_x` entries belong to the enclosing definition. They say how `apply`
receives its parameters. `P_f=Value(A_f)` does not specify the receiver role or
entry of the callable denoted by `f`. `I_x=Value(A_x)` is ordinary-value
evidence even if a later admissible substitution makes `A_x` latent. No
execution, concrete Pure value supplied to `f`, or successful comparison is
needed for that tag.

This derives fresh ordinary endpoints and their same-body lexical sharing.
Core §6's substitution theorem is conditional on preservation of tags,
typed paths and typing premises. It does not establish endpoint/profile
stability under generalization or arbitrary use-time instantiation. The
preallocation convention in theorem §2.1 can likewise allocate source labels
under its decorated-graph hypothesis; a source label alone is not `beta`.

## Exact first missing premise

At the point where the application needs a role-indexed callable interface
for `A_f`, the available tree has only a fresh value endpoint and a lexical
reference. The missing premise is:

> The resolved formal `b_f`, its absence of annotation, and its relevant
> declaration/definition/use component register one shared inferred callable
> contract at `A_f`, carrying the approved internal protected Handler seed and
> original source-position/profile relationship, before any use of `Q`.

This is an English proof obligation, not a newly defined judgment. Its immediate
missing link is **from the ordinary binder endpoint to the shared role-indexed
source contract**. Merely naming a fresh Function variable does not establish
that link. Merely assigning `beta := b_f` does not construct `Slots(beta)` or
prove that generalization/uses preserve the same contract. The approved §2
requires the position **and its contract** to form the stable slot.

The following demanded outputs remain behind this link:

| Output | Available forward evidence | Remaining obligation |
| --- | --- | --- |
| `beta`, `Slots(beta)` | Resolved binder/use labels; no annotation | Contract-to-position registration and profile inventory; a label is insufficient. |
| Stable callable endpoints | Fresh `A_f`, `A_x`, symbolic `E_c,A_c` | Common inferred interface endpoints and preservation through generalization/use. |
| Typed paths / `Flow` | Lexical name references and generated call obligations | Typed carrier/result receipt paths at the registered interface; lexical lookup is insufficient. |
| Owner/receiver incidence | Enclosing parameter entry skeleton | Slot-view/actual-invocation incidence with distinct receivers/receipts; no dynamic boundary is minted here. |
| One original `(nu,K,D)` | Symbols retained by conditional core relations | Source-component constraint/binder generation linking all incidences jointly; no satisfying assignment is constructed. |

None of the audited alternatives fills the first link. Callback delivery §2
starts from an already instantiated `F_cb,beta,Slots(beta)` and a known literal
slot; this example supplies an inferred formal instead. Theorem §2.3 translates
already decorated nodes, and §2.6 can add total derived coordinates only where
the required views/paths already exist. Source-contracts §3.2 inventories the
required incidences under §3.1's supplied kernel. Core §9 propagates signs over
already typed correspondences and expressly retains original slots. These
constructions preserve or interpret a registration; they do not derive this
registration from H1–H3.

Stop here. Later seed discharge is a separate open rule and is not attempted.
The approved seed is an internal inference view, so treating it as an actual
Handler-role fact to be contradicted later would change the selected meaning.
No generic Value-entry-implies-non-Handler rule follows from this tree.

## Evidence quality, failure conditions, and omissions

Method: documentary forward proof construction and a bounded rule-conclusion
audit. There is no executable oracle or comparison to production. The sources
predate this note and are independent inputs; the conditional core proof and
a future implementation would share H1–H3. Their agreement would not prove
that missing registration rules follow from the approved direction.

No seeds, numeric ranges, mutations, tests, builds, probes, or performance
measurements apply. The source witness is exactly the approved `apply` body,
without annotation or a concrete supplied callable. It is a proof-obligation
witness, not an asserted rejected or accepted executable program. No exhaustive
search of all repository rules is claimed.

A candidate derivation fails this gate if it assumes the missing contract in
`Gamma`, replaces original profile formation with label allocation, imports
conditional theorem decorations as conclusions, uses `Q` to create a path or
slot, independently solves ports then combines witnesses, or infers an actual
callable role from the enclosing formal's Value entry. This audit would need
revision if an in-scope existing source rule constructs the missing registration
from H1–H3 without those added premises; its exact rule and scope would be the
discriminating evidence.

Unverified: component closure and recursion; raw resolver correctness; contract
formation and provisional protection; typed receipt/owner construction;
original joint constraint generation and satisfiability; discharge eligibility;
annotation contribution mapping; generalization/use preservation;
uniqueness/principality; complete independent admission; production Option 2
extras; source adequacy; B-equivalent scheduling; production conformance.

Recommended next action: supply a narrow source registration rule whose input
is this resolved component and whose conclusion links `A_f` to the shared
protected inferred contract and original slot/profile. Review that first link
before using decorated-source theorems for subsequent paths or discharge.

## Commands, resource budget, and frozen dependencies

Budget: at most 12 sequential lightweight top-level command invocations; no
heavy process, test, build, probe, Git mutation, child, or interactive question.
Eight read invocations loaded policy, pinned governing sources/prior audit,
selective section locators, and SHA-256 hashes. One final lightweight artifact
read checks the lease text. Python source extraction uses sequential read-only
`git show` subprocesses; it is not an executable semantics experiment. Two
initial broad captures were truncated; all directly used theorem/contract/core
sections were subsequently captured narrowly. Index/task searches were
locators and are incomplete searches, not proof premises.

CPU time, peak memory, and elapsed wall time were not measured. Only the leased
note was written. Inputs were read at the pinned commit; live-tree dependency
drift was not checked and remains the primary's integration responsibility.

| Pinned dependency | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` | `568bb4649ba278519f3ad01af2091dd1baaca42850cd19e3b5734b3c47c2eefe` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/progress/2026-10-06-call-view-source-rule-derivation-attempt.md` | `0009795b060e3bac47d17437f7350f0e45f0bc1eee4131706e04bd4d44624c4d` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |

The inferred-call-views hash differs from the older audit's recorded
`2b04b178b08e8f4fbb74988c528eb1c324d89242c9e060e52cbbe2f14c8fd2f8`.
This derivation uses the later pinned text, including §1.1, rather than treating
the older dependency freeze as current. No dependency was written by this lane.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-source-registration-constructive-derivation.md`.
- Baseline SHA: `621d24b77453799e01ce46615ccabf5b30af183b`.
- Changed dependency hashes: no lane writes; pinned hashes above. The
  inferred-call-views dependency differs from the older audit as stated above.
  Live-tree drift is unverified and must be rechecked before integration.
- Review status: frozen unreviewed research-only premise audit; producer self
  inspection is not independent review. No gate closure or implementation authority.
- Checks already run: pinned original-source/section audit, dependency SHA-256
  calculation, narrow final artifact read. No tests, builds, probes, or formatting.
- Proposed commit message: `research: isolate inferred formal registration link`.
- Shared-record deltas intentionally left for primary/curator: record that
  fresh endpoints and preallocated source labels do not construct the shared
  role-indexed contract or its slot/profile; the first unsupplied premise is
  their registration link. Keep the source-generation and seed-discharge gates
  open. No shared task, authority, index, theory map, or question bundle was edited.

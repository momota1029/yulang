# Does the approved singleton determine the whole formal-use relation?

Date: 2026-10-06
Baseline: `7b1665c125a1883d36c682ee5c76e3757cce3ebd`
Status: frozen, unreviewed research-only bounded characterization and conditional model-theoretic separation
Lease: this file only
Method: abstract relation completions at one singleton use; no source-program or Oracle experiment
Authority/implementation status: none

## Objective and result

Attack the implication that the approved protected-seed/non-Handler outcome,
together with typed-core and source-contract composition, uniquely defines
`U_c`, the independently interpreted local predicate behind `Delta_formal`.

A two-fiber abstract pair agrees on the approved singleton conclusions and
all preservation requirements inventoried below, while differing on one
whole-tuple membership question. Both candidates conclude non-Handler at
every included fiber. There is one static use throughout. Consequently this
is neither an Any/All eligibility attack nor the earlier mixed-role deletion
witness.

The result is conditional on the explicitly supplied abstract fiber envelope.
It establishes underdetermination of the inventoried **formation-interface
requirements**, not two independently validated Yulang source semantics.
The precise remaining blocker is a source interpretation deciding which
otherwise compatible original fibers the local use licenses. The operational
call constructor does not supply that interpretation.

## Baseline and exact governing premises

The semantic reads below use the pinned revision. Live equality to that
revision was checked for every dependency in the snapshot table.

1. `inferred-function-call-views` §§1.1–5 and integrated
   `function-call-view-formation/q1`, approved answer `a2`, interpretation
   items 1–6: written contracts, public schemes and internal views are distinct;
   one relevant component forms one shared contract at original scope;
   unannotated `f` in the specified singleton pattern starts with fully
   protected Handler treatment and is determined non-Handler from ordinary
   value evidence; actual callable role/entry survive; original `(nu,K,D)`
   stay joint; formation and complete admission do not use pending `Q`.
   Exact generation, seed/refinement, protection association and principality
   clauses remain open. The specified `[io]` permission is retained; it is
   neither mandatory removal nor permission for unrelated effects.
2. `typed-computation-core-elaboration` §6: ordinary names reuse Value
   endpoints; `Result(Value(A_x))=Comp(empty,A_x)`; Call relates that whole
   argument to the shared callee interface. Lambda/Bind/Normalize construct
   the conditional source skeleton, without solving its unknown endpoints.
   Section 9 supplies actual entry/receipt/force/rebind/body/consumer/return
   composition after its typed inputs are supplied. Its containment law uses
   complete joint challenge/observation relations. Direction classification
   does not establish those relations or resolve the inferred formal.
3. `source-contracts-and-common-allowance` §§2–3.5,10: Primitive requires an
   independently specified whole-tuple relation. Conjunction, union, renaming,
   binding and constructor image compose such supplied relations. Active
   incidence interpretation, decorated typing, independent admission and
   certified transport are premises of C-realization. The theorem does not
   generate their primitive inputs. `DescMem` is independently interpreted
   and cannot be replaced by a source image. Production Option 2 extras
   remain permitted; no exhaustive production grammar is selected here.
4. `main-source-generation-minimal-clause` §§3–7: the exact skeleton retains
   shared `A_f`, whole `Comp(empty,A_x)` and lexical incidence. Its named rule
   inventory cannot first interpret the unknown formal. Section 5 names
   `U_c(xi;seed,refined,argument,invocation)` as the missing local interpretation;
   §6 separates original footprint and independent admission. These are
   reviewed research boundaries, not additional language axioms.

Prior attacks retained: `role-aggregation-constructive` stops at reusable
eligibility/lifting; `role-aggregation-falsification` compares sufficient
trigger implications; `source-formal-relation-mixed-use-falsification` asks
when restricting an already completed relation preserves it. None supplies
the singleton whole-tuple interpretation. This note changes the question to
whether its approved conclusions characterize membership completely.

## Abstract signature and candidate assumptions

Fix the singleton source-incidence record, annotation absence, original binder
tree, shared formal `A_f`, argument endpoint `A_x` and call `c`. No second use,
recursive component, dynamic entry or new source syntax is introduced.

Let `B` be a **candidate**, Q-independent envelope of original whole fibers.
Let `G(xi)` collect the known constraints at those fibers, including the
approved seed/refinement conclusions and independently supplied compatibility
premises. Assume for this mathematical attack only:

```text
B = {xi_0, xi_1},  xi_i = (nu_i,K_i,D_i)
G(xi_0) and G(xi_1)
z(xi_0)=0, z(xi_1)=1.
```

`z` is a metatheoretic classifier of the existing whole tuple, not a proposed
compiler field, source binder, runtime carrier, effect bit or actual role.
It distinguishes a still-uninterpreted contract/dependency alternative.
There is no claim that the actual Yulang singleton has these two admissible
fibers, or that either can be derived from its source. Neither `B` nor `G`
is an output of the ordinary skeleton.

The common part of `G` fixes the following at **both** fibers:

- internal seed treatment is Handler with full protection caused by absence
  of annotation, without inferring an empty row;
- refined inferred-formal/use view satisfies `NonHandlerFormal(A_f)`;
- provider role and entry are separate coordinates with the same independently
  supplied facts before and after refinement;
- the whole argument and complete call obligations, original source identities,
  profile/path dependencies and shared references remain active;
- all predicate tests concern the original whole tuple, with no Q-dependent
  formation and no independently chosen port witnesses.

No concrete profile, receipt or admitted typed history is manufactured by
this stipulation. An annotated case, callback B or other source component
receives the same interpretation in both abstract expansions; the difference
is confined to this unannotated singleton interface.

Candidate relations:

```text
U_narrow(xi) = B(xi) and G(xi) and z(xi)=0
U_wide(xi)   = B(xi) and G(xi)
```

These define sets over all satisfying original fibers. `U_narrow` does not
select a convenient valuation while generating a relation: its extra predicate
is a fixed candidate local interpretation, stated openly. Whether source
evidence justifies that predicate is exactly unproved. Likewise, `U_wide`
is only an upper-envelope candidate until source completeness is established.

`B` is not an already completed original source solution relation. This is
an attack on its first interpretation, not permission to narrow a fixed
`Phi` while claiming preservation. The candidates are not both asserted to
preserve one independently fixed source solution set. Determining that set,
and proving preservation relative to it, remains the missing source premise.

For scope/renaming preservation assume `z` is invariant under the same joint
renaming action as `B,G`; equivalently use the corresponding copies of both
fibers at each renamed scope and preserve the index. Rigid/environment
coordinates remain fixed. This is a candidate naturality premise, not a
derived generalization rule. No tuple is assembled from different copies.

## Minimized witness and conditional separation

| Whole original fiber | Protected seed | Inferred non-Handler | `U_narrow` | `U_wide` |
| --- | --- | --- | --- | --- |
| `xi_0` | yes | yes | yes | yes |
| `xi_1` | yes | yes | no | yes |

**Conditional theorem.** Under the displayed `B,G,z` assumptions, both
relations are nonempty, satisfy the inventoried pointwise conclusions and
joint preservation requirements, and differ extensionally.

Proof: `xi_0` satisfies both formulas, so both are nonempty. Every included
fiber satisfies `G`; thus neither candidate has a final Handler alternative,
changes a provider role/entry, drops a call obligation, derives authority from
Q, or splices coordinates. Joint renaming preserves each formula by the
naturality premise. At `xi_1`, `G` holds but `z=0` fails, giving the table's
single differing membership answer. Therefore `U_narrow != U_wide`. QED.

Two fibers are minimal for this **nonempty extensional-relation** method.
Over an empty domain no nonempty relation exists; over a singleton there is
only one nonempty subset. Over two fibers `{xi_0}` and `{xi_0,xi_1}` suffice.
Nonemptiness is a deliberate witness assumption, not a claim that the current
rules prove source satisfiability. Allowing an empty candidate would give a
smaller but vacuous witness. No minimality of valid source programs is claimed.

The proof does not require divergent role conclusions or a second use.
Even an exact universal assertion `U(xi) => NonHandlerFormal(A_f)` leaves
the domain of `U` uncharacterized. Replacing that implication by an iff with
all known preservation requirements would be an additional completeness
claim, absent from the inspected constructor rules.

## Why composition and C-realization do not discriminate

Keep the typed constructor operations fixed. Conjunction with the same other
source constraints yields `U_narrow and R` or `U_wide and R`. It identifies
the two only if `R` excludes their symmetric difference. Constructor image
may identify their outward observations, but equal observations do not imply
equal original fiber relations. No inspected composition clause proves the
needed exclusion or injectivity/completeness statement.

The approved outcome is therefore not a missing operational transition rule.
Section 9 can execute a supplied decorated call on any compatible included
fiber. Its equation cannot infer which additional fibers an unknown source
formal should admit merely from the fact that execution is defined there.

C-realization remains conditional and unchanged: when a source translation
independently supplies a primitive relation, local descriptor typing and
the complete admission/conformance certificates, the theorem transports
that supplied interpretation. It neither chooses between these candidates
nor validates both as source meanings. Applying its theorem to either
candidate would require separately proving those premises. In particular,
this note does not stipulate that source semantics equals the candidate and
then call their matching derivations independent validation.

If the independently fixed full descriptor/admission theory rules out
`xi_1`, or a source primitive requires it, the abstract separation cannot
be lifted to that theory. Establishing such a fact would be a useful
discriminator. Without it, claiming a countermodel to **all** completed
Yulang rules would exceed the inspected premises. The precise blocker for
that stronger independence theorem is the unconstructed source fiber
envelope/local interpretation, including its independently grounded typing
and admission. No inconsistency in approved language choices follows.

## Evidence quality, mutations and omitted coverage

Oracle independence: no compiler, legacy implementation, execution oracle or
checker supplies truth values. The documentary audit grounds the requirement
signature; elementary set logic supplies the conditional witness. Both
candidates share `B,G`, scope action and all typed constructor assumptions.
Their disagreement is deliberately the extra local predicate. A checker
encoding these assumptions would verify the table only; it would not prove
`B`, `G`, `z`, descriptor typing or a source rule.

Analytic mutations: asserting `G => U_wide` silently adds completeness;
asserting the extra `z=0` clause is source-entailed silently adds a primitive;
changing final role between the rows would repeat the earlier attack;
changing actual provider role/entry violates authority; allowing a per-port
choice abandons the joint tuple; choosing `xi_0` because Q succeeds violates
independence; treating equal call images as equal original relations needs
an unproved injectivity theorem. No executable mutation suite was run.

Coverage is exactly two original abstract fibers, one static formal-use
incidence and two nonempty relations. No seeds or numeric ranges apply.
Not covered: source validity of the fibers; the original typed footprint;
independent typed-hole admission; complete histories; finite symbolic call
presentation; capture attachment; relevance/recursion; actual export
principality; annotation conversion; production Option 2 completeness;
source adequacy; or B-equivalent inference implementation.

The previous trigger and restriction attacks already leave source
interpretation open. This method obtains a smaller blocker within the
approved singleton; further arbitrary bits or larger finite relations would
leave that same premise untouched. Stop here.

Recommended next action: supply one independently source-grounded
membership discriminator for the singleton's original whole fibers, with
both necessity and sufficiency (or a proved completeness envelope), before
turning the approved role outcome into a definition of `U_c`.

## Checks, resource use and frozen dependency snapshot

Commands already run: read-only `pwd`, `git status --short`,
`git rev-parse HEAD`; mandatory policy `cat`; task/index and filename `rg`
locators; narrow Python section extraction using pinned `git show`; direct
prior-note reads; and SHA-256/live-byte equality inspection. Initial combined
captures were truncated; bounded extraction recovered core §6, §9 entry,
source-contract §§2–3.5/10, minimal-clause §§3–7 and the constructive argument.
No build, test, Oracle access, formatter, executable experiment, Git mutation,
child agent or interactive question was run. Only this leased note was written.

Packet deviation: the parent requested no Git operations; the read-only Git
inspection listed above exceeded that wording. It performed no Git mutation.
One attempted patch with unmatched context failed without changing any file;
the following clarification patch succeeded. Final inspection checked the
leased path and dependency equality without further Git commands.

Local reads used one shell command at a time; lightweight independent reads
were invoked sequentially within each tool batch. Heavyweight process count:
zero. Tool-reported local command durations were subsecond; aggregate agent
wall time, CPU time and peak RSS were not measured. No process or numerical
search budget was supplied beyond the prohibition on builds/tests/Oracle.

| Dependency (under `notes/` unless shown otherwise) | Pinned SHA-256 |
| --- | --- |
| `design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `progress/2026-10-06-main-source-generation-minimal-clause.md` | `7b641ce7b54d1e8aa9a15ae233e7dcee0a7f2fdf51410158df69147dbc36bd38` |
| `progress/2026-10-06-role-aggregation-constructive.md` | `f6ae9dd9b58746aa22faefe94081e378b49215bd90e966b1f1a1e9ef1b58aec4` |
| `progress/2026-10-06-role-aggregation-falsification.md` | `b96d16bb741a60f10fd21a6422ee5af89fcc75989f3d87341e299e87631df4a7` |
| `progress/2026-10-06-source-formal-relation-mixed-use-falsification.md` | `b454b3ac11904f9ce0eec8153af098293d3c15278c31964ce68adeed44bed5ef` |

All eight live files equaled the pinned bytes at snapshot capture. They were
not written by this producer. Integration-time equality remains primary-owned.
Writes stop before submission for frozen review; no independent review is
claimed.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-uc-relation-underdetermination-attack.md`.
- Baseline SHA: `7b1665c125a1883d36c682ee5c76e3757cce3ebd`.
- Changed dependency hashes: none at snapshot inspection; eight exact hashes
  above, no dependency writes. Primary rechecks at integration.
- Review status: frozen, unreviewed, research-only conditional separation of
  the formation-interface requirements; no full-theory independence claim,
  source semantics validation, gate closure or implementation authority.
- Checks already run: governing-section audit, hand proof/table/minimality,
  pinned/live dependency equality; no tests/builds/probes.
- Proposed one-line commit message: `research: separate singleton role outcome from whole-fiber interpretation`.
- Shared-record deltas left for primary/curator: record that even singleton
  seed/refinement conclusions need a source-grounded membership/completeness
  discriminator; retain footprint and admission as separate open premises.
  Link this conditional result if accepted. Tasks, theory maps, index,
  authority, lane queue and question bundles remain untouched.

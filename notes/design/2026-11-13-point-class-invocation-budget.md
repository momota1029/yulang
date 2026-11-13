# Point-class termination: finite covers from invocation ancestry

Date: 2026-11-13. Base: `0f1a1598521e9d649a728c61212aba6958af913c`,
branch `astra/point-class-2`.
Status: Draft proof companion. **Conditional Class P accessibility; unconditional accessibility for
reachable role hierarchies. Arbitrary recursive Class P remains open.**

This continues [the actual-inspection repair](2026-11-13-point-class-inspected-cycle.md)
and [the source-frontier analysis](2026-11-13-source-frontier.md).
Authority remains spec/06-roles.md §6 and the B4 draft through addendum 7.
The relation here is exactly `GeneralNominalActualInspectionSteps.Step`.
No transition or guard changes. K2 still reads actual inspected origins;
missing certificates still leave expansion pending.

## 1. A concrete quantitative missing theorem

For a fixed registry, seed, and root occurrence, define allocator genealogy:
depth zero contains the root identity; a successor of p is
`source seed (origin p declaration.id 6 clause.id 0)` for a visible declaration
and one of its where-clauses. `AtDepth` is this inductive relation, and
`frontier n` explicitly lists all identities at depths at most n.
`child_identity` derives this genealogy from the actual canonical emitter;
`sites_ancestry` proves every registered site has some finite ancestry.

`InstalledDepthBound registry context root n` means that, at **every** state
reachable from this initial state, every generated, installable, novel packet
satisfying the actual PacketGuard has parent identity at ancestry depth ≤ n.
This bounds prospective installing parents uniformly across all schedules.
It assumes neither accessibility, a transition count, a finite signature list,
readback terms, nor a packet enumerator. It is stronger than bare termination;
termination alone is not asserted to imply such a uniform bound.

The main proved theorem is:

```
Checked registry
InitialSource registry context root
InstalledDepthBound registry context root n
------------------------------------------------------
Acc (fun next current => ActualInspectionSteps.Step
       registry root current next) (initial context root)
```

The proof constructs every allocation/report/cover bridge below. It works even
for strict initial intervals when the depth bound is supplied. Pointness enters
the still-open route to proving that bound, not the enumeration argument.

## 2. Actual allocation and ordinary source support

Let J be `frontier n`. Let S be the initial `GeneralNominalState.sources`
followed by all reserved allocator keys for each parent in J. All visible
declarations are included. Keys cover repeated-capture endpoints, output-only
binders, child input endpoints, clause equation targets, and occurrence IDs.

`source_pool` tracks both listed source IDs and output targets of registered
sites. Tracking only listed IDs would miss a pending output brought into an
ordinary constraint by same-input merging. Its actual-trace induction is:

1. Initial linkage puts root output targets in the initial source list.
2. Each installing parent is in J. Report captures use old slot source IDs;
   cross constraints use their endpoints. Singleton captures keep their
   interval; repeated captures use reserved targets for the lower join and
   upper meet of their old endpoints. Self-checks also use old IDs.
3. Each emitted named output target is either the reserved output-only binder
   or the reserved clause-equation key. Compound materialization and child
   endpoints use reserved keys; bare-variable child endpoints reuse captured
   pairs already covered by S.
4. Refresh has the actual support-subset certificate. Its slot table may grow,
   but its represented IDs stay in the prior source list.
5. Equating and merging use old IDs and the tracked pending output targets;
   reobservation introduces no source IDs.
6. Enqueue is impossible on a source-formed path: generated occurrences are
   already registered, as proved from actual reachability.

Separate theorems establish seed, constructor and interpretation preservation.
No overlapping intervals are equated and no interval interior is selected.
This is a support invariant over S, **not** a readback invariant over the
original source holes H. Its dependence on the ancestry bound is explicit.

## 3. The actual recursive reports have a finite enumeration

The packet's semantic delta uses `GeneralNominalPacketSupport.report`, the raw
recursive report seeded with absent root origins. Guards and the certified
emitter can use much longer inherited/recovered origins. Those guard histories
are not fields of the semantic delta or literal child demands.

`ReportErasure.Data` retains capture names, persistent endpoint IDs, capture
origins, checked intervals, anchors and tests. Only transient Fin slots and
unused diagnostics are forgotten. Capture **order and multiplicity remain**:
deduplication could change singleton versus repeated-capture allocation.
Erasure preserves the exact projection and materialization predicates,
including repeated actual-variable coherence.

The finite enumerator follows the real inspector's query syntax:

- bounds range over S × S and variable name lists come from the fixed query;
- structural and nominal inspection recurse on proper query subtrees;
- nonpoint nominal inspection may append both endpoint reports;
- conflicts, deferred cases and arity mismatches erase to included empty
  fragments, so descriptor child counts need no extra bound;
- root checked intervals are enumerated at the demand's exact role arity.

`inspect_enumerated`, `many_enumerated`, and `report_enumerated` prove membership
for the actual functions, using Section 2 for their source-membership premise.
Raw origin nesting is bounded by query recursion and source IDs in S. There is
no assumption on transient slot count, report length, inherited-origin depth,
or the number of refreshes.

## 4. Literal occurrence templates and exact packet codes

Semantic role/input values alone cannot cover novelty, which also requires
literal parent/child edges. For every parent identity in J, visible checked
declaration and enumerated raw report, run the actual child emitter with the
initial seed and erased bindings. `children_identity` proves that the emitter
uses the parent record only through its identity. The finite template list
contains the root and all these emissions. `sites_enumerated` covers every
registered occurrence. Different records with the same ID are retained.

A code consists of a literal parent, a visible checked declaration and an
erased report. Decoding with the initial seed, constructors and interpretation
reproduces captures, materialization requests, ordinary constraints, projection
constraints and output materialization. `encode_represents` proves equality of
literal parent and children plus pointwise equivalence of the complete
input/output delta. `encoded_member` proves every eligible packet belongs to
the finite code list; the actual located-bound length establishes its arity.

Support ledgers and proof certificates need not be enumerated. They gate
installation, while exact semantic deltas and literal edges determine whether
an installation is already committed.

## 5. SignatureCover, measure, and Acc

`ActualBudget.signatureCover` maps the finite codes to signatures. It covers
actual-inspection paths and guards only. The old SharedBudget cover quantifies
more paths, so an additive actual-relation interface and reduction are used.

The primary measure counts signatures not yet held. Holding means that the
signature's delta follows from current journal models and all its literal
child edges are recorded. Every Step preserves held signatures. Novelty
excludes the installing packet's signature beforehand; installation establishes
it afterward. Installations strictly lower the measure. Passive administrative
steps cannot increase it; when it stays equal, the existing administrative
accessibility theorem supplies the inner induction. This proves Acc for all
continuations, not merely absence of one infinite schedule.

`PointSource` requires literal point pairs for initially listed intervals,
nominal type and row parameters, and unnamed root inputs. Later observations
need not remain point pairs. `ClassPInvocationBound` universally quantifies the
one depth bound over Checked registries, InitialSource and PointSource.
`sourceBudget_of_invocation_bound` constructs the corresponding source budget;
`class_p_accessible` is the resulting conditional Class P theorem.

## 6. An unconditional class containing real role programs

`RoleHierarchy.Hierarchy registry active rank` requires each visible declaration
of an active role to have only active where-child roles with strictly smaller
natural-number rank. The root role is active. Other visible roles may recurse.
Heads, compound child inputs, associated equations, output-only binders,
intervals, same-input aliases, K2 and administrative steps are unrestricted.

`sites_ranked` extracts actual child roles from canonical emission and proves
that every registered site has ancestry depth d satisfying

```
d + rank(site.role) ≤ rank(root.role).
```

Consequently `installed_depth_bound` supplies n = rank(root.role), without
source readback or refinement hypotheses. `RoleHierarchy.accessible` is
unconditional for every Checked registry and InitialSource in this syntactic
class. It covers strict intervals too.

`HierarchyExamples.wrap_accessible` instantiates it on the existing
Wrap(list int) fixture, with Wrap and Container active at ranks 1 and 0.
The unchanged registry still contains recursive Display(list a) and Display int;
they are not generated from this root. `initial_source` and `point_source`
prove the actual source premises. `wrap_step` proves a real novel guarded
installation, `child_is_named` verifies its named Container item target, and
`after_wrap_accessible` covers all its continuations. This is not an
identity-leaf example. This particular step has a compound head and bare-variable
child input; the parent requests no associated output, so it does not test
materialization of Wrap.out. The general hierarchy theorem permits compound
child inputs and requested compound outputs. The fixture has no Container
implementation; this theorem does not assert a successful dictionary or
classify the final child.

Recursive Display does not satisfy this hierarchy. Its existing positive
installation, actual-cycle K2 exclusion, and the settled pump exclusions remain
valid because the Step is unchanged. No new whole-execution Acc for recursive
Display or the pump is claimed.

## 7. Exact remaining producer work

| Link | Proved here and remaining boundary |
| --- | --- |
| (a) Capture/label readback | Exact raw report erasure and consumer semantics; earlier point-nominal and alias readback remain available. General actual-origin readback over H is still open. Initial pointness does not imply point-only later reports. |
| (b) Producers over H | Actual source-ID, named-output and literal-occurrence producers are covered over S conditional on depth. A representation invariant over original H independent of depth is still open. |
| (c) Elimination history | Existing fixed-hole substitution arithmetic and observation preservation are unchanged. Extraction from every actual step is unproved. |
| (d) Instantiated descent/growth | Existing checked finite-pattern descent is not a realization theorem for arbitrary carrier captures. The shared-capture/settled-output finite-tree bridge remains open. Role hierarchy bypasses it for the stated class. |
| (e) Invocation/allocation/report/cover | From the concrete ancestry bound, allocation, report, literal occurrence and exact semantic cover are constructed; Acc follows with no further hypotheses. |

The Class P theorem has one named quantitative hypothesis, but its proof for
arbitrary recursive roles still needs the upstream work in (a)–(d). Giving that
consequence a name does not complete those producers. No new obstruction or
semantic decision was identified during this work.

## 8. Verification

The yulang-proofs skill was used. The configured prover launch role is absent;
no prover agent ran. The primary constructed these proofs; an independent
read-only reviewer audited their quantifiers and noncircularity. The reviewer
confirmed that finite support, codes, exact representations and the cover are
derived, and that pointness enters only at the unproved invocation bound.

New imports are appended to `lean/Yulang.lean`; all new public theorems are
listed in `lean/Audit/GeneralNominalPointBudget.lean`.

From `lean/`, the following final commands each returned exit code **0**:

```sh
lake build Yulang.GeneralNominalInvocationAncestry Yulang.GeneralNominalReportErasure Yulang.GeneralNominalReportEnumeration Yulang.GeneralNominalPacketCodes Yulang.GeneralNominalAllocationSupport Yulang.GeneralNominalActualTraceSupport Yulang.GeneralNominalOccurrenceEnumeration Yulang.GeneralNominalActualBudget Yulang.GeneralNominalRoleHierarchy Yulang.GeneralNominalHierarchyExamples > /tmp/yulang-point2-modules.log 2>&1
lake build Yulang > /tmp/yulang-point2-full.log 2>&1
lake env lean Audit/GeneralNominalPointBudget.lean > /tmp/yulang-point2-audit.log 2>&1
```

The focused command `lake build Yulang.GeneralNominalHierarchyExamples > /tmp/yulang-point2-examples.log 2>&1` also returned **0**; its imports include
all ten new modules. Development elaboration errors were corrected before
these final checks.

The audit covers 81 public theorems and the constructed `signatureCover`.
Its parsed allowlist check returned **0**; the dependency union is exactly
`propext`, `Classical.choice`, and `Quot.sound`. Existing Lean byte-prefix,
forbidden-token, protected-path, branch and HEAD checks returned **0**.
`git diff --check` returned **0**. No refs or commits were changed.
No source-language parser check was needed: no new Yulang source syntax was
introduced. The example uses existing Lean fixtures; no inference-to-fixture
producer or total dictionary-success theorem is asserted.

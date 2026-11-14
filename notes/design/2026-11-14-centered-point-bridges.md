# Centered point-source bridges and the merge-record obstruction

Status: bounded proof progress. The unrestricted centered ground-root
accessibility transfer is **open**. This note supersedes no owner decision and
changes no existing definition. It follows the requested order: point-source
simulation first, then the guard consequences available independently of it.

## Authority

The center decision in `spec/06-roles.md` §6.5 says:

> 実際の引数の名前（中心）は明示して持つ

and specifies:

> 中心は `lower ≤ 中心 ≤ upper` を満たす未知の型の名前で、具体的な型を選ぶものではない。

It also says:

> 実装が共有の情報を失ったことを理由に需要を保留にする規則は足さない

This work introduces no pending case. The model and raw-record distinctions
below are implementation proof obligations. The owner has already answered
the semantic question; there is no new owner question here.

For merging, §6.3 says:

> すべての名前なしの引数が同じものを指す（同じソースの識別子であるか、等式で同じと示せる）

and:

> impl を選ぶ前、保留のままでも行う。

Thus a proof of immediate packet installation cannot silently drop the
kernel's `MergesClosed` obligation. Whether a local selected state first needs
an administrative merge is distinct from the language's candidate choice.

## Initial point sources

`GeneralNominalCenteredPointSource` proves:

- Every supplied root site satisfying `PointNames` on point intervals is the
  default `rootSite`, independently of the seed. Consequently every centered
  `InitialSource` with a point root has the default initial representation.
- Centered and erased ordinary model sets coincide initially.
- Initial centered head justification (`ReadyAt`) and `DecisionGuard` are
  equivalent to the actual-inspection kernel's shared support predicates.
  The centered trusted list is empty at initialization; it supplies no extra
  equations beyond the point input names.
- Every centered refresh directly from such an initial state has the required
  raw-model consequence and erases to an actual-inspection step.
- The observed form of a point site satisfying `PointNames` is its raw
  `pointSite`.

These statements quantify over all point roots. They do not assume finite
ground syntax. They concern initialization, not a preservation invariant for
arbitrary descendants.

## Exact erasure is false on a reachable ground example

`GeneralNominalCenteredPointMergeExample` uses the existing checked Display
fixture with two distinct where clauses, both requesting `Display int` from
`Display (list int)`. The root interval is `(0,0)`, and source 0 denotes the
closed finite term `list int`; source 1 denotes `int`.

The module constructs, without additional transition assumptions:

1. A checked registry, ordinary and centered initial source, `PointSource`,
   and `GroundRoots` with label `list int`.
2. An actual centered root installation emitting distinct child occurrences
   10 and 11, both carrying center 1.
3. A centered same-input merge of those children.
4. A model of the final centered state, using the original inhabited source
   assignment. The counterexample is not caused by inconsistent constraints.

The raw emitter retains `nominal (source 0) 0 0` at each child. The centered
merge records the sites observed through `source 1`. These are semantically
equal inputs but unequal site records. The observed centered site is absent
from the raw registry of sites.

`GeneralNominalCenteredMergeBridge.actual_new_merge_registered` proves that
any newly recorded merge fact in an actual-inspection step names two sites
registered before that step. Installation cannot introduce a merge fact and
administrative actions preserve the fact list. Therefore the centered merge's
literal erased successor cannot be an actual-inspection successor.

`ground_point_counterexample` packages the checked source, point and ground
premises, centered prefix and step, and the negation of exact step erasure.
It refutes the proposed literal-erasure induction on reachable point roots.
It does **not** refute unrestricted centered accessibility or simulation by a
relation allowing different fact records.

## Matching raw execution and preserved semantics

The same module constructs a real two-step actual-inspection execution:
install the identical root packet, then merge the two registered nominal-path
sites. `matching_raw_path` proves:

- Its final ordinary saturation state is literally equal to the centered
  execution's final erased ordinary state.
- For every support list and every assignment, the two final `Slice`
  predicates are equivalent.

The support result uses this fixture's empty associated-output lists: every
added merge fact is semantically empty. It is not a general theorem equating
arbitrary merge-alternative lists.

The generic bridge module additionally proves that merging sites with equal
occurrences produces equal ordinary states, and that individual merge facts
with equal occurrences and the same support have equal dependency lists and
equivalent meanings. These are useful components for a relation between
centered and raw executions; they do not yet establish its preservation under
all installations, refreshes, or future support promotion.

A sufficient whole-trace connection must track corresponding registered
sites and recorded merge operands, source support and promotion, and a
conservative interpretation of allocated centers. In particular, equality of
ordinary states and support slices in this example alone does not justify
transporting every future `Trusted` derivation: those derivations also inspect
fact membership. The ground theorem has not been applied to an unproved
simulation relation or to a restricted replacement for the centered Step.

## Selected-state guards

`GeneralNominalCenteredInspection` proves coverage of recursive inspection:
when every supplied input has an origin, each inspected position has a test
origin. Structural descent retains the origin, and nominal descent records
its actual path. At a centered plan, location of its input arguments supplies
the input-list length, while `Site.observed` supplies every center origin.
No ground or point restriction is required for this coverage result.
Coverage accounts for inspected positions; it does not assert that inspection
is unblocked or successful.

For the unchanged centered local predicate, selection entails the centered
`DecisionGuard` and excludes root and candidate cycles. Combining these with
coverage proves `Safe` for registered, visible, head-ready plans and
`AlternativesSafe` for a registered selected input.

`selected_guard_reduction` and `selected_installable_iff` precisely expose the
remaining obligations. With a selected local outcome, a registered plan input,
and ordinary `FeedbackSteps.Installable`, the remaining centered guard is
exactly legacy `ValueSupport.PacketGuard` plus a common model satisfying the
current centered state and the plan. Those hypotheses have not been derived
from source reachability. In particular, the theorem does not assume only
selection and then conclude installation.

`unmerged_blocks` proves the separate scheduling obstruction: a registered
same-input site outside the packet's alias class prevents centered
installability through `MergesClosed`. It does not supply a reachable centered
selected counterexample by itself.

## Remaining work and review

1. Preserve a relation between centered and raw states along **every**
   unrestricted centered step from ground point sources, including compound
   center model extension, refresh consequences, and support promotion after
   merges. Then transfer the existing ground-root theorem and execution
   existence. This is the requested bridge (5), still open.
2. Produce ordinary installation readiness, value support, and a common
   centered branch model from reachable selected states, accounting for merge
   closure. The inspection and cycle portions are now discharged.
3. Construct the P/W trigger trace and its inhabited final cycle. The earlier
   conditional K2 consequence is unchanged; no trigger execution is claimed.
4. Prove allocation freshness/model extension and nested center invariants.
   Inspection coverage alone does not establish these.

The six existing structural V5 transfers remain as previously integrated.
No further V5 field is claimed here. No new operational descent proof is
attempted. No registered prover launch surface was available; the primary
constructed the bounded proofs, with separate read-only review of the source
counterexample, quantifiers, and guard reduction.

## Validation

Final commands from the repository root, all with exit code **0**:

```text
cd lean && lake build Yulang.GeneralNominalCenteredPointSource Yulang.GeneralNominalCenteredMergeBridge Yulang.GeneralNominalCenteredPointMergeExample Yulang.GeneralNominalCenteredInspection
cd lean && lake build Yulang
cd lean && lake env lean Audit/CenteredPointBridges.lean
git diff --check
```

The module build completed 818 jobs; the aggregate build completed 2335 jobs.
The new dependency audit covers 80 exported theorems and reports only
`propext`, `Classical.choice`, and `Quot.sound`. An additional filesystem check
confirmed that the only tracked edits are append-only imports in
`lean/Yulang.lean` and the appended index entry, that every new module is
imported, and that the branch remains `astra2/centered`. No commit or ref update
was performed. Intermediate elaboration failures were repaired before these
final commands; no failing module is included.

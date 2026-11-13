# Centered administrative readiness and the ground V5 boundary

Status: additive candidate boundary G′, eleven unconditional V5 fields, and
explicit conditional composition. This does not close B4. The Step, source
domain, models, stability, generation, and evidence are exactly those of the
previous centered ground boundary G. No existing definition was modified.

## Authority and diagnostic change

The owner requires merging before selection. [Roles §6.3](../../spec/06-roles.md)
says: 「同じ role の需要が二つあり、**すべての名前なしの引数が同じものを指す**
（同じソースの識別子であるか、等式で同じと示せる）とき、二つの関連型の出力を等しいとし、
需要を一つにまとめる。impl を選ぶ前、保留のままでも行う。」
It also says: 「兄弟と親は、更新のたびに作り直して再計算し、状態が変わらなくなったところで、
初めて保留・曖昧・拒否を最終結果にする。」 The supervisor explicitly authorized a new
merge-aware boundary with the same Step for this task.

The center decision in [§6.5](../../spec/06-roles.md) says:
「中心は `lower ≤ 中心 ≤ upper` を満たす未知の型の名前で、具体的な型を選ぶものではない。」
It also says: 「実装が共有の情報を失ったことを理由に需要を保留にする規則は足さない」.
This work adds no provenance-absence test. It does **not** establish that every
required merge can actually execute; an operational obstruction must not be
reported as a newly approved final pending outcome.

`GeneralNominalCenteredAdministrativeLocal.AdministrativeReady s d` means:

1. Some centered site in `s.sites` has occurrence `d`.
2. Every raw site for `d` satisfies the existing `FeedbackSteps.MergesClosed`.
3. Every centered site for `d` is aliased with every registered centered site
   having the same actual inputs in `CenteredSteps.Models s`.

G′ adds `¬ AdministrativeReady s d` to `InspectionPending`; all other local
predicates are unchanged. Consequently:

```lean
Local r s d (.selected key children) ↔
  GeneralNominalCenteredBoundary.Local r s d (.selected key children) ∧
  AdministrativeReady s d
```

This also defers ambiguity and zero-candidate rejection when readiness fails.
It preserves unknown-root priority and K2 rejection before administrative
deferral. The owner's K2 decision says 「拒否と曖昧性の優先順位 … 拒否が先」 and
「根（または head の非変数 pattern が調べる位置）が**循環の上にある**か」.
`root_cycle_rejected` and `inspected_cycle_rejected` hold without readiness.
Once ready, **every** frontier agrees with G. Every initial root is ready, so
all existing initial-root classifications, including positive examples,
transfer unchanged. Local remains functional and total for checked registries.

Required merge closure is stronger than absence of an enabled merge. In
particular, centered `At.merge` still requires
`SupportChoices.MergeGuard s.erased first.observed last.observed support`.
`CenterMergeSupported` names that residual; `stable_center_merges_closed`
proves center closure from stability and this certificate. Neither raw nor
centered merge availability on every reachable state has been established.

The concrete duplicate-Display fixture is checked: its source root remains
selected; after the actual first installation, the generated duplicate child
is now pending. `reachable_duplicate_pending` uses the existing source-formed
ground execution. This is an intermediate administrative diagnostic, not a
claim that the child remains pending at saturation.

## Generated children: exact residual

Merge readiness removes the merge premise from `selected_base_plan`. For
reachable generated selected demands, the remaining premises are:

* `GeneralNominalJointCandidates.Joint r s.erased.current d key`;
* for the resulting registered ordinary-installable plan, an old
  `GeneralNominalValueSupport.PacketGuard` certificate;
* a common centered model satisfying `Models s model ∧ plan.Holds model`.

`GeneralNominalCenteredAdministrativeProduction.Production` makes these
obligations explicit. It contains no Local tree, Generated conclusion, or
child-evidence premise. The proved chain is
`Production → selected_installable → stable committed packet → stored child
edges → Generated children`. `ReachableProduction` asks for this only at
reachable, generated, stable, selected demands with **nonempty** child lists;
leaves need no producer. Its universal plan clause is a sufficient certificate,
not a claim of logical minimality.

The exact field still requiring an unconditional proof is:

```lean
B4SkeletonV5.GeneratedChildren (boundary roles)
-- unfolded:
∀ r, (boundary roles).Checked r → ∀ s root d key children,
  B4TargetV5.Reachable (boundary roles) r root s →
  (d = root ∨ (boundary roles).Generated r s root d) →
  (boundary roles).Stable r s d →
  B4Target.SafeKnown (boundary roles) r s d →
  B4Target.Unique (boundary roles) r s d key children →
  ∀ child, child ∈ children → (boundary roles).Generated r s root child
```

The theorem `generatedChildren` proves exactly this field **conditional on**
`ReachableProduction roles`. Semantic packet commitment alone cannot replace
the producer: its definition already includes the child-edge obligations.
No new stable reachable counterexample to the field is claimed here.

## All-state where accessibility

Registration permits a proof stronger than the requested reachable-state law:

```lean
∀ r s root,
  Acc (CommonRoleOutermostResolver.Child
    (B4TargetV3.Local (boundary roles).toSourceBoundary r s)) root
```

Let `ceiling s` be the maximum occurrence identity in the finite centered site
list. A selected parent has identity at most this maximum. Its Survivor
witness constructs a packet without requiring installation or a model.
`GeneralNominalCenteredWhere.packet_child_above` gives
`parent.identity < child.identity` for each emitted child. Thus
`ceiling s + 1 - identity` strictly decreases on every Local child edge.
An unregistered child above the maximum cannot be selected. This proves the
all-state law and the exact `whereAccessible` field without a saturation,
production, Paterson-label, or common-model premise.

## Ordering and composition

`GeneralNominalCenteredAdministrativeOrder` proves fixed-snapshot registry
reordering for DecisionGuard, CandidateCycle, and the entire G′ Local relation.
It transports candidate declarations and checked signatures, while head
patterns and actual inspection positions remain identical. Required merge
closure is independent of the registry argument. Clause reordering uses the
existing canonical emission equality.

The executor reuses G's terminal-state choice and resolves G′'s frontier. The
following eleven fields are unconditional:

| Field | Proof |
| --- | --- |
| `progress` | G ground accessibility, unchanged Step and Initial |
| `execution` | G terminal execution |
| `halted` | G terminal halt law |
| `closure` | G closure |
| `stepModels` | G model restriction |
| `frontierLocal` | G′ total and functional Local |
| `localIdentity` | G′ frontier definition |
| `whereAccessible` | All-state finite registration rank |
| `treeExecution` | G′ resolver definition |
| `dictionaryRefl` | Unchanged dictionary relation |
| `initialReorders` | Unchanged ground source domain |

The remaining exact fields are the three members of
`GeneralNominalCenteredAdministrativeComposition.Remaining`:

```lean
canonicalLocalOrder : ∀ r r', (boundary roles).Checked r →
  (boundary roles).Checked r' → (boundary roles).Reorders r r' → ∀ s root,
  B4TargetV5.Reachable (boundary roles) r root s →
  B4TargetV5.Reachable (boundary roles) r' root s → ∀ d f,
  B4TargetV3.Local (boundary roles).toSourceBoundary r
    ((executor roles).run r s root).1 d f ↔
  B4TargetV3.Local (boundary roles).toSourceBoundary r'
    ((executor roles).run r' s root).1 d f
evidenceNode : B4SkeletonV5.EvidenceNode (boundary roles)
generatedChildren : B4SkeletonV5.GeneratedChildren (boundary roles)
```

Fixed-snapshot reordering does not compare the two independently chosen
terminal states. `canonicalLocalOrder_iff_final_local_agreement` gives a
necessary-and-sufficient residual: `FinalLocalAgreement` compares only Local
at registry `r'` on the two returned snapshots. No intermediate-state
confluence is needed. This exact reduction does not prove that residual.
`FinalObservationAgreement` supplies a more structural sufficient condition:
at the common registry `r'`, those two terminal states agree on RootPending,
RootK2, CandidateK2, InspectionPending, and every Survivor witness. This is a
sufficient structural observation-confluence certificate, **not** a proved
confluence theorem or a logically weakest condition. It requires no equality
of journal lists, plans, intermediate states, or final trees. The theorem
`canonicalLocalOrder` derives the exact final-state field from it.

The supervisor's separate evidence worker targets G. Its result transfers
directly by `evidenceNode_of_ground`: G′ selected implies G selected, and
Initial/Step/Models/Stable/Generated/Evidence are unchanged. No duplicate
evidence construction was attempted.

`composition` takes the exact three fields. The more operational theorem
`composition_of_observations_and_production` instead takes
`FinalObservationAgreement`, G's `EvidenceNode`, and `ReachableProduction`.
Neither theorem is an unconditional B4 instance.

## Trigger and review scope

The previous P/W trigger theorem still starts from four recorded plans and a
common centered model. This turn does not construct the source-to-ledger
execution. The added G′ K2 lemmas preserve rejection priority, but no actual
trigger trace or final-classification theorem is claimed. Closing the trace
still requires constructing its intermediate source readbacks and guarded
installations; this was not a cheap extension of the current fixture.

The `yulang-proofs` skill was used. No registered/callable `prover` launch
surface was available; the primary constructed these bounded derivations.
A separate read-only reviewer checked the new proof scope and boundary change.
The unresolved conditions are implementation/proof obligations; no new owner
question is introduced.

## Validation

Final commands and exit codes (the first three run from `lean/`):

| Command | Exit | Result |
| --- | --- | --- |
| `lake build Yulang.GeneralNominalCenteredAdministrativeExamples` | 0 | All seven new modules, 903 dependency jobs |
| `lake build Yulang` | 0 | Aggregate including all seven appended imports, 2361 jobs |
| `lake env lean Audit/CenteredAdministrativeComposition.lean` | 0 | All 54 new public theorems; dependencies limited to `propext`, `Classical.choice`, `Quot.sound` |
| `python3 /tmp/yulang-centered-administrative-check.py` | 0 | Frozen-file prefixes, exact modified/new paths, imports, audit coverage, prohibited-construct scan, whitespace, branch |

The only modified tracked files are the permitted appended imports and design
index entry. All other artifacts are new. No commit, push, or reference change
was made. The three remaining fields and actual trigger execution above were
not established by these checks.

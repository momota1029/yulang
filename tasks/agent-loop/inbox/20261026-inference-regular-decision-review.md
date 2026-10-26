# Independent review: constructed terminal regular evidence

Assignment: `20261026-inference-regular-decision-review`, revision 1.
Reviewer: `/root/regular_decision_review`, fresh non-author; no contribution to
construction or repair of the reviewed source. No descendants.
Producer: `/root`. Mode: M3, one assigned independent reviewer for this artifact.
Baseline: `eb3eef2f6a29d9c2a6132d648866c60900db276c`, branch `yulang3`.
Requested model/effort: inherited runtime settings; observed launch metadata:
UNKNOWN. The reviewer identity and this actual review are established by the
current collaboration assignment, not historical scheduling rows.

## Verdict

**ACCEPT for the exact frozen finite regular-graph decision construction and
its stated conditional applications.** No BLOCKING, major, or minor findings.
No repair or checker rerun is requested. This does not close original source
inference soundness, native correspondence, principality, or production gates.

## Frozen inputs and dependency identity

| Input | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/SimpleSubRegularDecision.lean` | `6b6e5e6f1c45140d935e1aa29fba4c1303ae89cd91fd6e1cde0d37387148db8d` |
| Producer handoff `tasks/agent-loop/inbox/20261026-inference-regular-decision.md` | `5c7e14cdac0e2c2dec61980b15f32dff0a4dec9e3996a6a52a37439890dafbf3` |
| Isolated `audit-04.log` | `fd6c65380c74a699d88dc498abdea295c2ae9463b7e0733ea6370615ea9914e5` |
| Isolated `DecisionAudit.lean` | `4af4882db7c82cf056a3982971cf6cc4b99fc2448fad5863a30544139344b0b8` |
| Isolated `check-03.log` | `df70e2598540632c917a3879e38a96515b8a1c005a308b30eb8fde2cea964573` |

The isolated directory is
`/workspace/scratch/f98087c7ac1a/inference-decision`. Its decision source is
byte-identical to the reviewed repository source. The following eight frozen
base modules were compared byte-for-byte with both `git show` at the stated
baseline and the isolated checked source copies; all match. `Contracts` was
also compared because it belongs to the actual import cone.

| Module under `notes/theory/lean/YulangClosure/` | SHA-256 |
| --- | --- |
| `BirthLevelSCC.lean` | `2c76b82d4dc85a4bf4c122731ba014b07df4c863ad679e9a795a57e6546243f0` |
| `SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `SimpleSubConstraintSoundness.lean` | `33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293` |
| `SimpleSubGeneralizationSoundness.lean` | `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246` |
| `SimpleSubRegularSolutions.lean` | `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29` |
| `SimpleSubRegularConstraintSoundness.lean` | `1d2266867115fc27afe39dbb80a3ca0e8f75247a2e16b739145137e83999de33` |
| `SimpleSubScopedPublication.lean` | `d64e9bffca5d513985237a9ff78dcf3d9e43baae1594edbc93dff4b5410d428f` |
| `SimpleSubRegularPublication.lean` | `18fc6f138204e1529dcd0bb9c01a20de7444a26e4dadc87677460ccd8ac9fc99` |
| `Contracts.lean` (additional direct dependency) | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |

## Mathematical review

All declaration names below have prefix
`YulangClosure.SimpleSub.RegularDecision` unless another namespace is shown.

1. **The fuel bound genuinely yields checked evidence.** `pruneStep` filters
   the current list using `Regular.checkPair graph certificate`. Filtering
   preserves order and cannot increase length. If it has equal length, no
   entry was removed, so the filtered list is equal to the original list.
   Consequently `pruneStep_strict` gives strict decrease whenever the algorithm
   recurs. `prune_checked` is quantified over every graph, fuel, and certificate,
   with the sole size premise `certificate.length ≤ fuel`. At zero fuel that
   premise forces the empty list, whose certificate check is true. At positive
   fuel, equality supplies the original postfixed check; inequality leaves a
   list of length at most the predecessor fuel. No stabilization, solution,
   termination, graph validity, or requested comparison is assumed here.

2. **Pruning cannot discard an original semantic pair.** The imported
   `Regular.RegularSub graph pair` remains `∀ depth, Approx graph depth pair`.
   It is independent of finite certificate acceptance. Its already proved
   `regular_unfold` supplies one actual child list: deterministic `expand`
   identifies the same list at every depth. `pruneStep_covers` uses that exact
   unfolding and `Layer.mono` to retain every semantic pair whenever all
   semantic pairs were previously present. `prune_covers` preserves this for
   arbitrary fuel, including early fixed-point exit. This does not assume the
   desired final relation is already accepted.

3. **The initial universe is complete and has no invalid endpoints.**
   `mem_kindPairs` and `mem_allPairs` characterize all pairs of the appropriate
   kind with both indices inside that kind's finite node table. For any
   `RegularSub` pair, one unfolding plus `expand_endpoints_exist` yields both
   actual lookups. `lookupList_index_lt` then puts that pair in `allPairs`.
   This remains true even for bottom/top comparisons: the imported `expand`
   requires both endpoints before applying the node rule. There is no assumed
   finite semantic enumeration and no restriction to requested demands.

4. **The result is exact, not merely a successful approximation.**
   `constructed_checked` uses the actual length of `allPairs` as its fuel.
   `constructed_exact` proves, for every graph and comparison,
   `pair ∈ constructCertificate graph ↔ Regular.RegularSub graph pair`.
   The forward direction uses the existing `certificate_sound` coinduction;
   the reverse direction uses universe coverage and pruning preservation.
   No `graph.Valid` assumption is needed for this equivalence. Global graph
   validity is a separate necessary condition for accepting demands.

5. **The executable decision preserves whole-graph validity.**
   `decideDemands_exact` has the exact conclusion
   `decideDemands graph demands = true ↔ graph.Valid ∧ Regular.Holds graph demands`.
   It reuses the existing `accepts`, which still computes `checkGraph` before
   certificate and demand membership checks. Empty demands do not remove
   `graph.Valid`. `decideDemands_rejects_iff` is the Boolean complement of that
   same conjunction; it does not replace failure by an unrelated condition.
   The retained dangling-graph/empty-demands example exercises this boundary.

6. **The applications retain their actual premises and one shared assignment.**
   `decided_original_demands` instantiates the existing concrete
   `Regular.ConstraintHistory` theorem. `decided_store_history` additionally
   requires successful decoding of the same original store.
   `decided_publication_with_clients` applies the existing
   `RegularPublication.publication_history_with_clients` with the computed
   certificate. The audited type has no free certificate parameter, model,
   semantic `LocalLaws`, or existential certificate-generation assumption.
   It still requires bounded bounds, inactive images, stopped closure,
   capture/allocation implications, use bounds, complete inventory coverage,
   successful decoding, a concrete history, and a true terminal decision.
   Original publication and every included client use exactly the same
   reference assignment
   `fun k i => refs k (publicationTransport n count afterUse q k i)`.
   Computing the certificate does not establish that an arbitrary graph and
   terminal demand list pass the decision.

## Complete type and axiom audit

I inspected all complete printed theorem types and axiom results in the frozen
log, including private/generated declarations. A separate read-only parser
matched each BEGIN name to its printed declaration, its single axiom report,
and its END name; checked uniqueness; matched all 23 source `theorem`
declarations; and checked the 37-entry trailer. Acceptance does not rely on
the reported count alone.

The driver enumerates all `.thmInfo` constants originating in
`YulangClosure.SimpleSubRegularDecision`, rejects project `.axiomInfo`
declarations, checks required roots, and rejects collected axioms outside the
standard allowed set. The observed results are 3 empty lists, 10 containing
only `propext`, and 24 containing `propext, Quot.sound`. No `Classical.choice`,
`sorryAx`, project axiom, or native-evaluation axiom occurs.

The following inventory records every matched entry. Names are relative to
`YulangClosure.SimpleSub.RegularDecision`; the two abbreviated private names
are exactly `_private.YulangClosure.SimpleSubRegularDecision.0.` followed by
that namespace and `prune.match_1.eq_1` / `prune.match_1.eq_2`.

| Theorem | Origin | Complete axiom list |
| --- | --- | --- |
| `dangling_empty_demands_decided` | authored | `[propext]` |
| `mem_allPairs` | authored | `[propext, Quot.sound]` |
| `decideDemands_rejects_iff` | authored | `[propext, Quot.sound]` |
| `decided_store_history` | authored | `[propext, Quot.sound]` |
| `prune.eq_2` | generated/private | `[propext]` |
| `decideDemands_exact` | authored | `[propext, Quot.sound]` |
| `pruneStep_strict` | authored | `[propext, Quot.sound]` |
| `decided_original_demands` | authored | `[propext, Quot.sound]` |
| `universe_covers` | authored | `[propext, Quot.sound]` |
| `constructed_checked` | authored | `[propext, Quot.sound]` |
| `allPairs.eq_1` | generated/private | `none` |
| `prune_covers` | authored | `[propext, Quot.sound]` |
| `two_cycles_regular` | authored | `[propext, Quot.sound]` |
| `decideDemands_exact._simp_1_2` | generated/private | `[propext, Quot.sound]` |
| `two_cycles_decided` | authored | `[propext]` |
| `pruneStep_fixed_checked._simp_1_1` | generated/private | `[propext, Quot.sound]` |
| `pruneStep_covers` | authored | `[propext, Quot.sound]` |
| `decided_publication_with_clients` | authored | `[propext, Quot.sound]` |
| `prune.eq_def` | generated/private | `[propext]` |
| `optional_mismatch_decided` | authored | `[propext]` |
| `prune_checked._proof_1_5` | generated/private | `[propext, Quot.sound]` |
| `prune_subset` | authored | `[propext, Quot.sound]` |
| `prune_checked._proof_1_1` | generated/private | `[propext, Quot.sound]` |
| `lookupList_index_lt` | authored | `[propext]` |
| `prune.eq_1` | generated/private | `[propext]` |
| `decideDemands.eq_1` | generated/private | `[propext]` |
| `decideDemands_exact._simp_1_3` | generated/private | `[propext, Quot.sound]` |
| `pruneStep_fixed_checked` | authored | `[propext, Quot.sound]` |
| `pruneStep_strict._proof_1_1` | generated/private | `[propext, Quot.sound]` |
| `delayed_mismatch_decided` | authored | `[propext]` |
| `mem_allPairs._simp_1_2` | generated/private | `[propext, Quot.sound]` |
| `constructed_exact` | authored | `[propext, Quot.sound]` |
| `_private....prune.match_1.eq_1` | generated/private | `none` |
| `dangling_graph_decided` | authored | `[propext]` |
| `mem_kindPairs` | authored | `[propext, Quot.sound]` |
| `_private....prune.match_1.eq_2` | generated/private | `none` |
| `prune_checked` | authored | `[propext, Quot.sound]` |

The successful producer log reports all 10 focused build jobs complete.
The retained first failure was namespace/reserved-identifier elaboration;
the second was the stale `mem_allPairs` reference. Their hashes are
`5a314275674862c58a4c8ba44abe8c930f7616a54bcfe8336c69b80f887d4eb0`
and `0f2eee7ceab6156ea809144593a502c2c747621610809c0ba19e5044268335b6`.
The final source and complete final axiom audit contain no residual proof hole.
The final decision examples use kernel `decide`, including cyclic four-port
Functions, a delayed recursive atom mismatch, optional metadata mismatch,
and dangling references with nonempty and empty demands.

The project pin, Lake configuration and manifest were inspected: Lean 4.35.0,
`-j1 -M1024`, no external packages. The producer reports the native toolchain
at `/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`,
`LEAN_NUM_THREADS=1`, and 120-second per-call limits. These are producer checker
receipts; this independent review did not rerun Lean or claim independent
checker execution. A source scan of the new module and its actual local import
cone found no `sorry`, `admit`, project `axiom`, `unsafe`, `native_decide`,
`sorryAx`, `skipKernelTC`, or `implemented_by` occurrence.

## Original parent, represented scope, and remaining work

The parent remains `YulangClosure.SourceProblem.InferenceSoundness`, whose
actual definition requires every supported source/generation/solution tuple
to yield an original `sourceJudgment` witness with the same `sameScoped`
relation. I inspected that definition and the original source-preservation
claim in `2026-10-13-intrusion-source-preservation-proof.md` §§1, 3, 5, using the
2026-10-24 immutable-birth correction, not the superseded cross-level rule.
The top-level inference principles remain unchanged.

This delta removes an externally supplied terminal finite certificate from
one already-established finite structural consumer. The interpretation still
covers kind-indexed atoms, bottom/top, all four Function ports, exact finite
record fields/optional bits, ordered tuple elements, exact variant tags and
payload lists, and constructor-guarded cycles. It does not introduce alias,
union/intersection, bare-variable-cycle, native open-row, width/presence
weakening, ordinary coalescing, or complete Call/effect semantics. Those cases
remain obligations of the original supported source domain, not cases deleted
from the parent theorem.

The all-pair table contains `n_value^2 + n_effect^2` comparisons and every
strict pruning round removes at least one. This is a finite reference
construction, with list membership and repeated expansion costs; it supplies
no optimized native complexity or total-allocation bound and does not replace
normal Simple-sub inference or search over alternative typings.

The next remaining evidence belongs to the graph-completion and native
serialization/history owners: construct an adequate exact finite graph,
reference assignment, inventory/metadata coverage and lawful history from
actual native results, and show their terminal demands pass the decision.
The original source-reconstruction owner must still obtain the complete
source/Call/effect witness with its original shared scopes. Neither these
premises nor the full `SourceProblem` instance is supplied by this module.

## Closure scope, resources, and stop receipt

Inspected scope: all 234 source lines; all 37 complete theorem type/axiom
entries; the audit driver and retained successful/failure logs; the actual
all-depth semantics, graph validity/checking, concrete history, decoder and
shared publication consumer definitions; baseline/checked-copy identities.
Previously accepted unchanged base proofs are carried forward rather than
claimed to have undergone a new whole-artifact review.

Uninspected scope: native Rust correctness/performance, the unfinished full
source instance, unrelated concurrent proof lanes, and primary-owned root
import/default-build/audit-integration edits. Those integration edits are not
part of this source-hash acceptance. No broad build, benchmark, or checker
rerun was performed. Budget: 700 seconds maximum; zero checker calls used.

Only the leased review file was written. No source/import/configuration,
shared scheduling state, Git index/ref, or other writer's file was modified.
No scratch directory was needed. No child or background process was started.
At freeze, review writing is stopped; primary adjudication and integration
remain with `/root`. The exact review-file SHA-256 is returned separately so
this revision does not contain a self-referential hash.

Freeze time: 2026-10-26 02:26:50 UTC (review began 2026-10-26 02:22:28 UTC).

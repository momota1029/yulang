# Centered ground composition, selection obstruction, and model extension

Status: partial construction, with a checked counterexample to the requested unconditional installation implication. The P/W execution from InitialSource is still open. This note does not claim the B4 statement is closed.

## Authority and scope

The controlling decision in [spec §6.5](../../spec/06-roles.md) is:

> 実際の引数の名前（中心）は明示して持つ

Its precise constraints are:

> 中心は `lower ≤ 中心 ≤ upper` を満たす未知の型の名前で、具体的な型を選ぶものではない。

> role の解決（候補の照合、曖昧、K2）は今までどおり区間の端点と既知の頭で行う。

> 実装が共有の情報を失ったことを理由に需要を保留にする規則は足さない

B4 addendum 8 expressly requires the trigger to be rejected by K2. No provenance-based pending branch is introduced here. Spec §6.3 also says:

> 同じ role の需要が二つあり、**すべての名前なしの引数が同じものを指す**（同じソースの識別子であるか、等式で同じと示せる）とき、二つの関連型の出力を等しいとし、需要を一つにまとめる。impl を選ぶ前、保留のままでも行う。

The existing definitions and Step remain unchanged. All additions are new modules; imports and this index entry are the only extensions to existing files. The full general carrier is retained. The ground boundary keeps the unrestricted centered Step and restricts only Initial, exactly as in the integrated accessibility result.

## 1. P/W readback: what is now established

[GeneralNominalCenteredTriggerReadback](../../lean/Yulang/GeneralNominalCenteredTriggerReadback.lean) uses the existing checked P/W declarations, including the additional `b` output in the Lean fixture. It computes the actual emitted W output list as `[anchor = T, out = T, b = U]`, where T and U are P's allocated output names. It never substitutes the standalone W fixture, whose output targets differ.

`w_named_schema` and `w_output_equation` derive `a ≈ V b` from that duplicated target and the W center equations. `p_head_value`, `child_value`, and `emitted_p_values` derive the recursive descent equation from P's head and its emitted child center. `emitted_w_values` identifies each W capture with the parent P capture. These facts supply all of the equations used in `recorded_trigger_cycle`:

- P0, W0, P1, and W1 occur in `state.plans`;
- their declarations are exactly the checked P/W declarations;
- W0 is P0's actual wrap child, P1 is P0's actual recursive child, and W1 is P1's actual wrap child, including their center functions;
- the common state has a model.

Under those premises, `recorded_trigger_cycle` proves a cycle in the centered recorded-test graph at W0's b binder. There is no supplied pump equation or supplied recorded-edge premise. `recorded_trigger_rejected` transports that cycle to W0's actual input center and proves Local = rejected, with the additional premises that W0's input is registered and its root is not pending. Unknown-root priority is preserved.

**This is a ledger theorem, not an execution witness.** The four installed plans, their common model, and their installation guards have not been constructed along a concrete path from the source fixture. The remaining route is P0 installation, compound endpoint refresh, W0 installation, source2 output refresh, P1 installation, compound endpoint refresh, then W1 installation. Fresh-ID assignment models, exact refresh certificates, and pre-state guard proofs are still required. The existing cyclic carrier value can witness final consistency, but no such concrete final assignment is claimed here.

## 2. Unconditional selected implies Installable is false

[GeneralNominalCenteredSelectionCounterexample.reachable_selected_obstruction](../../lean/Yulang/GeneralNominalCenteredSelectionCounterexample.lean) proves the following concrete conjunction:

```lean
Checked registry ∧
Reachable (groundBoundary roles) registry displayRoot cbefore ∧
Generated cbefore.erased.current displayRoot (child 10) ∧
Local registry cbefore (child 10) (.selected 3 []) ∧
¬ ∃ plan, plan.packet.site.occurrence = child 10 ∧
  Installable registry cbefore plan
```

The registry contains a Display implementation that emits two separate Display(Int) occurrences and the scalar Int leaf implementation. The initial root is the existing ground point Display(List(Int)) source. `cfirst` is an actual unrestricted centered installation from that source. At its successor, the scalar child is selected, but its equal-input sibling is not yet aliased. Every possible packet for the first child fails the retained `MergesClosed` installation condition. `required_merge_step` constructs the actual centered merge enabled in this state.

This refutes the requested implication on reachable states, including ground point sources. It does not refute a future implication scoped to states after required merging. It also does not refute selection implying installation **or semantic Committed**: the frozen Committed predicate is semantic branch entailment plus child-edge coverage, and can hold for an unrecorded scalar leaf with no children. The counterexample is specifically about the frozen Installable predicate and `CenteredWhere.Available`.

No new language decision is needed. The owner already requires merging before choosing. A subsequent additive boundary can classify after required administrative merging, or a bridge can establish availability only once the necessary closure is established. Neither repair is silently substituted for the quantifiers of the current request. Joint applicability, legacy value support, and a common centered branch model remain distinct obligations; closing merges alone is not claimed sufficient in general.

## 3. Models and nested centers

[GeneralNominalCenteredModelExtension](../../lean/Yulang/GeneralNominalCenteredModelExtension.lean) supplies:

- `source_models_same`: source Models are preserved by assignments equal on `GeneralNominalState.sources`, including type atoms, row atoms, base heads, intervals, and nominal descriptors.
- `site_extension`: a finite family of supplied center values fitting the intervals extends a source model, preserving all old supported names, provided equal center names have equal supplied values and already supported center names retain their old values.
- `root_extension`: for **every** source model and every raw InitialSource, an extended assignment models the default centered initial state and agrees on all old supported names. There is no point-root or finite-type restriction. Point centers retain the point name; nonpoint centers use the existing injective fresh namespace. Choosing endpoint values inside this existence proof does not change stored bounds or impose those values on all models.
- `observes_same`: arbitrary finite nominal/structural observation paths are preserved when the assignment agrees at their source identity.
- `nested_extension`: a finite family of nested nominal argument centers can be added while preserving the source model, given bounded supplied values, actual-origin readbacks, exact value coherence for shared names, preservation of supported centers, and supported endpoint/origin identities.

The nested theorem has no depth bound and preserves actual observational identity. It is not an automatic nested descriptor allocator or a general extension theorem for every installation plan. In particular, its supplied readback and coherence premises have not been derived for every emitted descriptor on every reachable centered state. Existing allocation namespace separation and stored-plan invariants remain available unchanged.

## 4. Exact V5 accounting

Let G = `GeneralNominalCenteredGroundBoundary.groundBoundary roles`, E = `GeneralNominalCenteredGroundComposition.executor roles`, and F = `GeneralNominalCenteredBoundary.frontiers roles`. The executor takes only registry, state, and root. It chooses a terminal state when checked reachability is available and otherwise returns the input state. Its diagnostic calls the existing resolver when exact frontiers and where accessibility are available and otherwise returns pending. That fallback has no claimed semantic correctness without the remaining accessibility law.

All state-dependent laws below retain the exact reachable-state quantifiers of [B4SkeletonV5.B4Bridges](../../lean/Yulang/B4SkeletonV5.lean): `∀ r, G.Checked r → ∀ s root, Reachable G r root s → ...`, except for the explicitly different signatures of localIdentity, dictionaryRefl, and initialReorders.

| Field | Exact conclusion / extra quantifiers | Status |
|---|---|---|
| progress | `Acc (fun next current => G.Step r root current next) s` | Proved by integrated ground accessibility |
| execution | `Steps (G.Step r root) s (E.run r s root).1` | Proved for E here |
| halted | `∀ next, ¬ G.Step r root (E.run r s root).1 next` | Proved for E here |
| closure | `(∀ next, ¬ G.Step r root s next) → G.Stable r s root ∧ ∀ child, G.Generated r s root child → G.Stable r s child` | Proved |
| stepModels | `∀ after, G.Step r root s after → ∀ model, G.Models after model → G.Models s model` | Proved |
| frontierLocal | `∀ d f, (F r s).frontier d = f ↔ B4TargetV3.Local G r s d f` | Proved |
| localIdentity | `∀ r s root, Reachable G r root s → (F r s).Local = B4TargetV3.Local G r s` | Proved |
| whereAccessible | `Acc (Child (B4TargetV3.Local G r s)) root` | Open on all reachable states |
| treeExecution | `∀ exact accessible, (E.run r s root).2 = resolve (F r (E.run r s root).1) exact root accessible` | Proved; exact/accessibility have the field's original types |
| canonicalLocalOrder | `∀ r r', G.Checked r → G.Checked r' → G.Reorders r r' → ∀ s root, Reachable G r root s → Reachable G r' root s → ∀ d f, Local G r (E.run r s root).1 d f ↔ Local G r' (E.run r' s root).1 d f` | Open |
| dictionaryRefl | `∀ dictionary, G.DictionaryEquivalent dictionary dictionary` | Proved |
| evidenceNode | `B4SkeletonV5.EvidenceNode G` | Open; exact model/parent/children stability signature retained |
| generatedChildren | `B4SkeletonV5.GeneratedChildren G` | Open; exact selected/stable/generated signature retained |
| initialReorders | `∀ r r', G.Checked r → G.Checked r' → G.Reorders r r' → ∀ s root, G.Initial r root s → G.Initial r' root s` | Proved |

`GeneralNominalCenteredGroundComposition.Remaining` contains exactly the four open field types. `bridges` inserts the ten proved fields without changing G, E, or F. `composition : Remaining roles → B4TargetV5.Statement G E` is conditional composition. The existing `CenteredWhere.whereAccessible` is only a stable-state theorem with Available as a premise; it does not discharge the stronger all-reachable field above.

## Verification and review

Final checks, all exit 0:

```sh
cd lean && lake build Yulang.GeneralNominalCenteredTriggerReadback Yulang.GeneralNominalCenteredSelectionCounterexample Yulang.GeneralNominalCenteredModelExtension Yulang.GeneralNominalCenteredGroundComposition
cd lean && lake build Yulang
cd lean && lake env lean Audit/CenteredGroundComposition.lean > /tmp/centered-ground-composition-audit.log 2>&1
python3 /tmp/check-centered-ground-composition.py
git diff --check
```

The module build completed 865 jobs; the full build completed 2354 jobs. The new audit covers all 52 public theorem declarations and reports only `propext`, `Classical.choice`, and `Quot.sound`. The validation script also checks the branch, exact new-file scope, unchanged prefixes of both permitted append-only files, import registration, audit coverage, and absence of prohibited constructs. Development elaboration failures were corrected before these final checks. No existing semantic definition was changed.

A fresh independent reviewer separately checked all four modules with `lake env lean` (exit 0), checked the key dependency outputs, and confirmed the stated scope limitations. The reviewer also checked the scalar leaf's semantic Committed property, which is why the counterexample is not presented as disproving the alternative installation-or-Committed statement.

The configured prover role and its registration/launch surface are absent in this checkout and live tool schema; no prover agent ran. The primary constructed these bounded proofs. Separate read-only source/counterexample probes and an independent artifact review were obtained; conditional results remain explicitly conditional.

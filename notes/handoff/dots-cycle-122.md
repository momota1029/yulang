# Cycle122: general dictionary equations and source-obligation ordering

**B4Bridges V2: 未証明 12 / 全 12。一般 B4 は未完成。**

Report prepared at 2026-11-11T18:13:56Z, after 46.43 minutes from heartbeat start
17:27:30 UTC. The completed heartbeat records terminal elapsed time after
publication and tree verification, within the approximately 50-minute budget.
The recovery plus several connected general-source subgoals did not fit in
25 minutes. First source publication was at about 15 minutes; the second
checkpoint completed at 17:53:17 UTC (about 25.8 minutes). The short delay was
bounded validation/Git object publication, not an early end or idle cycle.
Final stop reason: I-15 (a), the approximately 50-minute cycle limit.

## Closed subgoals and actual scope

1. **Recovery and real registry reorder relation** (first ~15 minutes).
   Reconciled cycle121's uncertain tree, retained the recovered I-17 target and
   both dictionary modules, then defined Reorders on the actual general Registry.
   Every constructor/signature/head/equation/binder/source identity is retained;
   only visible and where enumeration can move. All independent declaration
   checks, including capture stability, are transported.
2. **Exact child permutations and actual state equations** (~15–26 minutes).
   Reorders is symmetric/transitive and preserves Checked in both directions.
   Every complete emitted child structure is preserved up to permutation.
   Located head/output equations use actual state slots. Stored ordinary atoms
   imply their meaning in every model, using separate type and row source maps.
3. **Non-vacuous regressions, refinement, and order obstruction** (~26–30 minutes).
   A concrete satisfying model verifies repeated outputs remain separate (six
   atoms for one argument and two output occurrences), with type ID 10 and row
   ID 20. Global equations survive source-preserving refinements. Swapping two
   distinct clause IDs really changes the raw emitted list, so the skeleton's
   literal canonicalLocalOrder must not be assumed from a permutation theorem.
4. **Canonical source-clause emission** (~30–39 minutes).
   Existing unique clause IDs give a canonical declaration view preserving Checked.
   Reordered checked declarations produce exactly equal complete emitted children.
   No child is lost or duplicated; candidate/final-state correspondence is still open.

Recovered code comprises 32 I-17 target/assembly/regression theorems from cycle119
and 25 source-dictionary/equation theorems from cycle121. This cycle's new
modules add 34 theorems, not 91 new B4 theorems.
The 91-declaration audit covers recovery and all new work together.

## Theorems, quantifiers, and which part of M1 they serve

Full elaborated signatures, including implicit parameters and all premises, are
in [the theorem inventory](dots-cycle-122-theorems.md). Definitions and exact
source signatures remain in the seven listed modules. The following Japanese
claims describe the groups; none claims full completeness or principality.

- `GeneralSourceDictionaries` (18): 任意の role 宣言、source occurrence、有限辞書について、兄弟順だけの同値は根・実装 ID・全 occurrence の多重度を保つ。明示的な localRule が順序不変なら、その Evidence も同値。実 State の Linked は同値と source-preserving refinement で保たれる。**補助／条件付き健全性**。localRule の一般実装は未達。
- `GeneralSourceDictionaryEquations` (7): 任意の多引数 Demand、引数・出力ごとの ordinary 項、同一の任意の Assignment について、生成した全 atoms の成立と、全区間・全出力等式の成立が iff。Entailed がある場合は State の全モデルで出力等式が成り立つ。**局所の健全性・完全性／補助**。宣言から項を導く前提は解消していない。
- `GeneralRegistryReordering` (11): 任意の一般 Registry の Reorders は、可視宣言と ID 多重度を保存し、任意の DeclarationChecked を移す。**補助**。candidate や resolver の順序独立そのものではない。
- `GeneralRegistryChildOrder` (6): 任意の実宣言、where の permutation、各宣言の Signature、同一 Capture と clause-indexed Allocation について、emitAll の全 Emission が permutation。ID の異なる二つの子を交換すると raw list は異なる。**補助／反例による境界確認**。
- `GeneralDictionaryStateEquations` (6): 任意の State、Demand、Located package について、要求 atoms が実 ordinary list に保存されていれば、State の任意のモデルで全 head/output equations が成立。任意の Refines に沿って固定された global equations の Entailed は保たれる。**健全性の部品**。任意 State が Recorded を満たすとは言っていない。
- `GeneralDictionaryEquationExamples` (5): 具体的な充足モデル、二つの出力 occurrence、type/row ID の分離を確認。**回帰確認／健全性の部品**。新しい断片 classifier は作っていない。
- `GeneralCanonicalChildOrder` (6): 任意の Checked 宣言とその Reorders、同一 Capture と Allocation について、既存の一意な clause ID で正準化した全 Emission が等しい。正準化は全子と declaration checks を保存。**順序独立の局所部品**。異なる最終 State や候補の対応は未達。

No spec-mandated rejection range was weakened. New results either retain explicit
premises or prove their stated concrete storage/checking premise. The original
Lean theorem bodies, spec, plan, lake configuration, and other branches were not
changed. No new language decision was made.

## Thirteen SourceBoundary fields

| Field | Status at this cycle end | Remaining limit |
| --- | --- | --- |
| Checked | General certificate definition | Full constructor/Common adequacy and complete finite checker remain open. |
| Models | General checked-state component | No complete declaration/dictionary model. |
| Step | MISSING general definition | Refines is an update contract, not the saturation driver. |
| Stable | MISSING general definition | General EOF/sibling fixpoint absent. |
| Generated | General emitAll component only | Candidate provenance and actual materialization not connected. |
| RootPending | General partial snapshot definition | Needed is conservative; minimal applicability not derived. |
| RootK2 | General partial normalized definition | Partial normalization/source adequacy limits remain. |
| CandidateK2 | MISSING | Actual candidate inspection required. |
| InspectionPending | MISSING as full field | Existing normalization deferrals are only components. |
| Survivor | MISSING | Capture, ordinary propagation and where generation not unified. |
| Evidence | MISSING as full field | Source-indexed structural carrier, actual state equations and all-model lemmas exist; actual declaration-instance semantics and exhaustive child proof remain. |
| Reorders | General definition present | Canonical emission does not yet give whole candidate/state order correspondence. |
| DictionaryEquivalent | General source-indexed structural definition present | The key-only B4 payload still needs source-aware readback/canonicalization and model evidence. |

No generalVocabulary/generalBoundary instance or Executor.run is manufactured to
fill this table. No B4Bridges field is counted closed from a representation lemma.

## Verification

- Focused recovery build: `lake build Yulang.B4TargetV2Regressions Yulang.GeneralSourceDictionaries Yulang.GeneralSourceDictionaryEquations Yulang.GeneralRegistryReordering --wfail`: exit 0, 435 jobs.
- Child-order focused build: `lake build Yulang.GeneralRegistryChildOrder --wfail`: exit 0, 427 jobs.
- State-equation focused build: `lake build Yulang.GeneralDictionaryStateEquations --wfail`: exit 0, 424 jobs.
- Regression/obstruction/refinement focused build: `lake build Yulang.GeneralRegistryChildOrder Yulang.GeneralDictionaryEquationExamples --wfail`: exit 0, 432 jobs.
- Final aggregate: `lake build Yulang.B4TargetV2Regressions Yulang.GeneralSourceDictionaries Yulang.GeneralSourceDictionaryEquations Yulang.GeneralRegistryReordering Yulang.GeneralRegistryChildOrder Yulang.GeneralDictionaryStateEquations Yulang.GeneralDictionaryEquationExamples Yulang.GeneralCanonicalChildOrder --wfail`: exit 0, 439 jobs.
- Final audit: `env LEAN_PATH=/workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean cache/toolchain116/lean-4.35.0-linux/bin/lean --trust=0 yulang/cache/yulang122/FinalAudit.lean`: exit 0, 91 declarations; allowed-axiom whitelist passed. The inventory contains the full signature/audit output.
- `git diff --check`: exit 0.
- `bash tools/verify-lean.sh . origin/integration/m1-final --no-build`: exit 0 at final local code commit 4d81e472b.

Full no-build gate output:

```
verify-lean: yulang @ 4d81e472b (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

No whole lake build, full Audit.lean, or full verification gate ran in dot.
The first targeted audit had ten incorrectly qualified B4TargetV2Functionality
names; that harness error was corrected. A subsequent lake-env audit launch
hit its three-minute cap with no output. The combined signature/audit harness
also rejected an unsupported display option; removing it yielded the clean
exit-0 final run. The direct trust-zero audit then passed
all 68 declarations at that checkpoint; the final audit result is stated above.
Initial local proof attempts exposed a membership-name issue in canonical sorting
and a simplifier-order issue in state equation lifting. Final source uses actual
proofs and passed the stated checks; expected semantic results were not weakened.

## Publication and recovery

- Cycle121's exact uncertain tree `a8f5e34fbd557a4017a3d7399c102251ce635d72` returned GitHub 404. It had called neither create_commit nor update_ref. No uncertain branch mutation remained.
- Source publication 1: `abedb965832b07dccc8aaf34bba7676d0a2fc3f7`, all 21 blob hashes verified against tree `12e090a7b5d2344bdc79f7c8bd10cce006fce4e9`. core/proof CI passed for this exact commit.
- Source publication 2: `15fb561d4f7e937a773a50d1dd47f093a0ef29c6`, six changed entries verified against tree `40bf36d4c4ce2c30e1d8ada3e67498551ed8297a`. core/proof CI passed for this exact commit.
- Final source/report publication: source `d86ad8cf25226b8610742c447c262e124afcdf9e`, tree `2aeaa7574407128871e5e3c44b91d9f340098865`. The entire fetched tree equals the validated local intended tree. core/proof CI passed. This report and theorem inventory follow as documentation-only files and are verified after publication. Use the branch's final commit link rather than assuming the older CI results apply to later code.
- Every ref update used non-force expected-head publication to work/dots-main. Integration was read fresh at `4ec4ae877`; its supervisor additions were preserved. No denied operation was bypassed. Recovery reports119–121 and crash records119–121 were published. No source was lost.

There are 25 changed files relative to integration at the final source commit,
and 27 with this report and theorem inventory. Repeated heartbeat writes are
not counted as different files.

The final report tree hash and CI status are checked after this report's commit.
This avoids writing a circular self-commit hash into its own contents.

## Yulang2 comparison and remaining work

Read the fresh audit branch's `y2-claims-role-boundaries-cycle-2.md`, especially
ROLE-MORE-003/004. Old advertised where clauses and actual body dependencies
are distinct; old behavior was not imported into current spec 6.3. Spec 6.2
preserves call-site visible implementation identity, and 6.3 treats all where
children as a conjunction. No new old-runtime execution was performed.

No new semantic question note was added. Existing boundary-input/allocator
questions remain open and are not silently decided by a source ID field.
Next candidates, in order:
1. Define actual declaration-instance evidence from capture, emitted children,
   and materialized head/output terms. The generic constructor catalogue still
   needs its real ordinary/nominal interpretation; do not replace it by an oracle.
2. Connect canonicalEmit and source-indexed dictionaries to the real survivor
   children and B4 readback, retaining repeated source obligations.
3. Use recorded_entails/refinement to discharge evidenceNode once the actual
   candidate-to-state bridge supplies the stored constraints.

Usage quota: unknown. Writer and all completed command statuses are handed back
at cycle end; no unattended general build remains running.

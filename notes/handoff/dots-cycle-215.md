# Yulang cycle215 — general alias reinspection, raw projections and exact extrema residual

## Recovery and scope

Scheduled15:30UTC; actual start15:34:02UTC. Fresh integration92a801be7642ed7ffcdafbcab0a99c5b0ff034e5, standing orders and inbox reread, I40 unchanged. Cycle214 completed heartbeat/report and released writer checked before any source write. No overlapping previous writer was found. Research continued until16:15UTC, then verification/publication/report; conservative hard deadline16:25UTC.

Exact assigned goal remains `B4SkeletonV7.EvidenceNode (GeneralDictionaryDefaultBoundary208.boundary roles)`. FreshCompletion remains withdrawn. No target weakening, new semantic decision, target refutation, or full EvidenceNode proof is claimed.

## Verified mathematical progress (quantifiers and premises retained)

1. `RecursiveBounds215.inspect_bounds/many_bounds`: 任意の有限再帰query、構造/nominal/非点区間について、source Models、根の実観測の存在と区間Fits、schema head testsから、全anchorの観測存在とFitsを導出。有限中心やconstructor単射を追加仮定しない。`StructuralProjection215.structural_child` と `DefaultNominalProjection215.nominal_bounded` が全再帰形状を扱う。
2. `DefaultAliasCenters215.registered_alias_centers`: checkedなcorrected208 traceの登録済み入力2つは、実際のAlias閉包で結ばれていれば、任意のjournal Modelsで中心の意味が一致する。数値identity同一だけには制限しない。merge edge証拠、stepModels、同identityの既存証明を使用。
3. `DefaultAliasProjection215.projection`: checked、InitialSource、corrected trace、登録済みhistorical plan、current context、登録済みcandidate input、located bounds、Alias、同一declaration、任意のjournal modelからcurrent centered ProjectionModelsを導出。**Frame/Preparedは前提にしない**。current captureの同名共有もhistorical actual readbackから導出。
4. `DefaultAliasRawProjection215.projection`: 同じ前提でraw reportのProjectionModelsも導出。`WeakReport215`/`RawProjection215` は任意再帰形状のNone→Some origin対応を証明し、nominalのendpoint fallbackを一方向subtypeとinvariant nominal semanticsから処理。点区間や特定nominalだけの断片ではない。
5. `InspectionConflicts215.inspect_clear/many_clear`、`DefaultAliasConflicts215.conflicts_empty`: source Models、根Fits、schema testsから任意再帰inspectionのconflictsが空。actual Alias reinspectionではraw reportにも適用。blocked/arityの消失まではこの定理から主張しない。
6. `CurrentPropagation215.capture_compatible/raw_checks`: centered projectionからraw captureの全cross行列とselfChecksを導出。`CheckedAnchors215`/`CheckedOrigins215` は全checked intervalのanchorとorigin非依存性を証明。
7. `CurrentRawHead215.head_iff_merges/head_iff_capture_extrema`: 上記のhistorical Alias前提で**固定した同じjournal model**を使うと、current raw HeadModelsはcurrent merge equations（同値にpurpose0/1の下限union・上限intersectionの等式）と同値。投影やcross/selfcheckを追加仮定として残さず導出。`not_failed_of_merges` はこの同じmodelでmergesが満たされればcurrent Failedを排除する。
8. `AliasBranch215.revisit_branch`: checked/source/depth bound/trace、current Frame、歴史plan登録、Alias/同declaration、同一modelでjournal Modelsとraw HeadModelsがあれば、journalとraw branchを保ち全head equationsを足す保守的extensionがある。214で残っていたProjectionModels/BoundsFitの仮定を除いた。ただし共通modelの存在自体は結論にしていない。
9. `DefaultChoiceObstruction215.choice_iff_no_failed`: 正確なreachable selected domainで、ChoiceCompatibleは全historical aliased declarationのcurrent Failed排除と同値。pendingの代替候補はLocal.safeにより除外される。

## I40への到達範囲と未解決点

(A) の一般choiceはまだ未完成。conflicts側は排除できたが、current raw HeadModelsの非存在側を一般に排除できていない。(B) の一代入でjournal・packet・effectを同時に満たす主張も未完成。raw Preparedの存在証人とjournal Modelsの証人を混同しない。既存purpose0/1 slotsのextremaはhistorical/source制約に現れ得るので、actual binder purpose8のreadbackだけで書き換えてよいとは言えない。

No model exists → EvidenceAt vacuous, as I40 states; this cycle does not require an extra inhabitance condition for EvidenceNode. All fixed-model results quantify only where Models is supplied.

Counterexample-first audit: broad-nominal→pointで別候補を選ぶ素朴なprobeは、以前の選択時点でその候補がInspectionPendingとなりLocal.safeを満たさない。したがって目標の反例ではない。現在の補助の失敗をEvidenceNode反証とは扱わない。

## Next independent proof steps

1. Existing `DefaultAncestry208.sites_bounded head_readback` yields counted finite semantic labels for actual registered inputs from the real initial point/ground/coverage assumptions. `SemanticLabels.Inputs` is CountedMeaning (join-free covered labels), not merely arbitrary Meaning. Investigate deriving selected current head-schema tests and common head witnesses from that existing invariant plus Finished; do not add finite-center assumptions to the target. `FiniteBracket.structural_interval` is available only for canonical closed finite expressions, so the counted-pattern-to-expression bridge must be explicit. Existing HeadMatHeadReadback.readback itself assumes packet Holds and cannot be reused circularly.
2. Solve current/historical purpose0/1 extrema overlap or use semantic certificate replay where reinstallation is unavailable. The fixed-model `head_iff_capture_extrema` names the remaining obligation exactly; naming it is not its proof.
3. Alternative A route: backwards transport a selected candidate to the historical installation and use historical Unique/Safe. Design note lists the model-domain problem (Prepared's witness is not automatically a journal model), old focus/alias transport and private-extrema reconstruction obligations.

## Verification / publication / limits

25 new Lean modules; focused strict builds PASS, standalone trust0 audit **261 constants PASS**, diff-only gate PASS with3 reviewed audit scanner items. Full command outputs and explicit limitations: `notes/verification/dots-cycle-215.md` and `dots-cycle-215-logs.txt`. No full umbrella/legacy audit/runtime run. Tool/model usage quota: unknown.

First checkpoint4580a8d817a621dee3d59efab2eecc74ab08e9f5 (16files) readback16/16. Expanded30-file source/audit/index/design publication and final report hash/readback are recorded in completed heartbeat. Only work/dots-main is written; main/integration/spec/plan/lake config and pre-existing Lean source untouched. New audit within this cycle expanded from14 to25 modules; owner files only append imports/index entries.

## New module inventory

- `GeneralDictionaryAliasBranch215`
- `GeneralDictionaryCheckedAnchors215`
- `GeneralDictionaryCheckedOrigins215`
- `GeneralDictionaryCurrentBranch215`
- `GeneralDictionaryCurrentProjection215`
- `GeneralDictionaryCurrentPropagation215`
- `GeneralDictionaryCurrentRawHead215`
- `GeneralDictionaryCurrentRoots215`
- `GeneralDictionaryDefaultAliasCenters215`
- `GeneralDictionaryDefaultAliasConflicts215`
- `GeneralDictionaryDefaultAliasProjection215`
- `GeneralDictionaryDefaultAliasRawProjection215`
- `GeneralDictionaryDefaultAliasReadback215`
- `GeneralDictionaryDefaultChoiceObstruction215`
- `GeneralDictionaryDefaultNominalFallback215`
- `GeneralDictionaryDefaultNominalProjection215`
- `GeneralDictionaryDefaultPreFrame215`
- `GeneralDictionaryDefaultProjectionBounds215`
- `GeneralDictionaryInspectionConflicts215`
- `GeneralDictionaryInspectionHeads215`
- `GeneralDictionaryInspectionSchema215`
- `GeneralDictionaryRawProjection215`
- `GeneralDictionaryRecursiveBounds215`
- `GeneralDictionaryStructuralProjection215`
- `GeneralDictionaryWeakReport215`

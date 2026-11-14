# Cycle 181: 証明の主張と適用範囲

I-30 の目標は `B4SkeletonV5.EvidenceNode (GeneralNominalCenteredGroundBoundary.groundBoundary roles)`。この文書の補題群は、これを閉じる証明ではない。対象 G の新規閉鎖フィールドは 0 本。

## 任意の有限な観測族の拡張

`GeneralNominalObservationExtension181.extension_iff` と `GeneralNominalModeExtension181.extension_iff` は、任意の roles、任意の centered state、任意の自然数 count と `Fin count` で添字付けた nominal arguments、任意の以前の assignment を量化する。ただし以前の assignment が state の `Models` を満たし、各引数の上下端点および origin の source root が指定の有限 footprint に属することを前提に取る。二つの定理の差は footprint の定義で、前者は既存 fullSources、後者は今回証明した mode-sensitive fullSources を使う。

その前提の下で、footprint の全 assignment 値を**等号で保存**し、以前の Models と全引数の Holds を満たす assignment が存在することと、次の四条件の連言は同値である。

1. 各引数について、その origin に以前の assignment で観測される actual が少なくとも一つ存在する。
2. 各引数・各 actual について、当該 origin から観測されるなら、その actual は上下端点の Fits を満たす。
3. 任意の二つの引数・それぞれの任意の観測結果について、中心が同じなら観測結果は Equivalent である。添字が同じ場合も含むため、一つの origin の複数観測結果の整合性もここに含まれる。
4. 各引数・各観測結果について、中心が以前の footprint に属するなら、その観測結果は以前の中心値と Equivalent である。

Equivalent は相互の Subtype であり、構文上の等号ではない。`GeneralNominalSemanticCompatibility181.compatible_extension/compatible_iff` は代表値を明示した版。`GeneralNominalFramedExtension181.extension_iff` は任意の有限 footprint と、その上の assignment 一致が Models を保存するという明示的な frame 仮定を持つ版。ModeExtension ではその frame 仮定を ModeLedger の定理で解消したが、上の四条件や linked 前提は解消していない。

## 実際に検査された候補への接続

`GeneralDictionaryCenteredOverlapExact181.joint_model/compatible_of_joint/joint_iff` は任意の linear-leaf plan と既存モデルについて、対応する context/bounds と PointNames を前提に、非点 binder の旧 footprint との重なりにおける観測値の Equivalent 性と、指定した以前のモデルの旧 fullSources 上の assignment を等号で保存する joint model の存在を結ぶ。LinearLeafShape は terminal requirements、出力無し、一つの nominal query、異なる入力 binder 名、点の根の bounds という限定である。

`GeneralDictionaryCenteredProvenance181.compatible/joint` は、その形を持つ実際の Candidate、PointNames、centered path、および登録済み actual-use による Covered 証明を前提に上記互換性を作る。`installable/stable_instance` はさらに独立した raw installation と value-support guard の前提を残す。

`GeneralNominalLedgerReadback181.registered_actual/registered_readback/registered_alias_readback` は、任意の modeled ledger から登録済み head actual-use の意味を読み戻す。path や raw packet 登録はこの readback には不要である。これを使う `GeneralDictionaryCenteredLedger181.registered_covered/compatible/joint/alias_compatible/alias_joint` は path 前提を除いた。ただし実際の Candidate、LinearLeafShape、PointNames、plain/alias の Covered 証明は依然必要である。Reachable から Covered を生成する定理は未証明。

## 名前と source root の同一性

`GeneralNominalBinderIdentity181.binder_collision_iff` は同じ seed の非出力・非点 binder に対し、名前の一致と invocation/declaration/name の三つの一致が同値であることを示す。これは origin path の一致や型の構造的共有を意味しない。`binder_fresh` は非出力・非点 binder が purpose-8 の fresh 生成式に等しいことを示す（既存 footprint への非所属までは示さない）。`registered_readback/registered_identity_readback` は明示した登録済み actual-use witness からの意味の読戻しである。

`GeneralNominalOriginAlias181` の `nominal_congr/structural_congr/mapSource_similar/observes_mapSource/observes_mapSource_iff` は、意味的に Equivalent な source 名前替えの下で任意の nominal/structural path の観測を輸送する。非 source 観測は同じ actual 値を輸送するので、structural 観測の一意性は仮定しない。`GeneralNominalOriginRootAlias181.root_similar/root_observes_iff` は全 source ではなく当該 origin の root 値の Equivalent 性だけを必要とする。`certificate_equivalent/recorded_root_similar/recorded_observes_iff` は、root の等号、または現在の ordinary atoms に相反する二つの tyLe が記録されていることから、任意の source model でその Equivalent 性を得る。`GeneralDictionaryCenteredAliasProvenance181.compatible/joint` は、この RootRecorded と登録済み use の構文的 Covered 証明を消費するが、それを到達可能性から自動生成はしない。

## Mode に応じた frame

`GeneralNominalModeFrame181.schema_iff` は任意の plan/schema/二つの assignments について、mode-sensitive schema footprint 上の等号一致から SchemaHolds の同値を導く。actual use は origin と binder を、非 actual use は origin と capture の出力・上下端点を読む。`variableSources_subset/schemaSources_subset` はこの support が旧 support に含まれることを示す。`nonactual_singleton_iff` は非 actual 一件の schema への特殊化である。

`GeneralNominalModeLedger181.equations_iff/ledger_frame/centered_models_frame/centered_models_iff` は、全 plan equations、子の site/schema、centered sites に frame を持ち上げる。raw journal の footprint と capture bounds はそのまま保存する。`ledger_frame` は別途 raw Models を前提に持つが、`centered_models_frame/iff` は raw frame を接続している。いずれも到達可能性・充足可能性の隠れた仮定は追加していない。ある schema から binder が消えても、同じ binder が capture・別の actual use・子 site・raw journal に残る場合があるため、full footprint 全体から消えたとは結論しない。

## 四つの非空の回帰例

- SemanticCollisionExample181: 二つの引数が同じ fresh center を持ち、top と union(top,top) は Equivalent だが異なる。`semantic_extension` は拡張の存在、`exact_assignment_impossible` は両方を同時に構文等号で割り当てられないことを示す。Candidate fixture ではない。
- OriginAliasExample181: 異なる source root の間の ordinary equations と実際の int 観測を備えたモデルで、`recorded/observations/concrete_old/concrete_new/different_syntax` を示す。
- CenteredLedgerExample181: 非空 ledger、実際の検査済み Candidate、旧 binder との非点 overlap を持つ。`candidate/modeled/binder_member/not_fresh/covered/nonempty_joint` により、FreshInputs が偽でも joint model は存在する。既登録 plan 自身を使う例であり、novel な未登録候補の生成例ではない。Reachable/Stable/novel とは主張しない。
- ModeFrameExample181: 具体的な upper-use の一件の schema は、不要な binder を top から bottom に変えても成立し、旧 schema frame の一致は失敗する。完全な plan/journal をこの変更が保存するとは主張しない。

全 source 宣言名は `notes/verification/cycle181/final-declarations.tsv`（101 個）、private/generated を含む監査対象は 141 個。量化子・型・前提の機械可読な原本は各 Lean ファイルであり、本節はそれを省略した一般 EvidenceNode の完成宣言ではない。

### LinearLeafShape の省略しない読み方

上記の「出力無し」は **root.demand.outputs = []** という意味であり、declaration.outputNames が空という主張ではない。この構造はさらに declaration.role = root.demand.role、context の slot に descriptor が登録済みであること、descriptor の全 arguments が bounds から作る type 列に等しいこと、declaration.inputNames が injective names の列そのものであること、queries が指定 nominal descriptor と各一変数の pattern の一件だけであること、arguments context root が点の一件 [(slot,slot)] を返すことを要求する。これらは構造のフィールドとして全消費定理の前提に含まれる。Corresponding context/bounds、PointNames、以前の Models といった定理固有の追加前提も省いてはならない。

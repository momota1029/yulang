# Cycle255 宣言ガイド

全168明示宣言（定義＋定理）の名前をmodule別に列挙する。量化子・条件の正式な型は各LeanファイルとComplete auditの対象名に対応する。

側: すべてM1/B4のための補助。Models/Equivalentのiffは表現の健全性・完全性の保存に効くが、M1主型性やB4停止性の完了を意味しない。



## GeneralDictionarySourceAtom255

固定252 sourceについて、任意のowner候補keys・任意sideでint定数はvar-only basisに入らず、prepareはnone。実ordinary atomの所属とInitial・Modelsを併記する。全Viewを一律に正規化する案の診断であり、lo/hi限定案やsource Stepの反証ではない。

宣言: `constant_not_basis`, `prepare_constant_none`, `ordinary_member`, `actual_source_failure`



## GeneralNominalViewTypeTerms255

任意Viewの型fieldを列挙する。任意side・列挙された任意termについて、atomsはそのViewから採ったpoolに含まれ、prepareが成功し任意assignmentでEquivalent。row fieldの有限化は主張しない。

宣言: `parameter`, `descriptor`, `ordinary`, `slot`, `terms`, `pool`, `slot_mem`, `ordinary_mem`, `supported`, `prepare_success`, `normalize_equivalent`



## GeneralNominalViewTypeMap255

任意の型項変換f・View・assignmentについて、列挙した全型fieldでfがEquivalentを保つなら、slot/ordinary/head/nominal引数をfで写したViewのModelsは元と同値。row・interval・slot数は保持。

宣言: `parameter`, `descriptor`, `ordinary`, `map`, `ExactOn`, `equivalent_iff`, `parameter_exact`, `fitsAll_exact`, `descriptor_exact`, `ordinary_exact`, `models_exact`



## GeneralNominalViewNormal255

任意side/basis/Viewについてcheck=trueとSupportedは同値。prepare成功時の全Models同値、初期View自身のpoolでの無条件成功、支持の単調性を示す。任意の未来ViewのSupportedは仮定のまま。

宣言: `Supported`, `check`, `rewrite`, `prepare`, `check_exact`, `prepare_exact`, `rewrite_models`, `prepare_models`, `source_pool_success`, `source_pool_models`, `compiled_source_models`, `rows_unchanged`, `slots_unchanged`, `intervals_unchanged`, `prepare_none`, `supported_mono`, `expanded_source_success`



## GeneralDictionaryViewNormal255

252の実source Viewで、任意keys/sideのvar-only prepare失敗と、source atom＋public refsでのprepare成功・全assignmentのModels同値を対比。実sourceのModelsを持つ結果が存在する。

宣言: `constant_consumer`, `var_basis_fails`, `source_basis_repairs`, `inhabited_repair`



## GeneralPresenceSourceSupport255

任意carrierのtype/row置換について、全変数の置換先の読みがpool内なら結果の読みもpool内。identity置換の読み保存、二つの全読みcollector一致、union/inter atomの読みが元の読みの部分集合であることを示す。

宣言: `row_subst`, `type_subst`, `row_identity`, `type_identity`, `row_collectors`, `type_collectors`, `union_atom_sources`, `inter_atom_sources`



## GeneralNominalSourceViewSupport255

任意GeneralNominalStateをidentityでcompileしたViewについて、全type consumerとそのpool atomの読みがstate.sourcesに含まれる。row引数・arrow内部row読みも型項collectorの範囲では含む。

宣言: `slot_source`, `slot_row`, `slot_type`, `slot_rows`, `base_type`, `ordinary_type`, `parameter_type`, `descriptor_type`, `compiled_terms`, `compiled_pool`



## GeneralNominalSourceBasis255

任意context/keys/sideで、初期identity Viewのsource atom＋public refs basisはSupported・prepare成功・全Models同値。InitialSourceを持つ場合、purpose≤1の任意private名がbasisから読まれない。

宣言: `basis`, `source_separated`, `separated`, `source_supported`, `source_success`, `source_models`, `consumer_safe`



## GeneralNominalViewTypeImage255

任意f/Viewでconsumer listは厳密にlist.map f。パラメータ・ordinary・descriptor・Viewの写像合同、合成、identityを証明する。意味同値の一意正規形ではない。

宣言: `parameter_terms`, `descriptor_terms`, `ordinary_terms`, `slot_terms`, `view_terms`, `term_origin`, `parameter_congr`, `descriptor_congr`, `ordinary_congr`, `map_congr`, `parameter_comp`, `descriptor_comp`, `ordinary_comp`, `map_comp`, `parameter_id`, `descriptor_id`, `ordinary_id`, `map_id`



## GeneralNominalViewFixed255

任意basis/sideで各rewrite後type fieldは長さ2^basis.lengthの候補listに入る。Supportedのもとでwhole-View prepareは冪等。basis全atomがprivate名を読まなければrewrite型fieldも読まないが、意味保存には別途Supportedが必要。

宣言: `candidates`, `candidate_count`, `normalized_candidate`, `field_candidates`, `rewritten_supported`, `rewrite_idempotent`, `prepare_idempotent`, `field_private_free`



## GeneralNominalTemplateChoices255

任意raw template・有限leaf pool・variablesについて、実際に読む(mode,name)の値がpool内なら実compile結果が有限Cartesian menuに入る。nominal内部はactual mode。同一binderの別出現を独立に選べる過大近似。

宣言: `choices`, `choicesMany`, `reads`, `readsMany`, `compiled_mem`, `compiledMany_mem`



## GeneralNominalTemplateCongruence255

任意template/mode・二つのvariablesについて、実際に読む(mode,name)でEquivalentならvalueがEquivalent。type項variablesをevalした実materialized compileにも適用。

宣言: `value_equivalent`, `values_equivalent`, `compiled_equivalent`



## GeneralNominalTemplateNormal255

任意policy/basis/variables/mode/templateについて使用leafの実checkとSupportedが同値。prepare成功時に有限menu所属と任意assignmentで元compile結果へのEquivalent。rewriteだけの有限性では意味保存を結論しない。

宣言: `leafCandidates`, `normalized`, `Supported`, `check`, `rewrite`, `prepare`, `check_exact`, `prepare_exact`, `normalized_candidate`, `rewrite_finite`, `rewrite_equivalent`, `prepare_safe`



## GeneralNominalSourceTemplateMenu255

実sourceからの任意mixed trace・実frame・要求output・Supplies・compileBody成功について、使用leafの候補所属から固定source template menuへの所属。prepare成功なら任意assignmentで意味保存も得る。

宣言: `menu`, `source_compiled`, `source_normalized`, `source_prepared`



## GeneralNominalTemplateSupport255

任意finite template menu項のsource leafはleaf pool内。pool各項がprivate名を読まないならそのmenu項も読まない。候補subsetは元basisの部分集合。正規化後式のprivate非流出だけでは意味保存とは言わない。

宣言: `sourceTerms`, `sourceTermsMany`, `choices_sources`, `choicesMany_sources`, `reads`, `choice_private_free`, `selected_subset`, `candidate_private_free`, `rewritten_private_free`



## GeneralNominalCanonicalBasis255

raw source/public basisをeraseDupsし、任意context/keysでNodup。初期Viewの支持・prepare・全Models保存、InitialSource条件でprivate分離を継承。Supportedかつbasis.Nodupなら選択sideの正規化後atoms.Nodup。

宣言: `dedup_nodup`, `basis`, `basis_unique`, `basis_mem`, `source_supported`, `source_success`, `source_models`, `separated`, `normalized_atoms_unique`, `source_fields_unique`



## GeneralNominalNormalizedDepth255

任意basis/side/type項の保存syntax正規化深さ≤1+basis.length+最大atom深さ。任意raw templateではそのrawDepthを加算。実source frameなら固定template budgetで上界化。ground readback深さではなく、意味保存条件を代用しない。

宣言: `atomDepth`, `leafBound`, `atom_bounded`, `union_fold_depth`, `inter_fold_depth`, `normalized_depth`, `rewritten_depth`, `source_rewrite_depth`



## GeneralDictionaryTemplateMenu255

252の実Initial/frame/明示bodyでF(F(var2))が実compileBody・固定有限menuに対応し、canonical basis上prepare成功。任意assignmentで旧versioned output valueとEquivalent。保存syntax深さ2、具体modelではP（既存ground展開深さ4）を表す。

宣言: `supplied`, `compiled`, `reads_exact`, `materialized`, `actual_finite_menu`, `normalized_reference`, `supported`, `rewritten`, `prepared`, `all_models_exact`, `raw_depth_two`, `source_regression`



## GeneralNominalSourcePublicBasis255

source由来owner候補から実行前に固定basisを定義。実Initialだけから初期View prepare成功・basis.Nodup・private purpose0/1分離を持つbasisが存在。任意後続stateのGenerated/Installable/未Committed installのpurposes2〜5 port varがこのbasisに入る。全consumer/代入閉包ではない。

宣言: `basis`, `initial_success`, `private_separated`, `installed_port`, `installed_port_prepared`, `mixed_source_basis`

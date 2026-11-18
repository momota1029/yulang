# Cycle253 宣言ガイド

全115宣言の完全名は `CompleteAudit-declarations.txt`。以下は各公開モジュールの
定義と定理群の前提・量化範囲。定理は常に本文の全引数についての主張。

- **GeneralPatternAdditiveDepth253**: `depth/depths` はPattern/listの構文深さ。
  `subst_depth/subst_depths/substitution_from_pool` はcapture全像が深さB以下
  （または指定pool内）なら代入深さ≤template深さ+B。`rename_depth(s)` はvar
  renameで深さ不変。`member_depth` はlist最大以下。`tower*` と
  `additive_bound_sharp` は加算がsharpである構文例。
  `depth_le_size/depths_le_size` はencode木サイズ以下。最後のnormalize後や
  全semantic-equivalent代表の深さを抑える定理ではない。
- **GeneralNominalExprDepth253**: 実compiler243のRaw/Materialized式を使用。
  `compile_depth(s)` は全mode/nameのsource葉のtypeDepth≤Bを前提に加算上界。
  `reference_depth(s)` は全葉がvarならraw template深さのまま。typeDepthはtype
  constructorの深さでrow sortの構文を数えない。nominal内は実装どおりactual mode。
- **GeneralNominalRawFinite253**: `choices/manyChoices/templateChoices` は指定pool
  による有限列挙。`compile_mem/compileMany_mem/template_mem` は全mode/nameの
  葉がpoolにある場合の実compiler結果の在籍。`opaque_reference_mem` はvar参照版。
  `combine*`, `variableCount(s)`, `choices_count/manyChoices_count` は列挙長が
  pool長の変数出現数乗であること。異なる出現で選択を独立にした過大列挙。
- **GeneralNominalOutputNames253**: `outputs/output_mem` はownerキーとvisible
  declarationのnamed output binderをpurpose2で列挙。
  `installed_output_enumerated` はformed point ground source、coverage、実mixed
  trace、Generated、Installable、未Committedから在籍を導く。
  `mixed_finite_outputs/point_finite_outputs` は実source Initialから一つの有限list
  を作り、全将来の該当installのnamed outputを覆う。全public端点ではない。
- **GeneralNominalPublicPorts253**: `ports/names` は修正候補basis。named output2、
  child compound入力3/4、clause output target5を列挙する。
  `port_mem/output_mem/argument_mem/clause_output_mem/port_purpose` は候補の在籍と
  purpose範囲。`aggregate_not_port/names` はpurpose≤1のversioned aggregateが
  binding履歴によらず外にあること。`installed_port_enumerated/mixed_finite_ports`
  は上と同じactual source、Generated/Installable/novelの範囲で有限listを供給。
  center7/8/9や全状態supportを覆うとは主張しない。operational定義を変更していない。
- **GeneralDictionaryCompoundPool253**: 実238 fixtureに限定。
  `endpoint_allocated/new/not_pool/no_named_outputs` はcompound where入力端点が
  元source名とnamed output名のpool外（owner listは任意）であること。
  `emitted/site_reached/point_step/point_reachable/source_reachable_pool_gap` は
  I45の実一歩到達とこの欠落を組合せる。
  `private_rewrite_unsupported` は任意old blockが当該公開端点をtargetにしない
  明示前提の下で、端点var atomの置換後もpool外となること。
  未実装のrebase SnapshotNormal実行失敗や非停止のtraceではない。
- **GeneralDictionaryCompoundPoolRepair253**: 同fixtureの`endpoint_in_ports`、
  ownerキー在籍を仮定する`endpoint_in_names/repaired_atomic_support`と
  `pool_gap_and_local_repair`。狭いpoolの具体的欠落だけを修復。全source閉包ではない。
- **GeneralPatternDependencyDepth253**: `Build` は各nodeのcaptureがsourceまたは
  既に構成された出力を読む明示的topological構成。
  `sum_bound/lengths/sum_le_uniform/uniform_bound` はこの構成を前提に
  sourceDepth＋template深さの総和（粗くはnode数×T）以下。
  `no_positive_cycle` は有限Nat depthの正増分cycleの矛盾、`alias_cycle_possible`
  は0増分aliasをこの議論で排除できないこと。node数をowner数と同一視しない。
- **GeneralDictionaryOutputDepthRepair253**: 252の同一actual source・同一I45
  到達出力を維持した`sharp/additive/source_reachable_additive_repair`。
  maxの反例だった2,2,4が加算2+2=4をちょうど満たす。意味上の出力はinstalled
  Modelsを満たすすべてのassignmentでforcedされたまま。
- **GeneralDeclarationProducerRank253**: `Child/child_mass/accessible/calls_wellFounded`
  はchecked宣言のraw-before-counting呼出し関係だけのAcc。
  `NormalizedChild/normalized_child_mass/normalized_accessible/normalized_calls_wellFounded`
  は実Associatedと同じnormalizeArgs-before-captureの順序。後者は既存の
  CountsCovered＋ConservativeSmallerによる減少を使用し、両順序の交換を仮定しない。
  `child_inputs_independent` はinputNames一致からchild入力一致。
  `binder_producer/normalized_binder_producer` はProducedとSatisfiesOutputsから
  指定childの出力値とその小さい入力を取り出す。選択候補・scheduler・journal
  更新を実装したものではなく、そのStepのAccでもない。
- **GeneralDeclarationOutputDepth253**: `subst_supported` はtemplate使用変数のみ
  のdepth前提で加算上界。`associated_bound` はchecked scopeからinput bound Iと
  output-binder bound Oのmaxを使う。`produced_bound` はchild Associated値のboundを
  仮定しProducedからbinder値のboundを供給。`associated_from_children` はこれらを
  合成する。子のboundを無条件にowner入力boundへ落とさない。
- **GeneralNominalPublicBasis253**: `privateName/private_not_ports/private_not_names`
  はpurpose≤1の任意position（固定rebase0とversioned位置を両方含む）の分離。
  `basis/basis_separated` はformed sourceのbelow_seedとpurpose区別により、source名
  ＋public portsのvar poolが全private名を読まないこと。
  `lower_private_free/upper_private_free` は正規化結果の全typeSources（row含む）
  の分離。`lower_safe/upper_safe` はさらにatoms Supported前提を付けて、実モデル
  での意味保存・有限候補在籍・private-freeを同時に返す。Supportedは未導出。
- **GeneralNominalAllHeadReadback253**: `head_weight_covered` は実Frame/Holds、ground
  Inputs、正規化headのcoveredArgs=trueからhead schemaの重み上界。
  `finite_capture_covered/readback_covered` は全inputNames（associatedだけで使う
  入力を含む）の有限Partと各encodeサイズ≤入力labels massを導出。
  `readback` は非空whereならchecked.countsCoveredからcoverageを供給する版。
  `readback_depth/readback_depth_covered` はdepth≤encode.sizeで深さ上界も返す。
  coveredなleafには適用できるが、全leafを覆うとは言わない。output-only binderの
  child値やsource全体のreadback producerを仮定なしに得たわけではない。

# Yulang3 型推論の形式化

このディレクトリは [`spec/10-inference-core.md`](../spec/10-inference-core.md) の核を Lean で検証する。古い型推論器や proof sprint は復元せず、現行仕様に対応する定義と定理を置く。

Lean は `lean-toolchain` の **4.35.0** に固定する。依存は Lean/Std のみで、Mathlib や外部 solver は使わない。

```sh
cd lean
lake build
lake env lean --trust=0 Audit.lean
```

## 証明対象

| モジュール | 閉じる主張 | それだけでは示さないこと |
| --- | --- | --- |
| `Yulang.Types` / `Yulang.Inference` | 構造再帰する有限制約生成、独立な宣言的型付けとの双方向の一致、制約schemeの主性、非再帰の値制限付き多相let | 全制約の判定、再帰SCC、sourceのoperation/handlerのelaboration、公開型の正規化 |
| `Yulang.StructuralBase` / `Yulang.Structural` | 行の解釈を共有する具体的な構造部分型モデル、union/intersection・幅部分型・関数の分散、生成制約の正例と反例 | 完全なMLsub意味論、再帰型、部分型の決定手続き |
| `Yulang.Polymorphism` | effect付きcomputation変数の単相let束縛を受理し、そのeffectを空行へ消す生成制約を拒否すること | 再帰的な一般化、sourceのalias解析 |
| `Yulang.Effects` | 出現ごとの保護・解除、任意の行置換での非capture、well-founded computation treeでの非capture、shallow handlerのeffect上界 | sourceからのelaboration、operation署名の型安全性、全言語のpreservation/progress |
| `Yulang.EffectInference` | core生成器を使うrequest・boundary・shallow handler規則の健全性と完全性、有限個のoperation-local型変数の呼出側での存在具体化・handler側での全称検査、結果と外側環境へのescapeの構造的排除、単相規則と明示された実行時上界の合成 | sourceからのelaboration、atomのpayload内部にある局所変数、局所変数のrole制約、型付けから実行時上界を導く証明 |
| `Yulang.RowInference` | 同じrequest・boundary・handler制約生成を非負行と符号付き行に具体化する共通の双方向定理、operation-local型変数の存在具体化・rigidな全称検査、行置換と評価の両立 | sourceからのelaboration、atomのpayload内部にある局所変数、局所変数のrole制約、型に沿った潜在行の変換、量化を含む制約のsolver |
| `Yulang.SignedStructural` | 実際の符号付き行を持つ構造部分型モデル、operationのeffectと負の解除差分を保持する生成制約の正例・負例、局所型の任意の具体化と独立した二回の呼出し、rigidなpayloadを継続に渡す正例と固定int結果へ返す負例 | 完全なMLsub意味論・solver、sourceの由来条件の保存 |
| `Yulang.HigherOrder` | 有限の型shapeに沿ったproduct/list等の格納callbackの保護と非capture。単純なerase解除の限界を示す反例 | 任意の高階の境界の意味保存。`guard ∘ release` はこのモデルでは恒等でない |
| `Yulang.Directed` | 符号付きの境界差分、両方向の相殺、非負保護listの埋込み、明示した由来条件の下での非capture | sourceから動的な境界を構成し、由来条件を保存すること |
| `Yulang.FreshBoundaries` | 任意の単射による境界座標の拡張、既存の符号付き重み・capture・残余・handler実行の保存、新しい座標の割当てによる原点条件の構成と任意の元のrequest treeの非capture | sourceの全呼出しがこの割当てを使うこと、返り値・payload・response内部の潜在callbackの変換 |
| `Yulang.FreshRowInference` | 全有限RowExprについての境界名の写像と評価の可換性、任意の未知tailを含む評価結果のfresh原点条件、T3のsnapshot・保存履歴・formulaのgateの不変性 | source境界の発見、型slotのfreshening、潜在callbackの変換、型付けからruntime上界を導くこと |
| `Yulang.DirectedHigherOrder` | 任意の有限shapeと値における両方向の高階transportの相殺、由来条件付き非capture、混在した由来のcallbackの例 | 再帰型、atom・operation payload内部のtransport、sourceのelaborationとpreservation/progress |
| `Yulang.DirectedBounds` | 符号付き行でのshallow handlerのeffect上界、保護・解除による上界の双方向のtransport | sourceの型付けからaction・armの上界を導くこと、値内部の潜在行 |
| `Yulang.DirectedHandlerInference` | 成立した共通のhandler生成制約とaction・armの実行時上界から、実際の符号付きhandler全体の上界を導くこと | action・armの前提そのものをsourceの型付けから導くこと |
| `Yulang.Annotations` / `Yulang.AnnotationSnapshots` | 注釈時点の可視effect検査と正確性、符号付きの観測履歴の固定、T3 の具体化時に再検査しない規則と主制約生成器の接続、未知行の後の具体化と当初から既知で可視な禁止effectの区別 | 何がその時点で既知かを決める solver、source 注釈から観測時点を構成する elaboration |
| `Yulang.AnnotationFinalization` | binding/SCC全体の有限Horn制約を解いてから符号付き観測を固定する入口、最小解の真のfactと全モデルで強制されるfactの一致、制約順序・重複・member順序に依存しない受理、一般化前の検査と後の具体化の分離 | 構造型推論から有限fact interfaceへの翻訳、無限のsigned stackを含む全体solver、sourceのSCC発見と名前の振り直し |
| `Yulang.RecursiveInference` / `Yulang.RecursiveExamples` | 有限の同時再帰制約生成と独立な SCC 型判断の一致、全注釈の値型変数だけを具体化する多相再帰、明示的なeffect行の共有、SCC 後の値の一般化と computed slot の保持、有限の構造型すべてについて depth 型再帰の単相拒否と注釈による受理 | source の SCC 発見と全注釈認識、local/captured slot 分類の推論、解の探索、再帰型での depth の拒否、評価依存の検査 |
| `Yulang.QualifiedInference` / `Yulang.QualifiedGeneralization` | resolved method からの role 制約生成と独立な型判断の一致・主性、raw role 制約の自動分配、抽象辞書での定義検査と利用時の証拠要求、環境slotの共有、通常のletでの値型・行の独立した一般化 | 未解決の構造制約から一般化interfaceを発見するsolver、source の method lookup、任意に入れ子になった source qualified let の elaboration |
| `Yulang.ModuleRoles` / `Yulang.QualifiedExamples` | 与えられた部分割当てとinterfaceに対するEOF検査、実際のresolverによる残留role制約の確認、公開型に使う未確定slotの拒否、公開schemeの意味と解の拡張に対する独立性、辞書の有無・型の後決め・非空の潜在行の正例と負例 | module全体から未解決制約を漏れなく収集するsource pass、部分型の解を探索すること、opaqueな意味的型の内部表現に関する閉性 |
| `Yulang.RoleEvidence` / `Yulang.RoleEvidenceExamples` | role要求を持つ既存のPolySignatureについて、呼出側の存在具体化と証拠要求、handler側のrigidな全称検査と署名辞書、qualified生成器を使った双方向の一致、実際の符号付きモデルでの辞書使用と証拠欠如の負例 | sourceのoperation/handler構文全体のelaboration、atomのpayload内部の局所変数、型付けから実行時の上界・安全性を導くこと |
| `Yulang.Roles` | 第一階 impl 集合の一方向照合、Paterson 型条件による置換後の型サイズの真の減少と深さ制限なしの解決の停止、健全性、到達する head に重なりがない場合の完全性、到達可能な head の重なりと曖昧さの同値、正例・負例 | generic role の method dispatch、章6.4の receiver 下界による解決保留、effect との相互作用、operation-local role 制約、推論の制約言語との統合 |
| `Yulang.RolesAssoc` | 第一階の関連型の明示定義と default、解決成功時の宣言済み各名前の全域性・一意性、where の導出や照合置換によらない値、goal の変数だけを含む結果、明示定義の置換後のサイズ公式、正例・負例 | 関連型を含む method 署名、`value ~ int` 等の等式制約や where 条件との単一化、receiver 下界による解決保留、source 宣言検査。他 role の関連型を右辺で参照することは2026-11-05の決定により対象外 |
| `Yulang.RoleConstraints` | 具体的なresolverの成功と導出・非曖昧性の一致、関連型選択から普通の等式の追加への接続、全置換について等式制約追加の可換性・冪等性・順列不変性、既存制約との矛盾を上書きしないこと | 未知の置換を探索する単一化器、構造部分型とrole制約を合わせた全体solver。`Store.check` は与えられた置換での検査 |
| `Yulang.CheckedRoles` | 有限の宣言検査と全変数についての Paterson 適格性の同値、証明を入力に要求しないresolver入口、不適格な宣言の拒否、適格な集合での成功・曖昧さの正確性 | source parser/name resolution、関連型宣言の全検査、診断位置・文言、疎な変数番号での計算量最適化 |
| `Yulang.ImplHeads` | impl headの各holeを別の変数へ下ろす処理、全匿名識別子の一回性と名前付き変数の共有、whereから匿名変数への参照不能性、ref全体の照合と部分特化 | source parser・型/行のkind検査、未束縛名の診断、methodの可視性や段階ごとの検索 |
| `Yulang.Horn` | 任意の有限Horn制約に対する解の存在判定と最小モデル。成功・失敗の両方向の完全性 | 構造部分型、再帰型、無限の保護stack、roleの解決 |
| `Yulang.RecursiveRows` | 保護・解除・残余を含む正の再帰的行制約 `E ≤ slot` の最小集合解、全解で強制される出現との一致、固定上界との両立の必要十分条件、既存の有限行解釈の保存、有限行では解けない保護反復の例 | 解への所属の決定手続き、任意の右辺を持つ行包含、構造型solver、sourceからの制約抽出、すべての再帰行の有限表示 |
| `Yulang.RecursiveEffects` | 全既存core式とrequest・boundary・shallow handlerを同じ再帰ASTに置く有限制約生成、任意の入れ子について独立な型判断との双方向一致・制約schemeの主性、値制限付き多相letと署名のambient slotの保持 | operation-local多相・roleを含む統合、再帰SCC、source elaboration、制約solver、型付けからruntime安全性への接続 |
| `Yulang.FiniteReachability` | 有限隣接リストから計算する到達集合と独立な有限経路の判断の一致、空の始点集合からの到達不能性、辺・始点の順序と重複に対する不変性 | source の依存関係抽出、未具体化の多相 cast 集合の有限性、実用的な計算量 |
| `Yulang.EvaluationOrder` | 名前解決済みの有限宣言・module 文からの評価依存計算と独立な推移的依存判断の一致、computed 自己依存・未来の computed binding の拒否、受理された初期化・文の全依存が元の順序で利用可能なこと、lambda による遅延と直接適用時の依存の復帰 | source の名前解決、局所 closure/alias や格納された関数のフロー、任意の高階 callback の実行が依存判断に含まれること、全言語の副作用順序の保存 |
| `Yulang.EvaluationSafety` / `Yulang.EvaluationReads` | 名前で決まらない呼出しへのmodule全体の関数本体近似、独立なCBV読み取りprefixの上界、closure由来の保存、局所・返却・格納closureの読み取り安全性、既評価prefixからの参照先の利用可能性 | source elaboration、外部由来closure、可変store、計算全体の停止・progress。module内のlambda由来とsource位置の構造を明示 |
| `Yulang.Initialization` | 同じresolved本体のSCC生成と二つの初期化検査への接続、値制限の一致、型の割当てによらないcomputed cycle拒否、生成制約から実際の読み取り先の先行性と既評価prefixでの値の存在を導くこと | 全注釈を持つsource moduleのelaboration、module文の結果型検査、全言語のprogress/preservation |
| `Yulang.Methods` | unionの相異なるreceiver候補の0・1・複数の三分、全memberから選択先へのcast検査、選択と変換検査全体の順序不変性 | method lookupの優先順位・可視性、未確定receiver下界の保留、source unionの正規化。refは特別扱いせず全体を照合する（`ImplHeads`） |
| `Yulang.Casts` | 普通の適合性と別の境界変換判断、関数の入力反変・出力共変、tuple・record field・variant payload の共変変換の実行可能な検査と正確性、固定nominal引数を変えるには外側全体の規則が必要なこと | 普通の部分型の決定手続き、effectを持つcastの実行意味、等価な型表記の正規化、未具体化のcast宣言のground化 |
| `Yulang.PureCasts` | 空の符号付き行によるcast宣言検査、チェック済み本体から合成した構造変換の純粋性、境界挿入と関数wrapperによる実際のrequest tree・任意の行上界の保存 | 宣言本体のoperationalな行上界をsource型付けから導くこと、`Casts.Boundary`からtyped planを合成するelaboration、異なるcast経路の値の一致 |
| `Yulang.CastGraph` / `Yulang.CastExamples` | 有限ground登録の検査と深さ制限なしの経路判定、直接重複拒否と複数の間接経路許容、適合時の変換省略、nominal全体からpair・関数・unionへのunbox、source unionの全member検査 | 多相endpoint探索とのsource表現の接続、経路コードの合成、異なる経路の実行結果の一致。登録された直接sourceはnominal/baseに限定 |
| `Yulang.ParametricCastRules` / `Yulang.ParametricCastUniverse` / `Yulang.ParametricCasts` | 多相castの宣言検査と全置換後のサイズ非増大、入力と有限宣言から導く有限alphabet・サイズ上界・到達型集合、任意の有限経路との同値を満たす実行可能な探索、等サイズ循環と固定ground型の拡大の許容 | 明示規則のendpoint探索からsource境界へのelaboration、直接規則の重複・重なり診断、構造変換を混ぜた全言語のsolver、実用的な計算量 |
| `Yulang.LiteralCasts` | list literal の元の構築位置を保持した変換計画、期待要素型が決まった場合の全要素の境界検査、EOFで期待型がない場合の元の要素型のunionと変換省略 | 弱い要素型を解くsolver、cast本体の実行・effect、構築済みlistの変更、空unionを含む表示上の正規化 |
| `Yulang.NominalConstructions` | 任意の有限個の不変パラメータを持つstruct/enum/list構築、各元の位置での境界検査、パラメータごとのEOF unionと変換省略、構築子・tag・位置の保存、既存list plannerへの厳密な特殊化 | 全パラメータ出現位置のsourceからの収集、弱い型変数の解探索、未使用パラメータの既定値・公開可能性 |
| `Yulang.Variants` / `Yulang.VariantsMerged` | support の分割・残余の最小性と最大性、同一 tag の payload 合流と tag 一意性、合流と残余の交換、tag 全体の選択・除去、全 tag 処理と空行の同値、merge 準同型による payload 置換 | payload 内部の source pattern 網羅性（2026-11-05 の決定により対象外）、guard 付き arm の被覆（章3b.4により数えない）、payload の部分型 solver、open row の solver、source の case 検査への接続 |

`Variants.Merged.Row` は tag の重複がない有限行を表す。`normalize merge` は同一 tag の payload を入力順の右結合で合流し、`lookup_normalize` はその結果を `mergeAll` と一致させる。該当 tag がなければ `none`、一つならその payload、複数なら指定した `merge` を用いる。tag の列順は最後の出現順の逆順である。これらの定理に結合則・交換則・冪等則は不要で、入力の並べ替えや重複挿入で payload が等しくなるとは主張しない。`normalize_map` だけは `f (merge a b) = merge' (f a) (f b)` を仮定する。`variant_union_upper_bound` は既存の構造部分型規則から `variant l a ∪ variant l b ≤ variant l (a ∪ b)` の一方向を導く。case の入力型を閉じる推論器や、部分型モデル全体の正規化を証明したものではない。

`Roles.Term` は変数と有限引数列を持つ型構築子だけを表す。型構築子・型変数を各1と数え、複数引数の head / where 条件の大きさは型サイズの和とする。role 識別子と引数列の spine は数えない。`Impl.WellFormed` は各 where 条件について、head より真に小さいことと、各変数の出現回数が head を超えないことを要求する。`Term.subst_size` / `args_subst_size` は、置換後のサイズを元のサイズと各変数の出現回数に基づく増分の和で表す。`size_decreases` はこの二条件から、任意の置換の下での真の減少を導く。`resolve impls wf goal` は全 impl の適格性の証明を受け取り、goal の引数サイズを測度として停止する。`wellFormed_cons` は、impl の追加時も適格性が宣言ごとの条件であることを示す。適格性の診断を返す source 宣言検査器は未接続である。

照合は impl の変数だけを置換し、goal の変数は rigid に保つ。繰り返し現れる変数には同じ型を要求する。`matches_iff` は実行可能な照合と存在的な head 一致の同値を、`constraint_variables_in_head` は head にない変数が where 条件にもないことを示す。`matched_constraint` により、照合に使う置換の未使用変数の既定値は where 条件の結果に影響しない。`Impl.key` は宣言の識別子であり、同じ head / where を持つ別宣言も別候補として表せる。同じ impl 値の繰り返しは同じ宣言として除重複する。入力リストは可視な impl 集合を表し、import・可視性の検査は扱わない。

曖昧さは where 条件を調べる前の head 一致で判定する。head 候補が二つ以上あれば、条件の成否によらず `ambiguous` となる。一意な候補の全 where 条件を調べ、子の `ambiguous` は兄弟の `noImpl` より優先する。`resolve_resolved_iff` と `resolve_noImpl_iff` はこの成功・失敗条件を正確に述べる。`Derives` は resolver を参照しない存在的な宣言的導出であり、重なる impl でも導出自体は存在し得る。`resolve_sound` は成功から導出を、`resolve_complete` は導出と到達する head の非重複から成功を導く。`ReachesOverlap` は一意な候補の条件をたどって重なる head に至る有限経路であり、`resolve_ambiguous_iff` はその存在と `ambiguous` を同値にする。`Examples` は二重 list の成功、str impl の不在、rigid 変数、変数を複製する条件の拒否、サイズが増える Foo impl の不適格性と有限導出の不在、head が重なる例を検証する。Foo の有限導出の不在は適格性を仮定しない帰納法で示し、宣言的導出の健全性と解決の実行可能性を区別する。

`Yulang.RolesAssoc` の `Roles.AssocImpl` は既存の `Impl` を包み、関連型名から右辺 `Term` への辞書を添える。既存の `Impl` と定理は変更しない。`RoleDecl` は引数数と宣言済みの名前・default を表し、default の変数は `0..arity-1` の引数位置だけを指す。辞書の名前の無重複性と、同じ元の impl に同じ辞書を対応させる `AssocEnv.coherent` は表現上の不変条件である。source の重複宣言の診断や意味は定めない。`AssocHeadVars` は明示定義の変数が head に現れること、`AssocComplete` は署名との引数数の一致と必須定義の充足、`AssocDeclared` は未宣言名を提供しないことを要求し、`AssocWellFormed` は全 impl に対してこの三条件を要求する。

`assocOf` は既存の `resolve` が成功したときだけ、一意な impl の右辺を head の照合置換で一度具体化する。明示定義がなければ、default の引数位置を goal の型引数で置換する。`Term` に関連型参照はなく、別の関連型の展開や新しい再帰・停止測度は不要である（章6.3、確定, 2026-11-05）。`assoc_independent_of_constraints` と `assoc_explicit_eq` は、解決成功を前提として値が選ばれた impl と照合置換で決まり、where の解決導出によらないことを示す。`assoc_derivation_agrees` / `assoc_derivations_unique` は、resolver を参照しない `AssocDerives` の二つの導出でも値が一致することを示す。Paterson 適格性と関連型適格性の下で、`assoc_total_closed` は、解決済み goal の**宣言済みの各名前**について結果が存在し、その変数がすべて goal に現れることを証明する。`assoc_unique` はその値の一意性を示す。`assoc_explicit_size` は明示定義について既存の `Term.subst_size` と同じ正確なサイズ公式を与える。`AssocExamples` は str・box・定数と引数位置の default・明示定義による default の上書き・rigid な goal 変数の正例と、head 外の変数・必須定義の欠落・未宣言名の提供を拒む負例を検証する。関連型を含む method 署名や where 条件との単一化は `RolesAssoc` 単体の対象外である。関連型選択から普通の等式を追加する規則は確定済みで、`RoleConstraints` がその接続と解集合の順序不変性を扱う。未知の置換を探索する全体solverは別に必要となる。

`Horn.solve` は全 `2^n` valuation を列挙する参照実装で、実用solverの性能を主張しない。有限性は `Fin n` という入力型に明示されており、任意のYulang制約がそこへ落ちるという未証明の仮定を入れていない。

`FiniteReachability.closure` は有限グラフの始点と辺を Horn 制約に翻訳する。`closure_exact` は、結果の真の成分と、始点から有限回辺をたどる独立な `Reach` 判断とを双方向に対応させる。経路長の打切り・非循環性・解決成功の仮定はない。`closure_empty` により、循環する辺だけでは到達点は生じない。評価依存と ground cast の探索で共有する基盤であり、このモジュールだけでそれらの source 規則との対応を主張しない。

`EvaluationOrder` は局所変数と有限個の global 宣言を区別する式を入力とする。評価位置に現れた global 名から、その宣言の関数本体へ推移的に進む。関数を引数として渡す場合も同じ辺をたどる。名前付き宣言の `invokedReferences` は先頭の引数lambdaだけでなく、分岐の結果やcallee位置から返るlambdaも再帰的に開く。独立な `InvokedUses` 判断との一致と、旧来の有限回の直接適用で見つかる依存をすべて保持することを証明した。`check_exact` は computed binding の初期化と、位置を持つ module 文の両方について、実行可能な判定と独立な `Ordered` 判断が一致することを示す。到達した computed binding の位置には真の不等号を要求するので、自己依存・未来への依存は拒否される。関数だけの相互再帰を禁止する規則はない。

`lambda_no_dependency` は lambda **構築時**の依存がないことを示す。`applied_lambda_preserves_body_dependency` は直接適用すれば本体の依存が戻ることを示し、curried な直接適用にも負例がある。`accepted_initializer_earlier` / `accepted_statement_available` は、この依存判断で必要とされる computed binding が、並べ替えていない宣言順序で先行することを証明する。任意の source callback の実際の呼出しをこの判断が過大近似することはまだ示していない。分岐からlambdaを返す名前付きfactoryの即時呼出しには拒否・受理の回帰例がある。この基礎層だけでは局所変数を通るclosureを追わないため、決定23に従うmodule全体の近似と実行時の接続を、次の `EvaluationSafety` / `EvaluationReads` に追加する。

`EvaluationSafety` は、名前で決まらない呼出しで、宣言とmodule文に含まれるすべてのlambda本体の参照を候補にする。直接のlambda、または宣言本体がlambdaである名前だけは、その本体を使う。`EvaluationReads` の `Eval` と `Reads` はcheckerを含まないCBV意味論で、後で発散する実行の読み取りprefixも扱う。`Reads.read` はstoreに値があることを要求せず、未初期化の読取りも表せる。`reads_needed` はmodule由来のclosureを持つ任意のstore/environmentに対し、実際の読みが計算した依存集合に入ることを示す。`eval_closed` はclosureと捕捉環境の由来を実行に沿って保つ。`accepted_read_initialized` は、先行するcomputed bindingの結果を記録したprefix storeに対し、読まれる値の存在を導く。`initialize_next` は実際の初期化結果を記録するとprefix不変条件が進むことを示す。さらに `EvaluatedPrefix` は空storeから始めたcomputed宣言の実際の初期化履歴を表し、`EvaluatedPrefix.invariants` がclosureの由来と先行値の存在を導く。`accepted_prefix_read_initialized` はこの履歴から、現在の式の終了を仮定せず読み取り先の値が存在することを示す。位置を進めるときは、その位置の宣言が一意であることを要求する。間にあるmodule文の実行・終了や、その履歴全体の存在は別の義務である。これは保守的な上界であり、実際に読まれる集合との同値や全実行の停止を主張しない。

`Initialization.toCore` は同じ依存構文の本体を型推論の式へ翻訳し、global名の添字をlambdaの局所束縛の数だけずらす。有限のscope検査で、不正な局所添字がglobal名を指してしまう場合を拒む。`value_restriction_agrees` により両側のcomputed分類は一致する。`generate_exact` は、生成制約の解と「同じ本体の同時単相型判断＋初期化順序判断」の一致を示す。`computed_cycle_rejects_generated_constraints` は任意のモデル・割当てについて、computed cycleが合成後の生成制約を満たせないことを示す。対象にはunit・Boolean・pairのprojectionを含み、module文はこの層では依存だけを検査する。生成器は `EvaluationSafety.check` も要求し、`generated_initializer_read_earlier` は実際の読み取りprefixに対して先行性を導く。`generated_prefix_initializer_read_initialized` は、生成制約の解と実際の既評価prefixから、次の初期化の読み取り先に値が存在することを導く。現在の読み取りの被覆や利用可能性を別の前提として要求しない。

`Methods.resolve` は member ごとの method の有無が確定した段階を扱う。`resolve_unique_iff` / `resolve_missing_iff` / `resolve_ambiguous_iff` は、それぞれ相異なる候補が 1 個・0 個・2 個以上である条件を示す。`select_ext` はリストの membership が同じなら結果も同じことを示すため、順列だけでなく同一 member の繰り返しも曖昧さを増やさない。

`CheckedRoles.checkImpl` は各 where 条件のサイズ減少と変数出現回数を検査する。条件側の変数番号上界より上の出現回数は 0 なので、有限回の検査と無限個の変数についての `Impl.WellFormed` が一致する。`CheckedRoles.resolve` は全宣言を先に調べ、成功した場合だけ既存の停止性証明付き `Roles.resolve` に渡す。`resolve_exact` は適格性を前提にせず、結果が成功することと「宣言集合が適格で、導出があり、到達する head に重なりがないこと」の同値を示す。不適格な宣言は、その goal の解決で使われなくても拒否する。

`RoleConstraints.addAssociated` は既存の関連型解決が返した値を、普通の型変数との等式として蓄積する。`Store.permutation_preserves_solutions` は一つの選んだ置換だけでなく、**すべての置換**について解集合が順序に依存しないことを示す。`conflicting_constraint_rejects` は同じ変数への char と str の要求が、後からの代入で上書きしても解にならないことを示す。`Store.check_dichotomy` は固定した置換での整合・矛盾の二分であり、解となる置換の存在判定器ではない。

`Casts.accepts_exact` は、与えられた普通の適合性の判定と明示castの探索を用い、独立な `Boundary` 判断と実行可能な追加変換の検査を対応させる。適合すればそのまま通し、不一致の場合だけ構造に沿った変換を調べる。recordはfield名で照合し、既存の構造型モデルと同じく最初のfieldが後の同名fieldを隠す。`union_mismatch_iff` は不一致の場合に全memberの検査が必要なことを示す。無条件の `union_boundary_iff` では、普通の適合性がunionの除去則を満たすことを明示的に要求する。`structural_union_boundary_iff` は既存の `StructuralBase.Subtype` と一致する適合性からこの前提を導くが、その部分型の判定器自体は実装していない。

このground型構文で、登録先の同一性と固定nominal引数には構文的等号を用いる。nominal引数内のunionの並べ替えなど、意味的に等価な型を同じ表現にする正規化は前段の課題である。`equalityCompatibility` は検査の具体例用の適合性であり、Yulangの部分型solverを置き換えるものではない。

`CastGraph.Registry.find_exact` は、有限のground型の登録と、先に証明した有限経路判断を結ぶ。登録は型ごとに一つの頂点を持ち、同じ直接のsource/target対の重複を拒否する。異なる間接経路が合流するdiamondは許容する。`compatible_kept` は適合する境界で変換探索を使わないことを示す。`Methods.checkCall_exact` はmethodを持つ相異なる型がちょうど一つであり、すべてのreceiver memberからその型への境界変換が成立することを要求する。`checkCall_perm` はこの変換検査まで含めた結果の順序不変性を示す。例は固定した`list user_id`から`list int`への要素castの不許可と、list全体の明示規則による許可を区別する。 `cast(x: box 'a): 'a` の具体化ではtargetがpair・関数・unionにもなり得るため、直接sourceのnominal/base条件を保ちつつtarget制限を外した。`nominal_mismatch_iff` は任意のtargetについて外側全体の規則を要求する。source unionは引き続き全memberを個別に検査し、whole-unionだけのoracleでは欠けたmemberを隠せない。

`ParametricCastRules.Rule.substitution_nonincrease` は、targetのサイズと各変数の出現回数がsource以下なら、どの置換後もサイズが増えないことを証明する。固定したground castはサイズを増やしてよいので、全到達型には初期型のサイズと宣言のtargetサイズの最大値を上界として使う。構築子の有限性も仮定せず、初期型と有限個のtargetからalphabetを作る。`ParametricCastUniverse.reachable_types_finite` はこのalphabetとサイズ上界から計算した有限リストが、すべての有限cast経路の到達先を含むことを示す。等サイズの循環そのものは許される。`ParametricCasts.query_success_iff` は「宣言が適格、出発型がground、独立な明示規則の経路が存在すること」と成功を同値にし、`query_failure_iff` は同じ検査済みの領域で経路の不在と失敗を同値にする。有限instanceグラフは入力ではなく、証明済みの有限リストから実際に構成する。この探索は全候補型とBoolean valuationの列挙による参照実装で、実用的な性能は主張しない。構造的な持ち上げを自由に混ぜた全言語の探索とは区別する。サイズはnominal引数の内部も数える `Roles.Term.size` であり、構造変換の停止測度でnominal引数をopaqueにする `Casts.Ty.size` とは用途が異なる。

`LiteralCasts.finish_exact` は、保持された各要素の構築位置と元の型に対し、期待要素型が与えられた場合だけ境界検査を要求する独立な `PlanTyping` と実行可能な計画作成を対応させる。どちらの場合も元の構築位置を保持する。EOFまで期待型がなければ、元の型の列をunionとして記録し、要素の命令はすべてkeepになる。これはコンパイル時に保留された構築位置へ変換を割り当てる規則であり、すでに構築したnominalなlistの型引数へcastを通す規則ではない。`expected` を決める弱い変数のsolverは別に必要である。

`PureCasts.Declaration` は実際の `Directed.Computation` 本体と、その推論行による上界を持つ。宣言の検査は行全体の空性を要求し、保護されたheadや負の差分も純粋と誤認しない。`Plan.run_eq_pure` はチェック済みの基本変換から合成した任意の有限planの純粋性を導く。`insert_requestTree` は返り値を除いた実際の要求木（payload・継続の分岐・符号付き重みを含む）を保存し、`insert_bounded_iff` は任意の行上界について同値を示す。関数の `wrapper_requestTree` は、変換後の引数で元の関数を呼んだ場合との対応である。入力値を変える前後で同じ実行になるとは主張しない。宣言本体の上界をsource型付けから導くことと、境界判断から実行planを合成することは別の接続義務である。

`NominalConstructions` は各元の構築位置を有限の不変パラメータslotへ対応させ、同じslotに属する全値を検査する。未解決のslotは、そのslotに属する元の型だけのunionを記録して変換しない。複数field・別々のパラメータ・enum tagの例があり、`finish_literal_exact` は一つのslotのlist構築を旧 `LiteralCasts.finish` へ射影すると、失敗も含め結果が厳密に一致することを示す。出現しない未解決slotは `unionOf []` という記述のままであり、bottomや既定型への決定・公開可能性をこのplannerで作らない。

`ImplHeads` は名前付き変数を偶数、各holeを別の奇数の識別子へ下ろす。`anonymous_occurrences` は任意の有限headと任意の匿名識別子について、割り当てた範囲では一回、範囲外では零回の出現を証明する。`named_occurrences` は名前を共有する箇所の出現回数を保ち、whereの名前は匿名識別子へ触れない。`two_holes_accept_all_types` と `repeated_name_matches_iff_equal` は任意の二つの型について、この違いを実際のhead matcherで示す。refも同じ全体照合を使うため、intのmethodをrefの中身へ自動委譲せず、`ref _ int` の特化は任意のeffect引数に適用できる。

`EffectExamples` は、同じfamilyの保護されたtail、境界ごとの解除、繰り返した保護、型引数を含むkey、shallow/multi-shot、handler armが新しく起こすeffectを検査する。nested `sub` の核の例は`0`、保護を消した比較例は`2`と計算される。これらはsource例に対応して手で構成した核の式で、parserからの翻訳の正しさを主張しない。

`shallowHandle_bounded` は、value armとoperation armの実行時effect上界を前提として、結果のeffectが`residual input ++ armEffects`で抑えられると証明する。継続の上界には元の入力行を保つ。この前提を型付けから導くsource handler推論器まで証明した、とは読まない。

## 高階の衛生性

`HigherOrder` のerase解除では、先に解除してから保護する往復が壊れる。`Directed` は許可されていないkeyについて、各境界の整数weightを保護で `+1`、解除で `−1` だけ変える。同じ境界と同じ許可maskの一対について両方向の相殺が成り立つ。handlerがcaptureできるのは、keyが一致し、すべてのweightが0のときだけである。

`DirectedHigherOrder.transport_opposite` は、product・sum・list・arrowで構成する任意の有限shapeと、その任意の値に対してこの相殺を証明する。関数の入力では方向を反転し、戻りcomputationと値では方向を保つ。新鮮性・weightの上限・fuelの仮定はない。

一方、非captureには由来の条件が必要である。weight `−1` に `+1` を足すと可視になるため、任意の符号付き入力を保護すれば必ず非captureになるとは主張しない。`guard_arrow_noncapture` は、反変方向に引数を変換した後の関数呼出しについて `ZeroAt` を仮定する。

`contravariant_debt_preserves_local_callback` は、callbackを奪う内側handlerの結果 `99` と、transportを入れて呼出側のhandlerへ届く結果 `7` を比較する。引数側の負の差分が内側でのcaptureを阻止し、帰りの正の差分が元の可視性を回復する。

## 型推論の主定理

`AnnotationSnapshots.observe` は、現在の行式に含まれる concrete な頭を符号付き行として計算し、残った行変数をこの観測では opaque とする。観測を取る前に、その時点ですでに分かっている置換は適用されている必要がある。`TrackedRow.subst` は行式を具体化し、注釈時点の履歴をそのまま保つ。`principal_observed_exact` は、保存した観測の許容性と既存の宣言的型判断の連言が、観測を付けた主制約schemeの意味と一致することを示す。許容された観測から後の行変数へ上界・等式は追加しない。T3 の例では、未知行を観測してから禁止effectへ具体化した履歴は受理され、その具体化後の行を**新しく**観測すれば拒否される。当初から既知で可視な禁止effectを未知tailの横に置いても拒否される。

`AnnotationFinalization` は有限Horn factの層で、SCCの全memberの制約を集め、実際の `Horn.solve` の最小解を計算した後に観測する。`known_iff_forced` は、その解で真のfactが全モデルで強制されるfactと一致することを示す。`finalize_constraint_order` と `scc_member_order` は制約の生成順序・memberの収集順序に依存しないことを示す。並べ替えても名前解決済みのfact/row識別子は固定する。`principal_finalized_exact` はこの検査を既存の主制約生成へ接続し、`gate_subst` は後の具体化で再検査しないことを示す。同じSCCの別memberから伝わるeffectは検査対象で、入れ子のbindingは自身の単位を先に確定する。この実装は既知の置換を外から渡すだけの層より進んだ有限solverだが、sourceの全制約がその有限interfaceへ翻訳できることまでは証明していない。

`RecursiveInference.generateSCC_exact` は、任意の有限 member 列について、同じ再帰仮定環境で全本体を検査する生成制約と独立な `SCCTyping` を双方向に対応させる。`closeSCC_exact` は slot 群を全本体の外側で存在量化するため、呼出しごとに型を選び直さない。全注釈の `FullAnnotation` は値型の有限変数だけを呼出側で具体化し、定義側ではそれらすべての割当てで本体を検査する。`rowsCaptured` の構文検査により、注釈中の明示的な行slotは外側の共有割当てを参照する。同じ SCC の別 member からも同じ注釈schemeを使う。これらは制約生成の正確性であり、source の SCC 発見や制約の解探索そのものの証明ではない。

`generalizeMember_exact` は、SCC全体を検査した後の一つの値memberの具体化を記述する。存在量化するlocal slotに属する全unannotated memberへ、構文上の値かつpureに型付けされるという検査を入れる。computed memberはcaptured slotに残り、別々の具体化で同じ割当てを参照する。`RecursiveExamples` では、SCC後のidentityをintとstrで独立に使うこと、別memberを公開するときにもcomputed memberをlocal slotへ隠せないこと、全注釈の関数と単相関数が互いに呼び合う例を検証する。

`unannotated_depth_not_typable` は、`x`を`(x,x)`へ変えて再帰する式について、既存の有限 `Structural.Ty` の**すべての型と実行行**を量化して単相型付けを排除する。pairの深さの単調性と関数入力の反変性から、`depth(A)+1 ≤ depth(A)` が必要になり矛盾する。union・intersection・bottom・部分型の推移もこの証明に含む。`generated_annotated_depth_satisfied` は同じ本体を全注釈のschemeで受理する。source例の算術と条件値はliteralへ抽象化しており、実行の停止性や再帰型のある体系での拒否は主張しない。

`QualifiedInference.principal_exact` は、resolved methodの有限のrole要求を制約に加えた生成器と独立な宣言的型判断の一致を、元の構造的な式の全ケースについて証明する。この層の通常の `letE` は単相で、qualifiedな値の一般化は `qualified_let_exact` の別規則で接続する。一般化interfaceはlocal slotと環境slotを明示する。`partition_exact` はraw role要求を自動で分け、local slotを含む要求をschemeへ、環境slotだけの要求を残留制約へ移す。混合した要求の環境slotは量化せず共有する。定義は抽象辞書を仮定して全local割当てで検査し、利用時にその具体化の証拠を要求する。

通常のqualified letは `Comp` slotを量化し、値型とeffect行の両方を独立に具体化できる。operation-localの型変数や全注釈による多相再帰とは量化の種類が異なる。`QualifiedRowExamples.independently_instantiates_latent_row` は一つのschemeを任意の符号付きcallback行で具体化できることを示し、相異なる非空行でも確認する。`QualifiedExamples` は、具体的なimplがなくても未使用の`twice`を定義できること、そのschemeを証拠なしでは使えないこと、実際の`Add int`解決が利用を可能にすること、環境に由来する制約が消えないことを示す。これらは供給された有限interfaceの正確性であり、未解決の部分型制約からそのinterfaceを発見するsolverまで証明したものではない。

`ModuleRoles.finishModule` は、EOFで渡された部分割当てとinterfaceについて、公開型およびraw role要求に現れるすべてのambient slotが確定しているか検査し、残留role要求を実際の `Roles.resolve` で確認する。`finishModule_no_unresolved_exports` と `finalized_scheme_exact` は、受理した公開schemeが元のschemeと同じ意味を持ち、未使用の未確定slotをどう補完しても意味が変わらないことを示す。未確定weak slot、同じファイル内でintに決まる例、証拠のないstr、implなしで公開する抽象qualified関数の各場合を検証する。module全体から全残留制約を収集するpassと、その部分割当てを求めるsolverはこの入口の前段である。

`RoleEvidence.Signature` は既存の `PolySignature` にrole要求を追加する。`request_constraints_exact` は局所型を存在的に具体化して呼出側の証拠を要求し、`handler_constraints_exact` はactionとvalue armの型を先に決めてから、すべての局所型で署名の辞書を加えてoperation armを検査する。外側の環境と結果はその局所型によらず、継続は元のinput rowを保つ。`RoleEvidenceExamples` は実際の符号付き構造モデルで、抽象payloadにAddを使ってからresumeする腕を署名辞書つきで受理する。同じ腕の辞書なしの場合は**すべての外側の結果型・行**で拒否し、呼出側に証拠がないrequestも拒否する。handlerの型判断からoperationalなeffect上界を導く定理ではない。

`principal sΓ e` は一つの結果slotを持つ有限の制約schemeを返す。`principal_exact` は任意の型・行のモデル、対応する入力環境、型と行の割当てについて、次を証明する。

```text
(principal sΓ e).Holds m (extend ρ (A, ε))
  ↔ Typing m Γ e (A, ε)
```

環境の前提 `EnvRel` は、入力schemeと入力bindingが同じ型の候補を表すという条件であり、solverの成功や式自身の型付けを仮定していない。空環境には無条件に成立する。`Typing` と `BindingTyping` は `generate` や `Formula` を参照しない独立の帰納的判断である。

対象の式は変数・基本literal・lambda・computation application・非再帰let・分岐・pairとprojection・recordとfield・variant注入。多相letは純粋な構文的値の有限schemeを保存し、利用ごとにfreshなslotへ代入する。外側の環境のslotは共有したまま。単相letはすべての右辺に使え、一つの型を共有して右辺と本体の実行行を合流する。構文的な値にはこの二つの経路の選言を生成する。`Polymorphism` は、computation引数を指す変数を束縛でき、そのeffectが消えないことを検証する。

`Structural`では、混合分岐が`int | str`を持ち`int`だけにはならないこと、多相identityの二回の利用で`pair(int, str)`が得られること、余分なfieldを持つrecordから`int`を取り出せることを、**生成された制約の意味について**検証する。record spreadのtailには `restType ≤ emptyRecord` を要求し、scalarをtailにする式は任意の結果型・行について拒否する。任意の制約を受理する空虚なモデルではない。

`RowInference.handler_constraints_exact` はcore生成器とhandlerの規則を接続し、同じ定理を非負行と符号付き行に使う。継続には元のactionの行を持たせ、結果にはactionの残余と両armの行を加える。既存の単相署名と定理は維持する。潜在行を含む高階の型変換はこの定理の対象外である。

`EffectInference.PolySignature α n` はambient slot `α` と局所型変数 `Fin n` を分け、署名の入出力を `TyTerm (α ⊕ Fin n)` で表す。局所slotは値型だけを具体化し、行成分は空行とする。`poly_request_constraints_exact` は、呼出側の生成制約が「ある局所型の割当てで独立なrequest規則が成立する」と同値であることを証明する。各呼出しの存在量化は独立し、好きな型を選べる。

両モジュールの `poly_handler_constraints_exact` の型判断は `∃ input returned, … ∧ ∀ ι, ∃ operated, …` の順序である。actionとvalue armの型・行を先に固定し、すべての局所型割当て `ι : Fin n → m.Ty` についてoperation armの型付けと結果への包含を要求する。継続は元のactionの型・行を保持する。結果 `out : CompTerm α` と外側のscheme環境 `SchemeEnv α` は局所slotを含まない。`local_result_no_escape` は局所割当てを変えても結果の型・行が同じであることを、`local_outer_environment` は任意の局所割当てで同じ外側binding環境を表すことを示す。これはescapeを構造的に排除する核の規則であり、source上のescape検出・エラー報告の証明ではない。atomのkey・追加effectは局所割当てによらず固定され、atomのpayload内部の局所変数とrole制約は扱わない。

`SignedStructural.generated_poly_request_at_any_type` は任意の構造型（複合型・effect付き関数型も含む）で呼出制約が成立することを、`generated_poly_requests_independent` は同じ署名・同じ外側の割当てでintとstrへの二回の独立した具体化が成立することを示す。`generated_poly_handler_resumes_payload` は任意の局所型のpayloadを同じ型を受け取る `k` へ渡す腕を受理する。`generated_poly_handler_payload_escape_rejected` はそのpayloadを固定のint結果へ直接返す腕を拒否する。後者は局所型をstrとしたときの `str ≰ int` による具体的反例であり、任意のモデル・任意の結果上界についての拒否を主張しない。

`SignedStructural` は実際の符号付き行を使い、生成されたoperationの制約が自身のeffectを含む行で成立し、空行では成立しないと証明する。保護前の解除が作る `−1` の差分についても、生成された境界制約がその行を保持し、空行へ消せないことを証明する。型構築子・部分型規則・scalarの分離は `StructuralBase` を通して非負モデルと共有し、別の型体系を複製しない。

`DirectedHandlerInference` の `generated_signed_handler_composes_effect_bounds` は、成立した `RowInference.handlerConstraints` から得たaction・armの型付けと、明示された実行時の上界を組み合わせる。結論は実際の `Directed.Computation.shallowHandle` の出力上界である。制約の定理とoperationalな定理を別々に置くだけでなく接続しているが、型付けから実行時上界を得る前提そのものを証明したとは扱わない。

## 検証ゲート

`lakefile.toml` は全モジュールのコンパイルに `--trust=0` を指定する。`Audit.lean` はYulangの各モジュールからimportされた**すべての宣言**について依存公理を走査し、`propext` / `Quot.sound` / `Classical.choice`以外があれば失敗する。私有宣言も対象とする。その後で主要定理の依存を個別表示する。

`sorry`、追加の公理、`native_decide` での証明を使わない。Lean が通常使う公理と、未証明の主張を公理化することを区別する。GitHubの`Lean inference kernel` workflowも、ビルドとこの監査を実行する。

構文例の計算確認と一般定理も区別する。全言語の推論器、Rust との接続、公開型の表示、実行時の型安全性については、対応する定理を持つまでは完了と呼ばない。

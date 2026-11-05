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
| `Yulang.DirectedHigherOrder` | 任意の有限shapeと値における両方向の高階transportの相殺、由来条件付き非capture、混在した由来のcallbackの例 | 再帰型、atom・operation payload内部のtransport、sourceのelaborationとpreservation/progress |
| `Yulang.DirectedBounds` | 符号付き行でのshallow handlerのeffect上界、保護・解除による上界の双方向のtransport | sourceの型付けからaction・armの上界を導くこと、値内部の潜在行 |
| `Yulang.DirectedHandlerInference` | 成立した共通のhandler生成制約とaction・armの実行時上界から、実際の符号付きhandler全体の上界を導くこと | action・armの前提そのものをsourceの型付けから導くこと |
| `Yulang.Annotations` / `Yulang.AnnotationSnapshots` | 注釈時点の可視effect検査と正確性、符号付きの観測履歴の固定、T3 の具体化時に再検査しない規則と主制約生成器の接続、未知行の後の具体化と当初から既知の禁止effectの区別 | 何がその時点で既知かを決める solver、source 注釈から観測時点を構成する elaboration |
| `Yulang.RecursiveInference` | 有限の同時再帰制約生成と独立な SCC 型判断の双方向の一致、単相slotを全本体の外で一度だけ選ぶこと、全注釈の値型変数の呼出しごとの具体化と定義側の全称検査、明示的なeffect行の共有 | source の SCC 発見と全注釈認識、解の探索、SCC 後の一般化（後続層）、評価依存の検査 |
| `Yulang.Roles` | 第一階 impl 集合の一方向照合、Paterson 型条件による置換後の型サイズの真の減少と深さ制限なしの解決の停止、健全性、到達する head に重なりがない場合の完全性、到達可能な head の重なりと曖昧さの同値、正例・負例 | generic role の method dispatch、章6.4の receiver 下界による解決保留、effect との相互作用、operation-local role 制約、推論の制約言語との統合 |
| `Yulang.RolesAssoc` | 第一階の関連型の明示定義と default、解決成功時の宣言済み各名前の全域性・一意性、where の導出や照合置換によらない値、goal の変数だけを含む結果、明示定義の置換後のサイズ公式、正例・負例 | 関連型を含む method 署名、`value ~ int` 等の等式制約や where 条件との単一化、receiver 下界による解決保留、source 宣言検査。他 role の関連型を右辺で参照することは2026-11-05の決定により対象外 |
| `Yulang.RoleConstraints` | 具体的なresolverの成功と導出・非曖昧性の一致、関連型選択から普通の等式の追加への接続、全置換について等式制約追加の可換性・冪等性・順列不変性、既存制約との矛盾を上書きしないこと | 未知の置換を探索する単一化器、構造部分型とrole制約を合わせた全体solver。`Store.check` は与えられた置換での検査 |
| `Yulang.CheckedRoles` | 有限の宣言検査と全変数についての Paterson 適格性の同値、証明を入力に要求しないresolver入口、不適格な宣言の拒否、適格な集合での成功・曖昧さの正確性 | source parser/name resolution、関連型宣言の全検査、診断位置・文言、疎な変数番号での計算量最適化 |
| `Yulang.Horn` | 任意の有限Horn制約に対する解の存在判定と最小モデル。成功・失敗の両方向の完全性 | 構造部分型、再帰型、無限の保護stack、roleの解決 |
| `Yulang.FiniteReachability` | 有限隣接リストから計算する到達集合と独立な有限経路の判断の一致、空の始点集合からの到達不能性、辺・始点の順序と重複に対する不変性 | source の依存関係抽出、未具体化の多相 cast 集合の有限性、実用的な計算量 |
| `Yulang.EvaluationOrder` | 名前解決済みの有限宣言・module 文からの評価依存計算と独立な推移的依存判断の一致、computed 自己依存・未来の computed binding の拒否、受理された初期化・文の全依存が元の順序で利用可能なこと、lambda による遅延と直接適用時の依存の復帰 | source の名前解決、局所 closure/alias や格納された関数のフロー、任意の高階 callback の実行が依存判断に含まれること、全言語の副作用順序の保存 |
| `Yulang.Methods` | union の相異なる receiver 候補について、0 個・1 個・2 個以上の失敗・一意選択・曖昧さの正確な三分、順序と重複に依存しない選択 | member ごとの method lookup の優先順位・可視性・参照型の処理、未確定 receiver 下界の保留、選んだ receiver への cast |
| `Yulang.Variants` / `Yulang.VariantsMerged` | support の分割・残余の最小性と最大性、同一 tag の payload 合流と tag 一意性、合流と残余の交換、tag 全体の選択・除去、全 tag 処理と空行の同値、merge 準同型による payload 置換 | payload 内部の source pattern 網羅性（2026-11-05 の決定により対象外）、guard 付き arm の被覆（章3b.4により数えない）、payload の部分型 solver、open row の solver、source の case 検査への接続 |

`Variants.Merged.Row` は tag の重複がない有限行を表す。`normalize merge` は同一 tag の payload を入力順の右結合で合流し、`lookup_normalize` はその結果を `mergeAll` と一致させる。該当 tag がなければ `none`、一つならその payload、複数なら指定した `merge` を用いる。tag の列順は最後の出現順の逆順である。これらの定理に結合則・交換則・冪等則は不要で、入力の並べ替えや重複挿入で payload が等しくなるとは主張しない。`normalize_map` だけは `f (merge a b) = merge' (f a) (f b)` を仮定する。`variant_union_upper_bound` は既存の構造部分型規則から `variant l a ∪ variant l b ≤ variant l (a ∪ b)` の一方向を導く。case の入力型を閉じる推論器や、部分型モデル全体の正規化を証明したものではない。

`Roles.Term` は変数と有限引数列を持つ型構築子だけを表す。型構築子・型変数を各1と数え、複数引数の head / where 条件の大きさは型サイズの和とする。role 識別子と引数列の spine は数えない。`Impl.WellFormed` は各 where 条件について、head より真に小さいことと、各変数の出現回数が head を超えないことを要求する。`Term.subst_size` / `args_subst_size` は、置換後のサイズを元のサイズと各変数の出現回数に基づく増分の和で表す。`size_decreases` はこの二条件から、任意の置換の下での真の減少を導く。`resolve impls wf goal` は全 impl の適格性の証明を受け取り、goal の引数サイズを測度として停止する。`wellFormed_cons` は、impl の追加時も適格性が宣言ごとの条件であることを示す。適格性の診断を返す source 宣言検査器は未接続である。

照合は impl の変数だけを置換し、goal の変数は rigid に保つ。繰り返し現れる変数には同じ型を要求する。`matches_iff` は実行可能な照合と存在的な head 一致の同値を、`constraint_variables_in_head` は head にない変数が where 条件にもないことを示す。`matched_constraint` により、照合に使う置換の未使用変数の既定値は where 条件の結果に影響しない。`Impl.key` は宣言の識別子であり、同じ head / where を持つ別宣言も別候補として表せる。同じ impl 値の繰り返しは同じ宣言として除重複する。入力リストは可視な impl 集合を表し、import・可視性の検査は扱わない。

曖昧さは where 条件を調べる前の head 一致で判定する。head 候補が二つ以上あれば、条件の成否によらず `ambiguous` となる。一意な候補の全 where 条件を調べ、子の `ambiguous` は兄弟の `noImpl` より優先する。`resolve_resolved_iff` と `resolve_noImpl_iff` はこの成功・失敗条件を正確に述べる。`Derives` は resolver を参照しない存在的な宣言的導出であり、重なる impl でも導出自体は存在し得る。`resolve_sound` は成功から導出を、`resolve_complete` は導出と到達する head の非重複から成功を導く。`ReachesOverlap` は一意な候補の条件をたどって重なる head に至る有限経路であり、`resolve_ambiguous_iff` はその存在と `ambiguous` を同値にする。`Examples` は二重 list の成功、str impl の不在、rigid 変数、変数を複製する条件の拒否、サイズが増える Foo impl の不適格性と有限導出の不在、head が重なる例を検証する。Foo の有限導出の不在は適格性を仮定しない帰納法で示し、宣言的導出の健全性と解決の実行可能性を区別する。

`Yulang.RolesAssoc` の `Roles.AssocImpl` は既存の `Impl` を包み、関連型名から右辺 `Term` への辞書を添える。既存の `Impl` と定理は変更しない。`RoleDecl` は引数数と宣言済みの名前・default を表し、default の変数は `0..arity-1` の引数位置だけを指す。辞書の名前の無重複性と、同じ元の impl に同じ辞書を対応させる `AssocEnv.coherent` は表現上の不変条件である。source の重複宣言の診断や意味は定めない。`AssocHeadVars` は明示定義の変数が head に現れること、`AssocComplete` は署名との引数数の一致と必須定義の充足、`AssocDeclared` は未宣言名を提供しないことを要求し、`AssocWellFormed` は全 impl に対してこの三条件を要求する。

`assocOf` は既存の `resolve` が成功したときだけ、一意な impl の右辺を head の照合置換で一度具体化する。明示定義がなければ、default の引数位置を goal の型引数で置換する。`Term` に関連型参照はなく、別の関連型の展開や新しい再帰・停止測度は不要である（章6.3、確定, 2026-11-05）。`assoc_independent_of_constraints` と `assoc_explicit_eq` は、解決成功を前提として値が選ばれた impl と照合置換で決まり、where の解決導出によらないことを示す。`assoc_derivation_agrees` / `assoc_derivations_unique` は、resolver を参照しない `AssocDerives` の二つの導出でも値が一致することを示す。Paterson 適格性と関連型適格性の下で、`assoc_total_closed` は、解決済み goal の**宣言済みの各名前**について結果が存在し、その変数がすべて goal に現れることを証明する。`assoc_unique` はその値の一意性を示す。`assoc_explicit_size` は明示定義について既存の `Term.subst_size` と同じ正確なサイズ公式を与える。`AssocExamples` は str・box・定数と引数位置の default・明示定義による default の上書き・rigid な goal 変数の正例と、head 外の変数・必須定義の欠落・未宣言名の提供を拒む負例を検証する。関連型を含む method 署名、関連型の等式制約や where 条件との単一化はこの核に含めず、未決定のままとする。

`Horn.solve` は全 `2^n` valuation を列挙する参照実装で、実用solverの性能を主張しない。有限性は `Fin n` という入力型に明示されており、任意のYulang制約がそこへ落ちるという未証明の仮定を入れていない。

`FiniteReachability.closure` は有限グラフの始点と辺を Horn 制約に翻訳する。`closure_exact` は、結果の真の成分と、始点から有限回辺をたどる独立な `Reach` 判断とを双方向に対応させる。経路長の打切り・非循環性・解決成功の仮定はない。`closure_empty` により、循環する辺だけでは到達点は生じない。評価依存と ground cast の探索で共有する基盤であり、このモジュールだけでそれらの source 規則との対応を主張しない。

`EvaluationOrder` は局所変数と有限個の global 宣言を区別する式を入力とする。評価位置に現れた global 名から、その宣言の関数本体へ推移的に進む。関数を引数として渡す場合も同じ辺をたどる。`check_exact` は computed binding の初期化と、位置を持つ module 文の両方について、実行可能な判定と独立な `Ordered` 判断が一致することを示す。到達した computed binding の位置には真の不等号を要求するので、自己依存・未来への依存は拒否される。関数だけの相互再帰を禁止する規則はない。

`lambda_no_dependency` は lambda **構築時**の依存がないことを示す。`applied_lambda_preserves_body_dependency` は直接適用すれば本体の依存が戻ることを示し、curried な直接適用にも負例がある。`accepted_initializer_earlier` / `accepted_statement_available` は、この依存判断で必要とされる computed binding が、並べ替えていない宣言順序で先行することを証明する。任意の source callback の実際の呼出しをこの判断が過大近似することはまだ示していない。lambda を値として渡すことと、その値が後で呼ばれないことを混同して全言語の実行時順序保証とは読まない。

`Methods.resolve` は member ごとの method の有無が確定した段階を扱う。`resolve_unique_iff` / `resolve_missing_iff` / `resolve_ambiguous_iff` は、それぞれ相異なる候補が 1 個・0 個・2 個以上である条件を示す。`select_ext` はリストの membership が同じなら結果も同じことを示すため、順列だけでなく同一 member の繰り返しも曖昧さを増やさない。

`CheckedRoles.checkImpl` は各 where 条件のサイズ減少と変数出現回数を検査する。条件側の変数番号上界より上の出現回数は 0 なので、有限回の検査と無限個の変数についての `Impl.WellFormed` が一致する。`CheckedRoles.resolve` は全宣言を先に調べ、成功した場合だけ既存の停止性証明付き `Roles.resolve` に渡す。`resolve_exact` は適格性を前提にせず、結果が成功することと「宣言集合が適格で、導出があり、到達する head に重なりがないこと」の同値を示す。不適格な宣言は、その goal の解決で使われなくても拒否する。

`RoleConstraints.addAssociated` は既存の関連型解決が返した値を、普通の型変数との等式として蓄積する。`Store.permutation_preserves_solutions` は一つの選んだ置換だけでなく、**すべての置換**について解集合が順序に依存しないことを示す。`conflicting_constraint_rejects` は同じ変数への char と str の要求が、後からの代入で上書きしても解にならないことを示す。`Store.check_dichotomy` は固定した置換での整合・矛盾の二分であり、解となる置換の存在判定器ではない。

`EffectExamples` は、同じfamilyの保護されたtail、境界ごとの解除、繰り返した保護、型引数を含むkey、shallow/multi-shot、handler armが新しく起こすeffectを検査する。nested `sub` の核の例は`0`、保護を消した比較例は`2`と計算される。これらはsource例に対応して手で構成した核の式で、parserからの翻訳の正しさを主張しない。

`shallowHandle_bounded` は、value armとoperation armの実行時effect上界を前提として、結果のeffectが`residual input ++ armEffects`で抑えられると証明する。継続の上界には元の入力行を保つ。この前提を型付けから導くsource handler推論器まで証明した、とは読まない。

## 高階の衛生性

`HigherOrder` のerase解除では、先に解除してから保護する往復が壊れる。`Directed` は許可されていないkeyについて、各境界の整数weightを保護で `+1`、解除で `−1` だけ変える。同じ境界と同じ許可maskの一対について両方向の相殺が成り立つ。handlerがcaptureできるのは、keyが一致し、すべてのweightが0のときだけである。

`DirectedHigherOrder.transport_opposite` は、product・sum・list・arrowで構成する任意の有限shapeと、その任意の値に対してこの相殺を証明する。関数の入力では方向を反転し、戻りcomputationと値では方向を保つ。新鮮性・weightの上限・fuelの仮定はない。

一方、非captureには由来の条件が必要である。weight `−1` に `+1` を足すと可視になるため、任意の符号付き入力を保護すれば必ず非captureになるとは主張しない。`guard_arrow_noncapture` は、反変方向に引数を変換した後の関数呼出しについて `ZeroAt` を仮定する。

`contravariant_debt_preserves_local_callback` は、callbackを奪う内側handlerの結果 `99` と、transportを入れて呼出側のhandlerへ届く結果 `7` を比較する。引数側の負の差分が内側でのcaptureを阻止し、帰りの正の差分が元の可視性を回復する。

## 型推論の主定理

`AnnotationSnapshots.observe` は、現在の行式に含まれる concrete な頭を符号付き行として計算し、残った行変数をこの観測では opaque とする。観測を取る前に、その時点ですでに分かっている置換は適用されている必要がある。`TrackedRow.subst` は行式を具体化し、注釈時点の履歴をそのまま保つ。`principal_observed_exact` は、保存した観測の許容性と既存の宣言的型判断の連言が、観測を付けた主制約schemeの意味と一致することを示す。許容された観測から後の行変数へ上界・等式は追加しない。T3 の例では、未知行を観測してから禁止effectへ具体化した履歴は受理され、その具体化後の行を**新しく**観測すれば拒否される。当初から既知の禁止effectを未知tailの横に置いても拒否される。

`RecursiveInference.generateSCC_exact` は、任意の有限 member 列について、同じ再帰仮定環境で全本体を検査する生成制約と独立な `SCCTyping` を双方向に対応させる。`closeSCC_exact` は slot 群を全本体の外側で存在量化するため、呼出しごとに型を選び直さない。全注釈の `FullAnnotation` は値型の有限変数だけを呼出側で具体化し、定義側ではそれらすべての割当てで本体を検査する。`rowsCaptured` の構文検査により、注釈中の明示的な行slotは外側の共有割当てを参照する。同じ SCC の別 member からも同じ注釈schemeを使う。これらは制約生成の正確性であり、source の SCC 発見や制約の解探索そのものの証明ではない。

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

# M1 solver の内部契約と局所更新

Status: Draft — 実装済みの限定された kernel と、統合前の境界を区別する。
Date: 2026-11-07
Scope: `integration/m1-solver` の要求モデル、tail/cache 表現、selection と増分計算の内部設計。言語仕様の追加決定ではない。

## 1. 決定済み仕様との境界

決定46・47と demand-model Q5 の回答に従い、要求は union を含まず、型変数と role 制約を持つ。
有限 rigid 観測の列だけに型変数を割り当てる旧候補は `int | str = any` を導くので採用しない。
旧候補の証明と、この過剰な同一視を示す反例は削除しない。
record の tail へは先頭 label の要求だけを取り除いて渡す（`spec/04-types.md` 4.3）。
variant の tag row に書く `|` は正位置の型 union とは異なる。

内部モデルの選択肢はこのメモで比較する。Yulang のコードで観測可能な未決定差だけを
`notes/questions/` に置く。cache の shape、mask の列挙、観測の rank の選択はユーザーへの問いにしない。

## 2. SCC の selection を一度で確定する条件

`MethodResolutionLocality` は既存の `MethodResolution.resolve` をそのまま呼ぶ。
未知 receiver では当該 method 名の可視 role/declaration 候補集合だけを読む。
既知 receiver ではその field の存在を優先し、不在時だけ typed fallback を読む。
他の field の payload、別の名前の role、処理しない SCC の snapshot を変更しても結果は変わらない。

SCC が確定した snapshot と、SCC が所有する selection site ID 列を渡し、各 site の解決結果を
回答表に書く。候補なし・一意・曖昧の三値を保持するので、エラーを黙って捨てる比較ではない。
同じ SCC 集合を含む任意の処理列で結果が等しい。順序入替えに加えて重複処理も冪等である。

採用理由は決定29の「SCC 確定時に選択し、後続具体化で選び直さない」と一致するため。
代案の全 selection 再走査 loop は、この snapshot 確定後の解決には必要ない。
ただし receiver の最終知識を得る constraint solver、SCC の抽出、scope の整合性は別の前提であり、
この定理から上流の求解そのものが一回で終わるとは結論しない。

## 3. module cache と実際の増分手続き

### 表現

`ModuleIncremental.Dependencies` は node `i` の依存を `List (Fin i)` に保存する。
node は module、または import cycle を既に縮約した SCC。すべての依存が先行することを型で表す。
順序と重複を消去しないため、compile が順序を観測しても定理は成立する。

`compile : Source → List Interface → Interface` の `Source` はソース本文だけでなく完全な cache key を含む。
`Interface` は成功した公開型に限らず、エラー、残余 qualifier、辞書依存、nominal identity なども含められる。
純粋な関数が読む入力を明示することで、成功を前提にせず全結果の一致を証明する。
本体以外の ambient state を読む compiler を、この型の関数と同一視してはならない。

`dirty` は変更フラグを依存先から利用側へ伝播する有限の topological pass である。
独立判断 `Affected` は「直接変更された」または「影響を受けた node に依存する」という有限経路で定義する。
`dirty_exact` が両者を一致させる。
`rebuild` は dirty node でのみ実 compile 分岐を通り、clean node は cache を返す。
その呼出し列は dirty な node の昇順列と等しく、長さは node 数以下である。

### cache に必要な前提

`rebuild_changed_graph_exact` は新旧依存 graph が異なる場合も扱う。
変更なしとマークした node は、自身の source/key と直接依存列を変えてはならない。
dirty の伝播は新 graph 上で行う。全体 build と増分 build の artifact 表は文字通り等しい。
したがって任意の決定的な表示関数を適用しても等しくなる。

採用したのは、意味的同値の判定器を仮定しない、完全な artifact/key の等号による cache 境界である。
代案の「同値な型なら同じ key」という意味的 cache は、完全な標準形を構成してから追加する。
`ProducerNormalForm.normalize_equivalent` は同値を保存する一方向の整理であり、
`Equivalent A B ↔ normalize A = normalize B` をまだ与えない。
標準形の完全性を仮定した wrapper を、その構成を済ませた定理として数えない。

この kernel は source の名前解決・依存抽出・SCC 発見・topological ID の新旧対応をまだ証明しない。
また `rebuild_calls_le` は compile の呼出し数だけであり、型 solver の時間計算量ではない。
参照実装は `dirty` の prefix を再評価しうる。Rust 実装では一度得た dirty 表を再利用するが、
そのデータ構造実装の時間上界はこの定理には含めない。

### EOF の独立性との関係

`EOFNoDefaulting.accepted_export_independent` は、同じ model・decode・割当て・interface の下で、
二つの impl 環境で **両方の finish が成功した場合**、公開された `ClosedInterface` が等しいという定理。
後から impl が増えて曖昧になる可能性を消していない。型の表示 cache と、EOF の成功判定や
辞書 artifact の cache は読む依存が異なる。
既存の Rust oracle plan §6.1 にある visible impl・辞書 body・設定・version まで key に保持し、
公開型が変わらないことだけを理由に診断の再検査を飛ばさない。

### interface が変わらない地点で再計算を止める

`ModuleInterfaceCache.rebuild` は、dirty flag による保守的な再計算をさらに精密にする別の実行可能な手続きである。
新旧 source/key の等号と、依存する完全な artifact 列の等号を実際に検査する。
等しければ旧 cache を返し、異なればその node の compile を一回呼ぶ。
新旧 source と graph は任意で、正しい旧 build が cache として与えられるだけで全体 build と一致する。
caller が dirty set、推論成功、solver の解を与える必要はない。

実際の compile 呼出し列は「完全な入力が異なる node」の昇順列であり、重複せず長さは node 数以下。
変更 flag が自身の key と依存列の不変性を正しく表すなら、その逆依存範囲の外では呼ばない。
範囲内でも依存 interface が変わらない地点で止まれることを、三 node の chain で計算して証明した。
key/interface 比較の費用はこの compile-call 上界とは別である。

採用理由は、不変の interface が得られた利用側を再コンパイルする必要がないことを、
純粋性だけの標語でなく実際の branch を持つ手続きで示すため。
型の意味的同値を仮定して検査を省略する代案は採らない。
ここで使う decidable equality は完全な artifact/key の等号であり、未完成の型標準形を同値判定器として仮定していない。

## 4. 要求変数と全 arrow 分解: contextual モデル

`ProducerContextual` は既存の `ProducerRanked` を変更せずに追加した具体モデルである。
Q5 の回答に合わせて、型変数を有限の rigid observation の列としては解釈しない。
`Environment.types : Nat → StructuralBase.Ty Row` により任意の有限意味型を割り当て、
`Demand.var n` はその型が満たすすべての観測を要求する。要求の構文には型 union を追加しない。
意味型への代入と、負の位置に union のソース構文を書くことは別である。

`Observation.arrowArgument n` も同じ型環境の `n` を使う。負の文脈の深さを `rank` とすると、
rank `k+1` の引数要求は rank `k` の全環境・全観測による producer order で比較する。
全 rank を量化するため、これは solver の fuel ではない。
任意の target 引数 `B` を環境の `0` に割り当て、要求 `arrowArgument 0` を選べるので、
`(A → C) ≤ (B → D)` から `B ≤ A` を取り出せる。closed `Negative` の稠密性の仮定はない。
逆向きも同じ比較で証明され、行の前順序の仮定の下で四成分の完全な iff を得る。

role 要求は具体的な有限 head table で解釈する。head は base・pair・record・variant の tag・arrow
であり、role 名ごとに許可する head の列を環境が持つ。型の union は両方で role が成立することを要求する。
`[base int, base str]` を許可する role は `int | str` で成立し `any` では成立しない。
この区別が arrow の引数文脈でも失われないことを証明した。
許可表に抽象的な monotonicity/distribution 公理は課さず、構造的部分型の保存と grouping を直接証明した。
ただし、これは実装 head による role 観測の核であり、条件付き impl の探索・辞書・method selection
全体のモデルではない。payload の rigid 要求は別の観測パスとして保持する。

mask は要求側の演算 `Demand.mask` である。隠す label の field 観測を record-kind 観測に写す。
`AcceptAt` におけるこの意味を `acceptAt_mask` がそのまま記述する。
有限型 carrier `StructuralBase.Ty Row` 自体には `var` / `mask` の constructor を追加していない。
任意の代入後の値に対して arrow の分解は適用できるが、これだけで新 solver の自由 parameter・
mask family を評価する関数を構成したとは言わない。

### regular graph への拡張

`ProducerContextualRegular.ProducerLe graph leRow a b` は、任意の
`Graph Row State` とその `Layer Row State` に対して、すべての constructor depth における有限展開を
上記の全 rank・全環境の順序で比較する。有限性・非循環性・solver 成功・fuel は前提にない。
`ReferenceLe graph leRow s t` は任意の graph state の全展開について同じ比較をする。

`producerLe_arrow_reference_iff` は、任意の graph、任意の四つの graph state、任意の四つの行に対し、
行関係が反射的かつ推移的なら、arrow の比較が引数の反変比較・入力行の反変比較・結果の共変比較・
出力行の共変比較と同値であることを示す。さらに既存の
`RegularInferenceModel.Ty Row` に引用した具体的 carrier の `producerLe_arrow_iff` を証明した。
ここでの symbolic unknown は要求環境の意味値として表し、regular 値は graph state として表す。
producer syntax の `mask` を graph state に変換する新しい解釈はまだない。
また、graph の payload 参照は既存 `Layer` 文法で guard される。この定理から、由来のない
非 guarded な tail の循環の求解が得られるわけではない。

既存の `IsRecord`・lookup を使った旧部分型保存、pair/variant の完全な分解、record の単調性、
union/inter の単調性、同じ構成子の grouping、引用後の全 constructor congruence も保持する。
`emptyRecord` は既存の record 幅の上界のままである。

### 旧 solved family の具体接続

`Core.ProducerContextualInstances.order` は、上記 regular 順序を実際に
`Core.ProducerLegacyInstances.OrderExtension` へ代入したものとなる。
旧比較の保存、推移律、union 上界則はすべて具体的な証明から供給する。
instance は旧 scheme を同じ自由な値・行 parameter で評価してから、新しい順序で結果を比較する。
旧 instance や旧 Typing の存在量化を instance の定義として使わない。

任意の旧 `Result`・任意の結果値と行に対して、旧 instance はこの直接評価による instance に入り、
新 instance からは同じ結果行を持つ旧 instance と要求同値な値が得られる。
任意の旧 supported 式では、行代数の反対称律を前提として旧独立 Typing を使った同値定理と、
新 concrete model の独立 Typing への健全性が得られる。
これは旧入口の solved family の再解釈であり、独立した presence solver の completeness ではない。

### 未接続の補題

1. 新しい presence signature の評価を、この carrier（または拡張 carrier）へ結ぶ具体解釈。
   特に自由 parameter とその各 mask family の評価を構成し、mask の各要求を保存・反映する補題。
2. `exactEmpty`・`required`・全 `recordDefault` image を実装した同じモデルで、上記 arbitrary arrow iff
   が保存されること。現モデルは旧 record 幅上界を持ち、これらの演算を実装したモデルではない。
3. 任意の独立した新 Typing から `Core.ProducerContextualInstances.Instance` へ戻る完全性。
   証明済みの source sound と source_instances_exact_modulo を逆向き Typing completeness と取り違えない。
4. arbitrary target の分解は閉じ、以下の rigid graph 文法では実 inspector・全入力の branch saturation・
   拒否完全性へ接続した。全 contextual 解の solved parameter への retraction と、presence 文法への拡張は別に必要である。
5. role head table の核から、条件付き role impl と辞書の実際の意味への対応。

代案として (a) 旧 finite-rigid demand に戻す方法は Q5 の区別を失い、(b) arbitrary role predicate に
分配等の法則を仮定する方法は必要な数学を前提に隠す。今回はいずれも採らず、具体的な head 観測と
任意型を名前付けする要求変数を採った。これらは Lean 内部の設計判断なので新しいユーザー質問にはしない。

`ProducerContextualNormalForm` は、既存の同一 constructor grouping 関数を変更せず、新しい順序でも
全要求の受理を保存・反映すると証明する。有限型の全再帰処理は行の前順序を前提とし、
arrow の負位置も新しい合同性を使う。
`normalize_not_complete` は同値な `int | str` と `str | int` の出力が異なることを証明する。
この関数の同値保存だけでは spec 7.4b の完全な canonical interface を得られない、という境界を形式化した。

### record の head を消費した後の要求

`ProducerContextualRecord.FieldLe hidden S T` は、hidden にない label の field 観測だけを比較する。
すべての負文脈 rank・要求環境・payload 観測を量化する。
same-label record 比較は、payload の通常の `ProducerLe` と、head label を hidden に加えた tail の
`FieldLe` に正確に分解される。元の要求を tail にそのまま渡すことや、head を `any` に置換することはしない。
外側 record が kind と role-head の要求を既に満たすため、tail そのものを whole-type 比較する必要はない。

target が `{x:B}`（旧 width `{}` を rest に持つ required singleton）なら tail の要求は空になる。
同じ label の内側 head を消しても要求同値であることも証明した。式の評価順を消す変換ではない。
任意の regular graph と具体 regular carrier にも全深さで移し、tail は同じ観測深さで扱う。
この regular carrier の tail は有限 layer なので、次の非guarded node-tail 解法とはまだ別の境界である。

### 実 constructor solver と型制約 compiler

`ContextualNestedModels.Models` は任意の外部 regular graph と元 slot の割当てに対する独立判断である。
graph の rigid node は変数・base・bottom/top・pair・行付き arrow・proper record spine・variant を持つ。
実 `NestedValueSolver.inspect` の子制約と行制約が新順序で健全なことを全深さで示し、
既存の finite Horn 飽和をそのまま用いて全モデルを保存・反映する。
任意の入力で solve の拒否は独立 contextual model の不存在と同値である。
逆向きでは既存の実 coalescer が構成する regular 解を旧部分型保存で移すため、
存在するはずの解や successful solver を caller の前提にはしない。

`ContextualBranchSolver` は edge の任意の有限論理積・論理和を実際に DNF 列挙し、各枝でこの solver を呼ぶ。
全入力の任意のモデルはある受理枝の cache に残り、受理 cache の任意のモデルは元の入力モデルになる。
各受理枝から constructor/variable `Closed`・整合性・slot 数の二乗の cache 長上界を得る。
空結果とモデル不存在も同値である。DNF の枝数が多項式とは主張しない。
この Closed は古い「子辺を全 mask で閉じる presence cache」とは異なり、既存反例を変更していない。

`ContextualTypeConstraintGraph` はこの順序の lattice/congruence 則を、既存型項 compiler の generic 契約に供給する。
共有するソース変数への各割当てを保ったまま、型制約の充足と実 compiled graph の独立モデルを双方向に結ぶ。
さらに同じ具体 regular inference carrier 上で全自由 parameter の健全性と拒否完全性を示す。
任意の rows と型制約について、実 `TypeConstraintInference.infer` の rejected は、既存 supported check が true であり、
新順序による充足割当てが存在しないことと同値である。成功・Closed・解・fuel の前提はない。
source union・target intersection・fixed record spine という既存 compiler の境界は変更しない。

採用理由は既存の実 inspector/compiler/coalescer を使い、model 判定を solver 成功の定義にしてしまわずに接続するため。
代案の独立な新 compiler を同時に追加する方法は共有変数と行の対応に別の証明義務を増やす。
ただし任意 contextual 解のこの同じ coalescer への retraction は、旧構造解の存在からは得られない。
この部分と simultaneous row inference、presence 全体への lowering は未完として残す。

## 5. 有限の正方程式を解く核

`PositiveEquationElimination` は、未知変数と任意の atom に union/inter を適用する有限方程式系を扱う。
同じ観測深さでの循環を許す。全座標列の長さ N 回の上昇 `x ∨ F(x)` の後、N 回の下降 `x ∧ F(x)` を行う。
任意の parameter で結果が不動点となり、既に不動点だった parameter はそのまま返る。
この有限回数は座標数から証明された lattice の高さであり、探索 fuel の増減によって正しさを変えない。

実際の返却値は union/inter の有限式である。atoms は任意の命題であり、有限サンプルにしない。
`solve_sound` と `solved_instances_exact` は解の存在も solver 成功も仮定しない。
非単射の座標写像と step が可換なら `project_natural` によって消去結果も可換となる。
具体的な mask family では、この step の可換性と有限座標化を別に構成する必要がある。
また一般の producer subtyping の負位置の循環や、guarded payload をこの Boolean 系と同一視しない。

### 具体的な tail と mask family

`PresenceTailElimination.Body` は既存 `PresenceLayers.Layer` の atom と同深さの tail ref を分ける。
union/inter/mask の下に任意の同深さ循環を許し、record head は required atom と label を除いた tail で構成する。
slot と有限 mask の積を座標とし、上の消去を実 layer の union/inter で実行する。
結果 layer を追加 mask した構文は、対応する座標の結果と等しい。
従って自由 parameter は通常の具体 layer で足り、深さごとの任意述語 family を別に仮定しない。

独立判断 `Satisfies` は、任意の payload 述語割当て、外側 mask、data 値で元の方程式が成り立つこと。
実際の `solve` は全 parameter でこれを満たし、任意の独立した layer 解を同じ parameter として回収する。
構成に成功や解の存在は使わない。比較の両方向を示す `solved_instances_exact` は任意の具体 layer 解を対象とする。

mask の語彙は `Fin labels` として宣言し、容量は `slots * 2^labels` と証明した。
Rust では言及された label の局所 intern を使う案とするが、任意 Nat label をこの dense 語彙へ移す補題はまだない。
外側 mask は任意の Nat 列を量化するので、語彙外の field を有限サンプルとして捨ててはいない。
guarded payload の再帰 graph 化は次の接続で閉じた。関数・行・whole default の統合、producer 不等式への適用は別の義務である。

### 同深さ循環を消去してから regular graph に閉じる

`PresenceTailRegular.solveGraph` は実際の有限 tail 消去の後、payload ref を regular graph の内部参照へ閉じる。
外部の任意 graph と任意 parameter layer を保持し、tail の同深さと payload の一段の差を変えない。
独立 `Realizes` は元の Body 方程式を、任意の深さ・外側 Nat mask・内部有限 mask・slot・data 値で解く判断である。
実構成がすべての parameter で Realizes を満たすことと、任意の独立 regular 解の全深さ・全 mask での回収を証明した。
従って source 由来を持たない非 guarded な tail の循環も、この positive data-demand 文法では具体的に求解できる。
外側 mask と atom/parameter 中の label は Nat のままで、有限語彙の外を観測から削除していない。

採用理由は同深さの循環を先に有限消去してから guarded graph を閉じることで、tail に一段の guard を挿入する代案を避けるため。
深さごとの任意述語 family を free parameter と仮定することも不要になった。
この layer 文法には関数・行・exactEmpty・whole recordDefault image がない。
`Body.record` は required head と除去後の tail 要求を組み立てる演算であり、producer 全体のモデルとは主張しない。

## 6. 計数付きの参照実装

selection は元の `MethodResolution.resolve` と値が等しい計数付き実装を使う。
visible role 数 R の scan は `1+2R`、型 node 数 V の既知 receiver lookup は `1+V` 以下。
method-name index を一回構築して N 個の名前を引く場合は、可視 declaration 数 D に対して `3D+2N` 以下。
catalog の role/name ごとの関数性の下で元の解決結果と一致し、列順や重複 entry は意味を変えない。
上界自体は関数性も成功も仮定しない。map 操作は抽象単位で、visibility filtering と map 実装の費用は別である。

`InferenceSubstitutionCost` は stored scheme の実際の substitution と同じ値を計算する。
formula だけでなく、その中の値型・行のすべての constructor を数える。
binder の下では捕捉された置換値の両成分を rename する費用を加える。
全 node 数 N、binder 深さ H、具体化先 computation の node 数 K なら、
`N * (1 + max(2,K) * H)` 以下、従って `N * (1 + max(2,K) * N)` 以下である。
旧 `Scheme.instantiation_nodes` が論理 node 数だけを保っていたことを、定数時間性と読み替えない。
参照実装には source body の再推論を含めない。ID bit cost、allocator、後続 solver の費用も別である。

`TypeSimplificationSize` は既存 automatic pass の全入力で、最終項の値 node 数と行込み node 数が
どちらも入力以下であることを示す。受理/不受理のどちらの候補分岐にも成立する。
一時的な joint substitution だけは各変数を union/inter の3 nodeに広げ、全体で元の3倍以下となる。
実際の候補列は parameter 数 n に対して merge が n²、scalar sandwich が 4n。
`TypeSimplificationCheckCost` は続いて `symbolicCheck` の計数付き参照実装を与える。
全11枝を eager に評価し、型・行の equality と record-spine 検査も実際に再帰走査して数える。
Bool の結果は既存 checker とすべての入力で一致し、source/target の行込み node 数の和 S に対して
`(S+1)*128^S` 以下である。128 は再帰枝と局所走査を覆う保守的な定数であり、tight bound ではない。
再帰深さは入力の既存 termination measure から計算し、caller の fuel 前提はない。
ID の等号は原始単位とするが、型全体の等号を一単位とは数えない。
多項式 bound を仮定する代案は採らず、同じ部分問題を繰り返しうる現 checker の指数上界をまず証明した。
これと候補数・size 非増大を全 automatic pipeline に合成する義務は別に残る。

## 7. 残る統合義務

- rigid constructor graph の全入力分岐・実 Closed・拒否完全性は閉じた。
  残るのは exact/optional/default/mask を持つ任意 presence 制約の lowering と同じ carrier での飽和である。
  旧 cache の子辺まで全 mask に閉じる表現には既存の反例がある。別の obligation 表現が必要。
- positive tail 方程式の具体 mask family と全深さ regular 解は閉じた。
  残るのはこの family と contextual constructor 不等式の共通解釈・全解 retraction の接続である。
- Q5 対応 contextual モデルで任意 arrow 引数の分解は閉じた。残るのは exactEmpty/required/whole recordDefault image と自由 parameter/mask の評価を含む同じモデルへの統合。
- 具体モデルで `presence_solve_complete` と `presence_generate_exact` を結合し、残余 existential 制約を持たない scheme family を得ること。
- 新独立 `Typing` から旧 scheme の新 instance を得る完全性と、統一 `Core.infer` の主型性・拒否完全性・unsupported 排除。
- role・nominal・effect・regular graph を含む全 interface の完全な標準形と、実 module compiler への cache kernel の接続。

これらは定理の成功や自由 parameter の制約を前提にして閉じたことにはしない。

# M1 の具体共通 carrier と残る compiler 境界

Status: Draft — concrete implementation choices; no new language decision.

Date: 2026-11-07

Scope: `integration/m1-common`。正本は spec 4.3・4.7b、決定46・47。

## 1. 構文と要求意味

`CommonFinite.Ty` は base、bottom/top、union/intersection、pair、width/exact record、
record head/tail、whole default、variant、両行を持つ arrow、外側 mask の有限構文である。
`CommonSyntax.Layer` と有限 `State.block` が regular 表現を与える。要求、環境、観測は
solver や Typing に依存せず、型構文と負文脈 rank による再帰で定義する。

要求の変数は任意の型構文を名前で参照する。`Common.Parameter` は finite と regular の
二つの具体構文の和である。finite はその有限型全体を保持し、regular は producer と同じ
constructor depth で展開する。`Environment.atDepth` の同じ環境を負の arrow 観測にも渡す。
有限 rigid 観測列や任意の述語を parameter の代用品にはしない。

regular だけを環境に許す案もあるが、各 depth における任意有限環境の実現補題が余分に必要に
なる。二つの構文を明示する案では、その実現は `.finite` により直接得られ、任意 regular 型の
割当ても `.regular` で保持できる。source/scheme の自由変数は `TyTerm.var` の代入として扱う。

## 2. optional と旧型の保存

optional 要求は「field が存在すれば payload 要求を満たす」を表す。未知 width 型に対しては
自明な payload 要求だけが成立し、exact empty にはすべて成立する。record head が要求 label と
同じなら payload へ降り、それ以外は tail の optional 観測と自明要求へ分解する。

旧型への新 optional 観測は、payload が自明なら旧 records 観測、そうでなければ旧 field 観測へ
射影できる。負位置では、新しい任意 parameter が満たす関連 arrow 引数の有限リストを取り、
それらの旧 intersection を witness とする。rank ごとの保存・反映を帰納することで、
新環境を旧型に限定せず有限 embedding の iff を示す。

`CommonLegacy` では旧 graph の各有限観測と埋め込みの交換を証明し、この有限定理を全深さへ
持ち上げる。`Common.contextual_embedding_exact` は任意の旧 regular 型の比較を保存・反映する。
これは新 infer の instance 保存・反映を定義だけで置き換えるものではない。

素朴な「構文にその label がない」という absence 判定は採用しない。例えば旧モデルで同値な
`record 0 bottom bottom` と `record 1 bottom bottom` を区別してしまうためである。
この選択は集合論的包含を導入するものではない。

## 3. mask、record tail、default の深さ

producer mask は要求の mask と異なる。隠れた field の要求を消し、payload 内の mask と外側の
mask を混同しない。外側の hidden-label 集合は tail と default source へ同深さで渡し、
payload へ降りるときには空へ戻す。合成は hidden-label の和集合に一致する。

record/default の型判断は、tail/source が width record 以下であることを別途要求する。
head の比較のために tail へ同名 field の要求を追加しない。

default は新しい field を構築するので、その payload も普通の record と同じ深さを消費する。
`Layer.evalAt 0` では default の head を bottom に置き、source の残りの観測は同深さで保持する。
正の深さでは具体的な finite default 演算を使う。この初期層を設けず finite default を全深さで
そのまま使うと、`default l width F ≤ required l any` が深さ0で壊れる。
旧構文には default がないため、旧 graph の観測保存には影響しない。

## 4. 行と独立した data readout

`Common.Row` は `(key : Nat, signedWeights : List Int)` の集合である。行自体は無限でもよく、
負の重みも各座標も捨てない。M1 の空行・join・包含をこの具体集合演算で定義し、前順序、
反対称性、空行と join の法則を証明する。これは M2 の全 source scope 解決の統合ではない。
行を有限集合や空行に固定する案は、自由 parameter と無限行を失うため採用しない。

`Common.DataReadout` は同じ構文上で、既存 `SourceDataRuntime.Value` の有限値を読む独立な
帰納的解釈である。exactEmpty は空の field 列だけ、width は任意の record を受ける。
whole default は既存 `Fields.insertDefault` の正確な像であり、present source でも fallback の
値の存在を残す。要求同値な型の data 集合が等しいとは仮定しない。

## 5. solver との残る接続

上の構文と constructor 法則だけで、残契約の全入力 compiler や公開 infer が完成したとはしない。
特に、既存の positive data-demand `Body.record` を producer record へそのまま移すことはできない。
`inter(required l A)(mask [l] bottom)` と producer の `record l A bottom` は同じ意味ではない。
必要なのは、field 要求だけを同深さの方程式へ移す独立な projection と、その完全な compiler bridge
である。default の有限完全 inspector、型・行の simultaneous な自由 parameter family、全 source の
公開 principal/rejected/unsupported、完全 interface canonical encoding は別々に検証する。

`Common.common_record_iff` は、任意の同名 head の比較を payload と残る tail 要求に分ける。
tail に渡すのは、先頭 label を除いた field と非自明 optional の観測だけである。optional の
自明な payload は構築済み head が常に満たすため、tail に戻さない。required target なら tail の
要求はすべて消える。構築時の tail ≤ width は生成器の別制約として残る。

同深さ record 方程式には、次の正しい producer polynomial を採用した。

```text
record l A R ≈ inter (record l A top) (union (record l A bottom) R)
```

record の各観測は head／shape による定数か、そのまま tail に渡る観測である。観測の真偽に
関して `F(false) ∨ (F(true) ∧ p)` に分解でき、任意の外側 mask でも同じ証明が成立する。
代案は required-bottom と masked-tail を含む polynomial だが、採用案は新たな mask label を
増やさず、二つの端点 atom だけを追加する。`CommonRecordTailElimination.compile_models_exact`
は実際の record 構築を含む独立な方程式と変換結果の両方向を証明する。

`CommonTailElimination` は全 mask 座標の有限 Boolean 方程式を、型の intersection による上昇と
union による下降で解く。反転は producer union が観測の論理積になるためである。反復数は graph
から計算する内部値であり、公開定理に fuel 前提を置かない。任意の Common 型 parameter が解に
なり、任意の独立解をそのまま parameter に選ぶと回収できる。mask の単調性は fresh label の
観測で別途証明済みなので、全 mask 下の同値と通常の Common.Equivalent は一致する。

## 6. whole default の同深さ方程式

default は source の一つの観測だけで決まらない。選択 label の optional payload と、存在または
fallback の観測を組み合わせる。そのため record と同じ一観測 polynomial へ無理に縮めず、
元の型構文のまま反復する。証明側では、元の query、optional query、存在、optional な存在の
4モードを追う。default は label を変えず、このモード集合の中だけで遷移する。

`CommonPresenceTailElimination` は各 slot × 全構文内 mask × 4モードの有限座標を使う。
外側 mask は任意の List Nat のままであり、深さ・rank・環境・元の観測もすべて量化する。
反復回数は座標数から決まり、有限個の要求をサンプルするものではない。独立な Models は
元の Body.eval による各 constructor 方程式そのもので、solve を参照しない。

この有限反復単体の payload と fallback は任意の固定された Common 型でよく、型自身は
regular/mask/arrow/default を含められる。さらに `CommonPresenceTailLayers` で payload を index に戻し、
Layer 構文上で同じ反復を行う。引用・rename・有限評価と実反復の交換を文字通りの等号で示した。

`CommonPresenceTailRegular` はその symbolic 解を `CommonSyntax.closeBlock` で閉じる。同じ未知 slot を
guarded payload／fallback／負の arrow 子と同深さ tail に代入する独立 Models を定義し、任意 parameter の
健全性と、任意独立解の retraction を証明する。`Layer.evalAt_congr` は前の constructor depth の全 rank の
payload 同値を保存するため、負位置に単調性を仮定する必要がない。default の初期層もそのまま保つ。

presence だけを見て default を source に消す案は採用しない。
`inter exactEmpty (required l int)` は width 以下かつ required l top 以下だが、default 後の str field
要求を元の source が満たさない。`CommonDefaultBoundary.presence_does_not_erase_default` が任意 label
についてこの境界を証明する。source が構文上同名 record head である場合の既存法則とは区別する。

`CommonDefaultRequired` は required target をさらに有限2 branch へ分ける。正の全深さの field 存在は
outer Layer から計算でき、payload index の名前変更に依存しない。source の optional payload は深さ d+1、
target payload と fallback は d で比較する。深さ0の record-bottom 近似は別に処理する。
同名 record target には、先頭 label を除いた `RecordTailLe` を追加する。この規則でも optional/presence
条件は独立な義務であり、未知 source slot を含む全 compiler が解消したと数えない。

## 7. 行・formula・旧型付け

`CommonRowTailInference` の入力は有限 syntax であり、行右辺を var/empty、左辺を var/empty/join とする。
型 atom、record payload、default fallback の両 arrow 行も同じ symbolic row ID を共有する。
`.layer` は同じ未知 Fin slot を guarded 子／負の arrow 引数へ置き、`.recordRef`／`.recordDefaultRef` は
未知 payload/fallback を同深さ tail/source と共有する。実 Body.eval は両位置へ同じ values を代入する。
まず実 RowFlowSchemes の有限 scheme を作り、その行代入で実 presence-tail solver を実行する。
任意 parameter が元の独立 Models を満たし、任意解は行を文字通りの等号、型を要求同値で回収する。
元の行を保持できるため、型内部の行を交換する法則を model の前提として追加しない。

実生成 Formula の正規化では、局所 existential を有限 slot に移し、値と行を同じ computation slot と
して保持する。捕捉環境を一般化し直さず、value-let の両枝と strict fallback の全制約を残す。
`PresenceNormalForm.closed_core_exact` は全 Core 式・任意結果の型判断との iff だが、右辺に原子制約の
充足を残すので solved family ではない。explicit row と新観測 inspector の row 保存もこの区別を保つ。

旧モデルへの transport で、literal な ModelMap の構成子等号を強制する案は採用しない。
`.legacy (.node A)` と `.node (embedOld A)` は構文上異なるが、全深さの観測は等しい。
`CommonLegacyTyping` はこれを使い、評価の観測等号、実 existential witness の移送、旧 Typing と
旧 infer instance の独立 Common Typing への保存を証明する。新 infer の instance や反映は未完である。

## 8. 標準形の実装範囲

scalar lattice は最小 Boolean clause の有限表へ正規化する。共有 variable ID を先に並べ、具体 base は
bool/int/str/unit の辞書順とする。同じ ID の全 Common 型割当てについて、要求同値 iff 同じ encoding を
証明した。有限の固定 Shape 内では pair/required/tag/同じ行 ID の arrow の union を成分ごとにまとめる。

この節の `CommonCanonicalOpen` / `CommonCanonicalShapes` の equality は同一割当てでの pointwise equality
であり、存在的 instance 集合の equality や binder の α 同値ではない。Shape の code は label・行 ID を
Shape 側に保持する。自己完結 code と α 正規化への拡張は §11 を参照する。全 interface の混合 head、
一般 record/default/mask、役割・nominal の義務、regular graph の一意化は残る。
全 concrete Common.Row は任意の述語なので、正規化対象は有限 interface 構文にする必要がある。

参照アルゴリズムは n+4 atom の全 profile を列挙する。最小性判定はその表を繰り返し走査し、
出力も指数的になり得る。既存 infer/display の呼出経路は変更せず、完全な interface encoder への統合時に
共有表現・未使用 parameter・費用を別途検討する。

## 9. Optional payload の実射影と有限 outer inspector

`CommonPayloadProjection` は outer Layer を実際に再帰走査する。結果は
`Option (Payload Index)` であり、`Payload` は元の子参照、bottom、top、union、intersection の有限構文である。
`none` は自明な観測さえ持たない状態、`some top` は自明な観測だけを持つ状態である。
この区別を Bool 一つや top への既定値化で失う案は、未知 width、非 record、optional を誤って同一視するため採用しない。
mask は outer の label 集合に蓄積し、payload に降りるときは既存の解釈どおり空に戻す。

任意の payload 割当て、正の深さ、負文脈 rank、要求環境で、元の field/optional 観測と射影後の
子型の観測が一致する。Common への持上げでは参照 state の実 `graph` を一度読む。
これにより source の深さ d+1 と payload の深さ d が正確に対応し、`OptionalPayload` を通常の
`Common.Subtype` へ置き換えられる。regular state を有限深さのサンプルに置き換えることはない。

`CommonRecordTailProfiles` は深さ0を別に処理する。このとき全 guarded payload は bottom であり、
default は record head になるため、field と非自明 optional の二つの Bool がすべての初期観測を決める。
正の深さは射影後の子比較へ移る。tail の optional は自明要求を渡さないので、両側の欠けた profile を
top で埋める操作はここだけで正当化する。通常の field 比較では `none` と `some top` を引き続き区別する。

`CommonOuterLabels` と `CommonRecordTailFinite` は、source/target の outer record/default/mask に現れる
label と、そこにない新しい label 一つを調べれば十分であることを証明する。payload 内の label は現在の
層に混ぜない。有限表の外で field/optional の射影と初期 Bool が不変であることから、全 label の量化を除く。
`CommonRecordEnvelope.outsideRecords` は role 観測を使って非 record head の要求を正確に判定する。

`CommonDefaultInspection.inspectDefault` の返す最終 branch は `List (Common.Ty × Common.Ty)` だけである。
head/presence/初期層の Bool は実行して除き、`OptionalPayload`、`RecordTailLe`、元の whole-default 比較を
最終 atom に残さない。任意 source/fallback/target の subtype と branch の子比較の充足が同値となる。
これは **outer 一層の完全分解** であり、子が regular graph の元の state に戻る場合の有限飽和・停止性や、
未知 source slot の射影を推論時の symbolic graph に取り込む定理とは区別する。

`CommonRecordInspection` は通常の record 構築も head、実 payload、head を隠した残りの tail に分解する。
実装は default への付替えではなく、この三部分を直接 compile する。present default の同値は証明内だけで
利用する。required は rest を width empty record にした場合であり、exact empty へ読み替えない。

## 10. 実際の生成 clause からの方程式消去

`CommonPresenceConstraintGraph` は既存の実 subterm collector を使い、生成された `TyTerm` ごとに
共有 node を割り当てる。record tail/default source は同深さ参照、payload と負の arrow 引数は guarded
参照へ置く。型変数には一つの node、行変数には元の ID を保つ。定義方程式の任意の意味的実現から
元の TyTerm 評価を要求同値で回収するため、単に一つの標準評価だけを正しいとするモデルではない。

`CommonPresenceClauseFamily` は実 packed clause の定義方程式と明示行制約を、既存の simultaneous
solver へ渡す。どの自由 row/value parameter でもこの部分は解になる。元の独立解を parameter に選べば、
行は等号、すべての値は要求同値で戻る。source の生成不変量から row support を証明し、呼出側に要求しない。

`CommonPresenceSourceFamily` は normalize、binder packing、graph construction、行/方程式求解を
実際につなぐ。任意の閉 source/Core 式と任意結果に対する iff を得たが、有限の subtype edge は
`Scheme.ResidualHolds` として明示的に残る。この述語は元の Typing/Formula.Holds/Models の別名ではなく、
node 間の比較の有限リストである。それでも制約なしの family ではないので、入口名は `inferSource`/`inferCore`
をこの専用 namespace に置き、公開 `Core.infer` と呼ばない。

具体化した後の Common 型を完全に inspect できることだけでは、推論時に固定した有限 scheme を構成できない。
未知 slot の profile/presence と同じ型・行 ID を symbolic graph 上で保持し、残る比較を有限に飽和させる
完全な compiler が必要である。これを row/definition solver の定理の前提や scheme の law field に隠さない。

## 11. 自己完結した有限 code と型パラメータの名前変更

`CommonCanonicalInterface` は固定 Shape の code を、構成子、label、arrow の共有行 ID を含む
自己完結した `Code` に拡張する。二つの入力で Shape が等しいことは仮定しない。実際の role/field/row
観測で root、label、行 ID の違いを識別し、同じ code iff 全行・全 Common 型割当てでの要求同値を示す。
対象構文は scalar lattice、nested pair、単一 required、tag、scalar domain の arrow と同じ Shape の union である。

`CommonCanonicalAlpha` は generalized type slot の同時全単射を有限に列挙して code を選ぶ。
同値は encoding の等号で定義せず、「一つの同時全単射の後、全行・全 Common 型割当てで要求同値」とする。
同じ parameter の全出現を一緒に移し、任意の固定行割当て・任意 target について、target と要求同値な具体化の
存在を両方向で保つ。slot 数にかかわらない正負位置による消去・共起/併合と一般の再parameter化、異なる
slot 数の比較、弱い変数、行変数の α 同値、nominal/role 義務、一般の regular interface は対象ではない。
forward map と backward map の直積列挙は避け、forward map を列挙して逆写像を有限 lookup で回収する。
候補数の上界は n^n と証明した。参照用の全探索であり、既存 infer/display の実行経路には追加しない。

`CommonCanonicalNames` はこの意味的代表を選んだ後、異なる型変数の最初の出現を左から数え直す。
未使用 slot は逆写像を完成させるために末尾へ置くが、表示する新しい名前は生まない。出力 Form 内で
最初の出現順に並べた番号が `List.range k` であること、α 同値 iff 同じ正規化出力、冪等性、任意固定行と
target に対する要求同値な具体化の存在の保存・反映を証明した。weak variable の metadata や renderer は別である。

## 12. 変数の上下限と実 source pool の接続

`CommonBoundCoalescing` は有限の lower/flow/upper/check を、固定した境界型の比較へ消去する。
祖先の lower を union で集め、到達先の upper を intersection で集める。変数 i の展開は
`lower(i) | join [parameter(j) & upper(j) | j reaches i]` である。固定比較の成立を仮定したとき、
すべての Common 型 parameter が元の問題の解を与える。任意の独立解は、その全 slot を parameter に
選べば要求同値で回収される。証明は join/meet の普遍性を用い、負位置の単調性や未証明の分配律を仮定しない。
変数間の循環は有限 reachability が扱い、呼出側の fuel や非循環性は不要である。

`CommonPresenceVariableBounds` は実 pool の `.var` node を同定し、var-var を flow、rigid-var を lower、
var-rigid を upper、rigid-rigid を check に分類する。rigid はここでは「元 pool の非変数 node」という意味であり、
未知型の参照を持たないという意味ではない。元の node/row ID を保持し、変数 node の方程式を上の展開へ置き換える。
実 record/default/mask の同深さ参照と payload/arrow の guarded 参照を同じ regular solver で閉じる。
別々に求解して共有 slot を失う案は採用しない。

`compiled_joint_elimination_exact` は任意の実 atom 列（行右辺は var/empty）で、全明示行制約、定義方程式、
変数辺を消去する。任意の元モデルを同じ行・要求同値な全値で回収し、逆向きも成立する。最終の条件は
元 pool の非変数 node どうしの比較の有限リストである。境界型は未知 graph node を読み、その解が parameter に
依存するため、この条件まで成立することを自由 parameter の定義に隠さない。次に必要なのは、同じ共有 graph 上で
この rigid 比較を分解し、有限に閉じた分岐へ飽和させる compiler である。

`CommonPresenceCoalescedSource` はこの変数辺消去を、実 source/Core の生成器、binder packing、
shared pool、行 solver に接続する。Scheme が持つのは有限 pool、元 edge、行 scheme、結果 ID だけであり、
semantic model certificate は持たない。具体化は行・元型変数・recursive equation の三 parameter family を取る。
任意閉式と任意結果について残余条件付き principal iff を証明し、GoodAtoms は実生成器から内部で供給する。
残余の両端が元 pool の非変数 node であることも証明する。具体化後の型比較を推論時に実行したと見なす案は採用せず、
この明示的な残余を除く symbolic saturation を最終公開入口の前に残す。

## 13. 未知 slot の全 label を保持する symbolic tail view

入力の有限構文に現れる label だけを調べる案は採用しない。未知 slot の具体化には、入力にない label を持つ
任意の Common 型も許すためである。§9 の concrete `inspectLabels` は実際の具体型を走査した結果であり、
その有限支持を代入前の推論 scheme にそのまま移すことはできない。

`CommonSymbolicTailView` は、任意の hidden list H と任意の型 S/T に対し、同深さの `RecordTailLe H S T` を
有限の型構文による通常の subtype 比較へ正確に符号化する。H の各 label を同じ top payload の record head で
覆った型を `cover H S` とし、次の二つの head を組にする。

```text
view H S = pair (record 0 top (cover H S)) (record 1 top (cover H S))
```

head 0 が隠す label 0 はもう一方の成分で観測でき、head 1 についても同様である。両方の成分を比べるため、
H 以外のすべての label の field と非自明 optional を保持する。未知 slot の型から fresh label を探す必要はない。
`tail_view_exact` は任意 H/S/T でこの iff を証明する。通常の subtype 比較へ移すだけでなく、
実 `TyTerm` の `termView` を構成し、任意 slot 割当てでの `symbolic_tail_exact`、rename/subst の可換性を証明する。
元 slot は同じ ID で参照し、型代入を compile の引数に取らない。

これは tail 義務の有限表現であり、同じ義務を view に包んで再展開することを saturation の進行とは数えない。
7.2 では、この表現を含む共有 graph の閉性と、全 parameter での比較成立を別途証明する必要がある。

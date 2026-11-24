# Cycle 398: B6 の記号的入力から B4 の元出力等式へ

正本 be3aaeb1d3d27dc31e42a2ee3a5def68db47318e、I-70 inbox b9b52159d2e018bfa65f9f7daacd58308a64c027。[C397 の質問](https://github.com/momota1029/yulang/blob/d195b1cef01ecd96b25d33f35a7c258541daa8f1/notes/questions/dots-cycle-397-mixed-rhs-declared.md) は保留のまま。再質問せず、混在 `.declared` vector・固定 `dictionary_sound`・S13bbba を変更しない。source の読合せ・設計のみ（Lean 未検証）。

## どの型付けも B4 でやり直さない

[§10.1](https://github.com/momota1029/yulang/blob/be3aaeb1d3d27dc31e42a2ee3a5def68db47318e/spec/10-inference-core.md#L21)、[§10.8.1](https://github.com/momota1029/yulang/blob/be3aaeb1d3d27dc31e42a2ee3a5def68db47318e/spec/10-inference-core.md#L275-L283) は、B6 が値型・行・残余制約を出し、role 要求を生成する時点では具体 impl を探さなくてよいことを指定する。B6 入力は**元 Body の lexical source site に索引づけた、型/行と構造を持つ記号的 RHS**。実 where 出力名はまだ記号のまま。B6 lookup に選択済み辞書、解けた where result、fixed output receipt、モデルを渡さない。B6 が元型判断と整合した typed plan を作ることは別の B6 義務であり、今回立証したとは言わない。

明示 Body の B6 key は元実宣言 ordinal と元 Equation の位置。role default の key は元 role・associated 名・default 本体で、選ばれた impl の明示 binder と別。両方の key を同じ数値 index で引かない。正規化後の部分構文の順序、kind/variance と source 型の整合は B6 が供給する。どの候補が選ばれるかはこの情報から逆算しない。

## B4 に残る一つの source 操作

1. 実選択によるすでに独立な source frame と元 output リストの `Fin` 位置から、実 request の source name / fixed target を読む。[元 lookup_exact](https://github.com/momota1029/yulang/blob/d195b1cef01ecd96b25d33f35a7c258541daa8f1/lean/Yulang/GeneralDictionaryAssociatedProvenance.lean#L72) によって、実原 Body の `Supplies` を明示／default の優先どおり得る。body や target を後からモデル値で選ばない。
2. exact Body の元 B6 key を読み、**その記号的 RHS** にだけ、その同じ frame の元 capture を代入する。[C393 slots](https://github.com/momota1029/yulang/blob/d195b1cef01ecd96b25d33f35a7c258541daa8f1/lean/Yulang/GeneralDeclarativeI65OriginalBodyEvent393.lean) の explicit は lexical capture lookup、default は元 demand positional center。where 出力専用名は元 where の actual output point の参照として読む。その実点を新たに C366 の signed atom membership で型付けし直さない。
3. 代入は純粋な構文再帰。value/row のタグ・point/nonpoint の段取りは B6 側の入力から読む。value と row の center/low/high を混ぜず、record の label/payload/tail、variant、join 左右、declared nested argument の元順を保存する。代入後の `SourceRhsCode394.source` は元 Body の normalized Pattern に戻る。**output ledger は元 `Fin` ごと**なので、同じ associated name の別 target を名前でまとめたり、missing metadata の行を filter して ordinal を変えない。
4. [§6.3](https://github.com/momota1029/yulang/blob/be3aaeb1d3d27dc31e42a2ee3a5def68db47318e/spec/06-roles.md#L88-L95) の要求は元 fixed target = この同じ RHS。論理等式 `CompoundEquation394` を使う読取りの draft で、元 request occurrence / ordinal / Body / target の保持を出力型にする。旧 C386 の exact mixed `.declared` データへの変換は一切選ばない。この論理中間結果は `ExactSourceRhs` 全体の代用品ではない。

## 残り

B6 input の実装・coverage・型付け健全性、全 Classifies がこの independent source frame を与えること、元混在 `.declared` の既存 write との一致が残る。draft は宣言型を含む C394 の表現範囲で、任意の primitive 混在まで通ると主張しない。lookup/plan/slot が未対応ならこの prototype で証拠が出ないだけで、言語の受理拒否を変えない。S13bbbb の保持/モデル、検査器、停止性、追加 fixture は対象外。

## draft の局所不変条件（厳格検証は復旧待ち）

symbolic plan の根は元 `normalize(bodyPattern)` で索引づける。declared application の計画には [C357 Use](https://github.com/momota1029/yulang/blob/d195b1cef01ecd96b25d33f35a7c258541daa8f1/lean/Yulang/GeneralDeclarativeWitnessConstructorModes357.lean) の実宣言と current table の同じ引数順、actual kind、effective variance を入れる。B4 は数値や slot から型種を推定しない。継承 invariant なら元計画が interval で、実 where の slot が同じ値の point でも **interval を point へ取り替えず**、その子の exact fixed target を lower/upper に置く。default は lexical capture ではなく元 role positional center に戻る。独立の C395 where binder と C393 default slots から、これらの局所等式を点検する draft を保存した。

proof draft の回帰条件: [C394 CompoundSourceRhs](https://github.com/momota1029/yulang/blob/d195b1cef01ecd96b25d33f35a7c258541daa8f1/lean/Yulang/GeneralDeclarativeI65CompoundSourceRhs394.lean) のすでに導出済みの表現部分に限り、同じ actual slots で元コードと**値が同じ** symbolic plan があることを、その元導出の構造帰納で示す。ここで使う旧型付き証拠は旧経路への保守性の検証だけで、B4 が実際に plan を作る方法ではない。B6 側の coverage/well-typedness/actual declaration 型注釈の妥当性は別義務。primitive 混在の型付き入力や C386 mixed vector をここから新設していない。

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

## 保留した wire と独立に進められる元 ordinary 経路

[C393 BodyWrite.ordinary](https://github.com/momota1029/yulang/blob/d195b1cef01ecd96b25d33f35a7c258541daa8f1/lean/Yulang/GeneralDeclarativeI65OriginalBodyEvent393.lean) は、元 normalized Body の既存 ordinary `translate = some nf` と、使われる slot が実際に読めることを要求する。B6 に前者（source と照合した記号的 nf）だけを出してもらえば、B4 は元 lookup で Body を選び、実 lexical/default slot を確認し、`logical (bodyCapture …) .actual nf` を元 target に置く。式の型の推論をしない。元 ordinary writer と同じ `translate` 関数の同一入力なので、両者の nf は Option.some の injectivity で同じ。そのとき source Body、ordinal、target および普通等式の literal 内容が同じ。declared-nominal/structural の未対応混在を ordinary とみなす案ではない。

補助条件は「成功した explicit/positional slot read が旧 C320 bodyCapture と一致」。explicit は生成済み capture table の元名前を読むので、他の binder の数値で代用しない。default は original argument の center があることを確認して初めて使うため、旧 total `positional` の unobserved fallback に行かない。これによって B6 入力での型付け責務移動と既存普通の raw write の保持とを、保留中の混在 .declared から独立に検証する draft を用意した。新規 Lean の確認はまだ行っていない。

## lookup 境界に対する二つの判別条件

- **明示優先の不変性。** [C320/C393 の supplier](https://github.com/momota1029/yulang/blob/d195b1cef01ecd96b25d33f35a7c258541daa8f1/lean/Yulang/GeneralDictionaryAssociatedProvenance.lean#L103-L129) は、型付き計画の有無を見る前に確定する。同じ source frame と output position では、別の B6 atlas を渡しても、成功結果の元 Body、output occurrence・ordinal・target は変わらない。実 explicit があるのにその B6 情報が未提供なら、prototype に証拠は出ないが、role default に戻って別 Body を選ばない。これも selector の新しい拒否ではない。
- **前方だけの名前付き出力。** 元 demand の出力リストに同名の異なる target がある場合も各位置を保持する。型付き論理式を `List.ofFn` に載せ、未対応の位置は `none` のまま保持する。後の要素の ordinal が前へ詰まらない。role 規則が許す需要の統合と、出力 ledger を順序つきで写すことを混ぜない。S13bbba の exact C386 形式を置換するものではない。

確認用 draft は (a) 既存 ordinary literal、(b) C394 表現内の typed symbolic substitution と保持される元位置、(c) C394 の旧導出から同じコードへの保守的 replay およびこの二条件、の順で独立チェックできるよう保存した。今回 source 内容だけを照合し、新規 Lean の strict 実行は未実施。

## 全域性のうち、実 source frame で B4 が示せる部分

B6 の入力を将来 State/Request に入れるなら、元 source の有効な lexical site にだけ全域な型付き表として置く方向。B4 の `Supplies.explicit` は元宣言と実 Body の所属を、`Supplies.default` は元 role の `assoc` を提供するので、どの B6 site を読むかはその証拠から直接確定する。型付け表の coverage/soundness は B6 の義務で、B4 の選択結果や具体 receipt を表に持たせない。今回は state や既存 theorem を変更していない。

slot 読取りの全域性は別で、明示 RHS では [Declaration.Scoped](https://github.com/momota1029/yulang/blob/d195b1cef01ecd96b25d33f35a7c258541daa8f1/lean/Yulang/GeneralDeclarations.lean) により normalized Body の各変数は inputNames または outputNames。C393 の capture table はその両リストを実 frame の names で写すので、使われる名前の lookup が存在する。default は [RoleDecl.defaultsScoped](https://github.com/momota1029/yulang/blob/d195b1cef01ecd96b25d33f35a7c258541daa8f1/lean/Yulang/RolesAssoc.lean) と実選択の role arity が揃えば、同じ元 demand argument position の lookup が存在する。したがって、slot の存在を B6 の「型種」の証拠と混同しなくてよい。B6 が提供した plan の実使用変数にこの性質を構造帰納で運ぶのが B4 側の構成。これはすでに与えられた実 source frame に限る読み取りの議論であり、すべての Classifies がその frame を構成することや mixed literal writer を示すものではない。

# Cycle 396: 同じ where 選択の元 body が型種を供給する箇所

正本 e13dfcc5f08874310c14d4179f38914ffae07f99、I-69 inbox 5e202637769e290325b60e4425812e784428f3d7。[固定文と S13bbba](https://github.com/momota1029/yulang/blob/528bf2c2b570911043633cd2ebf3ba179d9ca7f2/notes/design/dots-cycle-380-i65-step1-skeleton.md#L325) は変えず、S13 は分けない。S13bbbb の保持やモデル評価には進まない。現時点でクラウド未接続。以下は source の読合せと証明設計で、Lean の検証済み追加ではない。

## 足りない事実 (a)

**元 where で名前を作るその子が、同じ State で選択されたその子の局所 source rule から、その元 output ordinal に型付き body を出すこと。** 既存の固定住所や、辞書を一つ選べるという事実だけでは、型付き body の出所まで戻らない。独立の宣言側局所 rule が供給するべきで、同じ request/辞書・同じ数値の先から拾わない。

[仕様6.3](https://github.com/momota1029/yulang/blob/e13dfcc5f08874310c14d4179f38914ffae07f99/spec/06-roles.md#L136) は関連型の糖衣を where の子＋元の名前付き等式へ展開し、その束縛は出力だけで使う。[C395](https://github.com/momota1029/yulang/blob/528bf2c2b570911043633cd2ebf3ba179d9ca7f2/lean/Yulang/GeneralDeclarativeI65SelectedWhereBindings395.lean#L102) は元 clause/output/index と同じ有限 where forest の child request/dictionary を揃える。ただし取出しで子導出を Nonempty に入れるため、次の処理が実際の子導出の body に依存する場合には、同じ子を再選択せず元 forest からデータつきの部分木を読む。さらに [C386](https://github.com/momota1029/yulang/blob/528bf2c2b570911043633cd2ebf3ba179d9ca7f2/lean/Yulang/GeneralDeclarativeI65LiteralReplay386.lean#L72) の localRule/eventAt は抽象で、既存 event の receiptAt は authored Supplies と fixed target を読むだけ。actual source kind や選択の独立性をその event から逆算しない。

## 型種と端点の切分け

- [C366](https://github.com/momota1029/yulang/blob/528bf2c2b570911043633cd2ebf3ba179d9ca7f2/lean/Yulang/GeneralDeclarativeI65Capture366.lean#L13) の ValueBind/RowBind は、元二端点について四つの**実 ordinary atom の所属**を要求する。where の lexical point が known、あるいは Bound.refl が導けることだけでは、この所属を作れない。C320 State は normal の atom 列と logical equations 列を別に持つ。選択した関連型が exact target に等式を出すことは、普通の atom 列に reflexive な四所属があることを意味しない。同じ数値に value/row の双方を付すのでなく、子が出した実 body と declared kind に結びつける。
- 位置づけ: 子の actual typed *value RHS* が、元出力と同じ request/dictionary/subtree・同じ output ordinal で作られてはじめて、where 名に対する value の独立 source 証拠になる。C395 の prepared value input は各端点を明示の生成 atom で裏づけた別経路。旧 C392 ticket を直接使う経路では同じ ambient State に atom が実際にあることが要る。この二経路を代用しない。
- default は別の原位置。[C291 の RoleRow](https://github.com/momota1029/yulang/blob/528bf2c2b570911043633cd2ebf3ba179d9ca7f2/lean/Yulang/GeneralSourceMetadataRoles291.lean#L11) は実 default body の変数上限を role arity で保証する。[C367](https://github.com/momota1029/yulang/blob/528bf2c2b570911043633cd2ebf3ba179d9ca7f2/lean/Yulang/GeneralDeclarativeI65Heads367.lean) の ordered head の All₂ と joined head の実 demand/宣言 head 長から、実選択における demand arity を元 role arity と一致させられる。元 default の正規化構文に出る変数は、この bound と実 arity によって元引数の正しい位置を読む。明示 body の capture と同じ数値に見えても lookup 先は違う。[C320 の default positional center](https://github.com/momota1029/yulang/blob/528bf2c2b570911043633cd2ebf3ba179d9ca7f2/lean/Yulang/GeneralDeclarativeOutputs320.lean) の定めどおり原 positional center を点として使い、種別は occurrence/宣言型から別に読む。未検証の default を拒否しない。

## 次の実装の確認条件

同じ finite I-67 導出の子をデータで読む（proof irrelevance・物理 release・producer journal で補わない）。元の selected local rule から生成した actual prepared frame/where 形と、actual child の original body を同じ導出に固定。S13bbba の局所 proof をモデルなしに行い、後に必要な retained semantics は S13bbbb に残す。未対応を採用済みの言語規則に置き換えない。C386 の .declared は full Pattern を保存するが、任意 mixed compound の actual ordered typed writer は未証明。別形式・flatten を定めない。意味仕様への質問はまだ見つかっていない。

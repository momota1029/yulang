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

## 元子の Body を receipt からではなく実宣言から決める

1. C395 の準備済み Frame の where 順は C322 children に一致する。その実 child request について、[emitted_declared](https://github.com/momota1029/yulang/blob/528bf2c2b570911043633cd2ebf3ba179d9ca7f2/lean/Yulang/GeneralDeclarativeWitnessDeclaredState357.lean) が親の元 Clause.Signature だけから output 名が role に宣言済みと保証する。子の output batch は要らない。
2. [C386 GeneralForest](https://github.com/momota1029/yulang/blob/528bf2c2b570911043633cd2ebf3ba179d9ca7f2/lean/Yulang/GeneralDeclarativeI65LiteralReplay386.lean#L87) の元 ordinal をたどって実子 subtree と its literal root event を取り出す。その子の declaration.role と元 child demand.role の一致は [visible_exact](https://github.com/momota1029/yulang/blob/528bf2c2b570911043633cd2ebf3ba179d9ca7f2/lean/Yulang/GeneralDeclarativeI65State365.lean#L64) による。同じ request や辞書を持つ別の candidate/frame を拾わない。
3. [declared_covered と lookup_exact](https://github.com/momota1029/yulang/blob/528bf2c2b570911043633cd2ebf3ba179d9ca7f2/lean/Yulang/GeneralDictionaryAssociatedProvenance.lean#L72) を元 child output name に適用すると、実子の元宣言から **explicit があればそれ、なければ role default** の Body を同じ子出現で一意に得る。子の receiptAt、すでに書いた RHS、モデル、保持の事実は引数に不要。
4. この由来つき Body の **型付き評価**は、なおその子の実選択と body 環境から構成する必要がある。slot/role の同じ数値や source lookup 成功だけでは型種を与えない。ここまではチェック済み既存補題をつなぐ設計であり、新しい合成の Lean 検証はしていない。

狭い負の確認（言語上の反例ではない）: generic C386 の receiptAt の条件下では、occurrence・ordinal・request・Body を全部据え置き、written だけを固定 target の別の .declared payload へ変えても、構造条件はいずれも保存される。その interface の eventAt を任意に許す場合は、同じ候補選択の guard を付けられる。これは **抽象 interface単独**では exact RHS を保証しないことを示す。実言語の selected rule や GeneralLocalMeaning に誤りがあるとの主張ではない。局所 source producer を具体化する理由であり、別の literal 形式や却下条件を追加する理由ではない。

## 実 where writer を読んで分かった境目

元 Generated OutputBinder の equation RHS は同じ binder の .var、binder 名は元 declaration.outputNames にある。この実ケースでは [C327 entry / alreadyNamed](https://github.com/momota1029/yulang/blob/528bf2c2b570911043633cd2ebf3ba179d9ca7f2/lean/Yulang/GeneralDeclarativeWhereOutputBatch327.lean#L20) が変数を読んだ後、その equation に対して **some []** を返す。つまり親が auto-generated binder に x = x を後から書くのではなく、同じ型名は実子の output 紐づけによる。この挙動はソース上で既に明示されており、順序や拒否を新しく決める余地ではない。

さらに [C350 execute](https://github.com/momota1029/yulang/blob/528bf2c2b570911043633cd2ebf3ba179d9ca7f2/lean/Yulang/GeneralDeclarativeWitnessCompiler350.lean) の成功経路では、準備後に whereBatch と fixedBatch の結果を [appendFacts](https://github.com/momota1029/yulang/blob/528bf2c2b570911043633cd2ebf3ba179d9ca7f2/lean/Yulang/GeneralDeclarativeEntailment320.lean) で連結する。appendFacts は State.equations の末尾に足すだけで State.normal を変えない。したがって、**普通の where/固定出力の書き込みに成功したという事実だけから、C366 が要求する新しい signed value/row atom の所属を作れない**。準備中または現状態に独立の atom が既にある可能性は排除しない。次の source producer は実子の型付き body と元 output から authority を受け取り、独立に存在する normalized constraints と混同しない。新しい Lean 合成テストは未実施。

## 実 prepared port の atom を同じ State で読む入口

すでに独立に生成された普通の本体については、[WrittenBody.run と retained](https://github.com/momota1029/yulang/blob/528bf2c2b570911043633cd2ebf3ba179d9ca7f2/lean/Yulang/GeneralDeclarativeWitnessDeclaredState357.lean) と [ran_body_has_literal_ports](https://github.com/momota1029/yulang/blob/528bf2c2b570911043633cd2ebf3ba179d9ca7f2/lean/Yulang/GeneralDeclarativeI65Body367.lean) から実 preparation を再取得できる。[C330 Receipt.constraints](https://github.com/momota1029/yulang/blob/528bf2c2b570911043633cd2ebf3ba179d9ca7f2/lean/Yulang/GeneralDeclarativeCurrentReceipt330.lean) は式の意味上の同値ではなく、normal atom の**実所属の包含**である。上の normal 不変性により、準備の value atom を同じ current State に移せる経路がある。これは C395 PreparedSourceFrame の Extends 全体を得られるという主張ではない。C330 の intervals は Bound、logical rows は Derives であり、元 raw 行や interval の所属は要求しない。C395 の局所型種読み取りに必要なのは prepared normal atom の包含と独立した kind の権限であり、他の強い包含を仮定し直さずに済む。

限界: この入口は実 WrittenBody の独立した既成 ordinary compilation を消費する。全 Classifies でその packet を作ったことにも、子の output-only binder や row の種別を発行したことにもならない。S13bbbb のモデル/保持の定理はここでは実行しない。検証復旧後は C395 の固定三モジュールを closure とし、元 default 位置、実 child subtree→Body、direct binder の空行、prepared normal の保持を scope ごとに Lean 4.35.0 の trust0・warningAsError と独立 audit で確認する。未検証 draft は branch に置いていない。

## 選択された typed head の経路を残す時点

[C367 DeepHead と shallow_head_projection](https://github.com/momota1029/yulang/blob/528bf2c2b570911043633cd2ebf3ba179d9ca7f2/lean/Yulang/GeneralDeclarativeI65Heads367.lean#L15) で DeepHead は Prop。SourceHead.ordered にある All₂ の証明は Lean の proof irrelevance により、同じ capture と引数列では、内部証明を取り替えても同じ値になる。たとえ二つの妥当な ModeWindow/DeepRead が同じ head の命題を満たしても、その ordered 値から「最初に実際に記録した経路」を同定することはできない。さらに [authored_node](https://github.com/momota1029/yulang/blob/528bf2c2b570911043633cd2ebf3ba179d9ca7f2/lean/Yulang/GeneralDeclarativeI65Body367.lean#L67) は shallow_head_projection を呼び、[SourceNode.ObservedNode](https://github.com/momota1029/yulang/blob/528bf2c2b570911043633cd2ebf3ba179d9ca7f2/lean/Yulang/GeneralDeclarativeI65SourceNode365.lean#L41) には ReadsHead だけを置く。C395 は実葉に対応する *妥当な* typed source read を得るが、全 Classifies の exact 経路を、消去後の証明から取り戻す定理ではない。

必要な修正箇所は source 選択がこの read を作った場所。ModeWindow/DeepRead のデータ付き経路をその時点で保つか、本当に同じ original lower/upper endpoint が source rule で一意であることを**消去前**に確かめる。固定 endpoint pair と mode table の下の leaf 列の一意性と、どの endpoint pair を actual source が選んだかの一意性は別（前者の再帰証明を draft 済み、Lean は未検証）。実言語で二つの合法経路が実在する、または受理結果が異なると主張しない。

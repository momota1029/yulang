# dot cycle 320: 宣言的な辞書の再帰と通常制約からの局所証明

実測開始 2026-11-21 11:27:10 UTC（定時枠 11:30）。開始時に
`integration/m1-final` `03c7f36c5dbf3d8d2b88911621b56676611500f5`、
standing orders `7ae4d68d2ac7df80d1eadbd061dadd2296faf4c4`、
inbox `f259434f2d1b233c3dde6e6e2b9d804df9349b5a`、C319 完了 pin
`c160c98e7f989e6cb17d5d2b3ea9db285df7d073` を照合。
後半の integration `ab9d9fcece6431fa5ad1dbcecc6397558cd86d56` でも指示ファイル
は同一。スロット・版・帳簿の改修はしていない。
設計メモ: [I-56: 通常等式・捕捉・局所選定の境界](../design/2026-11-21-cycle320-declarative-centers.md)。

## 宣言的な (4) で閉じたこと

- **任意の通常状態と全モデルに対する局所読取り。**
  `GeneralDeclarativeHead320.read_sound`, `source_head` は普通の構成子等式と
  共有中心への相互の型不等式から、全モデルで実引数が同じ捕捉による正規化済み
  source head と同値であることを示す。型・行制約への拡張は不変 nominal を表す
  型式の普通の等式だけ。空の拡張では C319 と全く同じモデル。
  `Point320.actual_of_endpoints` はモードで値が変わらない読みから中心の式を導く。
  不変 nominal では両端から実値が決まり、中心の等式や三つの論理名の一致は不要。
- **実際の宣言の正規化・where・関連型出力。**
  `ReadScope320.tracked_from_declared_inputs`, `Normalized320.normalized_where_clause`
  は宣言の正規化後のスコープから必要な区間を導き、順序と重複を維持する。
  `Assembly320.prepared_sound` は実 head、子の役割・上下端・実値、名前つき
  子出力、親の明示定義もしくは role default を一つの捕捉で同時に意味づける。
  `DefaultScope320.default_never_falls_back` はチェック済み default が実在の
  位置だけを読むこと、`NamedAgreement320.same_named` は一節点の同名出力の
  複数の target がすべて同値であることを示す。
- **候補・子の論理名から普通の等式の有限コンパイル。**
  `NodeFacts320.nodeFacts` は実 source 宣言を既存 compiler で読み、列を
  対応づけて head、where の三端、子の名前つき出力、親の明示/default 出力の
  等式を生成する。生成した等式が状態に文字どおり入っている必要はない。
  `Entailment320.entailed_batch_sound` は型・行・区間と普通の等式からそれらが
  全モデルで帰結すれば十分であり、帰結のみを追加してもモデルを変えないことを証明。
  候補選定、実行や据え付けをこの compiler に入れていない。
- **実中心の共有と合流。**
  `RepeatedHead320.repeated_head`, `RepeatedNode320.repeated_source_node` は
  変数のみからなる任意個の引数で、同じ変数を繰り返す場合も最初の出現から中心を
  作り、普通の中心同値・下端の join・上端の meet から捕捉を構成する。
  `CaptureClosure320.batch_from_origins` の捕捉不等式の追加はモデル集合を保つ。
  `MergeAgreement320.merge_agrees` では同じ出現集合からの合流の値は
  三モードで同値。resolver 全体の順序独立ではない。
  `CanonicalRead320.associated_agrees` は正準有限 head が同じなら、その可視な
  head 変数だけを読む正規化済み関連型は捕捉名の付け方によらないことを示す。
- **順序つき辞書の再帰の橋。**
  `Evidence320.classify_sound`, `CompilerTree320.compile_classify` は任意の
  通常状態・任意のそのモデル・チェック済み registry について、独立な
  `Classify = Resolves + Summarizes` が選択した完全な辞書から Evidence を作る。
  前提は、実際の局所 `selected` 辺が `ChosenRecipe` または `BatchRecipe`
  を供給する `Compiles`。診断木の各子も選ばれたことを同じ証明から取り、
  各節点を同一のモデルで検証する。`NamedTree320.linked_output` は **i 番目の
  where・j 番目の出力**を実際に選ばれた子の明示/default の右辺に結び、
  同じ名前の別の要求や重複位置を取り違えない。有限の与えられた証明木の
  帰納であって、solver の停止性は使わず、主張もしない。

## 実例と境界

- チェック済み source `wrap` と `item` を返す子で、
  `ExampleFacts320.compiled_evidence` を検証。親が子の名前つき出力を実際に
  要求して自分の nominal 出力に使う。親の実中心の等式は状態に書かれておらず、
  両端・区間から帰結する。同じ非空のモデル集合で二節点の辞書を構成する。
  これは具体 branch の局所関係であり、承認済みの一般分類規則の実装完了ではない。
- `ExampleUnsettled320.parent_local`, `child_not_evidence`: 子の `item` 等式だけ
  を外すと、親の普通の等式は依然すべて帰結するが、実際に子の辞書を否定するモデル
  がある。親の局所選定と全体完成は別。
- `Repeat320.realization_not_universal`: 二つの引数の上下端が同じ `[int, top]`
  で、共有できるモデルもあるのに、実中心が `int` と `top` に分かれる状態モデルが
  ある。「端点の両立」や「共有できる割当が存在する」だけでは、すべてのモデルの
  同じ実捕捉は出ない。承認済みの判定がこの入力を選ぶ、あるいは新たに拒否すべき、
  とは主張していない。

## 残る橋

**宣言的な (4): 残り 1 本。** 実際の独立な source `Local` を承認済みの
下界既知・K2・保留・候補条件に従って与え、その `selected` ならば
`Compiles` を満たすこと。具体的には一般の観測から共有された実捕捉と順序つきの
子需要の論理名を得て、生成された通常等式がすべて帰結すること。
順序つき辞書の帰納と名前つき出力の接続は、この前提だけで一般に閉じた。
新しい選定・保留・拒否の規則は追加していない。特に、未完了の impl 出力を
観測の根拠にしてよいことや、中心情報を失った実装に新しい保留を許すことは
別途仮定していない。

**(2): 残り 2 本。** (i) solver 到達状態の通常制約・区間への射影と詳化。
(ii) 停止して返した診断木が射影先の宣言的分類と一致すること。本周は両方を保留。
次周は `Compiles` の生成側を優先する。意味を変える判断はしていないため
質問ノートなし。使用量の枠は不明。

## 検証・公開

Lean 4.35.0。34 新規モジュールの focused `lake build … --wfail` は exit 0
（依存込み 1000 jobs）。全34ソースを個別に `--trust=0 -DwarningAsError=true`、
I-51 standalone audit 11 本も個別再検査し全 exit 0。I-52 diff-only は exit 0。
標準公理のみの scoped gate は 59,990 宣言で PASS。さらに全 685 新規定数の
型・値の成分を辿った 4,851 依存では、指定した旧状態・帳簿・solver `Step`・
構造上の slot・実行版 `resolve` が証明依存に入っていないことを照合した。
I-53 の34件を同じ公開に含めた。全ログと検証範囲は [検証](../verification/cycle320/verification.md)。
全体ビルド、Rust、Sat は実行していない。

心拍・途中公開の照合済み pin: 10分 `fa2ea783f021c628cceba49ee26fdf91a3c78457`、
20分 `d889640e64e2dc5489588cff9931daea901b7927`、
30分 `c58c8571d78fc70175a0c38b2bb657e881f03f85`、
40分 `f10c34dc989aeac46328af2bb2b1adf29abe3724`、
50分 `06315a25c352680d89af15417b887e88de0cf178`。
12:17 UTC に検証済みの報告を作成、以降は最終公開と照合。
成果・検証・報告は前周から 78 ファイル、別に心拍1パス。
公開は `work/dots-main` のみ。

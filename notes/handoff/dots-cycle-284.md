# dots-main cycle 284: 履歴索引を捨てられる条件と、実反例での限界

- 定刻 2026-11-19T23:30:00Z、実開始 2026-11-19T23:33:14Z、記録終了 2026-11-20T00:23:18Z（50.07 分）。全 75 パスの変更。公開先 private `work/dots-main` のみ（非強制・expected head）。使用量の残枠は不明。
- sole writer を確認し、283 完了 `b9bb2a19` から開始。開始時 `e62f33b58`、後半 `0f9cf719` で統合ブランチの standing orders と inbox を再取得し、ACTIVE・I-51〜53・凍結に変更なし。後半の統合コードは作業 tree にすでに含まれ、巻き戻さず照合した。
- 読み戻した途中 pin: 開始 `ad911758`、早期 `d37af59d`、10分 `e2050d2d`、20分 `e5f4df3d`、30分 `a55947f6`、40分 `d95bc6ec`、最終検証済み成果 `07a5169a`。各公開は編集中のファイルではなく固定した commit から送信。

## 証明したこと

1. **将来も読む索引だけを保持する条件（健全・完全）。** 型付き右辺の依存先を全て含む watch を指定し、過去に定義済みの名前を新たに読むなら直前の watch にも含まれていたことを要求する。実 install は保持表と新 packet だけで差分更新でき、監視内のリテラル型の値と全 row が完全一致する（`FutureWatch284.trim_exact`、`WatchStep284.advance`、`WatchTrace284.trace_correct`）。旧候補の Common や次状態の到達性を仮定せず、実 journal の読みが範囲内なら候補の Common、範囲を覆う有限の証明集合について全 Models と再帰 Evidence が同値になる。各時点だけの依存閉包では不十分。閉包を満たす二つの watch でも、既に捨てた定義を二期目だけ読むと top が bottom に変わる閉じた反例を追加した。
2. **検査器と、適用できる実経路。** 実行可能な検査器は過去の全定義キーの上界を一つ持ち、次の watch は直前の watch または上界より真に大きなキーに限る。保持分と新 packet だけで型依存閉包を検査し、保持行数を watch の長さ以下にする。過去に存在しないが上界以下のキーも保守的に拒む。反復できる合成例は保持1行、raw は n+1 行。これは保持行数の上界で、上界整数のビット数や全実行状態の一様有限性は主張しない。source 側の対応と範囲を明記した往復の実経路定理を証明し、setup、novelty、Generated と install 以外のガードを残した。実 Display の全経路で完全な二つの plan と非葉の証拠、optional の二度目の実 install を確認した。検査器の拒否が source での拒否を意味しない例も追加した。
3. **guard と provenance を捨てていない範囲。** 読み元の型付き被覆があれば Eq と SameInputs の結果が保存される。206 の役割既定出力から実際に Eq が返ることを検証。指定範囲を覆う witness と選択した子の閉包の下で `EvidenceAt` を双方向に移せる。Display の実 plan で検証したが、任意の `EvidenceNode` やあらゆる `Local` を有限化したわけではない。
4. **実 239/240 の raw 問い合わせには効かない。** n 段の 2n 個の索引すべてが、保持する実普通等式に型付きで現れる。どの1個でもリテラル表から消すと、その座標だけを bottom にした割当で全 decode の Models は合格し、trim は不合格になる。任意の raw 割当で full Models と実 payload `.node 0 []` の同時成立を保存するだけでも、全履歴が要る。任意 raw ID の Known または任意 raw 割当の Models は、それぞれ単独でも有限状態への厳密な圧縮が不可能。特に、実際の異なる段が下記の同じ窓状態を持っても raw Models は異なる。
5. **観測を明示すれば、実 239/240 に最小6状態の窓がある。** previousKnown / latestKnown / canInstall に関して最小の窓を構成し、raw ラウンド番号は保持しない。両反例の指定した実微小遷移は往復対応し、初期の全型座標・全 row と previous/latest の順序付き相対ポートを合わせた観測について、同じ witness を将来の任意の段まで使って全 Models と葉 payload を同時に再現できる。239 の下上根は 2・2、240 では 2・4。不在と未知を区別し、ポート不変の結合問い合わせも保存する。これは相対ポートを使う特定の実経路の結果で、旧 raw ID を引けることや release の他の全遷移を含むことは意味しない。窓自体も巡回し Acc でないことを形式化した。汎用停止性は未解決。

## 検証

- Lean 4.35.0。新規41モジュールを warning-as-error、trust=0 で個別再構築。Yulang のみを import した独立監査6本・重複なし176宣言、標準公理のみ。barrel 登録、禁止語・凍結、旧 pin と新旧の統合先を基準とする static diff、型付き使用9件、`#eval` 13件が通過。40分点のフィールド名が Lean では合法でも静的検査の予約語に当たったため改名し、全対象を再検証した。
- 旧回帰の独立監査9本（206、218、230、233、239 First、240 Independent、282、283の Archive と Locality）も全て exit 0。239 Second の再監査や全体 `lake build`、CI は行っていない。[再実行ログとコマンド](../verification/cycle284/)。
- Yulang2 は既存の `work/dots-audit` `55574b60` の X1/X2/X3/X5 と C3-ROLE-01/02 の記録を比較。今回の変更は既存の Lean 意味判断への保持条件の追加で、言語仕様・受理判定・凍結済み実装は変更しない。Yulang2 新規実機検査なし。持ち主に新たな仕様判断を求める質問なし。

## 次の候補

raw ID 照会の保存を前提にせず、単一変数の正規形を越える source について将来の読みを被覆する型付き根拠を導く。constructor の深さと節依存、明示出力・役割既定の両方、子の由来、効果 row を入れて非葉を検証する。watermark は十分条件であり、型付き名前空間や証明付き cut があれば保守的な拒否を減らせる。今回の raw 下界を回避するには、公開する Known / Local の観測範囲を別途仕様として固定する必要がある。

設計記録: [将来読みの閉包](../design/2026-11-19-cycle284-future-read-closure.md)、[履歴なし検査器](../design/2026-11-19-cycle284-archive-free-validation.md)、[認定付き実経路](../design/2026-11-20-cycle284-certified-watch-driver.md)、[相対窓](../design/2026-11-19-cycle284-finite-window.md)、[ポート問い合わせ](../design/2026-11-19-cycle284-window-predicates.md)。

次回の最初の比較対象として、非点の反例だけでなく `GeneralRebaseOutputDepthSuccessor271` の `F(Int)` → `F(F(F(Int)))` の実 install を使う。ここには深さを加算すべき非変数の明示出力と、既に確認済みの実 weak step・投影後の停止がある。順に (i) `GeneralNominalJournalSupport249.support` と証明 plan の読みから型読みの出所を分ける、(ii) slot への正準化で、選んだ観測に対してだけ現在・将来の読みが閉じることを示す、(iii) 同じ証明を効果行と非葉の子へ組み合わせる。raw `journalReads` 全体を小さな watch に入れようとすると 239/240 の下界に直に反するため、(ii) で意味を同定する対象を先に定義し、旧 raw relation に対する停止性へ読み替えない。

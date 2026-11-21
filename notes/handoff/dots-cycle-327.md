# Yulang C327: 反復捕捉・実在の where 一括生成・宣言的診断木

2026-11-21 18:30 UTC 枠。実開始 18:33:47 UTC、ローカルの検証済み基準は C326 の GitHub 固定版 `00b591e4342c49122bd7d30cf83afcd4bbe17196`。監督役ブランチ `5cc1efc85d4f9c34b01d113398de09ba6459f31a` の standing orders / inbox を再読し、I-56・I-57 を適用した。公開は private `work/dots-main` のみ。I-57 の二つの凍結ファイルは本文を読み書きせず、blob ID だけ照合した。使用量の枠は不明。

## 証明済み

1. **同じ型変数を二度使う非点の共変ペア。** 任意の通常状態について、上下限と実中心それぞれの独立な普通の導出があり、実中心を同じ式の二箇所として読む導出があるなら、`RepeatedProjection327.same_from_actual_source / merge_from_source` は、端点の一致ではなく実際の成分の一致を導き、下限を join・上限を meet で合流する。古い論理名と指定された出力先を保ったモデル拡張を与える。`RepeatedHead327.compiled_head` は合流後の実中心で二箇所とも読む通常の head バッチを証明する。この式導出を、端点照合だけから勝手に仮定しない。実例 `RepeatResolve327.every_model` は、center 1 の直接行がないのに host 11 から実中心を読み、合流捕捉 `(18,13,19)`、複合 where 子 `(20,21,22)` を生成し、選定された親子の辞書を**全モデル**で証明する。`RepeatModels327.genuine_two_models` の int / bool の両具体モデルで、実中心はどちらの端点とも同値でない。子の支持は実際の通常ソース行で、未完の関連出力に頼らない。
2. **可視候補と診断木。** 任意の checked registry / 状態について、`Frontier327.coverage` は、既存の正規化済み局所判断の存在を「支持なしと K2 の未決の重なりがない」「ready・非K2・非保留の唯一生存候補なら、実際の子リストを生成できる」の二条件に正確に分離した。`CandidateScan327` は同じ role の実際の登録宣言のみを調べ、候補通過と保留を独立に扱う。`FrontierView327.exact` は、独立な観測・生成がそれぞれ正確な場合の有限表の双方向照合。`RelationalCheck327.at_exact / FiniteTrees327.classifies_iff` は**与えられた有限の診断木**と順序付き子需要リストを照合。仮定は観測、K2、正・保留判定と、唯一候補での提案子リストに対する独立な検査の正確さ。四診断を保ち、未知の重なりには verdict を付けない。探索や停止性の定理ではない。
3. **論理名の表現と意味を分けた。** `AlternateNames327.no_literal_producer` では同一の checked な正規状態で、許された現行の Frame 関係が `(20,21,22)` と `(21,21,21)` の二つを実際に選べる。違うのはリテラルの論理名だけで、型・要求された固定 target・辞書は同じ。この関係を文字通り列挙する単一の Option 子生成関数はない。`PlacementEquiv327.complete_ordered` は任意の同じ捕捉・target 関数に対し、実在の二つの where frame が、各モデルで順序も出力も保つ同値な子値を与えることを示す。`PlacementEvidence327.retarget` はそれで親の意味と子辞書の証拠を移せる、と証明した。意味の同値を Classify の同値には使っていない。
4. **支持の境界を固定。** `EndpointAlias327.enough / recur_exact` は任意の正規化済み正照合片で、両端点に実際に支持された alias と両側の区間証明があれば、Ready、正候補および通常 K2 の検査を保存する。単なる意味同値では不足する。`AliasStatus327.real_comparison` は同一の通常状態にある二需要の三値・出力が**どのモデルでも**同じなのに、出所を支持された方だけ selected、未完出力だけが alias の根拠の方は pending と確認した。出力 owner 42 が片付いたと与えれば後者も selected。この fixture は owner の完成証明を置き直してはいない。K2 と保留が重なる優先順位は決めていない。
5. **全 where 句と普通の出力バッチを同じ実捕捉から構成。** `ClauseBatch327.read_order / exact_projection` は、全 clause の正規化済み構文が読め、checked な実捕捉に区間があれば、順序どおり複合引数の三名と区間を一括生成し、旧モデルと固定名の射影を両方向に保つ。`ClausePlacement327.checked_inputs` は checked な clause ID に対応する実際の port を選ぶ。`WhereOutputBatch327.exact` は非直接 where 出力に対して、もとの target に正規化 RHS を書く行だけを生成する（直接の出力専用 binder は既存名を使う）。出力適用は本物の通常制約であり、モデルを絞ってよい。`AppliedClause327.compiled_frames / InPlace327.current_sound` は、独立に計算した行が現在の状態に実際に存在し、通常の head 読出しがある場合、任意の現在状態で完全な通常バッチと局所意味を導く。二句の checked 実例は、子の順序 `(20,21,22)→5`, `(23,24,25)→8`、第2句の実更新 `8 = variant 4 (var 13)`、親の固定 `6 = 5` を実際に生成し、そのバッチと局所意味を照合した。この二句実例を別途全面選定された実行とは報告しない。

## 残り

- **(4) 一般辞書健全性: 1本。** 任意の承認済み安定 `Local.selected` が、実際の支持観測から同じ正規の head・共有捕捉を生成し、その独立な現在の write/子リストが実際の選定と一致すること。今回は全 where/output の実コンパイラと非点反復の実例まで進んだが、一般の opaque/別 mode の実中心を端点観測だけから導けない。文字通りの placement 一意性は偽なので、次は独立 source 規則からの実リスト検査、または支持を保存する論理名対応に繋ぐ。意味同値だけの対応は pending/K2 の代用にならない。
- **(2) 成功停止を条件にした部分正当性: 2本。** 各到達済み停止成功から安定宣言フレームへの射影と、その診断木・全要求出力の対応。今回は着手対象外。停止性・solver/帳簿・Rust の証明・言語の受理条件変更なし。質問ノート追加なし。

## 検証

Scoped Lean 4.35.0 Lake warning-as-error、追加ソースの trust zero、独立監査、scoped axiom gate、宣言的依存監査、I-57-safe diff gate、宣言一覧、独立の再実行を実施。focused build 1,175 jobs、追加ソース33件、standalone 監査9件、宣言チェック192件がすべて PASS。Scoped gate は62,724宣言、依存監査は660個の C327 定数と5,510個の型・値の推移的依存を照合し、physical state／Step／journal／既存 resolve 依存なし。固定 proof pin の独立な3監査ソースも取得してバイト照合し、同じ trust zero で再検証した。出力は `notes/verification/cycle327/` を参照。全体 Lake / Rust は実行していない。新規公理、証明の穴、kernel を迂回する決定手段なし。固定 GitHub コミットの許可済み変更パス・凍結 metadata を照合する。

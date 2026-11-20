# dots-main cycle 285: 入れ子出力の型付き読みと、実 install 後の停止

- 定刻 2026-11-20T00:30:00Z、実開始 00:32:29Z。報告固定 2026-11-20T01:22:30Z（50.02 分）、変更 68 パス。private `work/dots-main` だけに非強制・expected head で公開。
- 統合先 `0f9cf7192cc7b4911005db40f4cb507452ef5485` の standing orders と inbox を開始時と再起動復旧時に取得。ACTIVE、I-51〜53 と凍結条件に変更なし。前回完了は `34bfac45d404cb3173746b43a4b730770c72a271`。
- 00:42 頃の実行環境切替で先行作業者が交代。00:42:50Z の遠隔 `d94196b2` と保持済みローカル tree を全 tree hash で照合し、未公開の新規2ファイルを trust=0 で再検証して 00:51 の pin から復旧。周を進めず元の開始時刻を維持。利用枠残量は不明。
- 中間 pin: 開始 `0af577e3`、早期 `e0dba565`、10分 `d94196b2`、19分 `f614d02a`、29分 `7b1201e7`、38分 `3e1267e8`、47分の最終検証済み成果 `01dc3976`。作業中のファイルではなく、固定した local commit の内容を送信。各復旧後 pin は、遠隔 head・commit parent・全 tree hash を照合。

## 達成した結果

### 宣言の RHS、等式、raw journal を別々に読む

- 補助／健全・完全: `GeneralRebaseSourceDemands285.exact_support/exact_many` と `GeneralRebaseCoordinateProfile285.rows_exact/ofEquation_exact/exact_observation`。任意の対応表、評価モード、右辺で、source 由来の順序付き (mode,binder) の読みを、型座標・効果行座標へ別々に展開すると、コンパイルした式の構文的 support と一致する。任意 plan、写像、出力と provenance についてコンパイルが成功した場合、計算された二つの有限リストで同意する全割当は実等式の成立・不成立が同じ。名目型の内側は actual mode、役割既定は位置対応。これは全式に対する構文的 support の厳密計算で、全式の意味的最小性を主張しない。
- 実 fixture／補助: `GeneralRebaseDepthReads285.real_readback`、`GeneralRebaseDepthRaw284Bridge285.raw_not_inputs_only`。実 252/271 の `F(Int)` 入力から `F(F(F(Int)))` 出力を据え付ける経路で、RHS の型読みは [2]、等式は [3,2]。実 raw journal は出力座標 3 を含む。206 の実役割既定出力は RHS [1]、等式 [0,1] で、全 installed Models にその Eq が成立する。変換された矢印では型 [3]・行 [7] となる計算用回帰で、全型が同じでも行だけを変えると実式の値が変わる。これは mapping の回帰であり、252/271 fixture の実入力を矢印に置換したとは主張しない。
- 実 fixture／健全・完全: `GeneralRebaseDepthGroundModels285.final_check/no_row_requirement`、`GeneralRebaseDepthMinimal285.minimal_raw/minimal_canonical`、`GeneralRebaseDepthView285.projected_exact/arbitrary_rows`。全割当で、raw installed Models は 0 と1の Int、2 の F(Int)、3 の三重 F 値との型同値を要求する。任意の有限型読取り表が raw Models を区別する必要十分条件は全 0,1,2,3 を含むこと。正準補完後の同条件は 0,1,2 のみでよい。出力を補完し、任意に選んだ ambient row を保った一つの割当が、指定三座標を持つ raw Models と葉 payload の存在判断を再現する。正準補完を任意の raw 割当と同一視しない。
- 実非葉／健全・完全: `GeneralRebaseDisplayFrame285.parent_exact/child_exact/parent_finite/child_finite`。コンパイル済み Display の実到達状態について、全割当・payload に対し、Models と親・子の Evidence の同時成立は型座標 0,1 の検査と、順序付き payload `.node 1 [.node 3 []]` または `.node 3 []` によって厳密に判定される。任意非葉への全 row 除去ではない。

### 射影の停止と raw の停止を区別し、実 raw の後半を閉じる

- 実反例／停止性の範囲: `GeneralRebaseDepthScalar285.separation`。271 の有限射影で次の遷移がなくても、同じ実 installed raw から 0,1 の既存 source scalar を認識する proper refresh ができる。この時は全 raw Models と有限射影が同じ。深い出力自体は存在するが、`GeneralRebaseDepthRefresh285.no_certified_deep_head_of_model` により、この実モデルに健全な証明付き cache では、深さ2の中間名義型を支える source 下端がないため、出力3を既知の頭として登録できない。現在の表現での障害であり、出力の言語的拒否ではない。
- 実停止／補助: `GeneralRebaseDepthPathRank285.exact/drop/actual_accessible/all_after_install`。この実 installed 状態なら、**すべて**の実 mixed-kernel 継続は、元の Models を保った scalar refresh だけで、高々2回。任意のその到達状態で、計画を型・source 対応の精密化に沿って再構成すると既処理のままなので、再 install を排除できる。point 記述、既に成立している raw 等式、単一 site と center、空の生成辺も保つ。残った refresh は未認識の座標 0,1 の少なくとも一方を認識するため（private名の反例割当や中間名義型の欠落も確認）、未認識数が真に減る。 `GeneralRebaseDepthPathSharp285.two_refreshes` は 0 と1 を順に認識させる実2歩を構成し、同時認識と厳密に同じ raw 末端へ着く。この上界は鋭い。
- 実証拠／健全・完全: `GeneralRebaseDepthPathEvidence285.query` は、installed からの任意の実経路・同じ割当・任意 payload に対して、Models と Evidence の同時成立が経路の両端で同値。 `GeneralRebaseDepthPathSelection285.selected` と `GeneralRebaseDepthPathEvidenceAt285.evidence_at` はその全到達点で実 V8 選択が `.selected 0 []`、対象範囲の EvidenceAt が成り立つことを示す。 `GeneralRebaseDepthPathComplete285.actual_total` は任意のその到達点から、合計2歩以内で安定・選択・EvidenceAt に到達できることを示す。任意の選択がいつも実行可能であるとの仮定は置かない。

## 検証・限界

- Lean 4.35.0、追加30モジュールの個別 build、15独立監査で重複なし143宣言、11型付き適用例と旧回帰9本を確認、`--trust=0 -DwarningAsError=true`。監査は Yulang モジュールを単独 import。具体ログ、実行コマンド、統合基準の静的検査は [verification](../verification/cycle285/) を参照。全体 `lake build`、全体検証、CI は実行していない。
- Yulang2: `work/dots-audit` の `55574b6052ef1534fd0fc36d6d3617ebede59a0e` で X3–X5 と C3-ROLE-01/02、現仕様6.2–6.5 と K2 の記録を照合。昔の parser が通らない boundary 表現と、実行可能な where の実機記録を混同しない。この周は既存の Lean 意味判断の範囲を証明したものであり、新しい Yulang2 実機実行や言語変更はしていない。質問ノートなし。
- 今回の停止は **この例の最初の install 後の全 raw 継続**のみ。最初の install に至る任意の順序、他の constructor、全 T1c、B4/V8 の全体主張、主型性、239/240 型の一般停止、任意の深い値に対する raw refresh の完全性は未証明。この実 nonleaf と deep-output は別 fixture。論文や言語仕様ファイルは変更していない。

- 追試の一般化（補助／健全・完全）: `GeneralRebaseTowerEndpoint285.subtype_eq/descriptor_iff`。単一不変引数の名義型塔の間では部分型 iff 深さ一致。全 source スロットがその塔の値を取る一つの割当と、既知の1引数カタログがあれば、深さ k+1 の値に対してカタログ適合の即時 descriptor が存在する iff 深さ k の source スロットがある。非点の descriptor も必要条件に含めた。これは一つの割当で表現できる条件であり、全モデルに対する refresh 証明書の十分条件ではない。

## 次の候補

1. `GeneralRebaseDepthPathRank285` の初期状態 Anchor を、install 前の保留・見直しを含む相に拡張する。特に一意性、再据付け防止とモデル狭窄の向きを分ける。
2. 名義塔の一割当について得た下端条件を、全モデルに共通の端点選択と証拠へつなげる。複数引数や異なるコンストラクタにも一般化する場合は raw Known と public readback を区別する。
3. 手を付けるなら、constructor がありかつ非葉・生の効果行も読む一つの実 where fixture を選ぶ。本周の二例を同じ source へ結合してから一般命題を作る。

[設計記録](../design/2026-11-20-cycle285-source-read-coverage.md)

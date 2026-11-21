# C331: inline の元の RHS から候補を読み、実中心・子・固定出力まで繋ぐ

## 指示と公開範囲
22:30 UTC 枠、実開始 22:33:42 UTC。開始時の integration/m1-final は c35cb70b92e2c59b2bc0849e345a895282a67032。standing orders、inbox、最新版 spec/06-roles.md §6.3/6.5、C330 完了点 f3118ca9e9a5faff5833617ab6dc6104ad08c49a を読んだ。I-56 の宣言的健全性を先にし、I-58 の選定後の実中心等式と、I-59 の狭い根 K2 の規則を残した。private work/dots-main だけを更新し、I-57 の凍結ファイルは blob ID だけ照合した。

## (4) 宣言的健全性: 今回繋いだ範囲
1. **支持された元の inline RHS を候補が直接読める。** 古い名前専用 Trace では読めなかった C330 の同じ実例を、原行と明示された inline 項から読む。閉じた行の正規化で先に見える field・要求順・幅／厳密空終端・残余を保持する。既存名を開くときは支持された行を要求し、導出した通常等式を候補の入力に先回りして渡さない。候補照合は独立した下端と上端から行い、同じ端点間で適法な別中心に替えても positive 照合は同じ。任意個の record field が binder である範囲では、元の閉じた行と要求ラベルの実 lookup から、field trace を追加仮定せず証拠を生成できる。普通の primitive・不変 nominal・variant・join の inline 構造は、実際にその構造の読取りがある場合に任意有限の内側へ組み合わせられる。InlineTrace331.realize、InlineEndpoint331.restores_positive_read、InlineFieldProducer331.raw_head/independent_endpoints/independent_actual。
2. **実中心から、正確な子列と書込みへ。** 同じ元の項からの実読取りを別に行い、昔からある論理名を再利用し、実際に捕捉した複合項だけ fresh な式を足す。古い名の区間が既知なら、中心を端点に置換せず、三つの名前ごと保持する。任意長の実観測（旧対応形も混ぜられる）から既存 I-58 コンパイラを通し、固定 target 関数と実 where／root の二段階の通常行 append が明示された Frame を生成した。子の順序・役割・三名・出力先は実コンパイラの検査に従う。実コンパイルを提案と独立に済ませた後、現在の選定ガードと普通の receipt が別に検証済みなら、実リストと一致する提案だけが選定の枝に入る（InlineReplay331.independent_readback）。InlineAllocation331.name_walk、InlineIntervals331.read_with_ranges、ExactFrame331.frame_after_exact、InlineCompiler331.compile。
3. **本当に選ばれる root と子。** checked 宣言と元の記録行の実例。field 7 の隠れた出現を落とした残余 field 9 は fresh 19 に、複合 pair は 18 に束縛する。最初の例では従来名 3 の子が出力 5、親は 6=19。もう一つは同じ checked 宣言で元の field を交換し、実コンパイラが fresh 18 を子に渡し、5=18、6=19 を読む。子の開始根拠は 18 の論理等式それ自体ではなく、元の支持のある式からの経路であり、まだ未完了の子の出力は支持行にはしない。二例とも具体モデルを示し、任意の同じ現在モデルで再帰 Evidence が成り立つ。第三の例では、旧名 3 の有効な区間 (1,3,2) を崩さず実子に渡す。実モデルで中心 int ∪ bool は下端 int とも上端 top とも同値でない。InlineModels331.checked_dictionary、InlineChildModels331.checked_dictionary、InlineRangedModels331.real_nonpoint_child/strictly_internal。
4. **支持の由来を混同しない。** 新しい名前の根拠は親の原 RHS からの有限な構造経路で、実際に抜いた field／残余だけをたどる。元がソースだけで説明できるときだけ、新しい通常定義に source 由来の証明を付ける。元がすべて出力起源なら source へ付け替えることはできない。より一般に、実際の一つの読取りで使った行・alias・終端に元の起源を一つずつ記録し、同じ通常区間と、記録された全起源が使える現在状態で同じ読取りを再構成する。二つの出力 owner にまたがる具体例では、同じ非空モデル集合のまま、両方が完了したときに限り lower-known となる。どちらかが未完了で根が循環しない場合は実 Classify が pending で、I-59 の根 K2 例外は発動しない。単独 owner だけに由来する場合は、その owner の完了まで新しい捕捉名の支持は使えず、完了しても元の owner 由来を source に付け替えない。実 pair 名 7 を使うこの例でも通常状態は同一でモデルを持つ。InlineGround331.no_forgery、InlinePending331.no_pending_promotion、InlineOrigins331.exact_uses/allocation_origins、InlinePhase331.real_pending、InlineOwnerExample331.real_gate。
5. **失敗の根拠を区別する。** 支持された閉じた下端に要求された必須 field がないとき、いずれの現在モデルでもその field を必須とする実 layout と両立しない。要求ラベルは先頭である必要はない（InlineBoundary331.missing_blocks_layout）。単に読取りが見つからないことを拒否や保留と同一視したのではない。さらに別の checked inline 例では実端点で候補が選べるが、変数を二度出す宣言のまま実位置を新しい 7 と 8 に置くと、I-58 の実書込み 7=8 が既知の int / bool と矛盾する。書込み前のモデルを示し、当該試行の診断は pending ではなく rejected と確認した。InlineNegative331.absent_requested、InlineRepeat331.proposal/exact_tie/actual_rejected。

**残り 1 群。** 任意の承認済み安定 source 選定が、現在状態の支持付き観測・実中心・スコープ・固定出力と順序付き実子までこの producer / receipt へ入る一般定理。今回は支持された閉じた inline record、任意有限の binder-field 形、対応する式の根拠に限定。未知・不透明な残余、すべての候補保留／否定の独立完全性は未証明。複数 owner の証拠は連言として保持しており、それを単一の source origin に変換していない。通常の区間事実は現行宣言的状態の通り別に保持し、その由来が通常モデルの同値だけで復元できるとはしない。新しい診断優先や受理条件は足していない。

## (2) 成功停止を前提とする部分正当性
**残り 2 群。** (a) 任意の現行成功停止の状態・支持・解決済み子を宣言的境界に正確に射影、(b) 停止時の診断木、辞書と全要求の出力を同じモデル／固定名で接続。今回は (4) の一般化を優先した。停止性、物理 solver/journal、Rust 実行の検証はしていない。

## 検証
notes/verification/cycle331/ に scoped Lake build、全追加ソースの trust 0、個々の audit、axiom gate、宣言依存境界、差分検査、statement index、固定ソースとの再照合と再実行を置いた。Lean 4.35.0 の追加 39 モジュール・独立監査 8 本を直接検査し、全 47 ファイルを固定 GitHub ソースからバイト一致させて再検査した。

次に: 今回は閉じた head の各 field が binder の場合、全 field の観測を自動的に組み立てる。任意のネストした field pattern について、inline と名前付き RHS を含む型の構造から、同じ独立の供給を導くところを次に詰める。下端が不足して論理的に矛盾する例、上端側の資料だけ不足する例、実際の tail が未知である例を区別し、未承認の待ち・拒否の優先にはしない。

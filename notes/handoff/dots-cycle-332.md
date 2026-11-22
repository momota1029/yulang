# C332: 入れ子の支持付きソースから実捕捉・順序付き子列・辞書まで

## 対象

23:30 UTC 枠。実開始 2026-11-21 23:31:31 UTC、報告時刻 `2026-11-22T00:21:34Z`（実 50.0 分）。開始時と最終確認時の integration/m1-final は `2cd3096a87572aaabc6ef20b59fd93968defa45c`。standing orders、inbox、spec/06-roles.md と C331 の確定版 `a617f02266694ece56afb4e6b88a9cc47efb7893` を照合した。I-56 (4) を優先し、I-58 の実中心での等式、I-59 の根 K2 の限定された扱いを変更していない。private `work/dots-main` だけを expected-head / nonforce で更新した。I-57 の凍結ファイルは byte を変更せず、blob ID のみ確認した。

## (4) 宣言的健全性

- **入れ子の Read そのものを元の支持行から生成。** 実宣言の normalize / translate を通った式そのものを有限構文として再帰的に読む。閉じた record 内の field がさらに pair、variant、不変 nominal、record である場合も読める。既存の名を開く場合は、支持された RHS とそこへの正当な alias だけを使う。二重に現れる field は可視の最初のものを読み、名で参照した内側 record と外 record の残余を別々に保持する。nominal の引数だけを actual mode に切り替え、他の共変位置の lower/upper を混同しない。任意有限の対応済み引数列について、本当に計算できた場合のモデル保存と実 head 捕捉列を証明した。すべて同じ元の支持 snapshot を読むので、今から作る行をソースの裏付けには用いない。主要定理: `NestedDecode332.normalized_sound`, `NestedHeadList332.capture_sound`, `NestedHeadList332.probe_sound`。
- **元の捕捉から、通常の式と実子の順番まで。** 古い名を再利用し、必要な複合項のみ名前を作る。既存コンパイラの where 部、要求位置、固定 target、通常式追加をそのまま通し、順序付き実子を得る。実行可能な `NestedReplay332.replay` は子の提案を入力に取らない。`current_after_replay` は、独立に確認した現在の選定ガードと、同名の通常式を検証した receipt の下で、実子列に一致する提案だけに選定枝と全現在モデルでの意味を与える。target を選定後に入れ替えたり、現在の model から元の支持を逆算したりしない。
- **本当に生成された子を一つ、さらに順序のある二つで実証。** 元のネストした RHS を持つ実 checked 宣言で、内外の残余がそれぞれ 16 と 17、親の固定出力は `6=17`。最初の実子の引数は `(18,3,19)` で出力先 5、二つ目は `(20,11,21)` で出力先 10。子の並べ替え、出力先の取り違えを通さない。それぞれ実 compiler Frame と actual Classify を作り、両方を含む一つのモデルを示した。任意の同じ現在モデルでの再帰 Evidence も成り立つ。主要定理: `NestedModels332.real_nested_dictionary`, `NestedSiblingsFrame332.order_is_real`, `NestedSiblingsModels332.exact_siblings_same_model`。
- **未知、上端の情報不足、下端の矛盾を区別。** record 内の有限 named tail は指定済みの経路だけでなく実支持 index から自動探索できる。元 RHS の終端が確認できる場合だけ proof を返す。同じ通常モデルで owner 99 と 100 の両方の出力が使える場合だけ実 nested read が復活する回帰例を確認した。真の下端欠落は、実の正規化 pattern、支持された下端の記録行、可視の必須 field と閉じた終端から別の有限検査が証明する。未知の tail、上端が広いだけの例ではこの否定を行わない。広い上端では実中心が要求を満たすモデルがある。主要定理: `NestedSeek332.seek_complete_for_path`, `NestedSeekCases332.auto_read`, `NestedNegative332.actual_obstruction`, `NestedBracket332.upper_none_not_clash`。
- **I-58 の反例回帰。** 一つの head 内の実 repeated binder では `7=8` が int/bool の古い根拠と衝突する。さらに異なる head 引数を読む場合も、実中心の出現を同一視せず `3=11` を実書込みしてから矛盾を示した。後者は二引数 producer の局所再現で、選定全体の新しい診断規則を主張しない。主要定理: `NestedRepeat332.every_later_rejects`, `NestedReplayCases332.cross_argument_conflict`。

**残り 1 群。** 任意の承認済み安定 source 選定に対し、上記の producer を動かせるだけの現状態の実支持、適切な spelling/alias、端点・実中心・残余の観測と、固定 target の receipt が取れることを示す一般橋。今回、任意有限の対応済み構文、有限支持経路、実出力のある辞書まで繋いだが、任意の候補探索、すべての opaque/混合 mode、拒否と保留の完全性までは示していない。有限 read の budget は診断・受理の新条件ではなく、I-59 の例外を追加していない。

## (2) 成功停止を前提とする部分正当性

**残り 2 群。** 任意の現行成功停止を独立宣言的状態・支持・解決済み子へ正確に射影する橋、および停止時の診断木・辞書・固定出力を同じモデルに結びつける全体定理。今回は (4) を優先した。停止性、物理 solver/journal、Rust 実行は対象外。

## 検証と公開

Lean 4.35.0、追加 30 モジュールを scoped Lake でビルド。追加 8 監査は `Yulang.*` だけを import し単独の trust 0 で成功。実 GitHub ソースを固定版から取り、38 本を byte 一致させて trust 0・warning-as-error で再実行した。150 定理の個別 axiom 監査、65,086 宣言を含む scoped axiom gate、型と値の依存監査、差分検査が通った。記録は `notes/verification/cycle332/`。全リポジトリまたは Rust のビルドを通したとはしていない。

途中の転送で長い barrel が切り詰められたため、blob ID の累積照合で検出し、前周の完全な bytes に新規 30 import だけを足した版に `303673e58d5d212c3631db937787c06f4e95aa05` で修正。修正差分は `lean/Yulang.lean` のみ。凍結 2 ファイルは変更なし。修正後の今回差分を、ローカル Git の blob ID と比較して再照合した。追加 30 import だけの依存解析は成功した。全 barrel の直接依存解析は、この焦点ビルド環境にない従来の `SpecExamples` で前周・今回とも同じ位置で止まるため、全 barrel の build は主張しない。

## 今回確認した index の限界

同じ通常状態で、根の自明な式 `0=0` と構造を見せる元の RHS がどちらも支持済みのとき、前者だけを first hit にすると正規化 read は none、後者を先頭で読めば元の実観測が出る。自明な式の追加はモデル集合を変えず、実モデルもある。これは C332 の有限 index の選び方の反例であり、承認された安定選定の反例ではない（`notes/verification/cycle332/first-hit-contrast.lean`）。

## 次に検証する一つの橋

現 producer の基準例は「候補が実際に入る index の行順を選べた場合」に限る。C333 の優先候補は、同じ名前に複数の支持 RHS がある現行事例で、最初の構文は opaque な alias 行、後続の行は field を見せる場合。通常モデルが同じだというだけで書換えず、保存済み行／承認済み alias／完了済み owner を保つ二つの admissible index を作り、(a) 一方で positive scan 不成立、(b) もう一方で実 capture、子列、固定 target が得られる、(c) 独立した実 stable source 選定から少なくとも一つを得られる、のどこまで証明できるか詰めたい。有限探索は witness の列挙にとどめ、優先順位や新しい受理条件にしない。上端だけの不足と根 K2 に、今回の下端欠落証明を流用しない。

# C333: 支持済み source の全ての正の読み方から、実子と同じモデルの receipt へ

## 今回の範囲
00:30 UTC 枠。開始 2026-11-22 00:30:00 UTC、報告時刻 `2026-11-22T01:20:02Z`（実 50.0 分）。開始時の integration/m1-final は `2cd3096a87572aaabc6ef20b59fd93968defa45c`。最終確認時は直前の C332 を合流した `fc40615b8197b84163aa2db443d01f318eb61147` で、指示・spec の blob は同一。standing orders・inbox・spec/06-roles.md §6.3/6.5、C332 完了版 `43f7d3e19b112d7d8a74dbb131492c41c4008b3c` を確認。I-56 (4) を優先し、I-58 の選定後の実中心等式と I-59 の狭い根 K2 規則は変更しない。`work/dots-main` のみを expected-head / nonforce で更新した。

## (4) 宣言的健全性

1. **既存の独立 Read から、有限の実支持表を得た。** 位置への正当な alias、保存された所有者と RHS、実表示の根拠を保ち、そこにある選択肢をすべて列挙する。本物の `InlineTrace331.Read` または `Spine` の任意の有限導出について帰納し、各導出が使った行と alias の有限表を回収した。必要な情報がある表では十分な深さの全てで、同じ位置列、mode、raw 出現、閉じた残余を返す。上位の名前や構造が同じでも、各出現が別の実 RHS を読んでよい。実行側が返した項は同じ元の `Read` を持つ。任意 alias の決定器、モデルからの逆算、候補提案は前提にしない。`AlternativeReadComplete333.read_plan`, `normalized_finite`, `AlternativeSpineComplete333.spine_plan`, `AlternativeNeeds333.fulfilled`。
2. **旧 named と inline を混同せず、実際の正の候補述語を再現。** 同じ構造を名で一段ずつ読む旧 `Trace321` にも有限充足証明を作った。今の C331 候補の正側「全引数で旧 named の端点、または全引数で inline の端点」は、各区間の通常の有効性の下で有限支持表と十分な探索深さが存在することと同値。未完了の出力は支持表へ昇格しない。旧 named では未知の残余を名前のまま捕捉できる例があり、同じ通常状態にモデルがあっても、それを inline の閉じた残余とみなしてはいけない。最初の RHS が自明な alias でも後続の構造行を読める実例、および同じ名前の二出現に別の構造行を読む実例を確認した。後者は C332 の一つの固定 RHS 関数では再現できない。`AlternativeNamedComplete333.named_finite`, `AlternativeNamedHeads333.candidate_exact`, `AlternativeNamedCase333.both_source_modes_not_interchangeable`, `AlternativeCases333.both_spelling_orders`。
3. **実際の複数引数の中心を、証拠のある流儀を混ぜて組み立てる。** 任意長の head で、ある引数は旧 named、別の引数は inline を読む。すべて同じ元の支持 snapshot を参照し、今生成する行を次の source 根拠にしない。旧変数に独立した区間証明があるときは三つの名前ごと保持し、中心を端点に置換しない。実の where / output コンパイラを走らせ、固定 target と順序付き子列の `Frame` を返す。任意の checked/covered 宣言について独立した正の端点・実中心の証拠がある場合に有限の計算結果を得る定理で、Frame を入力仮定にしていない。選定の語を返す定理には、別に現在のガードと同名の通常 receipt、子の順序・出力先を含む完全一致が要る。`AlternativeMixed333.capture_plan`, `AlternativeMixedReplay333.replay_plan` / `consume_current`, `AlternativeRange333.materialize_exact`。
4. **同名の既存 receipt と、実際に検証した生成。** C332 の任意の成功実行は新列挙に、同じ通常状態、同じ捕捉名、同じ順序と固定出力先で含まれる。現状態の C332 二子例で実際に以前の名指し receipt を使い、両方の子を含む一つのモデルで辞書を確認した。非点区間の実例では捕捉 `(1,3,2)` を保ち、コンパイラが子 `(20,3,21)` と固定出力先 5 を生成した。`AlternativeEmbedding333.exact_replay`, `AlternativeCurrentCase333.real_current_dictionary`, `AlternativeRangeCase333.exact_frame`。

5. **一つの checked 二引数宣言に二種の実中心を混ぜた。** 第一引数の実中心は名付き record で残余名 5 をそのまま読み、第二引数の実中心は inline variant 内の pair を読む。端点の候補照合は別名 `(2,9)` と `(6,10)` の旧 named 証拠から行い、いずれの実中心も端点へ置き換えない。実 compiler 出力は子引数 `(15,3,16)` と固定出力先 14。実際の通常状態がモデルを持ち、そのモデルで Frame の Meaning が成り立つところまで確認した。この新しい二引数例で Classify 全体は主張しない。`AlternativeMixedDecl333.checked`, `AlternativeMixedCase333.mixed_exact_receipt`, `AlternativeMixedModels333.actual_mixed_child`。

6. **通常モデルが同じでも、完了済みの根拠かどうかは区別する。** 元の導出に必要な行と alias の由来を保存し、同じ通常の区間と、記録した由来が後の状態で使える場合に同じ読み取りを再建して、新しい有限表へ入れられると確認した。実 named residual の例で owner 二つの完了を別々に切り替えても通常状態と実モデルは不変だが、新しい alternative spine が終端を返すのは両方の出力が使える場合だけ。`notes/verification/cycle333/exact-phase-reuse.lean`。

**残り 1 群。** 任意の承認済み安定 source 選定が実際の中心の読み取り（既存正の named/inline、または許された区間射影）と、選ばれた同じ固定名の where／出力 receipt を与えることを、安定な通常伝播そのものから導く一般橋。今回、既に独立に導出された二種の正の読み取りの列挙完全性と、同じ子を持つ旧成功実行の保存は証明した。十分な探索深さの存在は source 観測に限る。深さ不足や資料の欠落から、任意の診断、候補の優先順位、受理条件を導かない。現在状態で任意の範囲表と正しい receipt の存在を仮定して一般健全性を閉じたとはしない。

## (2) 成功停止を前提とする部分正当性

**残り 2 群。** 任意の現行成功停止を現在の宣言的状態・支持・解決済み子へ射影する橋と、停止時の診断木・辞書・固定出力を一つのモデルへ結ぶ全体定理。今回は (4) を優先し、停止性、solver/journal、Rust 実行は扱っていない。

## 検証と公開

Lean 4.35.0。追加 25 モジュールの focused Lake build、追加 6 本の独立監査（Yulang のみを import）、公開 pin `603e801604042bde39a4ba2fb60c26d5c5441be3` の 31 本の exact bytes 再取得と trust 0 再実行が成功。128 定理の個別公理監査、65818 宣言を含む scoped axiom gate、型と値の依存境界、差分、statement index と別置き回帰も確認した。全記録は `notes/verification/cycle333/`。深い全探索をそのままカーネルで簡約する大きな回帰は打ち切り、同じ実導出の有限証拠と小さい実回帰で確認した。全 repo/Rust の build または利用枠の残量は未確認。

I-57 の二つの凍結ファイルには一切書き込まず、blob ID の一致だけを照合した。長い `lean/Yulang.lean` は各公開前に元の全 bytes を独立 hash し、追加 import だけを足し、更新前の候補 tree の Git blob と更新後の全 bytes を照合した。C333 の追加 25 import の依存解析は成功。全体の build は行っていない。

## 次に
上の (4) の観測側で、C330 の区間射影が実際の centre からの読み取りを構成できる範囲と、構成の代わりに別の正当な Frame を保存すべき範囲を切り分ける。where／固定出力側では、今回の receipt の仮定を現在の通常伝播と関連型の安定化から作る。旧発行が普通の規則列に残ることは `RuleSequence324.remains_applied`、同じ意味の再観測が既に証明された場合の出力は `RuleSequence324.replay_sound` が担当する。次は実選定と当該旧発行の対応、現在の論理 target と子の同一性、普通に検証できる再観測をこれらへ供給する。質問ノートは新規なし。診断の優先順位に新しい仕様判断を加えていない。

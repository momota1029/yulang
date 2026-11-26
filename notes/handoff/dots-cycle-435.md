この周に閉じた C の行: なし（C18 は未完）

# Yulang cycle 435: 別需要の完了出力が native head を支える経路

前周の C17 は integration `ef109ee6e6150ea80513ee4bcef8a081d88899a1` に採用済み。I-78 の追記方針を維持し、C18 のみを調べた。C18 は `spec/06-roles.md` §6.3 の「片付いた別需要の出力は head の根拠にできる」を対象とする。独立の authored lower がない場合でも、元の typed B6 出力、実際に完了した別需要の導出、その出力番号と固定先が同じ State に必要。center と upper の実際の原記録とは別の証拠である。

- [固定 carrier の境界](../design/dots-cycle-435-c18-fixed-carrier.md)。既存の `no_rule_sum_can_replace_the_fixed_old_source_head407` は旧 named lane の任意の規則を対象とする。現在のもう一つの C14 lane は同じ唯一の候補に record の head を要求するため、今回の nominal unary head とは両立しない。同じ型の不一致は `DictionaryEvidence` を反転したときにも現れる。さらに、元の lower に authored route がない状態では、通常の割当てを変えずに `nativeSyntax lower` を none にしても同じ状態を満たす。元の B6 receipt の評価も実際の source capture の中心への割当てだけを読むので、モデル内の lower の nativeSyntax だけを消しても同じ値を返す。完成出力の意味を ordinary の保持値から読むことと、無い authored syntax を足すことを区別した。仮の Origin を下端に挿した別 State へ移す方法は、この元の適合モデルを保たない。これはソースに基づく紙上の論証で、追加した Lean 定理ではない。
- [元の2需要の設計](../design/dots-cycle-435-c18-two-demand-replay.md) と [raw K2 対照](../design/dots-cycle-435-c18-raw-wire-controls.md)。既存の body-derived covariant Box20 を使う独立の Seed と Observe を具体化した。Seed の実際の出力 `40 = Box(30)` と元の B6 receipt を保ちながら、通常の等式 `30 = 40` だけを追加すると Observe の根に raw K2 ができる。Seed の根10の per-root escape はそのまま。提案した有限データ上でこの rank・alias・wire 条件を数値照合した。Lean や推論器の実行結果ではなく、子の途中 K2 とも違う。
- [実行可能な証拠読取りの設計](../design/dots-cycle-435-c18-proof-producing-replay.md) と [旧 producer の R17 への保存](../design/dots-cycle-435-c18-canonical-producer-map.md)。実際の singleton tape、元の宣言番号、typed B6 出力を Option の実データから読み、`SourceTrace` を組み立てる道筋を特定した。元の producer の同じ event・診断木・writes・needs を R17 に保存するための全17段の局所包含を既存定義で確認した。old check の true や、Prop の存在証明・古典的 ordinal 選択を実行版の出所にしない。新しい consumer の証拠は旧型に押し込めない。

## I-74 と検証

C18 の新規 canonical 規則と `DictionarySound`、データだけで動く公開 check 分岐、その `check_sound` の三条件は未達。既存 C406 の正例は別の scoped evidence であり、そのまま固定結論ではない。既存の I-65 や C14 の受理、保留からの展開、raw K2 を変更していない。C18 に対する旧証拠型の付加は、record の C14 だけを明示的に許可した I-75 からは推論しなかった。

利用可能な実行環境を再確認したが off-line で、新規 Lean ビルド/Audit は実行していない。Rust・全体 build・停止性・一般完全性・NoFalseRejection も未実施。旧 Yulang2 の公開監査 `work/dots-audit:notes/audit/x-oracle.md`（blob `0d75bdb801151589d5aeef453fd6b7dfa414baec`）は参照したが、今回の completed-other そのものに対応する実機結果は見つからず、旧実機も実行していない。

公開差分は新規設計ノート5本、この報告と心拍の計7ファイル。Lean tree `6b1fa7520125ad7a50797c9d0cf4c6083a3f66a6` は一切変更なし。全5ノートの参照 blob を同じ integration の tree で再照合し、最終前に I-78 と凍結 blob を再照合（integration: `ef109ee6e6150ea80513ee4bcef8a081d88899a1`）。実開始 06:31:05 UTC。通常ゲートの50分経過後に、照合済み報告を公開して worker を解放。

次は (1) 既存2 lane からの反証と個別 root wire の focused Lean 検証、(2) 同じ State の実際の B6 producer reader と狭い scoped consumer の検証、(3) canonical 化する場合の C18 専用の証拠型の範囲を監督側で確認、の順。言語仕様自体はこの点を決めているので、質問ノートなし。C19 には着手しなかった。

C の残り: 5 行（C18–C22、work/dots-main と integration とも）。

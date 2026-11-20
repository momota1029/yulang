# Yulang dot 作業報告 第301周

2026-11-21 01:30 JST の回。実開始 2026-11-20 16:30:32 UTC。第300周の完了 pin `cfb0d6fd987ef4a40f87adeeac4efa771ccc890d` と報告を確認。I-54 の B4 本線を続け、公開先は `work/dots-main` のみ。

## 結果

1. **任意の正の深さの実 V8 source を構成し、raw 遷移を厳密に閉じた。** 深さ h≥1 の、観測済み unary List を h 回たどると Int に至る Display 梯子。固定の checked registry に対して全 h で source の `Initial` と実 install を証明した。相 k から可能な一歩は既存の V8 kernel の次の install ただ一つ（k<h）で、相 h は停止。enqueue・二種の refresh・equate・reobserve・merge・既に完了した候補の再据付をそれぞれ除外。到達した状態にはちょうど h−k 歩残る。全モデル集合を各 install で保存する。
2. **実 journal から辞書を計算し、独立な V8 判断と照合した。** 実在の記録済み行を読み、現 context で二つの候補の既存 inspector を実行し、capture から得た子と現 journal の実生成辺を照合する。辺が未据付なら `awaitingChild`、行が無ければ `absent`。根の辞書は終端だけで読め、reader の最少 fuel は h+1（raw の h install とは別）。辞書は key 1 を h 回、末端に key 3。最終の独立な V8 `Local` / `Classify` と一致し、各最終モデルで旧 ownership を保持した frame を再構成して evidence を得る。この初期族からの全到達相の `EvidenceAt` と安定時の実 selected child 生成も検証。
3. **同じモデルでも読み取りが異なる旧 source を、実 refresh がつなぐ。** 旧 equation-only 梯子は型・行の全モデル集合が同じでも、終端の list と scalar 候補はまだ両方 blocked。実 V8 `Initial` から唯一未観測の終端 ID を strict unknown→known とする、元の外側の等式を保持した `Refresh` を構成した。refresh は辺を増やさず、その後 h 回の実 install を経て同じ辞書を計算・証明できる。こちらは **refresh が先の存在経路**（合計 h+1 歩）。旧初期で可能な別の refresh 先・順序は排除していない。

## 主な定理（厳密な型は[索引](../verification/cycle301/theorem-index.md)）

- `GeneralObservedLadderInitial301.actual_initial`：任意の n について深さ h=n+1 の source は既存 registry/root の本来の V8 初期状態。`GeneralObservedLadderExact301.exact_step`：任意の相 k≤h・任意の raw 後続候補に対し、実一歩は k<h かつ次の相に等しいことと同値。`GeneralObservedLadderBudget301.exact_initial_budget`：この初期から任意の有限 raw 終端経路は長さ h、行先は同じ終端状態。`accessible_initial` はこの初期族のみ。
- `GeneralObservedLadderJournalCompiler301.root_available_exact`：任意の相 k・fuel で、この実 journal を読む根結果は k=h かつ fuel>h のときだけ、指定の辞書。`GeneralObservedLadderReadback301.exact_compiled_root`：全ての辞書 d について終端根の独立 selected 判断は指定辞書と同値。`compiler_sound` は任意の実成功・任意の終端モデルで evidence を構成。 `GeneralObservedLadderScopedB4301.evidence_at_reachable` はこの初期から実経路で到達した任意の相に限る。
- `GeneralObservedLadderSemanticGap301.strict_gap`：任意の深さで旧 source と既観測 source の全モデルが同じでも末端 probe は異なる。`GeneralObservedLadderRefresh301.actual` は代替 source における実 raw refresh。`GeneralObservedLadderRefreshProgram301.strict_focus` はこの代替初期で追跡済みかつ未知の identity を終端に限り、`actual_refresh_then_compile` は実証した一経路の長さ・計算結果・各最終モデルの evidence を合わせる。

## 検証・未確認

- Lean 4.35.0、独立差分 31 モジュール。独立監査10本で全 273 定理を `--trust=0 -j 1 -M 3200 -DwarningAsError=true` で確認（新公理なし、標準の `propext`・`Classical.choice`・`Quot.sound` のみ）。既存監査20本。データの Lean 実行3本を独立に読み戻し、深さ1,2,3,5,8を検査。journal 判定は1,3,5,8の全相・境界内外の行・fuel で検査。3本の再実行結果がバイト一致。barrel 追記のみ、source 等47点の SHA-256 一致。
- `tools/verify-lean.sh --no-build` を前周 work と正確な統合木に対して実行。前周 work 木 `489e061237fe8f1419d584844bfed4748d42d3c3`。比較した統合 `7a82901d9c500c67b3b09649e93b6b297d603134`、木 `5739699e7a1ce8882c44011b470e4a080a1bd604`。常設指示・I-54 inbox の取得時 blob は開始から不変。[全文ログ・再検証手順](../verification/cycle301/)。
- どちらも同じ checked Display registry、ground unary nominal の入力、point bounds、associated output なしに限定。一般 B4、V8 全般の停止性、任意 source の `EvidenceNode` は未証明。Rust、Yulang2、全 Lake ビルド、CI は未実行。仕様・既存 kernel・Rust は無変更。質問ノートなし。使用量枠は不明。

次の候補は、(1) capture source ID と実 journal 行番号が一致しない多 occurrence を証明付き索引で扱う、(2) 旧 source の合法 refresh 文脈の差と先行 install の可換範囲を切る、(3) 出力・複数 where に進むなら、局所観測と rejected 割当の被覆を独立に増やす。詳しくは[相・モデル・索引の設計ノート](../design/2026-11-20-cycle301-path-and-index.md)。

- 最終報告書の固定時刻: 2026-11-20T17:20:37Z（経過 50.08 分）。前周からの変更 74 ファイル（完了心拍・報告を含む）。
  書き込み後に固定 pin で報告と完了心拍を読み戻す。

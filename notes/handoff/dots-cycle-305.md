# cycle 305: 実 refresh は無限分岐し得るが、同じ有限 V8 入力を正確に使える例

- 2026-11-20 20:28:28 UTC 開始（11-21 05:28:28 JST）。前周完了の pin
  `6307188ff50293b3cbf98033072ff2a965ebfe96` を再読。統合版
  `079158c78d4dc46b0a8107e9f4927c7405052ca2` と standing orders / inbox を再取得し、
  ACTIVE / I51–I54 を確認して、単独で `work/dots-main` のみ更新した。
- 途中 pin: 正確な再帰 report
  `d53f632a9be869b680f18f1311ac7b8ac4bbc1eb`、
  診断・索引付き証拠
  `f28d11d613a5fec1dae06ac437fdc2452002d7f6`、
  無限個の raw 停止枝
  `b6d3e1791a435b0f4eceee5dbe54f476a9cb51a2`、
  二段の早期 refresh・再帰分類
  `71ac50b7703326c72d9983861aec41a2d578cab1`。
  pin ごとに期待する内容を取得・照合した。最後に実成果 56 パスをまとめて再取得し 56/56 一致。完了時刻は同じ公開の heartbeat に記録。

## I54.1: 一般の observer/証拠の、条件を明示した exact transport

1. `GeneralNominalReportRecompute305.inspect_exact / many_exact`:
   任意の query・bounds と origin（list 版は origin の列と offset も任意）に対し、
   source 名、正規化した head/ordered children、nominal の名前/type-only 引数読み出し
   を保つ slot 対応があれば、相手で実際に計算した **Report 全体**は
   元のものの slot 移送と等しい。捕捉の重複・順序、検査/checked、blocked/conflicts、
   arity、anchors/tests を削らない。二スロット入替と nominal の二本の枝の実検査を
   別々に計算し、どちらも核で検証した。
2. `GeneralNominalReportContext305.EquivalentContexts` は上の対応に加え、両方向
   の refines と等しい interpretation を要求する。逆 slot 写像は source 注入性
   から導く。`GeneralNominalVersionedCandidateCoordinates305` は任意の registry、
   occurrence、宣言・key・ordered children に対する prepared/failed/inspection、
   survivor/unique と、private allocator/Fresh/HeadModels（同じ assignment）を保つ。
   raw K2 の直接 nominal 辺には粗い inspector の読み出しでなく、完全 descriptor
   の refines を使う。semantic K2 は全 raw model 同値も使う。未使用の canonical
   shape をカタログに一つ足す操作は、任意の元カタログについてこの条件を満たす。
3. `GeneralMixedIndexedDiagnosticLocal305.local_iff / recursive_iff`:
   任意の registry・occurrence・frontier/tree について、上の current context 対応、
   raw/centered の sites・aliases・edges、full Models の一致、さらに history/class
   slices の独立条件から、実 V8 局所・再帰診断を双方向に移す。K2、sharing、chosen
   output/merged conflict の優先順位も変えない。C304 の反例で必要だった slice 条件を
   消さない。`GeneralMixedIndexedCompiler305.valid_iff` は任意の同じ入力について
   部分的な回答も含めて validity を移し、Complete なら実行版の出力が exact。
   current context だけを対応するものに置き換える場合は slices を別仮定にせず導ける。
   この置換だけでは新たに Known になる source がないので strict raw refresh ではない。
4. `GeneralMixedIndexedEvidence305.indexed_tree_iff / evidence_iff`:
   任意の assignment・registry・indexed dictionary/payload について、選択した計画、
   ordered children、同じ compiled output body（明示/既定）の witness を保ったまま、
   同一の索引付き証拠木と readback を移す。`GeneralMixedIndexedClassify305.classify_iff`
   は任意の source registry・root・result に対し、再帰的 Classify の全ケースを移す。
   `GeneralMixedIndexedEvidenceAt305.evidenceAt_iff` はさらに全 occurrence の
   **raw Stability 同値を別途与えた場合**の実 source EvidenceAt の同値であり、
   一般の EvidenceNode の無前提証明ではない。

## I54.2: 出力要求付き実例、任意のタグと早期順序

C252/C285 のプログラムは install 後に明示要求 `(0,3)` を持ち、出力は深さ3の
nominal 型（辞書子は空）である。実際の strict refresh を構成し、未使用カタログ項目
だけを任意の Nat タグ付き variant とする。各終点は全 raw 規則で停止し、要求を保持し、
選択 `selected 0 []` と同じ深い型・payload 条件を満たす。タグは raw 状態から
読み戻せるため終点族は単射。`many_actual_halts`、
`GeneralMixedRawFanout305.beyond_any_finite_list` は同じ据え付け済み状態からの、
同じ有限入力を共有する strict refresh 停止点すら、任意の有限 raw リストでは
列挙できないことを証明する。ここで有限とは列挙する実状態の個数で、経路長ではない。

`GeneralMixedRawSchedule305.exact_possible_lengths` は各終点タグについて install
後の実 raw 経路長が 1 または 2 に限られ、両方実現することを証明する。
`GeneralMixedTaggedEarlyRefresh305.both_orders_arbitrary_labels / arbitrary_early_fanout`
はスカラー 0・1 のどちらを先に既知にしても、途中タグと最終タグを独立に任意選択でき、
最後の代表元を固定しても途中の raw 状態を有限リストで尽くせないことを証明する。
この例に一般の無限 path があるとは言わない。

`GeneralMixedObserverNotRaw305.valid_on_any_prefix / observed_prefixes /
different_step_availability`: この install 状態からの**任意の実到達 prefix**で、
同じ完全な有限入力は常に valid で実行すると `selected 0 []`。任意の二つの
prefix で root の Local 全結果、全 Models、Models 付き root Evidence が一致する。
それでも、特定の途中状態には次の raw Step があり、観測上等しい特定の終点にはない。
この観測同値は raw の停止判定や遷移合同を与えない。

## I51–I53、検証と範囲

- Lean 4.35.0。新規30モジュール（すべて `lean/Yulang.lean` の末尾へ同時追加）、
  standalone audit 11 本、`#print axioms` 87 宣言。監査は
  `cd lean; lake env lean --trust=0 -DwarningAsError=true Audit/Cycle305…lean`。
  依存は標準公理 `propext`、`Classical.choice`、`Quot.sound` のみ。
- `lake build --wfail Yulang.<対象>` で各端点 target と依存を検証した。実際の
  target・出力は `notes/verification/cycle305/` の各 `*-build.txt` と監査ログ。
  `bash tools/verify-lean.sh <checkout> b13078cdd --no-build` は全差分のみ。
  `diff-verification-*.txt` はその出力を順に分割したもの。全体 Lake ビルド、
  全既存監査、CI、Rust/パーサ実行は行っていない。ソースと報告・検証ログ、
  心拍を含む今周の変更は重複を除いて 65 パス。
- 既存 Lean の削除・差替えなし。spec、plan、lake 設定は変更なし。監督版との
  ローカル merge は、監督側の import 順の後ろへ既存から不足していた行を積んだ。
  公開側は既存 branch barrel を変えず C305 の行のみ追加。Lean コードの公開先
  は `work/dots-main` のみ（expected-head、force なし）。
- 途中の初回ビルドに依存の冷えと Lean の局所エラーがあったが、scope を保って修正し
  再検証した。利用枠は不明。新規の意味論判断・外部実行・質問ノートは不要だった。

## 次に詰めること

1. 全 source の有限 observer/compiler 入力を **生成**する。特に chosen-output の
   棄却割当てと merged の history/class slice を、有限な index と正確な判定証拠
   へ落とす。今回の妥当な入力の移送からは生成法は出ない。
2. raw を有限化するには未使用カタログを消した代表を選ぶだけでなく、将来の新規
   Known / novelty に関する適切な対応を別途証明する。反例が示す通り観測出力の
   同値だけを状態合同に使わない。
3. 非自明な分岐 children を持つ一般 node について、到達状態での raw 安定性と
   generated children の保証を持ち込み、証拠木 transport と接続する。無条件の
   B4 主定理、全 raw 停止性、全 source compiler は未証明。

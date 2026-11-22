# Yulang dots — cycle 348

## 結論: I-63 の証人検査器へ切り替え

- サイクル途中の最新 `integration/m1-final` (`c65291c929b0fd2754fd34af93c9e617bbb06e63`) で
  [I-63](https://github.com/momota1029/yulang/blob/c65291c929b0fd2754fd34af93c9e617bbb06e63/notes/plan/dots-inbox.md)
  を確認した。既存の実行器から作者・release の証拠を取り出す路線はここで終了した。
- 主成果は [証人検査器の設計](https://github.com/momota1029/yulang/blob/aa52df695a7fcbd3ab4831f67dda35402ffd24d2/notes/design/dots-cycle-348-witness-checker.md)。
  有限な入力表・独立に認証した由来・通常グラフと支持付き読み・I-61 の非点端点と open/closed 残部・
  I-58 の選定後の実中心等式・順序付きの子と固定出力・返された診断木と辞書の構造照合を分けた。
  leaf だけでなく各階層を再生して検査する。特に 334 の鎖と、I-61 の正確な射影を含む 340 の鎖が、
  **同じ宣言的状態の同じモデル**で何を示せるかを別の義務にした。
- **残りは S1=1、S2=1、C=1（後回し）**。S1 は有限の Witness と決定可能な検査器の実装、
  S2 は `Checked / Coverage / Declared` の反射、同一モデルの辞書証拠および診断木・辞書・固定出力の一致。
  C は受理されるプログラムについて実行器が通る証人を作る完全性。今回の設計はこれらを閉じたものではない。
  証人を作れないことを Yulang の拒否・保留にしない。旧 `Local` 対応、停止性は目標外。
- I-63 確認後は、新規の旧路線 Lean も、大きな checker 実装も追加していない。設計と既公開物の監査だけを公開した。
  切替前にローカルで別に検証していた prior-choice ベースの物理 patch 証明群は公開・成果集計に含めていない。

## 切替前にすでに公開していた限定的な Lean 結果

開始時の owner 指示 (`4fe465927a7316948822982bc01e135e7ee54e87`) に従い、
C316 そのものではなく **同じ元の反復 binder 宣言を使う C317 の分離修正版**だけを調べた。
C319 の別々の binder に置き換えず、C316 の変更なし実行器の一般的な正当性も主張していない。

| 公開済み範囲 | 名前と確認した主張 |
| --- | --- |
| 一般的な実験用 transaction | `WhereTxn348.exact_models`: Checked、真の frame、独立な支持付き選定と入力、実際の raw refinement、prior-choice 互換性、旧 footprint を保つ拡大を持つ transaction について、各前モデルと agree を満たす後モデルの存在が同値。`TxnEffects348.literal_requests`: 生成子が全て出力なしなら全 request の並びと重複を保存。`TxnReceipt348.exact_position` / `TxnCell348.generated_cell`: 生の site、中心つき site、compiler の子、作者・mode・節内位置を実際の追加の添字で対応させる。 |
| 元の反復 binder の修正 fixture | `RepeatedTxn348.checked` / `RepeatedRows348.corrected_position`: 別名や現行の見かけではなく、C317 の実際の修正子を物理位置 2／子順 0 として確認。`ReplayCompile348.actual` は保護名の列を任意に取って元宣言の compiler を再生し、`RepeatedPlacement348.same_model_placement` は任意の修正版モデルから旧値を維持して両端と中心の論理配置を作る。`RepeatedSpelling348.actual_cut`: compiler の格納 RHS と現在の名前付き RHS は文字通り同一でなく、すべての当該モデルで同値。`RepeatedVisible348.current_source`: 現在の構造 scan と該当作者の receipt からだけ支持を付ける。初期 published fixture の raw 拡大証明は C317 の既存補題を再利用しており、内部に旧 native の選定を使う。 |
| 物理・宣言の両辞書 | `RepeatedClosure348.physical_tree` は実際の root stamp と完了した leaf certificate の木。`RepeatedRank348.ranked`、`RepeatedRoot348.rule`、`RepeatedChild348.rule` がこの fixture の宣言的な選定と literal compiler receipt を作る。`RepeatedReceipts348.paired`: 任意の修正済みモデルを、修正済み journal の全意味的 footprint を保って拡大し、同じ割当で物理・宣言の両辞書、子の配置と現行の両 mode、元の要求 `(name=0,target=4)` の証拠を得る。この分離 fixture を用いた正の回帰例に限る。 |
| 有限な検査済み履歴 | `TxnTrace348.path_extends / path_projects`: 明示された有限 fragment 上でのモデル輸送。`TxnHistory348.born_path / current_after_path`: 版・位置は残し、現在の構造行は再検査。`TxnQuiet348.requests_after / outputs_after`: 出力なしの transaction と観測の有限列に限り、順序も含む要求と既存作者の出力証拠を維持。`TxnAssemble348.install_iff / without_post_assumption`: silent 子の下で前 journal と raw model／固定 plan の式／現在の class effects から後 journal model を組み立てる。全実行器の transition や任意の新しい出力要求には拡張しない。 |

固定 checkpoint（いずれも I-63 確認前に公開、読戻し済み）:
初回 `f276bcc306e0e4ef3756a37a577f13bbc196dcfe`、反復 binder と receipting
`ac9a76b9ea1ec66342ea7a4a794f2658f86560d5`、両辞書と固定出力
`e007aa8714e900026f0c7dd3f1e0132c9dd8c424`。
公開した新規 source は 28 モジュール。既存 Lean 本体は変更せず、barrel の末尾にその 28 import だけを追記。

## 検証・復旧

- 開始: 2026-11-22 15:28:24 UTC。前サイクルは `5c45d7846fcccef5467f73334d5a1ed76c44a5fd`。
  途中でクラウド作業環境のローカル進捗が巻き戻った。許可済み retained environment と固定 Git 履歴を取り直し、
  未公開 source は再 build／監査してから公開した。中断後も心拍と固定済み公開分から再開可能な状態にした。
- 既公開 Lean の検証対象 commit は `fda52b6db1dfba0d79f2f7421f7e0ff67f29d7aa`。
  detached checkout で前周からの 44 path の exact blob、barrel の元の 328731 byte と追記 28 本を照合。
  その後の更新は設計本文、監査ログ、報告、心拍のみ。最後の tree の全差分 path は GitHub から読み戻す。
- Lean 4.35.0 の `lake build --wfail Yulang.GeneralDeclarative<Module>348` を今回の対象に限定して実行。
  detached source と独立した 3 Audit について `lean --trust=0 -DwarningAsError=true` が終了コード 0。
  独立監査 45 宣言の公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
  import scope gate は 103739 宣言 PASS。frozen file を走査しない同等の差分検査 variant
  `tools/verify-lean.sh … --no-build` は終了コード 0 (diff PASS)。全 Lean build、Rust 実行、既存 solver の一般正当性は未検証。
- `lean/Audit.lean` と `lean/README.md` は実ファイルを materialize せず、Git blob ID
  `97dd1cfaded3e3abc3fd8caa98a64843d6f7a3d9` と `9fd6842bcc00c5bc5c00a196d9ccb328c6b0c94a`
  が前周・統合・公開で一致。差分／exit・逐字ログは
  `notes/verification/cycle348/diff-only-full.txt`、`exact-trust0.txt`、`exact-axioms.txt`、`scope-axiom-gate.txt`。
  質問ノートなし。利用枠は不明。

## 再開

次周は最新の standing orders/inbox を読み直したうえで、I-63 が変わらなければ checker の設計に沿って
最初の有限宣言表と `Checked/Coverage/Declared` の反射から着手する。
C316 の古い作者の復元や native placement の追加探索には戻らない。

読み取りで見つけた再利用口:
`GeneralSourceMetadataBareRole291.buildRow` は finite bare row の scope から role の証明つき行を構築し、
`GeneralSourceMetadataRoles291.check_exact` と `roleTable` が role/出力テーブルを正準関数にする。
`GeneralSourceMetadataBundle291.ready_exact` は `Attached` の下で `Coverage` を反射し、
`GeneralSourceMetadataDeclarations291.explicit_exact` と
`GeneralSourceMetadataRoleManifest291.attached_manifest` はその宣言本体・既定値それぞれの部品。
これは `Checked` の全項（特に `captureStable`）や需要ごとの `Declared` を既に検査しているという意味ではない。
最初の負例は「候補リストに現れない role の不適格な既定値」と「declared な名前でも target を書き換えた返値」を別々に置く。前者は全表 `Coverage`、後者は元の要求・返値照合が必要な理由である。

報告公開時刻: 2026-11-22T16:18:25.368Z（経過 50.02 分、枝の読戻しはこの後）。更新は `work/dots-main` に限り、基準 head を確認した non-force のみ。

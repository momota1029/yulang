# dots-main cycle 290: 有限 metadata 証明と実 effect の公開前再検査

## 結果

前周は、実 descriptor に記録された constructor key を照合した。
今回は **旧コードが実際に読む候補 head と出力 body にも同じ有限検査を
広げ、別の表で読み直しても同じになる範囲を証明** した。候補 head と
履歴 producer の現在の output class は別の範囲として検査する。
旧 MixedKernel、Lean の既存モジュール、spec、構文、Rust、受理／拒否
ルールは変更していない。出力は元の journal に書き足さない補助結果。

### 1. 旧 inspector の実読取り（補助、局所的な健全性と十分性）

- `ObservedMetadataKeys290.keys` は正規化済み pattern の app キーを
  集める。binder 名、レコード label、variant tag は別種の名前。
  deferred 分岐も残すので十分な上界であって最小 read set ではない。
  `Entry290.agree_exact` は任意の有限キー列と二つの表について、計算上の
  成功と「各キーの constructor layout/name、primitive（scalar 値込み）、
  invariant flag が等しい」との iff。`Local290.primitiveOK_exact` は
  検査したキーの primitive parameter layout 適合性と iff。
- `Translation290.translate_eq` は任意の pattern と二組の表について、
  そのキー上の等しさから**既存**の translator が同じ Query を返す
  ことを示す。`Report290.report_eq` は任意の固定観測状態・宣言・bounds
  で、この仮定なら既存 recursive report **全体**（captures、anchors、
  tests、blocked、conflicts、arity 等）が等しい。
  `Gate290.ready_has_provenance` は補助 receipt ready のとき、既存の
  正確な生成辺と、同一 role の全候補・全 bounds の report 再生を返す。
- 閉じた対照：実記録のキー `[6,0]` に現れない key 5 を追加 head だけ
  で使い、5 を削除すると従来の descriptor 検査は通るのに、同じ観測
  状態で conflict から blocked に変わる。提案 invariant flag を変えて
  も観測は変わる。key 8 の `int` と `str` は両表とも旧 Metadata を
  満たせるが、当該 key を読む head の Query は違う。layout 一致だけ
  では足りない。追加 head は独立対照で、実据付は主張していない。

### 2. 出力コンパイラと履歴所有（健全性・補助）

- `Branch290.accepted_branch`：任意の固定 registry、context、実 root、
  checked declaration、bounds について、head と、元 report の捕獲から
  計算した request の正規化 pattern のキー双方を検査すれば、旧
  recursive `generated` の report、request 列、schema が、提案表の
  再生でも等しい。出力 rhs だけに key 1 を置いた checked 宣言で、
  head-only の検査が通るのに schema が deferred になる対照を確認。
  この legacy recursive schema は MixedKernel の class-effect body
  コンパイラとは**別**。
- `Expressions290.explicit_eq/default_eq` は任意の明示式と positional
  default を別々に取り上げ、該当キー上の三項一致が**現在の** centered
  body コンパイラの Option Expr を保存することを証明。
  `Live290.accepted_live_models` は、任意の固定 state/root/plan/割当て
  について、現時点の alias-class request から lookup した body の
  キーに限って検査し、提案表の schema 条件と従来の ClassEffects の
  iff を得る。`Historical290.one_effect_sound` では同一の記録済み
  effect が実の親／子・要求 target に合っていることを要求。他の effect
  で body 検査だけ通す合成は許さない。versioned 効果とは既存
  `class_effects_iff` で接続した。
- `Total290.total_iff_ready`：任意の固定 state/root/plan において、
  上記 body キーの局所一致のもと、全 live request に lookup と
  コンパイル結果があるという追加 Bool と、元の `Ready` が iff。
  同じ表で key 1 の invariant 分類がない独立供給 plan は、有限表一致が
  成功し、各割当てで空 schema の ClassEffects を満たすが、実際には
  `Ready` でない。実親は据付前の Ready と据付前後の request 一致から
  現行全性も成立する。

### 3. 保存データの再計算と実二枝（健全性、二枝に限る完全性）

- `Seal290` は旧型付き stamp、現在と履歴の有限 entry 列、現行
  `(出力名,対象,Option Body)` 列を保持。request が body の constructor
  キーを増やさない場合も target を失わない。前周とは別の cycle 264
  の実 MixedKernel merge で request が増えて列が変わることを確認した
  （その供給済み旧 journal が今回の source から到達可能とは言わない）。
  `Publication290.publishFrom_exact` は保存データが現在の許可列の
  要素で、実コンパイル値が一致するときに限り補助出力を返す。
  実据付正例で [正しい seal, 現在表改変, 履歴表改変, request 欠落]
  を再生し、`released, staleOrUnsupported, staleOrUnsupported,
  staleOrUnsupported`。後三例は旧型付き stamp 自体を変えていない。
- `Strict290.actual_owner_total` には同じ effect の現行出力全性も
  要求する厳格版。`Public290.strict_live_sound` は任意の固定 journal
  上で厳格版が出力したとき、正しい target と実生成辺、全対象候補の
  report、記録済みの同一 producer とその現行 Ready、および**元
  journal の任意のモデル**で提案表の当該 class-effect 条件が成立
  することを示す。任意 journal について補助 mark 自体の一般的な
  entailment を主張していない。
- `StrictActual290.strict_release_exact` は、二つの指定 raw source からの
  あらゆる到達状態・入力 seal・mark について、厳格版の補助公開と
  「型全体を取る正の枝の実据付後・正規 seal・mark `(2,0,1)`」が iff。
  行分解の枝は `unfinished`（inspection pending）であり拒否ではなく、
  据付前は `missingProducer`。正の枝では元 raw Models は source
  slice と mark を満たすことにちょうど一致し、旧 raw は型座標 2 を
  Known にしていない（`Public290.strict_fixture_mark_sound`）。
  `Canonical290.canonical_dictionary` は任意の元割当てと payload で、
  正規補完後の元 registry の生モデル＋辞書と「source slice と辞書
  `node 0 [node 1 []]`」の iff。補完は型2のみ、すべての行と他の型を
  保つ。既存の行分解や後続の raw Step を実装したわけではない。

### 4. この検査の境界（補助、閉じた負対照）

- `Closure290.metadata_iff`：任意のキー列、registry、context について、
  元 Metadata は有限 check 成功 **かつ** 範囲外の constructor 一致と
  primitive 適合性を別に証明したこととちょうど同値。同じ既定表と範囲内の
  全 primitive support は、残りを満たす一つの十分条件。
- `RegistryCongr290.equal_publish`：固定 raw state、親子、Offer と保存
  seal について、二つの registry の宣言列が同じで、現在の候補／descriptor
  と全記録 effect の live-body key 上で表が一致するなら、元アンカー検査、
  許可 seal 列および厳格版の結果が等しい。実正例の保守的な全キー列は
  `[6,0,0,0]`。範囲外の key 8 を登録から消し、同じ key を不適合な
  primitive `pair` に変更しても厳格版の補助出力は同じだが、**全
  Metadata は不成立**（`RegistryFixture290.whole_gate_unchanged_offscope`）。
  この提案 registry の current Frame はどの選択・plan にもない
  （`Canonical290.strict_finite_release_not_new_frame`）。観測した
  key 6 の除去は比較で検出。一般 Frame、任意の registry の
  正しさ、resolver の完全性、主型性、一般停止性は証明していない。

- 例外の正方向も検証した。`Overlay290.closed_world_iff` は**独立に
  証明した**共通既定＋有限 constructor override と、none を既定と
  する有限 primitive override を仮定し、両 override 域を加えた
  有限検査と**元の全 Metadata**の iff を得る。実 fixture の representation
  を構成し、拡大検査では key 8 の欠落登録・不適合 primitive を区別して
  拒む。元の有限 seal で全 Metadata が認められたという意味ではない。
  任意 source の exporter がこの representation を与えることは未証明。

## 検証・継続

- 05:30:05 UTC 開始。統合先の standing orders、次いで inbox を実際に
  読み直し、ACTIVE、I51 と I53 を適用。前周完了と競合なしを確認。
  `integration/m1-final` は `14ecc280dc7c28982a02c6d9b56879c172d77a63`、
  tree `7bccdf08d67d08257696732dd0f924b1921df07e`、同じ内容の手元祖先
  `d1b1494efa0481b196f6c0623a11ccf37fab82b8`。前周最終は
  `f02834cb166c3fd127f2b2a2893362062c0d6ae6`。
- Yulang2 照合: `work/dots-audit` の `55574b6052ef1534fd0fc36d6d3617ebede59a0e`
  にある C3 旧実機ログ（関連型と where 正常／未充足）を再読。
  今回の補助証明は Lean のみ。Yulang2 の新実行や、任意の metadata
  について Yulang2 と同じだという照合はしていない。
- 次の候補は (1) 有限表を閉じる実 source exporter と範囲外既定の証明、
  (2) hoist された役割／metadata を実 raw Step で変更できる場合の明示
  不変条件、(3) 本当に独立した行読取りの実 source。今周はその入口・
  spec を変えず、設定待ちの質問ノートは作っていない。使用量の枠は不明。
- 詳細: [設計](../design/2026-11-20-cycle290-observed-metadata.md)。

### 実行結果

- Lean 4.35.0。`lake env lean --trust=0 -M 3200 -DwarningAsError=true`:
  新規モジュール 38、9 standalone audit、すべて exit 0。
  99 宣言中 1 は公理なし、98 の公理報告は `Classical.choice`、
  `Quot.sound`、`propext` のみ。6 件の実行可能 `#guard` を同じ監査で
  実行。監査名の coverage を宣言単位で照合。
- prior-only の shadow cache から当周 38 モジュールと standalone
  監査 9 本を再構築し exit 0。通常焦点ビルドと 38/38 個の OLean が
  SHA-256 一致。旧依存を保持した独立の当周再構築であり、全 library
  ビルドではない。旧回帰 37 本（199–289 の選抜）、主要インターフェース
  の `#check`、`git diff --check` も exit 0。
- `verify-lean.sh --no-build` は前周と統合内容の両ベースで exit 0。
  当周差分に REVIEW はなし。統合ベースからの累積に前周の `#eval`
  2 項目。barrel は 38 を同じ変更で追記、関連ファイルの凍結検査も通過。
  全体の `lake build`／全体監査は実行していない。
- 一時ファイルだけの Lean 純評価も exit 0: 正規 seal は mark (2,0,1)、
  表・要求を改変した 3 例は staleOrUnsupported。拡大有限検査は
  原本 good、欠落登録 disagreement、primitive 不適合 incompatiblePrimitive。
- 検査全文:
  [焦点・公理](../verification/cycle290/focused.txt)、
  [独立ビルド](../verification/cycle290/isolated.txt)、
  [旧回帰](../verification/cycle290/legacy.txt)、
  [静的検査](../verification/cycle290/static.txt)、
  [主要定理の型](../verification/cycle290/interface.txt)、
  [ソース manifest](../verification/cycle290/manifest.txt)。

### 公開途中の照合

`work/dots-main` のみに、期待先端と親 tree を検査して非 force 反映。
開始・早期・途中の readback を実施した:
`a7fc4ba00a56fb9c4395e22b189bceee1784a7c7` →
`61ebc6dc788c74b685cbcadaf511b43117313fa5` →
`8cb7f6510c83ca179c13aa5c7a82c8b8acc4568e` →
`0cf7580d3cc050203a5690f7bc95d85c18a5ee5a` →
`c36be70f78503188d333f13d8a401432f5f93c3e` →
`4a34059855b986db434492032a55d66dee195795` →
`989bc5f06c262afbbefa864e346d5f50014fd3b6` →
`bacca12d4c9f6bf3ad7795692beba7fadd36ed49`（検査済み候補、tree
`32ebd7f4c572248db91a5e90020519341e6248e7`） →
`62414ba640d783c9d543de716d78a7026df61b69`（次の反証基準と心拍のみ、tree
`c6bc436532cef92549d8c4d03790fe7775976a37`）。

- 最終報告書の時刻: 2026-11-20T06:20:12Z、経過 50.12 分。前周からの変更 66 ファイル
  （この報告と完了心拍を含む）。完了書き込み後に再読出しで照合する。

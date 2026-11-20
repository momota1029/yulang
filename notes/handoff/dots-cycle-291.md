# dots-main cycle 291: 有限 source 表の exporter と古い compiler の正確な境界

## 結果

前周は外から証明した共通既定＋有限 override を使った。今回は、**有限
で解決済みの constructor・role の入力データからその証明を組み立てる
Lean の入口**を作った。既存 fixture の表への一致は別途証明した。
パーサや arbitrary な metadata 関数を逆に走査する exporter ではない。
既存 MixedKernel、resolver、spec、構文、Rust、受理／拒否規則は変えて
おらず、raw に新たな到達状態を作っていない。

### 1. 有限表と全 Metadata の関係（健全性・完全性、表現に限定）

- `GeneralSourceMetadataRows291` は resolved key、constructor の layout
  と name（または明示削除）、primitive／invariant／未分類の排他的
  ラベルから三表を生成する。独立な有限既定コードは「不存在」または
  「同じ名前で空 layout」。任意の入力行列とキーについて
  `Lookup291.projected` は三値が同一の見つかった行に属す、または
  それぞれの既定値になることを示す。`Validation291.check_exact` は
  重複キーなしと、全 primitive 行が layout 適合であることにちょうど対応。
  重複による上書きは正常な source 入力にしない。row-bearing layout に
  invariant flag があっても、それだけで分解／材料化を約束しない。
- `Export291.representation` は共通既定と、元 registry・snapshot・
  interpretation への別証明付き添付から前周の overlay witness を構成。
  `Fresh291.different_table_at_fresh` は二つの入力の全行キーの最大値
  + 1 が両方の定義域外であることを示す。二つの既定コードが違うなら
  そのキーの値は実際に違う。`Comparison291.exact_linked_metadata` は
  任意の二入力と独立添付について、この不一致 branch も含めた有限判定
  成功と旧全 Metadata の iff。同じ有限候補の読みだけで全 Metadata を
  認めるものではない。今回の具体例では異なる既定の反証キーは 7。
- 既存の二枝の constructor/primitive/invariant 表を有限 4 行
  （0, 1, 5, 6）で表し、すべてのキーで元表に一致することを証明。
  旧 role map も「role 0 の required 出力 0、他は出力なし」として
  同一性を証明。重複行、primitive 形不適合、適合 scalar を別々に実行した。

### 2. source の材料化範囲と default の完全列挙（健全性・完全性・補助）

- `Use291.supported_exact` は任意の key/arity について、少なくとも
  layout、正確な arity、primitive または invariant 型引数条件を含む
  旧 ConstructorUse に Bool が一致。`Declarations291.explicit_exact`
  は明示 head、where 引数・出力、関連式の scope を採取し、
  `DeclarationCovered` と一致する。positional default の Term は
  明示 Pattern と別に走査した。key だけの重複排除で arity の差を消さない。
- `RoleManifest291.exact_manifest` は任意の有限 role 表で役割 ID と
  出力名が一意、default 位置引数が既存の scope に収まるとき、列挙した
  `(role,name,rhs)` の所属と、旧 `RoleDecl.assoc` の default lookup
  成功が iff。required（`some none`）は declared だが default ではない。
  任意の既存 role 関数へは別の一致証明が必要。明示宣言で使わない role 17
  の default は列挙される。key 6 を使う scoped default をリストから
  勝手に外すと「全 Coverage 成功」に見える閉じた反例を確認した。
  `BuildRoles291.build_exact` は証明を含まない resolved role 入力から、
  positional scope を実際に決定して証明を生成し、role ID・出力名の
  重複も検査する。成功 iff 出力を消去すると元入力と同一、かつ妥当。
  `BareBundle291.preserves_input` はこの変換で constructor rows と宣言
  列も保持することを証明。arity 1 の `var 1` はその時点で不成立、
  well-scoped でも非対応 constructor を読む default はこの段階では
  通り、材料化検査で初めて外れる。実二枝で data-only 入口も再実行した。
- `Diagnostics291.no_diagnostics_iff` は exact default manifest のもと
  診断列が空であることと旧 Coverage の iff。
  `DiagnosticProvenance291.exact_origin/sound_failure/complete_failure`
  は各通知が実 source 由来箇所に属し、その use が不適合で、逆にどの
  不適合 use にも通知があることを証明。診断は head・where・関連式・
  default の resolved ID と、不存在／arity／primitive layout／未分類／
  非対応 nominal layout を区別。元 resolver の言語診断は変更していない。
- `Bundle291.ready_exact`：任意の有限 bundle と別証明で添付した
  registry/context について、行検査 3 種、旧全 Metadata、旧 Coverage
  の連言に certificate の Bool がちょうど一致。旧 declaration
  `Checked` そのものや新しい Frame の証明ではない。実二枝は旧
  `Checked` も全 Metadata も両方真だが、row constructor を分解する
  枝だけは `head 1: key 6, arity 1, unsupportedNominalLayout`。
  その枝も旧 MixedKernel の親据付 Step は実行できる。
  **Coverage 範囲外は言語拒否ではない。**

### 3. 旧 output compiler と実 live request の局所条件（健全性・完全性）

- `ExprDomain291.compiler_domain` と `DefaultDomain291.default_domain`
  は任意の表と明示 Pattern／positional Term について、旧 centered
  expression compiler が値を返すことが各々 `PatternCovered`／
  `TermCovered` と iff を証明した。新しいのはとくに成功から
  syntax domain に戻る向き。旧 translate を変えず、すべての子と実
  arity を再確認した。旧 head inspector の保留と、このコンパイラの
  compile 成功は別。
- `Live291.live_ready_exact` は任意の現行 class と plan について、
  この source-use の局所検査と旧 `Ready` が、実際に読む metadata の
  一致のもとで iff。lookup 欠落と unsupported body は別診断。
  **実負枝の親は局所 Ready のみ通る**。それでも分解子は保留。
  `Publication291.same_result` は任意の固定 raw 入力と seal に対し、
  検査をこの局所 source-use に置き換えても前周の厳格補助公開結果が
  完全一致することを示す。実二枝では source から再構築した解釈で正だけが
  mark `(2,0,1)`、旧 raw の型座標 2 を Known にしない。
  その mark の生モデルとの iff は指定した二枝に限る。

### 4. source から再表現した観測 view と report（健全性・補助）

- `Snapshot291.check_exact` は任意の観測 state と有限 source で、
  記録済み全 descriptor の constructor layout が適合することに
  ちょうど対応。通れば constructor table と interpretation だけを
  入れ替えた Context を作れる。全 Models／Known／Linked は保存。
  元表・解釈が等しいなら `attempt_identity` は元 Context そのものを
  返す。実据付前後の二枝でも元 Context を回収。観測 key 6 欠落は
  不適合、未観測 key 8 欠落は view を構成して Models を保存するが
  旧全 Metadata は失敗。これは journal の移送でも新 Step でもない。
- `InspectTransport291.inspect_lower/many_lower` は任意の固定 Query と
  bounds に対し、元の再帰 inspector の結果が全フィールドで一致する
  ことを証明。Report は state を型添字にしているので capture の
  型ラッパだけを付け替え、座標、origin、tests、訪問と失敗は保存した。
  `ContextTransfer291.meaning_transport` は任意の宣言と全割当てで、
  head keys 上の表の有限一致があれば、元 Context と新 view の
  bindings、自明検査、Finished、ProjectionModels が保存される。
  対照：実親で key 0 の分類 flag だけを外すと、constructor table も
  Models も旧全 Metadata も保つが、report は blocked に変わる。
  対照は観測 view であり、異なる raw 状態への実到達や、独立な正の行
  読取りは主張しない。

### 5. 順序の境界（補助）

`Permutation291.source_perm` と `RolePermutation291.same_role_table`
は、一意キーの妥当な行の順序だけ変え、既定が同じなら、全 export 表と
default manifest の所属が変わらないことを示す。
`BundlePermutation291.whole_ready_unchanged` は正しい添付、同じ宣言列、
妥当な元行の仮定に同じ readiness を証明。表示順や任意の raw receipt
世界が可換という主張ではなく、重複を並べ替えで修復もしない。

## 運用と次の境界

- 実開始 06:31:17 UTC。統合 branch の standing orders → inbox を再読し、
  ACTIVE、I51～53、sole writer、290 完了を確認。開始時の
  `integration/m1-final` は `ed519652eae7f3610d2a2b9e9f1bd9206495bd19`、
  tree `ddef5bf70a52c6aad057a44eb040c19aba6644fc`。同じ内容の手元祖先
  `fc167a05d8ace9dcc15822e9bb50ff2023ccc658` で検査。
  前周完了 `396ffa8a4a7984a19431e299b434f4d65bceb664`。
- Yulang2: `work/dots-audit` の既存ログ
  `55574b6052ef1534fd0fc36d6d3617ebede59a0e`（C3 の関連型と正常／
  未充足 where）を再読。今回は純 Lean。Yulang2 の新実行や、
  この有限 exporter の Yulang2/パーサとの意味保存は未確認。
- 次の候補は、(1) 実 frontend の resolved list が constructor/role
  override を漏れなく出す独立な証明、(2) 今回の局所 check を使う
  認可済み後継 view での実 class-effect 証拠の接続、(3) source lowering
  から得る真の独立 row-only 読取り。一般停止性、主型性、一般 Frame
  生成は未証明。新たな言語判断を要する質問ノートは作っていない。
  使用量の枠は不明。
- [設計・境界](../design/2026-11-20-cycle291-source-metadata-export.md)。

### 実行結果

- Lean 4.35.0。焦点 `lake env lean --trust=0 -M 3200 -DwarningAsError=true`:
  新規 45 モジュール、9 standalone audit が exit 0。96 宣言の照合は
  `Classical.choice`、`Quot.sound`、`propext` のみ。
  7 件の実行可能 `#guard` も各単独監査で実行。
- 既存依存のみを利用した別 shadow cache で当周 45 と監査 9 本を再構築し、
  exit 0。焦点ビルドとの OLean SHA-256 は 45/45 一致。
  旧回帰 46 本（199–290 の選抜）、主要 theorem `#check` も exit 0。
- `verify-lean.sh --no-build` は前周ベースと統合ベースの双方で exit 0。
  当周追加に REVIEW はなく、統合ベースからの累積に過去の `#eval`
  2 項目。全体 `lake build`／全監査は実行していない。append-only barrel
  45件、凍結ファイル、`git diff --check` を検証。
- データのみの入力で Lean 純評価を実行し、実二枝の source validation と
  Metadata 適合が共に真、材料化 readiness が `[some true,some false]`。
  異なる既定では `fallbackMismatch 7`、未使用 default で
  `roleDefault 17 0` の非対応 layout を返した。
- 検証全文:
  [焦点・公理](../verification/cycle291/focused.txt)、
  [独立再構築](../verification/cycle291/isolated.txt)、
  [旧回帰](../verification/cycle291/legacy.txt)、
  [静的](../verification/cycle291/static.txt)、
  [インターフェース型](../verification/cycle291/interface.txt)、
  [純評価](../verification/cycle291/smoke.txt)、
  [source manifest](../verification/cycle291/manifest.txt)。

### 公開途中の照合

`work/dots-main` のみに、元の先端と親 tree を確認して非 force 反映。
開始・早期・途中の pinを再読した:
`9c799447d4469815790a93b5d86897d36380c79e` →
`d94441113425eb37506008c4fbc93cbed5118bcc` →
`52c4d4692f0e734ab6b5adf7bb15d0889975ba46` →
`1f4d2f7cd9d90cf5c5f5c4722ef4c55e01b798d6` →
`9761c0f126cb7d5baeb94db869e5312746326e8b` →
`26837882ed64b230a7a898e5175d2eb73eda10b0` →
`9e598e61179e5b2b0d0b229afb897ae62d85412c` →
`09e1011eb5f3a4464e027b345095b0df835c6b78`（最終検査済み候補、tree
`c0f51fb9adfa50d558be0efed0138f31852af070`）。

- 最終報告書の時刻: 2026-11-20T07:21:24Z、経過 50.12 分。前周からの変更 74 ファイル
  （この報告と完了心拍を含む）。完了書き込み後に再読出しで照合する。

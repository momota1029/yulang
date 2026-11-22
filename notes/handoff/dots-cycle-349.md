# Yulang dots — cycle 349

## I-63: 動く検査器の最初の範囲

最新の `integration/m1-final` は開始と再確認時ともに `2b1409b057315b5ece60fa63a677afe5f35cab52`。
[I-63](https://github.com/momota1029/yulang/blob/2b1409b057315b5ece60fa63a677afe5f35cab52/notes/plan/dots-inbox.md)
と、前周の [設計](https://github.com/momota1029/yulang/blob/1c897dca8ef668b6c2b1484d6289547a66c52763/notes/design/dots-cycle-348-witness-checker.md)
を引き継いだ。旧 solver の作者復元・旧 `Local` との対応・停止性は取り扱っていない。

**実際に受理した証書から健全性へつないだ。** 1 候補・ground primitive・点引数・where なしの断片について、
検査器は独立に供給された元のテーブル・通常状態・需要を使い、実際の compiler を再実行する。
同じ診断木と辞書、固定された名前・target の順序付き列、compiler が計算した記号的 RHS を照合する。
`WitnessPointReplay349.checked_result` は任意の同じ状態のモデルで C334 の `Evidence` を与える。
読取りと出力はモデルを選び直しておらず、正の回帰例には実際のモデルがある。

**非点 record は別の検査器を実装した。** 版を推測せず、独立なソース manifest の索引を検査し、
下端と上端を異なる名前のまま読む。具体例で、下端が exact-closed、上端が width-open、
現在の中心行は普通の等式として存在するが source としては未承認でも、可視 field と
standalone 削除の残部が同じ割当で正しく読める。名前付き tail をたどる場合は tail 自身の作者も検査する。
次に、実際に正規化した record パターンから field と残部の仕事を順番どおり作る。
反復 binder の両出現を保持するが、I-58 の選定後 tie をこの段階で入れたり、同名だから値が同じと仮定したりしない。

## 検証済みの部品

| 独立した部品 | 主な定理・確認範囲 |
| --- | --- |
| 入力・宣言 | `WitnessProblem349.first_sound`: role/全既定値/constructor の正準有限表を caller 入力から作り、`Coverage` と元需要の `Declared` を反射。未使用 role の不正な既定値は、raw の表が通っても検査不合格。`WitnessSignature349.checked_signature` と `WitnessHeader349.sound`: 実際に受理した schema について `Checked` の各項も得る。where なしと、既存の普遍安定性 `unary_descent` を使える where に限定。安定と証明できても対象外の schema があり、不合格は言語の拒否ではない。 |
| 診断木・辞書・固定出力 | `WitnessTree349.exact_report` / `classifies`: 実際に再生した木の構造、既存の要約が作る辞書、要求列を順序・重複込みで照合。2 子順を反転、同じ長さの逆順辞書、保留の子を親の保留に畳む木はいずれも検査不合格。`WitnessSymbolic349.actual_readback` / `exact_writes`: checked ground leaf で実際の compiler の記号的出力行を再生し、固定 target に同じ順で書かれ、任意の現モデルで成り立つ。名前・target と木が正しくても RHS 改変・行追加は不合格。 |
| 実行可能な正の C334 縦切り | `WitnessPointReplay349.decode` はソース由来の root 行・点を確認、可視の唯一の declaration と独立した両端の照合、全通常行の十分な K2 guard、compiler の現行 receipt を再検査。生成した `Witness` から `checked_result`。正の `WitnessPointFixture349.nonvacuous`、偽の木/辞書/target、未支持 root・不足 receipt、同 role の競合宣言を別々に試験。 |
| 有限の普通の証明書 | `WitnessLiteral349.eq_expr` / `rows_ordinal` は compound 構文と行順の exact comparison。`WitnessBound349.bounds_sound` / `alias_sound` は実際の区間または通常原子の索引と合成。`WitnessEquation349.in_every_model` は現行の行・束縛・record/variant/join/nominal/primitive の congruence を同じ状態で評価。`WitnessReceipt349.same_model` は長さと各位置の証明書を照合し、全構成を同じモデルに移す。単なる文字列一致では通らない別 RHS と区間合成を正の非空モデルで試験。 |
| 作者つき非点 record | `WitnessManifest349.authored` / `cannot_promote`: 独立 manifest 外の普通の行は出典として使わない。`WitnessRecord349.residual_same_model` / `field_same_model`: exact と width の両端から standalone 削除および field の型の区間。`WitnessProjection349.ordered` / `replay_same_model`: 実際の正規化パターンから field/tail の仕事、binder の順序と値を証明。非点モデル、支持のない中心行、独立な名前つき tail、誤った端点／bounds／field をチェックした。 |
| 同じ状態・同じモデルの C340 への部品 | `WitnessExactProjection349.fixed_models`: 既に状態にある slot に対し、中心の普通の形の証明書と field/standalone residual の現在の各式を照合し、任意の当該モデルに `ModelsExact` を構成。型値や slot を補修しない。通常の中心行を出典へ昇格しない。`WitnessExactProjectionFixture349.same_fixed_model` で field と residual の両方を一つの実モデルで走らせた。`WitnessTaggedBoundary349.sound_given_replayed_tree` はこの片を 340 に接続する条件つき定理。独立なタグつき子／候補の `Resolves` は明示された外部義務で、自己申告の木がその義務を満たすわけではない。 |

## 残りの本数

- **S1 = 1 群（部分実装）**: 狭い点 root と record 観測・通常の証明書・exact projector まで。一般の nested/compound で現行の承認済み候補判定、I-58 の選定後 tie、各節から再生した root/子の順序つき receipt、未完成出力と完成した出力の release の独立確認を実行できる証書へ拡張する。今回の manifest は元のソース出典から与えられた入力で、parser 出力と独立に結ぶ工程や solver がこれを推測することは示していない。unknown tail を width-open に読み替えない。全確定済み診断の検査を実装したわけではない。
- **S2 = 1 群（部分証明）**: 334 の狭い正の縦切りは完了。340 の exact 側は有限で既に普通の形・名前がある場合に同じモデルで確認。一般の同じ状態での独立タグつき tree の構築・I-58/59/61、全階層の子、証書と診断の照合へつなぐことは残る。
- **C = 1 群（後回し）**: 通る証書を任意の受理されるプログラムに対して実行器が作れる完全性は未着手。受理範囲、優先順位、拒否規則は変えていない。

次周は、ソース由来の record read と観測の現行証明書を、**再生成した** record の局所選定と節の実際の子順に接続する。
既存の独立 projection job の slot と exact 証明書の slot を照合し、I-58 を入れる場合は実際の selected-center tie を別に反射する。
これらが検査できない証書を新しい言語上の拒否・保留として扱わない。

## 公開・再開情報

- 前周: `1c897dca8ef668b6c2b1484d6289547a66c52763`。開始時点で割当環境が一時 unavailable。
  許可済み retained 環境へ通常の attach で復旧し、焦点を絞った Lean 再ビルドをしてから変更を公開した。
  現行枠の通知から実作業の初回確認までは遅延があり、絶対期限 17:25 UTC を優先する。
- 既公開固定 pin: header `fd907295aeb00d8ed3795c79c583d077b5d5b822`、
  正の点 C334 `419399e4f1b275c1398521ab3e568813c1bedee9`、
  非点 record/有限証明 `673894f4bb31093990f184895426e0cbfe3c6f74`、
  独立に計算した記号 RHS と正規パターン `dbd0604f240d06c62e3612325a2cf96db628179a`。
- 変更は private の `work/dots-main` のみ。expected-head non-force。frozen 二つは ID 比較のみ。
  使用量の枠は不明。質問ノートなし。全体 Lean build/Rust/元 solver の実行は行っていない。

- 最後の技術的な次手: `WitnessProjection349.Checked` の実データ（正規化パターン、`Read`、`ready` の実等式）
  から `GeneralDeclarativeTaggedInputs340.Input.prior (.record …)` を組み立てられる形まで来ている。
  `EndpointInput336.Input.record` が選ぶ `prepare` と `spans/receipts` の実 slot を再計算し、
  receipt の有限証明書をそれに対してだけ受け取る。既存 named-sidecar fixture に手作業で置いた slot が
  任意の入力で allocator と一致するとは言わない。その次は、最新の独立な `Election` と actual compiler の順序つき子を
  1 本の非点 selected record で確認し、成功断片を再帰化する。

## 検証

- 固定した科学側の commit: `ed0a65121471e92a0d3415471f4e9fc62dbed668`。
  そこまでの前周からの 51 path を detached Git で逐字照合。`lean/Yulang.lean` の既存の
  330080 byte を維持し、新規モジュール 30 本の import だけを追加した。
- 対象限定 `lake build --wfail Yulang.GeneralDeclarative…349` と各回帰 fixture が成功。
  exact detached source 30 本と独立監査 5 本は `lean --trust=0 -DwarningAsError=true` (終了コード 0)。
  独立監査 93 宣言の依存は `propext`、`Classical.choice`、`Quot.sound` の範囲。
  同じ import の scope gate は 109081 宣言 PASS。
- 凍結対象を読まない差分検査 variant `tools/verify-lean.sh … --no-build` は終了コード 0。
  `lean/Audit.lean` / `lean/README.md` を materialize せず、ID
  `97dd1cfaded3e3abc3fd8caa98a64843d6f7a3d9` / `9fd6842bcc00c5bc5c00a196d9ccb328c6b0c94a`
  が開始・統合・公開で一致した。
- 全ログは `notes/verification/cycle349/diff-only-full.txt`、`exact-trust0.txt`、
  `exact-axioms.txt`、`scope-axiom-gate.txt`。最終報告と心拍を足した全差分 56 path を読戻しで照合する。
- 初期の復旧時に同じ冷 cache 上の並列起動で一時的な build ログの不整合が出た。重複側を停止し、以後は
  本成果の依存を焦点ビルドで再構築後、kernel 回帰と exact detached を通した。

同点の次手を小さく始めるなら、`Ranked` の有限証明書を独立に検査する。
全 interval と変数同士の通常原子に対する rank の単調性、変数 RHS の rank 等値、
compound RHS の全依存名に対する狭義不等式を照合すれば、`Bound` の帰納で 340 の正の K2 guard を構成できる。
全域 rank がないこと自体を言語の拒否にしない。I-59 の正の K2 根の診断は別の到達証明書を検査する。

報告公開 2026-11-22T17:20:52.771Z、開始から 44.50 分（読戻しはこの後）。

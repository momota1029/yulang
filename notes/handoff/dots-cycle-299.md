# Yulang dot 作業報告 第299周

2026-11-20 23:30 JST の回、実作業開始 14:31:16 UTC。前周の完了 pin は `6911a1bf49dad2fee9d138d9ab611dd9662aa70c`。
`integration/m1-final` の standing orders と inbox を再取得し、I-54 の B4 本線を継続した。書き込み先は `work/dots-main` のみ。

## 結果

1. **実 C277 の親と生成子の辞書を、同じモデルで再帰的に構成できた。** 実据付後の親にも子にも完全な `Current` を構成した。親の再演は既に記録済みの子 site を重ねるが、新しい request は増やさない。`Installable` と `Committed` は両立するので再据付はできない。既存の executable frontier の実際の子順から表を読み、子の辞書を再帰的に作って親へ渡した。既製の子辞書や一括 `EvidenceAt` はこの構成の前提ではない。最小 fuel は親2・子1。
2. **純粋な表の成功と、実 raw 状態の根拠を分けた。** C277 の初期状態では子が生成されず、親にも子にも、どのモデル・payload に対しても辞書 evidence がない。実 raw install はモデル集合を保ったまま、生成・選択・親子 dictionary evidence を成立させる。辞書の形が先に計算できても、据付前に証拠として使うことはできない。
3. **有限で閉じた表では、全登録を含む一覧の長さが十分な fuel 上限になる。** 各参照先が閉じ、全登録を列挙した有限表で、既知行の辞書が有限 fuel で得られることは、同一状態の選択子グラフがその行で accessible であることと同値。accessible な子の経路が祖先へ戻らないので、1段ごとに許される添字を1個減らせる。最初の成功値は辞書の高さと一致し、沿辺で減少する。辞書本体を作らず、各段で最初の成功値だけを保持する実行版も同じ値を返す。忠実な表なら同条件で実 source の where accessibility にも同値で、独立 `Classify ... (.selected d)` に対して具体辞書ごとに正確。実 C277 の両行でこの対応と全モデルの evidence を照合した。この rank は raw 遷移に関する停止性ではない。
4. **同じ状態・同じ demand の成功辞書は、添字や表が違っても一致する。** 比較対象の両表が同じ独立 `Local` 判断に忠実であることが前提。根付き表では、実到達済みで停止した状態・選択に忠実な表・各行の `Current` 証跡から `Generated` と安定性を復元できる。全域について `Current` が自動的に見つかるとは仮定しない。根の成功経路だけを切り出しても同じ辞書を得る。非連結の循環を切り落とせる例は人工対照で、到達する欠損は切り落とせない。
5. **実際の深さ2の辞書は旧 rigid elaborator で照合した。** `Display (list (list int)) → Display (list int) → Display int` の候補と実際の where 順から表を計算し、旧 `RoleDictionaries.elaborate` の木 `0 → 0 → 1` と一致。先頭2節は同じ impl key でも別の demand。これは旧 rigid elaborator の実 Lean 実行であり、新しい V8 raw の深さ2の経路ではない。欠損・不足 fuel・循環は失敗または未解決として分け、意味上の拒否へ変換しない。

6. **V8 でも深さ2の実際の初期状態までは構成した。** 三つの slot で全モデルの型が入れ子リスト・リスト・int となる V8 の ground initial state を構成し、到達性とモデル実在を証明した。初期の候補 packet の計算は、隣接して異なる occurrence を slot 0 → 1 → 2 へ一つずつ出し、末端は子なし。二つの `Installable`（後者は一歩目の後の正確な snapshot）と packet 形を供給すれば、両ステップの novelty は記録済みの辺から導け、二歩の raw 経路・末端の正規生成・後のモデルの過去への保存が得られる。この二つの据付可否はまだ証明しておらず、この V8 例で二歩を実行したとは主張しない。

## 主な定理の適用条件

- `GeneralGeneratedDictionaryCoherent299.cross_table`: 任意の二表、二つの decode、fuel、添字について、同じ source 局所判断に忠実で、同じ demand を指し、両方成功したなら、順序・重複を含む辞書は等しい。
- `GeneralGeneratedDictionaryAcc299.iff_accessible`: 任意の表、閉性と既知行を仮定し、ある fuel での成功と表辺の accessibility は同値。`GeneralGeneratedDictionaryFiniteCap299.check_length`: 加えて全ての登録行を含む有限 domain に対し、長さを上限にした検査成功 iff domain の各行が既知かつ accessible。`GeneralGeneratedDictionaryRankBook299.book_ranked`: その domain の被覆と検査成功から、実装が返す最小値 rank は表の全子辺で厳密に減少する。
- `GeneralGeneratedSelectedExact299.bounded_exact`: 任意の忠実で閉じた表、全登録を含む有限 domain、登録済みの根の行、任意の辞書について、domain 長でその辞書を返すことと独立 `Classify ... (.selected d)` は同値。`no_result_iff` の不成功はこれら前提のもとで「有限の selected derivation がない」という意味に限り、意味上の拒否や曖昧性の分類ではない。
- `GeneralGeneratedDictionaryHeight299.height_threshold`: 任意の表・根で一度成功した辞書について、別 fuel でも同じ辞書を返す iff その辞書の高さ以上。`GeneralGeneratedDictionarySlice299.at_root` / `closed_slice`: 任意の成功した根について、訪れた添字への制限で同じ辞書が返り、制限表は閉じる。
- `GeneralGeneratedMixedRooted299.after_halt`: 任意の混合境界の到達済み停止状態、根付き表、忠実な観測、範囲内 `Current`、実際の読取り成功に対し、根の分類を構成し、同一状態の任意のモデルで辞書 evidence を構成する。各子 evidence と親 evidence は同じ最終モデルに対して組み立てる。各 effect の「据付可能な共通モデルが存在する」は別の条件で、それを辞書側のモデルと同一視しない。
- `GeneralGeneratedDisplayPhase299.genuine_phase_change`: 固定された実 C277 経路の一歩、全割当での raw `Models` 同値、初期の全モデル・全 payload での根 evidence 不在、据付後の任意の raw モデルの根 evidence を一つにまとめた。`GeneralGeneratedRigidCompile299.matches_elaboration`: 旧 rigid の固定 fixture で実候補から作った表の出力が既存 elaborator の木と一致。
- `GeneralGeneratedNestedInstallInterface299.cascade`: 固定した三 slot の初期例で、第一 packet が親、第二の focus が中央の子・出力先が末端で、各ステップでの二つの据付可否を仮定し、二歩の経路、末端の raw 生成と全モデルの巻き戻しを帰結する。初期の到達性自体は `GeneralGeneratedNestedInitial299.grounded_reachable` で無条件。

## 検証・未確認

- Lean 4.35.0、焦点を絞った分離再ビルドで **33 モジュール**。独立監査10本で **全 200 定理**を `--trust=0 -j 1 -M 3200 -DwarningAsError=true` で確認。新公理なし（標準の `propext`、`Classical.choice`、`Quot.sound` のみ許可）。旧監査28本、5つの実行出力のバイト一致、barrel 追記と固定 hash も検証。
- `bash tools/verify-lean.sh . <基点> --no-build` を前周と正確な統合木で実行。全文は [static/](../verification/cycle299/static/)・[実行コマンドと監査](../verification/cycle299/) に保存。前周の木 `b70c7db2915288719aff28cb278a2b129ed8c117`、再読した統合 `0d86f2ec35c2bcf6f122abe4ced6da1f3c376ef3` の木 `3b1a65e2f5714f6bbc0c3e537187ffad923c9f51`。最新 standing orders と inbox（I-54）は開始時から同じ。
- [旧 Yulang2 oracle の比較](https://github.com/momota1029/yulang/blob/55574b6052ef1534fd0fc36d6d3617ebede59a0e/notes/audit/x-oracle.md)では X1 の子 Display 使用を局所的に確認済み、X2 の増大 where は旧 lowering で挙動が異なる。本周に Rust、Yulang2、完全 Lake ビルドや CI は実行していない。仕様・既存 Lean kernel・Rust は変更なし。
- I-54 の到達範囲は、既存 scope の選択表の正確な読取り、実据付前後の evidence の差、同じ source/model の根付き有限表の再帰。任意の B4 source の observer/Current の完全性、raw 停止性、V8 の深さ2の具体的な raw 実行は未確認。意味論の選択は不要だったため質問ノートは追加なし。使用量枠は不明。

次の候補は (1) `GeneralGeneratedMixedRooted299.after_halt` に渡す `Providers` を任意の到達 source の選択へ広げられる条件の分解、(2) `GeneralGeneratedDictionaryFiniteCap299.check_length` の前提になる source domain 被覆を既存 observer 証跡から導く、(3) 三 slot の `cascade` に必要な二つの `Installable`、特に第一回の後の freshness・選択・共通モデルを確かめ、二段目の実 install と局所再読を検証、の順。選択子 rank を据付前相の raw rank と混同しない。

- 最終報告書の固定時刻: 2026-11-20T15:21:20Z（経過 50.07 分）。前周からの変更 86 ファイル（完了心拍・報告を含む）。
  書き込み後に固定 pin で報告と完了心拍を読み戻す。

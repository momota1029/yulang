この周に閉じた G の行: なし。G03 は、出力指定のない実 where の同入力類について、同じ raw graph で一つの内部 K2 と全原位置を保つところまで確認した。併合後の正規報告と一般の phase 接続は未完。残り19行。

# C452: 空の出力等式発行と、元位置をすべて保つ内部 K2

- 実開始: `2026-11-26T23:30:00.006Z`。実終了・経過は同じコミットの heartbeat。使用量の枠は不明。
- 作業開始時 I-83。終了時 I-84 / inbox `2090aabcfcbeaaf7a37f73fe6762109168047354`。作業時の正本 `integration/m1-final@76a9a16da8d6647ae9bb303f386bdbca44cb75c5`（C451 採用、Lean `27176957e463256bddbffcf8b4f60ca411bb5f6a`）。
- 技術 pin: `work/dots-main@a2b2f1b0119e7e9d9f7a3ff6ce87bc4415e4bfe6`、Lean `0f84913b1d969faf9f29ec1edcfb975f6886758b`。終了直前の正本 `integration/m1-final@0c1de4c59ec6e3cdb9026c377e3429c96f337895`、Lean `27176957e463256bddbffcf8b4f60ca411bb5f6a`。 この周の Lean の正本への統合は未確認。

## 新しい I-84 を確認

開始後に I-84（終了時の同じ inbox）を確認した。C451 の質問に対する決定は**利用者向け表示位置を今は決めない**こと。その代わり、併合需要の正確な報告には対応する全ての元 where の位置を宣言順のまま持たせ、報告にも witness にも代表位置を入れない。候補・K2・併合・拒否そのものは変更しない。公開の決定は `yulang3@a7ce840b4aee2c8706bfe3d459d3ea9e687ac47c` の spec §6.3（L264）でも確認した。本周の検証済み内部記録はこれに沿うが、I-84 の指示する併合後の正確な報告を累積 `check_full450` につなぐ Lean は未追加。後半で到着した指示を理由に未検証コードを出してはいない。質問ノートの再掲による再質問はしない。

## 元 source と実際の等式発行サブステップ

1. `WhereOutputPhase452`: `original_mark_has_exact_actual_source_site452` は任意の検査済み原 mark に対し、その元 where 番号にある実 `SourcePointAt` を復元する。書かれた節 ID、真の捕捉 center と元 request（実出現 path）が一致する。同 role・同 raw Alias 類の任意の二つについて、`each_emission_pair_is_authorized_and_writes_nothing452` は同じ FullState の全適合モデルで既存の `SameInputs` を示す。実 source site 二つに既存 `GeneralNominalDemandMerging.outputAtoms` をそのまま呼ぶ。両方とも元需要の出力指定が空なので、その発行バッチは空。
2. `WhereOutputPairRead452` / `WhereOutputBatch452`: ふたつの元番号だけで実 site を読んで検査済み同類の pair を再構成する。`actual_pairs_at_exact_original_ordinals_have_finite_read452` は任意のこの独立な pair をその元番号で同じものに再生する。`all_actual_pairs_are_in_verified_emission_batch452` は任意の実 pair が有限全元番号の検証バッチにあることを示す。`actual_complete_pair_batch_only_checks_real_same_input_and_writes_nothing452` により、そのバッチはすべて真の入力同一性を持ち、空行を普通の制約へ追記した結果は**元 raw と等しい**。等しいのは出力等式発行サブステップ。center の alignment、ドライバ全体、候補選びの順、非空出力の結果はここからは言えない。
3. `WhereInternalK2452`: `one_checked_entry_means_K2_at_every_original452` は各内部エントリに全元位置が原順序で入り、各元位置に実 root K2 があることを示す。逆向き `actual_cycle_has_exactly_one_internal_diagnostic452` は任意の実元 mark について、root K2 と唯一の該当内部エントリを対応づける。`checked_batch_internal_report_is_exactly_for_its_same_phase452` は実発行を適用した同じ raw graph でこの対応を使う。内部キーは表示位置でも診断コードでもない。`independent_scoped_internal_report_has_finite_replay452` はこの局所の独立な証拠から同じものを読む有限データを得る。
4. `WhereLiteralInternal452`: 新しい内部記録と旧 positional C450 trace は同じ復元データから併置できる。`source_cohorts_and_literal_report_replay_together452` は任意のこの局所 evidence の exact 再生、`any_literal_replay_preserves_original_scoped_report_meaning452` は元の完全な literal report、かつ同じ FullState の任意の適合モデルで旧 trace の意味が成り立つことを示す。旧 WhereForest は各元節を一つずつ持ち、短くしない。raw-safe な兄弟に実選択を与えるには別の真正な G02 leaf 証拠が必要。

## 実データと負例

- 同 role の元節 60・61 が元 path `[27,31,0]`・`[27,31,1]`、異なる本物の捕捉名 1・6 と flat Alias を持って両方実 K2。元節 62 (point 4) は別の raw-safe 類で、実 authored leaf を使って第三の子に選択結果を置く。実 source bundle を Lean で構築・compile し、recursive nominal と Bool の解釈を含む適合モデルを明示した。ソース文字列の parser/Rust を通したわけではない。元 literal 結果は三子 `[rejected, rejected, selected 88]`、内部 K2 は元 60・61 を持つ一件。第三の「安全」を選択で代用、誤った leaf、K2位置への leaf、旧昇格 checker への同 role 入力は通らない。
- 実 pair 0/1 を二つの source site へ戻して既存演算を実行。全 pair は `[(0,0),(0,1),(1,0),(1,1),(2,2)]`、発行0行、内部エントリ `[[60,61]]`。ラベルの改名でも同じ。別の真の類・範囲外番号・偽ラベル・古い Alias 証拠・親自身の K2 を対照にした。これは証拠 reader の失敗であって、言語の一般の不受理ではない。
- 非公開の補助検査は、同じ元親で別の独立な有効 wire を読んでも各内部エントリの全元位置が同じこと、C445 の実 typed append が base/raw を保存する範囲、一つの実モデルで値が等しい別二類が二件に留まること、適合する全安全 graph では none でなく空内部リストであること、同じ元識別子を二度参照しても二元 path が残ることを確認。加えて、非 cyclic の元子を全部残しても cyclic 類の一つに二元位置があれば旧 forest の子数より少なくなること、実 outputAtoms について各同名先が元から有向 Bound 双方向なら raw K2 を移せることを局所検査した。後者はその十分条件であり、値同値や一般遷移の主張ではない。以下の公開検査数には含めない。

## 検証と残り

公式 Lean 4.35.0 `--trust=0 -DwarningAsError=true`。公開の exact 5 production / 7 standalone Audit を focused 検証、公開 Git ref の12ファイルを取り直した作業者の同条件再生も全て exit 0。監査 29 件は標準公理のみ（または公理なし）。guarded `#eval` は実行対照 2 件で、定理の証明には使っていない。Audit の import: Yulang.* 以外 0 件。継承 C449 ListFrameSpec / C450 WhereGuardSpec / C451 CohortGroupsActual の実入口も exact 取り直し版で exit 0。既存 7748 production / 2152 Audit blobs、凍結 Lean ファイルの ID は不変。集約は5 import追記だけ。今回の変更は Lean 13パス、design 1、heartbeat 1、この報告 1。全体 build・verify-lean.sh・Rust は実行していない。累積入口・過去の witness Bool・spec は変更なし。

次の候補: (i) 実 outputful/compound source の同じ where 出現・発行段階に対する独立な接続（G15–16 は今回着手しない）、(ii) 実 ordinary を変えた段階では exact raw の再読、または元グラフ保存の別証明。モデル集合の保存だけで K2 を移さない。(iii) `notes/questions/dots-cycle-451-g03-merged-k2-location.md` への回答は I-84（表示だけを遅延／内部に全原位置）。質問の追加はなし。残作業は、全元位置を持つ新しい正確な併合報告を、旧分岐の全入力 Bool を保った単一の累積入口に接続すること。内部記録でも言語の意味や既存の判定を変えない。G03 は未完、残り19行。G04、一般の診断完全性、NoFalseRejection は対象外。

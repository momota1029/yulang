# dots cycle 296: 有限の名前観測から選択 role の証跡を作る

## 再開と範囲

2026-11-20 11:30:00 UTC 開始。統合版
`9473ae40eefdbb76016a520751669d6c970a90a2` の standing orders → inbox
を読み直した（ACTIVE、I-51〜53）。同じ tree のローカル祖先を確認。
前周の公開 `eb56f968fa4b64a02bb4d824665f50784fef7204` の完了心拍と報告を
照合して開始し、別 writer の稼働を示す状況はなかった。Yulang2 の固定監査は再読したが、
今回の Lean 連携を Yulang2 実走で確認したとは扱わない。
`work/dots-main` のみ、以前の head と tree を照合した非強制更新と、途中心拍・再読を実施。

## 結果

- **全域の名前表を渡さず、有限の観測表から選択 role を既存の Lean exporter に渡せる。**
  role 名、role ID で限定した出力名、nullary constructor 名は別々のキー。
  未観測・観測済みの不存在・観測済み ID・複数観測を区別した。必要なキーの複数観測は
  値が同じ重複でも拒否し、一件目を勝手に採らない。一方、使用されないキーの競合で
  選択済みの宣言を失敗させない。error は必要な問い合わせ順の最初の欠落または曖昧性を示す。
  「名前が存在しない」と観測済みなら旧 exporter 側の拒否であり、まだ何も観測していない
  場合の拒否とは別。必須の関連型が default term を持たないことも別で、その名前には ID がある。
- **保存済み Rust CST を有限入力で実行再演。**
  raw role `a` は元の `[0]` で method のみ。
  呼出側が **別に与えた** 一行 `a → 7` と保存済み回復範囲 `49..58`
  を使い、arity 1・関連型出力なしの旧 table を Lean で作成。
  選択した symbolic role とその table を逆変換すると、一行の観測表に戻る。
  空表、`a → null`、競合、選択を別の位置へ移した場合はそれぞれ拒否された。
- **既知の lowering の証跡を逆抽出し、最小の観測表で再実行。**
  支持するのは C295 で選択した required/binder/nullary 断片。
  binder の位置違い、非 nullary の構成子値、同じ constructor 名への異なる ID を拒否。
  同一 constructor を二度読む場合は観測表を一件にできるが、実際の問い合わせ trace は二回を保つ。
  成功した同じ選択・同じ旧 table を生む観測表は、すべてこの最小観測表の行を含む。
  合成二宣言を対象に旧 `assocOf` の実行を再演し、`[0]` は `int`、`[2]` は `char`。
  逆抽出で無関係な行を除き、table と trace を同一のまま再実行した。
- **検証用の JSON で重複と型を保存。**
  version 付き配列なので同名キーの行が JSON object の上書きに消えない。
  別名前空間のキー、ID の誤った型、バージョン・形式違いを拒否する。
  行順を入れ替えても検査結果と必要な trace の順序は変わらない。
  これは Lean の検証用 schema で、Rust 本番用 schema の変更ではない。
- **発行した証跡の再利用を同じ選択に限定。**
  元 wire・address・scope・policy・別途与えた環境の版・fallback arity が一致するときだけ再検査。
  同じ wire でも版や選択が違えば拒否する。診断 receipt が取れなければ同じ版でも拒否。
  版や観測の正しさをこの一致チェックが認証するわけではない。
  [反例](../verification/cycle296/issuer-authority.txt) では、同じ保存 wire、位置と版 41 に
  別々に数値 7 と 8 を入力すると、どちらも形式上は通る。両方を同じ観測表に入れると競合で
  拒否される。値の一致検査だけでは、どちらの ID が実際の名前解決結果かは決まらない。

## 定理と受け入れ範囲

[全 93 定理の正確な型](../verification/cycle296/theorem-index.md) に前提と量化子を記録。
以下は有限の手渡しの健全性・完全性と補助であり、M1 の一般型推論・主型性の証明ではない。

- `known_exact` / `empty_exact` / `ambiguous_exact` / `require_exact` /
  `first_failure`: 任意の見出し付き有限観測表と必要キー列について、値の確定は
  対応する fiber が一件であることと同値。成功は全必要キーへの一意の観測と既存
  capture に一致する。失敗の前にある問い合わせはすべて支持されている。
- `agrees_replays` / `run_exact`（選択された producer/consumer の対応）:
  選択と有限 lowering が成功した場合、その trace/table は独立した全域環境に対しても、
  実際に使用するキーで一致することと同値に C295 で再演できる。使用しない値は仮定しない。
- `recover_from_existing_lowerer` / `recovered_catalog_relowers` /
  `selected_old_table_inverts` / `extracted_table_replays`（往復）:
  既存の成功と一致する symbolic role・順序付き old row からは元の局所 trace が復元できる。
  復元の成功を仮定すれば、その有限環境から同じ row を得る。同一の選択・table は
  使用した trace を決めるが、table 自体の意味的な真正性は別。
- `trace_does_not_invent_row` / `trim_preserves_full_export` /
  `least_among_same_selected_table`: 成功した trace に含む行は必ず元の観測表にある。
  その重複だけをまとめた表で同一の trace/table を再現する。
  同一の選択と値の同じ成功 table を与える別の表はこの最小表を行として含む。
- `catalog_exact` / `text_exact` / `run_perm`: JSON 値が正確な version と
  必須の行形式を持つときだけ有限観測表が取れ、配列順・重複は復号で保持する。
  行の順序を入れ替えた表で結果を変えないことは、復号とは別に証明した。
- `issued_replays_exact` / `changed_revision_rejected` /
  `success_has_no_absent_replies`: 成功結果から発行した観測表は同じ選択・環境版・
  fallback と独立の診断条件で再演し、必要観測に `none` は含まれない。
  観測済みの不存在と必須 default の不存在は等しくない。

## 検証

- Lean 4.35.0、`--trust=0 -j 1 -M 3200 -DwarningAsError=true`。
  今回の追加 OLean を除いた影 cache から **27 モジュール**を直列で再構築。
  6 standalone audit の全 93 定理と、既存 C295 および境界 C294 の 13 audit を確認。
  新設の全 import を barrel に追記し、[まとめた import の点検](../verification/cycle296/barrel-dependencies.txt) と
  [個別 Lake 検証・旧 CLI の出力照合](../verification/cycle296/standalone-lake.txt)も独立に実施。
  [ソースの SHA-256 一覧](../verification/cycle296/source-sha256.txt)。
  公理は `propext`、`Classical.choice`、`Quot.sound` の範囲。
  [再現手順](../verification/cycle296/README.md) / [再構築と再演の全文](../verification/cycle296/focused-replay.txt)。
- 統合版から [Rust テスト原文](../verification/cycle296/github-rust-source.txt) を取得し、
  byte 照合後に保存 JSON を再抽出し、[独立な範囲確認](../verification/cycle296/independent-archived-source.txt)。
  3本の保存済み CST 再演と2本の合成 Lean 再演を行い
  出力一致を確認。合成例での `assocOf` は実行したが、Rust による解析は一度も行っていない。
- `tools/verify-lean.sh . <base> --no-build` は前周・統合版の双方で exit 0
  ([静的検査全文](../verification/cycle296/static-diff.txt))。全体 Lake ビルド・全体監査は
  standing orders に従い未実行。既存 Lean 本体、Rust、spec、lakefile、inbox は変更なし。

## 未確認事項と次の候補

接続できる環境では Rust toolchain を確認できなかった。関連型を持つ本物の CST の新規実走、
ランタイムの診断完全性、真正な環境の版・authority、実際の名前の由来は未確認。
今回の期間に、仕様変更を決める必要はなく、質問ノートは追加していない。使用枠は不明。

候補は (1) 実行できる Rust 環境で、同一 retained parse の実 CST と fallible diagnostics を取る、
(2) 独立した名前決定元が渡す観測を、その実際の namespace と版に従って照合する、
(3) 名前の曖昧性や後続 solver の selected 候補を観測できても、旧 kernel の一般停止性や
型推論の完成をそこから主張しない。

- 最終報告書の時刻: 2026-11-20T12:20:04Z、経過 50.07 分。前周からの変更 65 ファイル
  （この報告と完了心拍を含む）。完了書き込み後に再読出しで照合する。

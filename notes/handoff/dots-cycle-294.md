# dots cycle 294: 保存済み Rowan CST の回復位置と診断を混同しない

## 読んだもの・再開

2026-11-20 09:30:01 UTC に開始。GitHub の `integration/m1-final`
`adf9fae11d8e29273a28751089db2499bcf205d2` で standing orders、inbox
（ACTIVE、I-51〜53）、Yulang2 監査の親固定メモを読み直した。
`work/dots-main` の 293 完了 `9473ae40eefdbb76016a520751669d6c970a90a2`
と対応報告を確認。前回の中断なし、他の writer の lease/作業なし。
公開は `work/dots-main` のみ、毎回以前の head と tree を照合し非強制更新。
UTC の開始心拍と途中心拍を残した。

## 成果: 一つの選択 role の切出しと、ファイルを無回復と呼ぶことは別

- **実際の保存済み role fixture**（Rust の既存テストから抽出）:
  293 が切り出した未解決 role `a` は混合 child path `[0]`。
  Rust テストは構造的回復を **1 件**、`49..58` と記録している。
  wire には別々の Error token が **3 個**、`[1]` `49..50`、
  `[2]` `50..51`、`[3]` `51..58`。選択枝のみの検査は role を返すが、
  全 wire 検査は返さない。原始の 3 行を消したり、診断 3 件と数えたりしない。
  独立に提供した `49..58` は、非空 Error token だけの一意な run に対応し、
  3 行がすべて `[0]` の外側。範囲が短い、receipt がない／異なる brand、
  存在しない第二診断 path `[999]` のケースは拒否した。
- **同一範囲でも回復の所属は別**: 保存済み Rust `case` fixture に
  Missing node `[0,0,1,0,0]` と `[0,0,2,0]` がいずれも `4..4`。
  `[0,0,1]` を焦点にすると一方はその内部、他方は無関係。範囲だけでは判定不可。
  Missing receipt は実際の path と幅 0 の厳密な範囲、元ラベル・node 区別を要求する。
  保存済み Rust `for x in xs: @` は別の正例。`[0,0,9,0]` の Error token
  `13..14` を実証し、同一構文内の pattern 枝外として分類した。これら二例は role ではない。
- **Rust の診断と構造印も別**: 統合版 `full_parse.rs` の
  `ConflictingOperatorFixity` は環境／演算子定義の検査からも生じる。
  `structural_diagnostic.rs` の opaque `NestingTooDeep`、直接子の Error token
  を抑制する Error node、空 Error token を拒否する分岐も原文で確認。
  token run の範囲一致だけではこれらを plain token recovery と同定できない。
  より狭い確認では該当する三例を退ける。fixture との対応は Rust を新規実行せず、
  保存値と独立に記録された Rust 側の期待値を突き合わせた。
  なお深さ制限の場合、原文上は node 自体の範囲なのに診断 identity の path は
  末尾に 0 を追加する。[原文の照合](../verification/cycle294/retained-origin.txt) の通り、
  実在 path かだけではその診断の所有 node は決まらない。
- **同一 wire の照合**: receipt の brand だけでなく元 wire を正確に比較する任意の
  段を追加。保存済み role fixture の末尾 Newline を Whitespace に変えても
  compact tree と元の選択 gate は同じだが、元 wire と組にした receipt は再利用を拒否。
  一致そのものは診断一覧の完全性や、解析環境の同一性を認証しない。

## 定理と適用範囲

全定理の型（量化子・前提含む）と正確なファイルは
[完全な型一覧](../verification/cycle294/theorem-index.md)。
Lean の追加は `GeneralSourceRoleCst*294` の 35 モジュールと standalone 11 監査。
すべて同じ変更で `lean/Yulang.lean` に一度ずつ追記した。

- `marks_exact`, `entry_exact`, `original_exact`, `original_same_paths`,
  `original_paths_nodup`: 任意の有限混合-tree の path と kind について、
  原始印はその path が実際に非 plain 要素を指すことと同値。
  範囲は token の UTF-8 byte 幅から計算する。正確な `Transfer` があれば、
  原ラベルの復元後も元の path 順序・件数を保持し、path に重複なし。
  同一範囲の異なる node は残す。Rust 診断数に関する主張ではない。
- `selected_exact`, `ancestor_exact`, `unrelated_exact`,
  `guarded_exact`, `exact_corridor`: 任意の選択 path で raw prefix により
  選択先・厳密祖先・無関係を区別する。293 の wrapped role 射影成功を仮定すると、
  射影が指す subtree に印はなく、選択枝用 gate が追加で要求するのは祖先上の無印。
  その gate は元の未解決 payload をそのまま返す。無印でも選択 path や brand の
  正しさを保証しない。
- `runs_flatten`, `every_run`, `no_bridge_across_runs`, `unique_exact`,
  `origin_for_each`, `visible_range_exact`: 任意の原始印列を整形しても
  平坦化すれば元の列に戻る。結合は元ラベルが Error の token、同じ親、連続混合
  ordinal と接続 byte 範囲の場合だけで、隣接 group をこれ以上結合できない。
  外部範囲が 1 行の run に一致する時だけ受理し、正確な `Transfer` の下で各元 token
  を照合できる。強化 gate は Root からの見える経路・非空 token も条件とする。
  これは Rust の全構造診断 walk の一般的同値性ではない。
- `grounded_exact`, `export_exact`, `project_exact`, `whole_to_selected`,
  `use_bound_exact`: 任意の packet について、成功には同 brand の報告、
  すべての要素の scope 条件、wire 側の policy、既存の射影成功が必要十分。
  一般の owner は実際の混合 path でなければならない。範囲は一意の token
  run で確認する。全体 gate は報告済みの空リストを要求し、成功なら同一 payload の
  選択 gate も成功する。非認証の packet は本物の完全な診断に代用できない。
- `verified_names_original_missing`, `no_extent_only_decider`:
  任意の検証済み Missing anchor は元 wire の Missing node を指す。
  同じ範囲に scope が異なる anchor が 2 個あるなら、その範囲だけから全検証済み
  anchor の scope を決める関数は存在しない。
- `branch_descends`, `visible_range_descends`, `reported_scope_descends`:
  任意の path prefix の下で、既に外側である印・外部範囲・診断 receipt
  の外側性を保つ。焦点の変更で新しい role を作る定理ではない。

## 検証

- Lean 4.35.0、`--trust=0 -M 3200 -DwarningAsError=true`。
  [再現コマンド](../verification/cycle294/verify-focused.sh) は既存依存の
  OLean を再利用するが、今回追加の OLean をすべて除いた影キャッシュから
  35 モジュールを再構築し、今回 11 standalone 監査の全 140 定理と 293 の
  9 standalone 監査を確認する。[実行出力全文](../verification/cycle294/focused-replay.txt)。
  公理は `propext`・`Classical.choice`・`Quot.sound` の範囲内。
  [個別 lake 監査](../verification/cycle294/standalone-lake.txt) でも 11 本すべて exit 0。
  [証明・監査・再演のソース照合](../verification/cycle294/source-sha256.txt) も実施。
- 三つの保存済み Rust ソースを byte partition 付きで再抽出。
  実際の保存 fixture と人工境界を合わせた 12 レポートを独立の Python 混合
  walk と照合し、異常入力 4 件を拒否した。各 archived replay の出力を byte 比較。
  GitHub の統合 pin から取得した関連 Rust ファイル 5 本の
  [byte 一致](../verification/cycle294/github-rust-sources.txt) を確認。
- `bash tools/verify-lean.sh . <base> --no-build` は前 293 版と統合版 base の両方で
  exit 0。この二つの [静的検査全文](../verification/cycle294/static-diff.txt) は
  standalone ビルドとは別。大規模な全体 Lake ビルドや全体監査は standing orders
  に従い実施していない。旧 Lean 本体、Rust、spec、lake 設定、監査 main に変更なし。

## 未検証・次に進めること

Rust の新規実行・本番 serializer、実行時の真正な snapshot/診断の完全性・環境の
照合、診断 identity をそのまま raw path として使うこと、名前解決・型照合・raw
kernel の実行、一般停止性は扱っていない。環境に Rust toolchain がなく、
保存フィクスチャの再演と Lean 実行を明確に分けた。言語の受理規則の判断は変更せず、
質問ノートは追加していない。

次は (1) Rust が使える場合に、同じ retained Rowan から mixed child path、source
environment と完全診断をいっしょに取得する production bridge と実走を先に行う、
(2) opaque/node-owned 診断の raw path attachment を token run と分離して実例で確認、
(3) それらを解決済み declaration-ID の既存 producer 検証へ接続し、未解決文字列の
まま成功を主張しない。新しい意味論や一般停止性の結論はこの報告から出ない。

- 最終報告書の時刻: 2026-11-20T10:20:05Z、経過 50.07 分。前周からの変更 94 ファイル
  （この報告と完了心拍を含む）。完了書き込み後に再読出しで照合する。

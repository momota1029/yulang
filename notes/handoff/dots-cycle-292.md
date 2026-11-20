# dots-main cycle 292: 実 CST の境界、role 宣言の既定値と既存 resolver の接続

## 結果

前周は「解決済みの数値 ID の表」から始めていた。今回は、**所有を区別した
小さな構文形から role 表を組み、既存 Lean resolver が既定値を読むところまで**
を検証した。ケースは source 名前が平らな一つの名前空間、順序つき単純 binder、
bodyless required／単一 binder 参照／引数なし型名の default に限定。
**Rust パーサがその入力を自動生成する実装はない。Rust のパース、Rust 名解決、
構文・仕様、旧 kernel、停止性は変えていない。**

### 1. 実装の静的な追跡と、CST からは得られない情報

- 統合 tree と同一 blob の `full_parse.rs` と declaration parser を追った。
  実 `parse_file` は `ParsedFile` と Rowan CST を作る。role head は普通の
  `TypeExpression`。role の直下に書いた `type value` は普通の
  `TypeDeclaration` で、専用の関連型ノードではない。role 本体の所有と
  直下の statement 列を失うと、外側・入れ子の普通の型宣言を区別できない。
  親へのアクセスだけでなく直接性を証拠に残す必要がある。
- `SourceNodeKey` の等値は parse brand、green allocation、開始位置。
  既存の Rust テストは同一の green root でも別 brand の key は違うと期待し、
  同一 brand・同一開始位置・共有の空 green では異なる子位置の key が一致する
  内部構成も持つ。この後者は特殊な内部構成で、特定の source で再現するとは
  言っていない。Rust の `try_structural_recoveries` には path と ordinal がある。
  key／range を stable な semantic ID とみなさず、必要な occurrence は位置でも保持する。
- 既存の活性 Cargo workspace は syntax/recovery/xtask。今回の役割・関連名・型
  コンストラクタの numeric ID は、CST からは得ず独立の環境に渡す。
  `Fixture292.no_universal_source_role_id` と
  `SyntaxFixture292.no_environment_free_table` は、この限定 fragment の
  同一 shell（required/default と binder 順序も同一）が、どちらも受理する
  二つの供給環境のもとでは異なる ID と読み値を持つ閉じた反証（補助）。
  決定的な resolver が自身の ID を一つ選べない、という主張ではない。
- `Qualification292.leading_same_spelling_not_accepted` は、同じ短い名前の
  二宣言が先頭にある**任意の**入力末尾・環境について、同じ role ID にしか
  ならず一意性検査を通らない。異なる scope の同綴り名を扱う拡張には独立の
  qualified evidence が必要。Yulang が同名の多重定義を認めるという決定は
  していない。一方 role が異なれば同じ出力番号 2 を共有しても、役割別
  lookup の実行例では required と default を別々に読める（補助）。

### 2. 所有・宣言・有限 manifest（健全性／完全性）

- `Spelling292.position_exact` は任意の綴り・binder 列・番号で、先頭一致を
  飛ばさない帰納的な位置判断と実 lookup の iff。
  `BinderIndex292.index_exact` は binder 列に重複がないとき、同判断が
  独立な `binders[slot]?` と iff。重複した綴りの第 2 位置を単なる位置読み
  で誤って有効化できない閉じた例も確認した。
  `body_exact/body_scoped` は任意の環境・binder 列・body について、
  required、scope 内の位置参照、名前環境に載る nullary の判断との iff と
  `Term.bound ≤ binder count`。不存在は required に変換しない。
- `SyntaxBoundary292.projection_exact/projectRole_exact` は任意の shell
  について、所有が direct role で、recovery が無く、bare なら Equals/RHS が
  共に無く、default なら実 Equals と対応 RHS が揃う 3 ケースに限る iff。
  Equals 付きの欠けた RHS と、Equals 無しの読めそうな RHS はどちらも
  required にならない。これらは Rust ノードそのものではなく有限 hand-off。
- `ChildCoverage292.scan_exact/member_exact/ordered_members` は任意の
  **与えられた**直接 statement 列について、既知の非 type のみを飛ばし、
  型宣言を順序どおり全て持ち越し、unknown を一つでも含めば失敗する。
  `CoveredShell292.verify_exact/every_direct_type/run_exact` は独立に与えた
  完全列と shell の対応を検査する。既知の子一つを shell から落とすと
  生の shell だけなら成功するが、完全列との照合では失敗する。
  この検査だけでは、供給者が CST の子を先に落としていないとは証明できない。
- `Export292.output_exact/role_exact/lower_exact` は任意の環境・入力列・
  出力表について、対応する全 role/出力名、scope、順序、重複なし、
  fallback arity を含む関係との iff。`Pipeline292.pipeline_exact` がこれを
  形から合成。`Manifest292.manifest_exact` は任意の受理表と default について
  manifest 所属と名前／本体つき source の存在が iff。
  `AssocRead292.assoc_exact/required_exact/undeclared_exact` は受理表の
  三値それぞれを必要十分に読み戻す。required は `some none`、
  undeclared は `none`。実行例で `'key` 単独 default は第 2 引数で、
  binder 順を反転すると読み番号が 1 から 0 になることも独立に確かめた。

- 完全候補の head について `HeadShape292.head_exact/args_length/packet_exact`
  は任意の supplied head で、単純 primary と既知の bare binder **全引数**が
  順序・個数そのままでなければ export しないことを示す。既存 Rust parser の
  テストにある `role F (A->B) 't;` などは Rust 側が ordinary 型として読めても、
  この adapter のみに渡す際は arrow などを飛ばさず対応外とする。
- `ScopedExport292.lower_exact` は任意の scope carrier／独立供給環境、
  入口の scope 付き role 列、出力表について、scope 別 lookup と**全体**の
  ID 一意性を含む iff。 `ScopedShell292.source_scope_exact` は任意の
  成功した scope付き完全直接列で、required/default の読み値と同じ scope
  付きの直接宣言の存在が iff。`UniqueSource292.unique_packet/unique_packet_member`
  は同じ role／role-local output ID に解決する受理入力のデータが一致することを示す。
  実 CST の span やブランドの同定はしていない。
  同じ短い綴りの二 role を、独立の scope と異なる ID で与える補助対照は通る。
  独立の scope でも同一 semantic ID を供給すると通らない。
- `ArityRead292.present_exact/absent_exact` は任意の成功した表の
  key/arity の lookup と scope 付き source 宣言の存在が iff。absent の
  `roleTable` が fallback arity を返すことと実宣言を分けた。
  `HeadPacketRun292.assoc_exact` は任意の supplied head/body 列で、表の
  役割・関連項と exact な scope、head/binder 順、直接子、名前解決、本体の
  組を必要十分に接続する。既存旧 `Index str int` の実 fixture に対する
  同じ `assocOf` が `int` を読むことを、
  `HeadPacketFixture292.complete_packet_actual_old_consumer` で同一表から再証明。

- `Track292.tracked_readback_exact` は任意の scope/handle 型と受理済み
  tracked 入力について、関連項が読める iff **供給済みの** role handle と
  type statement handle の実メンバーつき証人があることを示す。ハンドルは semantic
  ID として使わない。閉じた例では正しい直接型宣言ラベル 102 を読めるが、
  非型の 101 からは読めない。ラベルを移動しても旧実 resolver が `int` を読む
  表は同一。記録された位置が実 Rust 側の位置であるという attachment は別途必要。

### 3. 環境の正確な添付と診断（健全性／完全性／補助）

- `EnvCheck292.shell_check_exact/shell_check_sound` は有限 shell に対し、
  到達する role・その出力名・出力 lookup 成功時の nullary 名を照合し、
  同じ compile result を保証する。関数表の全域同一性は主張しない。
  `EnvExact292.at_success_exact/shell_at_success_exact` は固定された元環境で
  成功した結果に対し、他環境が**同じ受理表**を出す iff この照合が真であることを
  証明。二環境がともに失敗する場合の逆は偽。未読の綴りの変更は通り、
  読まれる `char` の更新は照合で落ち、出力名同士の同一 ID は重複で落ちる。
- `Attach292.assemble_exact/ready_attached` は組立済み表と独立に添付された
  全 constructor／interpretation 表、role 関数、宣言列について、前周の
  readiness と旧 Metadata・Coverage 等の条件をそのまま保つ。
  `ActualAttach292.exact_actual_bundle` は手で与えた role shell と数値 map が
  既存の二つの Lean fixture の全 role 表および bundle に正確に一致することを
  証明した。片方の readiness が false なのは元の材料化範囲の差で、パースや言語の
  拒否ではない。
- `DiagnosticLink292.default_issue_exact` は任意の組立成功と role-default
  診断について、旧 constructor 使用診断の理由に加え、供給 shell の所有済み形・
  role と出力名・下げた RHS での当該 use の存在に正確に対応する。
  既存 fixture に**別の**未使用 role 17 を加える閉じた診断対照では、
  constructor 6 の 0 引数適用に `wrongArity 1` が出る。行を意図的に
  省くとその別表の readiness は true だが、完全表と role map が同一では
  なく、完全表への添付はできない。変更した表は旧実 fixture の raw 状態ではない。

### 4. 変更しない実 Lean resolver による readback（既定値の健全性／完全性）

- `ResolverUse292.selected_omitted_exact` は任意の受理済み shell 表、既存
  `Roles.AssocEnv`、well-formed な候補入力、既に resolved で一意選択された
  impl、そこで未記載の出力名について、旧 `Roles.assocOf` が値を与える iff
  source shell に対応する default 本体があり、それを goal の位置引数で
  代入した値に等しい。explicit なら同じ古い head 代入による値が優先し、
  default は読まないことを `selected_explicit_independent` で分けた。
  `supplied_positional` は引数数一致のときに out-of-range fallback なしで
  位置の値を返す。選択そのものを発明／再証明したものではない。
- 既存 `Roles.AssocExamples` の実 impl と goal `Index str int` をそのまま
  使った閉じたケース: `type value = 'key` を省略 impl に使うと `int`、
  明示 `char` があれば上書きされ、`char` の default も省略時に使われる。
  required を省略する対照は読出し `none` かつ既存
  `AssocWellFormed` を満たさない。正例の省略 impl は既存
  `AssocWellFormed` も証明。 `OperationalRead292.resolved_declared_has_compiled_value`
  は同条件のもとで既存の値の存在と goal に無い変数を持ち出さない主張を再利用。
  omitted reader の `Option.join` は required と undeclared を同じ値なしに
  写すが、これは両者が宣言として等しいという意味ではない。
- `RawAttach292.exact_registry_readback/same_existing_step` は別の旧一般
  fixture に**同一の Registry を再添付**し、既存 raw Step をそのまま再利用。
  `same_existing_strict_release` は元の到達経路を前提に前周と同じ厳密な範囲
  （true 側、既存状態、元 receipt・mark）での読出しを移した。false 側でも
  parent install は既に起こる。新規 raw 状態・遷移、K2 全体・停止性・主型性の
  結果はない。

## Yulang2 との照合

`work/dots-audit` の pin `55574b6052ef1534fd0fc36d6d3617ebede59a0e`。
`notes/audit/runtime-cycle-3-parent-fixed.md` は legacy
`Produce` に required の `type value` と実装側 `type value = int` を持つ
 既存成功例。旧実機が出力を使うことは確認済みだが、省略 default・位置 binder
 の今回の組合せそのものの Yulang2 新規実機結果ではない。
 `y2-claims-casts-roles.md` の Y2-ROLE-003 も関連型の更新の既存位置づけの参考まで。
 `default-effect-boundary-cycle-2.md` は record pattern の default で別機構。
 今回の規範は現行 `spec/06-roles.md` §6.1 と既存 Lean の
 `RoleDecl.defaultsScoped`／`assocOf`。Yulang2 を互換仕様として採用していない。

## 検証と再現

- Lean 4.35.0、`lake env lean --trust=0 -M 3200 -DwarningAsError=true`。
  この周の focused **36 modules**、**13 standalone audit**、監査名 **138 宣言**
  を完全一致で確認。監査で現れたのは `Classical.choice`、`Quot.sound`、
  `propext` のみ。新しい未証明仮定なし。モジュール内の実行可能 guard は 16。
  新規 module は全て同一変更で barrel の末尾に import、既存部分は byte-identical。
  [focused 出力全文](../verification/cycle292/focused.txt)。
- 旧 cache だけを複製して今周の全 olean を一旦外した環境で、実際の import
  DAG 順に 36/36 を再構築し、13 監査を単独実行。普段の focused と全追加
  olean の SHA-256 が個別一致。最初の隔離 runner は barrel の文字順を仮定し
  未構築依存で失敗したため、実依存順に直した。この初期失敗は結果に含めていない。
  [隔離出力](../verification/cycle292/isolated.txt)、
  [一致検査](../verification/cycle292/olean-sha256.txt)。
- `bash tools/verify-lean.sh . <base> --no-build` を前周同一 tree と、統合枝
  pin `f02834cb166c3fd127f2b2a2893362062c0d6ae6` と同一 tree のローカル祖先
  に対して実行し、ともに exit 0。追加 REVIEW なし。
  [コマンドと出力全文](../verification/cycle292/static.txt)。
  旧 55 件の絞った単独監査（前周 9 を含む）も exit 0。
  [旧回帰](../verification/cycle292/existing.txt)。
- [型の表示](../verification/cycle292/interface.txt) と
  [実行結果](../verification/cycle292/smoke.txt)。
  元二枝 `[some true, some false]`、新しい独立診断の role 17 と `wrongArity 1`、
  位置 1/0 の差、別 scope での二つの型 ID、旧 reader の
  `[some int,some char,some char,none]` を確認。対応のない head が一引数に
  短縮されず失敗することも実行。再現用の小さい [focused script](../verification/cycle292/reproduce-focused.sh)
  は既存依存 cache と前周 SHA を指定する。途中の34モジュール版では exit 0、
  最終版での追加の再実行は時間切れ（exit 124）。上記の最終版 focused・隔離・監査
  はそれとは別に 36 モジュールで完走済み。
- 全体の `lake build` や全体検証は実施せず。全 barrel の dependency-only
  診断では、前周版と今回版双方が同じ既存 `SpecExamples.olean` 不足で
  exit 1。旧 root 2 モジュールへ絞った準備も既存依存の cache 不足だったので、
  旧大規模グラフを再構築せず切り上げた。**既存行を除いた正確な追記部分**は
  `lean --deps` が exit 0 で 36/36 を解決した。
  [分離検査](../verification/cycle292/barrel-dependencies.txt)。
- [実 Rust の静的ソース追跡](../verification/cycle292/parser-boundary-source-trace.txt)。
  この環境に `cargo`／`rustc` が無く、実 Rust parser 実行、既存 Rust テストの再実行、
  Rust の scope/name resolver は検証していない。Yulang2 の実行も前述の既存記録のみ。
  使用量の枠は不明。承認待ち、別 branch の更新、新規 source 言語の設計判断なし。
  復旧なし。前周の完了心拍と報告、両 remote tree、単独 writer を確認した。

## 次の一手（候補）

1. Rust が使える場所で `parse_file` の bodyless・scalar default・positional default・
   malformed RHS を実録し、実 `SourceNode`／structural path に基づく producer を
   試作できる範囲を切る。最初は独立の source role 1 件で、bare/equals だけを
   比較する。parser/syntax の変更は主張せず、owner / direct member の完全列を先に検査。
2. `HeadPacketRun292` / `Track292` の入力に、実 resolver の scope と名前対応を独立
   添付する。現 active Rust にはその段階が無いので、source から numeric ID を発明しない。
3. 旧 raw work の独立の局所課題を取るなら、支持される通常の引数で本当に独立な
   row read を探す。今回の source export は一般停止性や K2 完了の証拠ではない。

質問ノートは積んでいない。実装の境界と技術的な入力義務は
[設計ノート](../design/2026-11-20-cycle292-parser-boundary.md)に残した。

- 最終報告書の時刻: 2026-11-20T08:23:36Z、経過 50.03 分。前周からの変更 78 ファイル
  （この報告と完了心拍を含む）。完了書き込み後に再読出しで照合する。

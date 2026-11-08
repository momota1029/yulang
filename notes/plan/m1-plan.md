# M1 計画表 (2026-11-08 作成)

運用は [README.md](README.md)。共通の前提（すべてのタスクで先に読む）:
`notes/handoff/2026-11-08-chatgpt-prompt-m1-recovery.md`（決定の一覧）、
`notes/handoff/2026-11-08-m1-spec-examples-conformance.md`（適合例 X1〜X24）、
`notes/handoff/2026-11-07-m1-completion-contract.md`（E1/E2。E2 は終わりではない）、
`spec/06-roles.md` 6.3〜6.5、`spec/04-types.md` 4.3・4.6、`notes/design/2026-11-08-research-harness.md`。
検証コマンド: `tools/verify-lean.sh <repo-dir> origin/integration/m1-final`（PASS、REVIEW は人が読む）。

## 現在地（2026-11-08 15:30）

- `integration/m1-final` 先頭 `6b37e906d`。ビルド 1108 jobs、Audit 通過。
- B4: 狭い断片（既知の区間の両端が等しいもの）で、局所判断の exactness と accessibility を証明済み（Astra）。X6・X8〜X12 は外側の単一の入口を通って PROVED。開いた区間（lower ≠ upper）は未着手。
- B5: variance の導出表と cast の費用上界は証明済み（Pro）。full nominal carrier の接続は未着手。
- X22（optional field の照合）は主の生成器と食い違う（MISMATCH）。
- 適合例の表が 2 か所に分かれている（`lean/SpecExamples.lean` と `lean/SpecExamplesSettled.lean`）。

## タスク

### T1 開いた区間への拡張 (B4)
- 状態: partial（2026-11-08 16:40、dots が実施。`work/dots-T1` を統合。verify-lean.sh PASS、1125 jobs）。**受け入れは未達**: 非単一区間での `resolve_exact` と、外側の入口を通る X13〜X16 は未達。続きは T1b。
- 得られたこと: Astra の断片の `where_state_recollection`（子の更新は no-op）は、開いた区間では**偽**（`open_capture_not_noop`: 空状態は整合だが、2 つの fresh slot に lower=int, upper=str を与えると不整合）。修正版の状態 accumulator（`OpenState.add/recollect/solve`、実 family solver と iff）と、同頭 constructor の持ち上げと異頭の区間保持の正規化、独立な二端点 Inspect の Step での下降（`checked_child_decreases`、`accessible`）を証明。更新列は事前入力で、兄弟の再生成と親 frontier の再計算を行う driver ではない。
- 目標: Astra の断片（`CommonRoleSettled*`）を、`lower ≠ upper` の区間と、その伝播・併合・下降へ広げる。`frontier_exact` と accessibility を仮定にせず、拡張した断片でも証明する。同じ頭の端点は constructor に単純化し、違う頭は区間のまま残す（spec 6.5）。入れ子は深さの上限なし。
- 受け入れ: 拡張した断片で `resolve_exact` が仮定なしで成り立つ。X13・X14・X15・X16 の少なくとも一つが外側の入口を通って PROVED。`verify-lean.sh` が PASS。
- 注意: 子の更新が親や兄弟に及ぶ問題（`where_state_recollection`）が、この断片で空にならない可能性が高い。そのときは、更新を伝える形を設計して証明する（E2 は終わりではない）。選択が要るなら質問ノートを 1 本。
- 参照: `notes/handoff/2026-11-08-astra-settled-frontier-results.md`、`notes/design/2026-11-08-b4-outermost-resolver.md`。

### T1b 開いた区間: 実 producer と driver で resolve_exact (B4)
- 状態: partial（2026-11-08 17:15、dots が実施、32 分。`work/dots-T1b` を統合。verify-lean.sh PASS、1131 jobs）。受け入れは未達（最終 `resolve_exact`、X13〜X16）。得られたこと: 具体 structural producer の child を二端点 Step に含めて Acc を導出、更新を返す再帰 pass（各子の戻り state を次の子へ渡し、全子の後に全兄弟と親を再生成）と独立判断 `Runs` の無条件 iff（`run_exact`）。これは**1 回の再帰 pass**で、source worklist の飽和ではない。続きは T1c。
- 依存: T1（部分達成を前提に続ける）
- 目標: T1 の残り。(1) 実 producer の全 child が、独立な二端点 Inspect の Step に含まれること（accessibility を producer の child へ接続）。(2) 更新後に各兄弟を再生成し、親 frontier を再計算する driver を作り、`where_state_recollection` に当たる定理を、開いた区間の断片で証明する（no-op ではなく、accumulator との対応として）。(3) 開いた区間の断片で `FrontierExact` と accessibility を仮定なしにし、外側の `resolve_exact` を無条件にする。
- 受け入れ: 開いた区間を含む断片で `resolve_exact` が仮定なしで成り立つ。X13〜X16 の少なくとも一つが外側の入口を通って PROVED（`lean/SpecExamplesSettled.lean` か新しい表に反映）。`verify-lean.sh` が PASS。
- 注意: 設計の選択が要る点（兄弟の更新順など）は、決めずに質問ノート（遅延案を先頭）を 1 本。E2 が出ても止まらず、定義を直す。
- 参照: `notes/handoff/2026-11-08-dots-T1-results.md`、`notes/design/2026-11-08-dots-T1-open-intervals.md`。

### T1c 飽和 (saturation) と最終 resolve_exact (B4)
- 状態: running（dots が `work/dots-main` で毎時のサイクル実行中。サイクル 1・2・3 は部分達成、統合済み。指示は `notes/plan/dots-inbox.md`）
- 依存: T1b
- 決定済みの規則（spec 6.3、2026-11-08）: where の子の解決は、兄弟の更新が安定するまで遅らせる。更新のたびに兄弟と親を再生成し、状態が変わらなくなってから初めて保留・曖昧・拒否を最終結果にする（最終化はファイルの終わりの安定時）。絞り込みは impl が一つしかないことからは起きず、関連型の等式を通して流れ込んだ型で起きる。兄弟の順序独立は確定（where は連言、順序で結果は変わらない。spec 6.3、2026-11-08）。証明の対象。
- 目標（T1b 報告の「次の正確な残件」）: (1) 候補ごとの state 更新と、その後に集計する source frontier（narrowing を扱う）。(2) Ty 端点・nominal 意味・slot/source identity を保存する実 allocator と capture provenance（`Allocation` は現在、証明されていない外部入力）。(3) 再生成で現れた child をさらに解く saturation の driver と、その進捗・停止性（宣言時の Paterson 検査と K2 から導く尺度）。(4) driver の最終結果と独立な source Classify の iff、外側の無条件 `resolve_exact`、X13〜X16 を外側の入口で PROVED。
- 受け入れ: 開いた区間を含む断片で、最終 `resolve_exact` が仮定なし（`Allocation` の保存性を含めて）で成り立つ。X13〜X16 の少なくとも一つが外側の入口を通って PROVED。`verify-lean.sh` が PASS。
- 注意: 関連型の等式を通した絞り込みの例を、具体例として一つ以上、外側の入口で通すこと。選択が要る点は質問ノート（遅延案を先頭）。E2 が出ても止まらず、定義を直す。
- 参照: `notes/handoff/2026-11-08-dots-T1b-results.md`、`notes/design/2026-11-08-dots-T1b-producer-driver.md`、`notes/questions/2026-11-08-T1b-sibling-recollection.md`（回答済み: 選択肢 1）。

### T2 optional field の統合 (B2, X22)
- 状態: done（2026-11-08 16:30、dots が実施。`work/dots-T2` を `integration/m1-final` に統合、commit `92edfa967`）。検証: verify-lean.sh PASS（1120 jobs）。新しい source structural 入口で X22 が PROVED。旧生成器は既存ファイル不変の規則のため置き換えていない（旧入口の MISMATCH 表示は残る）。
- 依存: なし
- 目標: `notes/questions/2026-11-08-x22-mismatch.md` の推奨案 1。既存の optional 用の規則とその生成器を、主の pattern 生成器へ統合し、照合が miss して次の arm へ進む経路を保ったまま、生成と case の結果を証明する。
- 受け入れ: X22 が PROVED（主の生成器が `{port: p}` を受理し、フィールドが無ければ miss）。既存の `strict_rejects` などの定理は削除せず、新しい規則の定理として追加する。`verify-lean.sh` が PASS。

### T3 variance 表と nominal carrier の接続 (B5/B1)
- 状態: todo / 依存: なし
- 目標: 宣言から導いた variance 表を、full nominal carrier の subtype・construction・cast の judgment と、元の source generator に接続する。不変な引数の中の共変・反変を不変として扱う規則（spec 6.5）、同じ頭の端点の単純化との整合を含める。旧来の「全引数不変」の一般 nominal 定理を流用しない。
- 受け入れ: 表に従う構造 cast の費用上界が、carrier の judgment と結びついた statement として証明される。X15・X17・X18・X19 が外側の judgment を通って PROVED。`verify-lean.sh` が PASS。
- 参照: `notes/design/2026-11-08-b5-interval-invariance.md`、`notes/questions/2026-11-08-b5-declaration-recursive-variance.md`。

### T4 適合例の表を一本にする (整理)
- 状態: todo / 依存: T1〜T3 のいずれか終了後が望ましい（随時でも可）
- 目標: `lean/SpecExamples.lean` と `lean/SpecExamplesSettled.lean` の状態表を一つにまとめる（既存の定理は削除しない）。X1〜X24 それぞれの状態（PROVED / MISMATCH / NOT-EXPRESSIBLE-YET）と、通っている入口の名前を一覧にする。
- 受け入れ: 一覧が実際の定理の存在と一致している（`verify-lean.sh` が PASS）。

### T7a 主定理のファイル (文芸的 Lean: 読むための窓口)
- 状態: partial（2026-11-08、dots サイクル 3 が `lean/Main.lean` に 11 定理を昇格、統合済み。全言語完成を宣言する Prop は無い。以後、新しい主要定理は証明の完成時に再掲し続ける）
- 依存: なし（随時）
- 狙い（ユーザー、2026-11-08）: 主定理は一つのファイルにまとめ、補題は別のファイルに置く。主定理のファイルを読むだけで、「これが示したい定理か」を判断できるようにする。主定理を先に置けという話ではない（Lean の順序どおり、補題の後ろでよい）。
- 目標: `lean/Main.lean`（新規。必要なら `MainB4.lean` などに分けてもよいが、読む場所は一つの索引から辿れること）に、M1 の主要な定理を**再掲**する。証明が完成した定理は、実際の定理として、補題を呼ぶだけの短い証明で置く。未完成の主張は `def B4Statement : Prop := ∀ ..., ...` のように Prop の定義で置き（`sorry` は使わない）、docstring に「未証明」と、現在証明済みの条件つきの定理の名前を書く。
- 各主定理に付けるもの（日本語の docstring）: 何を言っているか（量化子と前提を省かない）、どの spec の節か（`spec/06-roles.md` 6.3〜6.5 など）、前提が何か、使っている補題のファイルの案内。主要な定義にも短い説明を付ける。
- 対象: B4（区間 role 解決の無条件 `resolve_exact` と停止）、B5/B1（variance 表と nominal carrier・cast の費用）、B2（source 式の producer と adequacy）、B3（source 宣言全体の iff）、B6（`Core.infer`、`Typing ↔ ∃ S ∈ Core.infer e, ...` の区間・遅延・宣言別 variance を明示した版）。いま証明済みの範囲（例: Astra の断片の `resolve_exact`、variance 表の iff）も、断片であることを明記して載せる。
- 受け入れ: ファイルがビルドと Audit を通る。承認済みの全体 statement の更新（`notes/questions/2026-11-08-m1-interval-statement-alignment.md`）と一致する。**ユーザーが読んで「自分の言語の型推論の主張だ」と言える形**。主張の選択や強さに迷う点は、決めずに質問ノート（遅延案を先頭）。
- 以後の規約: 新しい主要定理は、証明が完成した時点で `Main*.lean` に再掲する。補題側の定理は、そこから参照される。
- 注意: 主張はユーザーの承認が要る。作業者は草稿を書き、監督役がユーザーに読んでもらう。

### T7b 不要な証明の到達可能性の解析 (読み取りのみ)
- 状態: partial（dots サイクル 2・3 が実測。根を全 Audit + Main + X の入口へ拡張。削除なし。報告は `notes/handoff/2026-11-08-dots-cycle-3-reachability.md`）。次は、結果をユーザーが読んで T7c の承認を判断する。 / 依存: T7a の草稿があると精度が上がるが、なくても着手できる
- 目標: `tools/Reach.lean` のような Lean のメタプログラムで、**主定理（T7a の `Main*.lean` の定理・Statement が依存する定理と、現在証明済みで残したい定理）から到達できる宣言**の閉包を計算し、モジュール単位で「どのモジュールのどの宣言も到達されず、残るモジュールにも import されていない」ものを列挙する。結果を `notes/handoff/` の報告にまとめる。**削除はしない**。
- 受け入れ: 候補モジュール一覧（旧い点モデルの B4、E2 の障害定理群、置き換えられた局所版など）に、各モジュールの行数と、残す理由／消してよい理由を付ける。
- 注意: 反例の定理（E2 の障害）は、過去の発見の記録としては価値がある。消す前に、git のタグで保存する（T7c）。

### T7c 不要な証明の削除 (要承認)
- 状態: deferred（ユーザー決定 2026-11-09: 今は消さない。T7b 測定ではモジュール単位で届かないのは例・確認の 19 個（約 800 宣言、olean の約 1%）だけで、削除してもディスク・時間は軽くならない。ディスクの原因は worktree とキャッシュの複製で、dots-inbox I-6 で対処。削除は B4 などの主定理が閉じて残す根が確定してから、宣言単位の自動削除の道具を含めて再検討する）/ 依存: T7b と、ユーザーの承認
- 目標: T7b が承認した候補だけを削除する。先に `git tag archive/m1-pre-prune-2026-11-08` で現状を保存する。削除は、承認した一覧のファイルとそれを参照する `Yulang.lean`・`Audit.lean`・`README.md` の行に限る。
- 受け入れ: 削除後に `lake build --wfail` と Audit が通る。T7a の Statement ファイルがビルドを通る。残した主定理の公理の監査が変わらない。`tools/verify-lean.sh` は、承認した一覧を `--allow-removed` として渡して実行する（現在は削除行を一律 FAIL にする規則。この規則はこのタスクに限り、承認つきで緩める）。
- 注意: 既存の定理を弱めない規則の例外になるので、必ずユーザーの承認を得てから。

### T5 B2・B3 の source 側 (後続)
- 状態: blocked / 依存: T1, T2
- 目標: 一般の source 式から実行 prefix を作る producer と adequacy（B2）、検証済み source 宣言全体の iff（返却 scheme の回収、arrow の cover、visible effect・permission・hygiene の lowering）（B3）。詳細は復旧文書の「続きの作業」。着手するときに、小さなタスクへ分割して、この表に書き足す。

### T6 B6 の統合 (最後)
- 状態: blocked / 依存: T1〜T5 と、監査の不一致（`notes/handoff/2026-11-08-m1-model-fidelity-audit.md`）の解消
- 目標: 公開入口 `Core.infer` への統合。着手前に、適合例 X1〜X24 がすべて外側の入口を通っていること、モデルの忠実性の監査を再実行することを条件にする。

## dots の役割（2026-11-08 の試しの結果）

- 取得、Lean 導入、`bash tools/verify-lean.sh . <base>` の全体実行（約 4.5 分）、報告の公開まで、一人でできる。`needs-verify` のタスクの検証役に使える。
- 書き込みは GitHub アプリ経由のファイル単位。報告は `work/dots-verify-<タスクID>` のようなブランチの新規ファイルに公開させる。統合（`integration/m1-final` への push）は監督役が行う。
- 長い処理は、実行を保持するセッションで回させる（`nohup` の切り離しは完了を取れなかった）。
- 定期実行（Scheduled、分単位）は未検証。次の試し: 30 分間隔で「`integration/m1-final` の先頭を取得し、前回検証済みの commit から変化があれば `verify-lean.sh` を回して報告する」を設定できるか。

## M1 のあと (計画に含める。2026-11-08、ユーザーの提案)

M1 が閉じてから着手する。前提が閉じていない間は `blocked`。担当は dots を第一候補（Rust の大きな実装は Codex でもよい）。いずれも、Lean の核が正本で、Rust は正本ではない（`AGENTS.md`）。旧スプリントの実装は、必要になった時点でタグ `archive/proof-sprint-2026-11-04` から**一つずつ**サルベージする。まとめて戻さない。

### T8 速い solver の正しさ (Lean)
- 状態: blocked / 依存: T1c（B4 の無条件 `resolve_exact`）以降、できれば T6
- 方針（ユーザーの提案、2026-11-08）: 「遅い solver と速い solver が一致する」を経由せず、**速い solver が、遅い solver と同じ主定理の形（宣言的な型付けとの iff）を直接満たす**ことを証明する。両者が同じ宣言的な型付けとの iff を満たせば、一致は副産物として出る。refinement は、直接の証明が難しいときの証明技術として残す（必須ではない）。
- 目標: 速い solver（境界を伝播し、量化を遅らせる Simple-sub 流）の定義と、(1) 健全性: 結果が宣言的な型付けを満たす、(2) 完全性: 宣言的に型が付くなら受理する、(3) 主型性: 結果が許される型付けをすべて、かつ余分なく表す。**健全性だけでは足りない**（すべてを拒否する solver も健全）。
- 先に決めること: 「主型が同じ」の定義（構文的に同じか、同値か）、let 多相との関係。ユーザーに聞く。
- 帰結: 速い solver が主定理の形を満たせば、遅い reference solver は不要になり、T7c の削除候補にできる（承認つき）。

### T9 費用の上界 (Lean)
- 状態: blocked / 依存: T8
- 目標: 費用モデル（何を 1 ステップと数えるか）を先に決め、solver の時間・メモリの上界を証明する。cast の費用上界（variance 表に従う構造 cast）と同じ流儀。漸近か具体的な上界かは、着手時にユーザーに聞く。

### T10 Rust 実装を核から導く
- 状態: blocked / 依存: T6（または、実装する範囲に必要な部分の T1c・T3）
- 目標: 型推論の実装（Rust）。Lean の reference solver と**差分テスト**で結ぶ: 適合例 X1〜X24 と、spec の確定した例を、Rust と Lean（`#eval` または抽出）に同じ入力で与え、結果が一致することを CI で確かめる。実装は、型表現と制約の生成、solver、role 解決、診断の順に、小さく分けて入れる。意味論の判断は決めず、質問ノートに積む。
- 受け入れ: 適合例が全部一致。パーサ（`crates/yu-syntax`）との接続。`cargo test` と差分テストが通る。
- 注意: dots は GitHub アプリ経由でファイル単位に公開する。Rust の複数 crate のような多数のファイルの公開が現実的か、T2 の 16 ファイルより大きい規模で先に試す。

### T11 label を受け取る値 `labeled` を核へ (Lean)
- 状態: blocked / 依存: T6（B6 の `Core.infer`）の後。モデル化の部分（下の (1)(2)）は、T1c の後で先行してよい。
- 仕様: `spec/03c-control.md` 3c.3b（確定した考え方と、仮採用の記法）。経緯は `notes/ideas/2026-11-08-label-receiving-values.md`。
- 目標（dots に証明させる、2026-11-08 ユーザー）: 核の計算体系に、普通の enum `labeled('l, 'a)` と、型が求められたときにだけ入る cast `'a → labeled('l, 'a)`（`raw` に包む）、および label を identity で区別する effect と handler を導入し、次を証明する。
  1. **保存的拡張**: `labeled` を使わない式の型付けと、推論の結果は変わらない。
  2. **cast の需要駆動**: cast が入るのは、`labeled` が上界の位置で求められたときだけ。それ以外の位置に `labeled` は現れない（二重 cast が起きない）。
  3. **label の衛生性**: label の操作の effect は、その label の identity を持つ handler にだけ受けられる。同じ型の別の `sub` の内側で、前の `sub` の label を使っても、そちらには受けられない。
  4. **持ち出しの静的な報告**: handler の外へ持ち出した label の操作は、処理されない effect として静的に報告される（行に残る）。
  5. **消去**: `raw` への cast は、型が静的に分かる場合、実行時の費用が 0（消去しても意味が変わらない）。cast の費用上界（variance の流儀）の形で述べる。
  6. `sub`・`for` の展開（`sub \'done -> body`）が、既存の意味と一致する。
- 受け入れ: 上の各項が、仮定を明示した定理として証明される。`verify-lean.sh` が PASS。`Main.lean` に再掲する。

### T12 A2 の修正した契約の E1 (小)
- 状態: todo / 依存: なし（随時。余り時間の仕事に向く）
- 仕様: `notes/questions/2026-11-07-a2-canonical-computability.md`（案1を採用、2026-11-08）。契約の追記は `notes/handoff/2026-11-07-m1-completion-contract.md` の末尾。
- 目標: 修正した A2 を証明する。(1) `∃ computableEncoding, ∀ I J, computableEncoding I = computableEncoding J → PublicEquivalent I J`（既存の `interfaceCode` が単射なら、構文が等しい ⇒ 意味が等しい、で足りる見込み）。(2) 表示・readback の契約: 任意の有限 interface `I` について、decoded/exported 表現の public-instance 意味が `I` と一致する。(3) 実 inference scheme などを保存する義務（A2 results/progress の既存の補題を再利用）。
- 受け入れ: 上の (1)(2)(3) が定理として証明され、元の障害定理は保存される。`verify-lean.sh` が PASS。

### T13 関連型の右辺で他の role の関連型を参照できるようにする (B4/B3, 設計と Lean)
- 状態: needs-owner（設計の詰めが要る） / 依存: T1c の後が望ましい
- 仕様: `spec/06-roles.md` 6.3（2026-11-08、方向は確定: 一般化する）。参照は新しい型変数と等式で表し、受け手が分かるまで遅らせる。
- 設計課題: (1) 停止性: 右辺が作る goal を where の子と同様に数え、Paterson 的な条件の対象にする。(2) `HeadDeterminesAssociated` との関係。(3) 右辺の参照の循環。
- 目標: 設計メモ（選択肢は遅延案を先頭に、Yulang の例つき）→ ユーザーの確認 → Lean のモデル（`impl` の宣言と associated equations）の拡張と、解決器の exactness・停止性の維持の証明。
- 注意: 現行の Lean（`Declaration` の associated equations、`HeadDeterminesAssociated`）は「右辺は head だけから決まる」を前提にしている。拡張はその前提を外す。

### T14 パイプ `|` はあらゆる計算を流す (設計と Lean)
- 状態: needs-owner（設計が要る） / 依存: なし（設計は随時。Lean は T6 の後）
- 仕様: `spec/03-expressions.md` 3.9（2026-11-08、方向は確定: 左辺は計算として流れる）。構想と未決は `notes/ideas/2026-11-08-pipe-computations.md`。
- 目標: 右辺が値を受け取る関数のときの受け渡し、計算どうしをつなぐ意味（conduit）、型を決める。決まったら、E7 の `x | catch:` が一般の規則の一例になることを核で証明する。

### F1 忠実性の確認: 引数の行は全能 (B6 の前に必須)
- 状態: todo / 依存: なし（読み取り中心。dots の余り時間の仕事の先頭）
- 仕様: `spec/05-effects.md` 5.5c（2026-11-08、ユーザー: 旧世代 Yulang2 の規則 `'a -> ['e] 'b` は `'a ['f] -> ['e, 'f] 'b` に cast できる。引数の行は空でなく全能。効果は関数の起動時に放出）。
- 目標: 現在の Lean の核（`Common.common_arrow_iff` の矢印の部分型、application の型付け、`Core.infer` の lambda・application、effect の行の規則）が、この規則と整合するかを調べ、報告する。入っていなければ、反例の式と、定義を直す案を出す。**B6 の前の忠実性の監査に入れる**（`notes/handoff/2026-11-08-m1-model-fidelity-audit.md` の続き）。
- 受け入れ: 報告（結論: 入っている／入っていない／部分的、その根拠となる定理名または反例）。適合例 X25 を状態表に加える。

### T15 Yulang2 の再現監査 (記憶でなく Yulang2 そのものを素材にする)
- 状態: todo / 依存: なし。最優先の一つ（B6 の前の忠実性の監査の本体。F1 を含む）
- 狙い（ユーザー、2026-11-08）: 旧世代 Yulang2 にあった規則が、新しい spec と Lean に持ち込まれていない取りこぼしは、区間、`box` の共変、引数の行（5.5c）と、今日だけで3回出た。ユーザーの記憶に頼らず、Yulang2 を**十分に再現**して突き合わせる。権威はユーザーの決定で、Yulang2 の挙動は素材（`spec/00-sources.md`）。
- 素材: 文書（`web/docs/ja/reference/*.md` 約30、`spec/*` 約20、`notes/design/yulang-language-report.md` 1638 行、`docs/`）、実装（`main` の crates、約400 ファイル）、**動く処理系**。Yulang2 の処理系は、`main` の worktree で `cargo build --release -p yulang --offline` により約1.5分で build できる（2026-11-08 に確認）。CLI: `yulang --std-root lib check|dump --poly|run <file>`。注意: 初回の `dump --poly` は標準ライブラリの処理で約10分かかった（2026-11-08、キャッシュ前）。以後は `yulang cache` のキャッシュが効くはず。型の表示で効果の行が省かれることがあるので、効果の規則の確認には、診断（`check`）や `run` の挙動と併せて使う。
- 手順:
  1. **主張の抽出（読み取り）**: 各文書・テストの規則を、1 行 1 主張（ID、出典、規則、例）で表にする（`notes/audit/y2-claims.md` など）。
  2. **実機の記録**: 各主張の例を Yulang2 に通し、推論された型・診断・実行結果を記録する（`notes/audit/y2-oracle/`）。実機が文書と食い違う点は、そのまま記録する。
  3. **突き合わせ**: 各主張を、新しい spec と Lean の核に対して、一致／違う／欠落／未確認に分類する。違う・欠落は、ユーザーへの質問（Yulang の例つき、遅延案を先頭）か、spec への追記案にする。意味論は作業者が決めない。
  4. **適合例への昇格**: 確定した主張の例は、適合例（`notes/handoff/2026-11-08-m1-spec-examples-conformance.md`）に X26 以降として加え、Lean の `SpecExamples` と、将来の Rust の差分テストの入力にする。
- 受け入れ: 文書ごとに、抽出した主張の数、一致・違う・欠落・未確認の数を出した報告。欠落・違うのうち、型推論の核（B4/B5/B6）に響くものの一覧。
- 分担の案: 文書のグループごとに別の作業者（types / effects / roles と cast / control 構文 / patterns と records / modules と標準ライブラリは後回し）。読み取り中心で、書くのは `notes/audit/` だけ。

### T16 後置 `if` のパーサ (yu-syntax)
- 状態: done（2026-11-08、Terra 3 巡、`cargo test -p yu-syntax --offline` 終了コード 0、1657 passed。残り: 層やインデントの組み合わせの網羅は未検証。spec への例のコードブロックの追加は、フィンガープリントの行の追加を伴うので別作業）
- 依存: なし（Lean の証明とは独立）
- 仕様: `spec/03-expressions.md` 3.7（2026-11-08、確定）。糖衣。`else` なし、結果は `opt`、結合力は最も弱い（`|` よりも、インライン `:` の本体よりも弱い）。前置との区別は、条件の後に `:`/`{` が来るか、文の終わりが来るか。
- 手順: (1) 文法の文書（`notes/design/` の該当する Authoritative 文書、`syntax-reference/` 英日）に後置 `if` を足す。(2) `crates/yu-syntax` に、後置 `if` の CST と解析を足す。既存の fixture は変えない。パーサのテストとフィンガープリントは、**一括再生成せず、変わった行だけ**置き換える（`recovery_mutation_tests::valid_corpus_cst_matches_phase_1_fingerprints`）。(3) spec に例のコードブロックを足す（パーサが対応してから。それまで spec は文章だけ）。(4) 誤り回復（recover）の挙動を確かめる。
- 受け入れ: `cargo test -p yu-syntax --offline` が通る。`say: 1 + 2 + 3 if 6 < 7`、`return x if c`、`last 'outer if done`、`(x if c)`、前置 `if c: x`・`if c { x }` が期待どおりに解析される。曖昧な入力（`if` が連なる、`for x in xs: last if done`）の CST が spec の読みと一致する。
- 注意: 意味論の選択は決めない。曖昧に見える点は質問ノート（遅延案を先頭）。

### F2 引数の効果の変換 (F1 の cast) を Lean にモデル化する (B5/B6)
- 状態: todo / 依存: F1 の報告（監査 dot のサイクル 1 で提出済み: `work/dots-audit` の `notes/audit/f1-effect-passthrough.md`）。T1c と並行できる
- 仕様: `spec/05-effects.md` 5.5c（2026-11-08 確定: 部分型に入れず、型が求められたときに入る明示的な変換の判断）。
- 目標: (1) 変換 `'a -> ['e] 'b` ⇒ `'a ['f] -> ['e, 'f] 'b` を、独立な coercion の判断として定義する（矢印の部分型 `Common.common_arrow_iff` は変更しない）。(2) 起動時の効果の伝播（引数の計算の効果を戻りの行に合流する）と、意味の保存を証明する。(3) 既存の `strictApp` の独立判断・生成器接続との関係（重複しない、または一致する）を示す。(4) 適合例 X25（`x | f`、高階の引数に普通の関数）を、この判断を通して PROVED にする。
- 受け入れ: coercion の判断と、効果の伝播・意味保存の定理。X25 が PROVED。`verify-lean.sh` が PASS。`Main.lean` に再掲。
- 注意: Yulang2 の「明示した高階の注釈で check は通るが run が失敗する」不一致（`conflicting type candidates: [ping] vs []`）は、新仕様に持ち込まない。選択が要る点は質問ノート（遅延案を先頭）。

### T17 パーサの回復: P0 (panic と stack abort) (yu-syntax)
- 状態: done（2026-11-08。欠陥 1 は Terra、欠陥 2 は Sol。`cargo test -p yu-syntax --offline` 終了コード 0、1667 passed、フィンガープリント変更なし。監査の probe は 91,310 回の解析で panic 0、以前 abort した 4096 段の括弧も正常終了。stack の予算ガード 256 KiB、深さの代替 8 項目、Yumark は 16,384。ガードの余裕はデバッグ 7.21 倍、リリース 29.61 倍（512 KiB 基準）。10 万段の字句どおりのインデントは 4 GiB を超えて表せないので 1,024 段で試験）
- 依存: なし。LS の前提（全入力で木が出る）なので優先
- 出典: `notes/audit/ls-recovery-audit.md`（2026-11-08、Sol の監査）。750 の入力・91,310 回の解析で、**panic が 20 件**（壊れた Yumark の経路: 例 `---\n\if@(c){yes}\n---\n`）、**深い入れ子の括弧 4096 で stack の abort**（SIGABRT。2048 は通る）。
- 目標: (1) 壊れた Yumark の panic の経路を除く。LS 側で panic を握りつぶす形にしない。最小の入力と、記録された 19 件の単一編集をテストにする。DocCommentDeclaration を損失なしで返し、後続の宣言を保つ。(2) 再帰する式の解析に上限を設ける（反復化、または回復可能な入れ子の上限。上限に達した領域もテキストを失わない）。釣り合いのある入れ子と釣り合わない入れ子を、別プロセスで、通常の LS のスレッドの stack で試す。
- 受け入れ: 監査の probe（`cargo run -p yu-syntax --example ls_recovery_audit --release --offline`）が panic 0、abort 0 で終わる。`cargo test -p yu-syntax --offline` が通る。既存の fixture とフィンガープリントは変えない。

### T18 パーサの回復: P1 (局所性と連鎖の抑制) (yu-syntax)
- 状態: todo（方針は決定済み 2026-11-08: 閉じが存在しない区切りだけ、後ろの文の先頭で再同期する。`notes/questions/2026-11-08-recovery-unmatched-delimiter-policy.md` の選択肢 1。閉じのある区切りと、有効な複数行は一切変えない） / 依存: T17
- 目標: (1) 宣言の field の回復を、companion/layout の境界で封じる（`}` の欠落と `with:`: 21 個の診断を、局所的な閉じの失敗 1 つに）。(2) 釣り合わない区切りの再同期を、宣言以外へ広げる（`say`、`for` の行、閉じ括弧、入れ子のインデント）。文法は複数行の項目を許すので、曖昧さの扱い（改行で区切りを止めるか）は**ユーザーの承認が要る**: 質問ノート（遅延案を先頭）を作る。
- 受け入れ: 監査の例 E2・E3 の診断の数と再同期が改善する。釣り合う区切りの保護と、有効な複数行の制御は保つ。

### T19 パーサの回復: P1/P2 (補完のためのスロットとカーソルの文脈) (yu-syntax)
- 状態: todo / 依存: T17
- 目標: (1) 通常の補完スロットを、既存の期待スキーマに写す（FieldTail、PathTail、UsePath、演算子のオペランド、ForIterable、Pattern/TypeExpression、case/catch、文字列、後置 if の Condition）。受理する構文は変えない。(2) 部分的な sigil（`my '`、`type T = '`、`$`、`&`）の文脈を保つ（受理の変更は承認が要る）。(3) CST のカーソルの文脈のアクセサ（空白、幅 0、トークンの間、空ファイル）。(4) EOF の `---`・演算子の暫定の扱いを決める。


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
- 状態: running（dots が `work/dots-main` で毎時のサイクル実行中。サイクル 1 は部分達成、統合済み。指示は `notes/plan/dots-inbox.md`）
- 依存: T1b
- 決定済みの規則（spec 6.3、2026-11-08）: where の子の解決は、兄弟の更新が安定するまで遅らせる。更新のたびに兄弟と親を再生成し、状態が変わらなくなってから初めて保留・曖昧・拒否を最終結果にする（最終化はファイルの終わりの安定時）。絞り込みは impl が一つしかないことからは起きず、関連型の等式を通して流れ込んだ型で起きる。兄弟の順序独立は未回答（仮定しない）。
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

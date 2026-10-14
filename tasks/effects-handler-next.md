# エフェクト・ハンドラ実装：次の実行計画

- 日付: 2026-10-14
- 対象: `research/simple-sub-intrusion`
- 実装基準: `343754251a1e6af057eb0b45be660cb882ea8391`
- 位置付け: 既存の承認事項を実行するための引き継ぎ。新しい言語仕様・実装権限の承認ではない。
- 今回の到達点: 現在の carrier で、保護すべき寄与を残すハンドラ残余を playground から観測できること。

## 1. 再開時はここから

1. branch、HEAD、差分、`questions/` の未統合回答を確認する。下記の段階表を更新し、完了済みの段階を再開しない。
2. [現在地](../notes/progress/2026-10-14-operation-catch-constraints.md)と
   [実装上の欠落箇所 §6](../notes/theory/2026-10-14-handler-boundary-construction.md#6-concrete-next-owner-handoff-no-third-unchanged-conditional-proof)を読む。
   判断に使う規則・Authoritative な節は各担当へ渡す。古い研究キューの全項目を開始条件にしない。
3. **現在の H1 は source profile incidence の実証待ち。** H1-A/H1-B は凍結・commit 済みで、
   独立 `compiler_referee` が blocking / major なしと判定した。H1 自体は OPEN。
   追加の bounded derivation は
   [`callback profile reconstruction/receipt`](../notes/theory/2026-10-15-callback-profile-reconstruction-receipt.md)
   に凍結され、fresh `compiler_referee` review でも bounded obstruction として採用可能、
   blocking / major なしとなった。minor は、relation のない captured bound にも
   `TransportWitness` が作られるように読めた箇所を条件付きの記述に直し、delta review で閉じた。
   結果は、実際に dispatch された Function 比較が正確な Argument child と FunctionPort
   parent/field incidence を作り、captured Function endpoint も一部の transport provenance
   に残すこと。一方、未注釈 formal の source profile 導入と、同じ profile/view incidence
   をその Argument 対応へ結び付ける判断はまだ native に存在しない。dynamic Receive/Observe、
   earlier extrusion lineage、alias/return の完全な保存も別の OPEN premise。
   source-profile 実装試行は、unknown formal に対する適用位置表が未選択という判断に達し、
   差分なしで終了した。`A [Ein] -> [Eout] B` のどの位置を保護するかは未決定のまま。
   意味を使わない D-only source-incidence certificate は実装・focused verification・delta review
   を完了し、[checkpoint](../notes/progress/2026-10-15-omitted-formal-structural-incidence.md)
   に記録した。認証範囲は captured FreshUse から一つの source Name handoff を通る経路までで、
   earlier extrusion、profile / grant / Receive / Observe / residual evidence は含まない。
   H3/P は有効にしない。

Luna は primary として、担当の分割、結果の採否、次の実行、Git 統合を持つ。
難しい証明は `prover`、承認済み構築は `implementer`、独立した反例・到達性確認は
`researcher`、査読は `compiler_referee` / `spec_auditor` に渡す。
設定の参照先は `.codex/`。この計画はモデル設定を変更しない。

## 2. 固定した現在地

| 完了・確定した事項 | 今後の扱い |
| --- | --- |
| 全分岐の制約生成、Value の出自を保持した extrusion/intrusion、playground | `if true` の事前評価や定数畳み込みへ戻らない。限定された実装・証明の範囲は維持する。 |
| 操作パターンの parser、payload と raw k の単相型制約 | parser/HIR を最初から調査し直さない。既存の `candidate_operation_catch` 12 件を回帰の基準にする。 |
| raw k の応答型 B、元の値 V、entry E / return R | `E <= R`、`S <= R` を保つ。S は保守的な上界であり、実際の suffix と等しいとは主張しない。 |
| native 残余 primitive P | [既存の証明](../notes/theory/2026-10-14-native-handler-residual-cut.md)を使う。新しい watcher や別の解法を作らない。 |
| 衛生性の既存定理 | [統合表 §3](../notes/design/2026-10-10-annotation-effect-hygiene-integration.md#3-existing-results-retained-and-reused)の仮定を実装で供給する。定理を最初から証明し直さない。 |
| 回答済み question | [receipt](../questions/2026-10-13-negative-formal-permission-field-law/receipt.md)を尊重する。回答は例の訂正であり、完全な負位置の field map の選択ではない。 |

**未完了の中心は U**：元の一つの scoped assignment の下で、処理対象の寄与だけが
残余除去へ入り、同じ effect family の保護された寄与、未処理の操作、外側の arm と
raw resumption の寄与が残ること。将来追加される制約と独立した残余の出自も含む。
空の context word、同じ family、型検査の成功だけでは U の根拠にならない。
注釈を省略した callback にも保護が必要である。

## 3. 当面の順序

日数ではなく、以下の実装単位ごとに確認して保存する。各段階の完了は言語全体や
production cutover の完了を意味しない。元の U の主張範囲を狭めて閉じない。

| 段階 | 状態・着手条件 | 実施内容と成果物 | 完了判定 |
| --- | --- | --- | --- |
| **H1: source 境界から live context まで** | OPEN。H1-A/B と bounded source-to-reconstruction/Argument correspondence は frozen・independently reviewed。D-only source-incidence certificate は実装・focused verification・delta review 済みだが、captured FreshUse と source Name handoff の経路だけを認証し、earlier extrusion を除外する。omitted-formal profile matrix が未決定のため protection implementation は pending。 | 決定された omitted-callback profile を元の owner・型上の位置・寿命から生成し、authentic Function Argument correspondence と consumer まで運ぶ。 | unknown formal、遅延 Function demand、alias/return、fresh use で同じ source protection を保存する。実コードの producer→consumer 対応と必要な不変条件を独立査読で確立する。dynamic Receive/Observe と full Call は別 gate。metadata だけ、detached PUSH だけ、新ノートだけでは完了しない。 |
| **H2: 後から来る制約とコピーへの保存** | H1 の構築と意味が固定されてから、その差分に着手。 | replay、extrusion、capture/freshening、Value-SCC intrusion へ H1 の context を接続する。既存の経路を拡張し、別の配送機構を足さない。 | 後着 lower/upper にも検査が届く。同じ use 内の共有と別 use の独立性を保ち、row の等化で権限や recipe の出自が混ざらない。H1/H2 の証明と source 対応が成立する。 |
| **H3: Catch の残余に接続** | H1/H2 の必要な仮定が実装で成立し、選択・coverage の根拠を確認できた後。 | resolved operation ID と実際の arm coverage を用い、適格な入力に P を適用する。保護された経路は除去を通さず、arm・応答計算・raw k は外側へ流す。 | 直接処理した寄与は消え、未処理操作と保護された同 family の寄与は残る。現在・将来の gamma feedback が働く。playground で成功例と拒否例を観測し、U のうち実装した範囲と未対応の source を明示する。 |
| **H4: 使い方を広げた回帰と衛生性の適用** | H3 の最小例が動いた後。 | nested Catch、local alias、返された callback、複数 use、同 family の再送出、raw suffix の後続操作を source から確認する。既存の衛生性定理の各仮定を code owner に対応させる。 | source から compiler consumer までの対応に穴がない。対応済み範囲の衛生性の結論を適用し、未解決の complete Call / lifecycle 前提を残したまま全体を閉じない。 |

H1 の証明に実装上の証拠が必要な場合、許されるのはその証拠を作る最小の可逆な
計測・構築差分である。反証条件を先に固定し、dependent な通常経路への切替は OPEN
のままにする。「実装がないので証明不能、証明がないので一行も実装不能」という循環を作らない。
逆に、その試作が動いたことだけで H1/H2 の未証明な前提を成立扱いしない。

## 4. 最初に渡すパケット

共通入力は基準 commit、上記の境界記録、
[top-level principles §1.1](../notes/design/2026-10-11-yulang-inference-top-level-principles.md)、
[annotation policy §§1,3–5](../notes/design/2026-10-10-annotation-effect-hygiene-integration.md)、
[context contract §§2–4](../notes/design/2026-10-10-contextual-attachment-admission-design.md)、
[charter §§13–20,24](../notes/design/2026-09-29-scc-intrusion-redesign-charter.md)。
各 child は `fork_turns: "none"`、独占する出力パス、安定した読み取り基準、予算を明示して起動する。
以下のパスは **未割当の候補** であり、開始時に primary が現在の差分を確認して lease を発行する。

### H1-A — 構築則と実コードへの対応

- 担当: `prover`。最初の区切りは 20 分。元の U は OPEN のまま。
- 前提: charter §24 の receiver role を先に保つ。通常の無注釈 function literal は pure、
  明示的に Function 注釈を持つ literal と callback 位置の literal はそれぞれ選択された
  handler role に従う。すべての invocation を handler 境界とは見なさず、effect port の
  綴りから role を逆算しない。Value / Computation の引数 entry との区別も維持する。
- 問い: `my relay cb = catch cb() { v -> v }` の formal row に対し、選択された role と
  型上の位置で必要になる保護を receiver entry の前に導入し、後続の Function demand
  によって判明する位置へ普通の制約伝播で運べるか。
  型全体の確定を先に要求しない。未知型・alias・返却経路を除外しない。
- 出力候補: `notes/theory/2026-10-14-callback-profile-native-construction.md` 一つ。
  最小の構築則、実際の constructor/consumer、既存定理へ渡す仮定を記す。
  producer が存在すると仮定しただけの条件付き補題を成果にしない。
- 反証条件: 元の保護の消失、別位置への権限の生成、後着 Function bound の取りこぼし。
- 止まる条件: 具体的な構築則が成立しない箇所、または未決定の意味が一つ特定できた時。
  同じ仮定の言い換えを継続せず、その箇所を primary と実装担当へ返す。

### H1-B — 独立した source の反例候補

- 担当: `researcher`。H1-A と並行、最初の区切りは 15 分。
- 対象: 省略 callback、alias / capture / return、同 family の二操作のうち一操作だけを持つ Catch。
  既存の [boundary note §3](../notes/theory/2026-10-14-handler-boundary-construction.md) の
  relay は source-qualified な候補であり、実行済み・誤除去の反例とは扱わない。
- 出力候補: `notes/progress/2026-10-14-callback-profile-source-falsifier.md` 一つ。
  source、到達した constructor、比較すべき寄与、観測結果／未観測を区別して残す。
- コンパイラの実観測が必要なら、最小の観測箇所を primary に返す。独自の仮想 solver を作らない。
  最初の有効な反例、または判別できる最小組が揃ったら止める。

### H1-C — 必要な最小構築、以後 H2/H3 の実装

- 担当: `implementer`。H1-A/B から必要な source 証拠と構築則を受け、primary が対象を限定する。
- source 側: `crates/yu-solver/src/candidate_source.rs` の formal/lambda 形成、
  `candidate_effect.rs::{candidate_formal_pair,candidate_signature_view}`、`lib.rs::admit_lambda_fact`。
- consumer 側: `candidate_context.rs::{candidate_context_seed,candidate_function_port_admit,candidate_context_execute_relation}`。
  必要な HIR/annotation/lifecycle ファイルは個別に lease を追加する。
- inferred Function capture/freshening/reconstruction: `candidate_scheme.rs`; retain the source
  formal/profile incidence and its typed-position map through per-use remapping. This owner is
  required by the H1-A/B result and is not an equality-keyed global lookup.
- 同じファイルの source / consumer を別の writer に同時に渡さない。
  proof・反例担当は凍結した commit を読む。新しい差分を使う時点で明示的に再凍結する。
- H3 の追加テスト候補: `crates/yu-solver/tests/candidate_handler_hygiene.rs`。
  既存 fixture の期待値を現出力に合わせて変更しない。

## 5. 判定に使う最小の確認

これは将来の実装時の実行候補であり、この計画作成時に実行したものではない。
primary 一人が Cargo を直列実行し、`CARGO_BUILD_JOBS=2 timeout 300s` と
`--test-threads=1` を使う。各段階では変更した owner の filter を先に選ぶ。

| 対象 | 既存の入口・filter | 証明していないこと |
| --- | --- | --- |
| source と raw k | `--test candidate_operation_catch`、HIR `--test catch_local_source`、playground `--test cli operation_catch_` | 現在の成功は残余除去を示さない。 |
| source PUSH | `--lib candidate_context::tests::source_unit_push_preparation_` | 現在は detached algebra の確認。live な保護の完成ではない。 |
| Function の文脈 | `--lib candidate_context::tests::function_port_context_` と `function_port_incidence_` | source callback profile の生成は別途必要。 |
| P と後着制約 | `--lib candidate_effect::tests::union_tail_preserves_flow_and_cached_effect_and_function_roots_replay_future_conflicts` | P の入力が source 上で適格かは別途必要。 |
| copy / intrusion | `--lib candidate_effect::tests::positive_extrusion_retains_mixed_allowance_before_capture_and_late_lower`、`raw_and_canonical_effect_roots_replay_late_conflict_after_parent_copy_intrusion` | 既存の plain 経路の証拠を、新しい非零 context 全体の証明に拡張しない。 |

solver は `-p yu-solver --features shadow-f5,shadow-apply-candidate`、HIR は
`-p yu-hir --features shadow`、playground は `-p yu-playground` を指定する。
新しい source controls は direct / omitted callback / partial operation coverage /
same-family outside arm / raw suffix / alias の順で最小化し、未実行の予想を確定値にしない。
H3/H4 のまとまった境界で一度 `cargo check -q --workspace` を実行する。
記録だけの更新で再実行しない。性能測定は具体的なリスクが出た時に既存予算で行う。

## 6. この先の準備と、判断が必要な場合

**汎用操作の rigid opening** は独立した準備が可能。charter §§19–20 に従い、
`echo : 'a -> 'a` の一様な arm と、`sink::put` の局所型を Int に固定する禁止例を対にする。
payload・response・raw k・依存する返却値を同じ existential package として保つ構築を
`prover` に渡す。余力があり H1 の統合を妨げない時だけ並行する。現在の柔軟な変数生成で
generic arm を有効にしない。実装は独立査読した構築と必要な実装承認が揃ってから開始する。

**負位置の具体 annotation** の正確な field map が必要になった場合は、元の
annotation 位置、実装 field、異なる結果になる source を具体化する。既存の承認から
導ける対応は実装へ渡し、本当に残る意味の選択だけを質問する。回答済みの旧例を再掲して
同じ選択を求めない。止めるのはその対応に依存する作業だけとする。

guards・labels・tuple patterns、完全な Call、型推論全体の性質、backend/F5 切替は
この計画で完了扱いにしない。H3/H4 の証拠が揃った時点で、実際の未対応 source から
次の小さな実装順を決める。現時点で未知の順序や完了日を固定しない。

## 7. Luna の進行判定

- child の最初の区切りは報告点であり、元の gate の終了ではない。
  結果を受けたら、証明を適用する／具体的な未充足前提を owner に渡す／反例を採否判断する。
  ノートの追加件数で進捗を数えない。同じ前提が残ったら構築か調査方法を変える。
- 新しい core 構築の A/B 不変条件は大きな依存実装より先に証明・反証する。
  H1-C の最小試作だけは、その証拠を得る目的で限定して許可する。
- 通常の実装は M2 を起点に意味と仕様の二観点で査読する。新しい広範な不変条件や
  certification は M3 を選ぶ。人数・修正の収束条件は既存の `rules/orchestration-budget.md` に従う。
- 有用な独立 packet を並行させ、writer の重なりと重い build だけを直列化する。
  `prover` を実際に起動できなければ既存の `rules/agent-orchestration.md` の fallback を使う。
  設定調査を証明の代替成果にしない。
- 各 coherent slice で対象テスト、必要な査読、`tasks/current.md`・`tasks/research-lab.md`・
  progress を同期し、明示したパスを commit、outbound 全体を確認して push する。
  未承認 question は混ぜず、未完了 gate は理由と owner を残す。

### 再開用の短い指示

> `tasks/effects-handler-next.md` を実行入口として、現在の HEAD と段階表を照合し、
> 最初の未完了段階から進める。Luna は primary を継続する。今の開始点は H1。
> 既存の衛生性証明と P を再証明せず、source callback profile と live context の
> 欠けている構築を埋める。H1-A/B を分担し、必要な最小構築を H1-C へ渡す。
> 完成済みの parser・payload/raw-k 制約・回答済み question は再開しない。
> 新しい言語上の選択だけを user に返し、独立した承認済み作業は続ける。

## 8. 計画作成・レビュー記録

この変更は M0 の引き継ぎ記録。`task_decomposer` が依存関係と開始 packet、
`explorer` が実在する owner・test filter・既存 fixture の証拠を読み取り専用で確認した。
独立した `compiler_referee` 一名が権限、proof/implementation の順序、U の範囲、
source 到達性の扱いを査読し、blocking / major finding なし。
軽微な明確化として §24 の receiver role を H1-A に追記した。

記録・参照・owner 対応と `git diff --check` のみを検査した。compiler code、設定、
テスト期待値は変更せず、build/test/benchmark は実行していない。
本計画と `tasks/current.md`・`tasks/research-lab.md` を同期する。
新しい設計決定や theorem status の変更がないため design index の更新は不要。
将来の H1〜H4 の worker はまだ起動していない。

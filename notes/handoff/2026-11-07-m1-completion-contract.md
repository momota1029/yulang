# M1 の完了の定義と、長時間ワーカーの契約 (2026-11-07)

状態: ユーザーの決定（2026-11-07）。署名: Claude (Sonnet 5.5)。

## 決定（ユーザー）

- **M1 は、A1・A2・B1〜B5 のすべてが「終わり」に達したときに完了とする。** B（全構文への拡張）を M1 に含める。
  理由: 毎回「一歩手前で止まる」ように見えるのを終わらせたい。終わりの線を固定する。
- 作業 C（要求駆動 solver）は M1 に含めない。別に進める。C の現状は `2026-11-07-common-demand-and-foundations-results.md` §8。
- A1 と A2 に、Astra（Codex の `gpt-6-astra`）のワーカーを一つずつ、長時間自走で割り当てる。
  これは `rules/workflow.md`「一つの依頼は一つの閉じた仕事。常駐ループなし」の**例外**であり、下の終わりの条件を満たす範囲に限る。

## 各目標の「終わり」

A1（`legacy_generated_shared_witnesses`）、A2（`public_interface_canonical_exact`）、B1〜B5 のそれぞれは、次のいずれかで終わる。

- **E1 証明**: `2026-11-07-core-common-coverage-results.md` §7（および `common-demand-and-foundations-results.md` §7）の statement を、量化子と前提を**変えずに**、Lean で証明する。
  `lake build --wfail` と `Audit.lean` が通り、`sorry`・追加の公理・`native_decide` が無い。
- **E2 障害の定理**: statement が偽、または証明が不可能であることを、Lean の定理で示す（例: B4 の `no_natural_descent_measure`）。
  最小の反例の構成と、**修正した statement の提案**（どの量化子・前提を、なぜ変えるか）を `notes/questions/` に書く。
  statement の変更は、ユーザーの承認が要る。承認前に、元の statement を弱めた定理を「完了」と呼ばない。

次は終わりに数えない: 部分言語での完了、前提を増やした同名定理、「報告して止まる」、`ResidualHolds`・support・fuel を parameter の条件に移すこと。

## 長時間ワーカーの契約

- 作業は、ワーカーごとの**別の git clone**で行う（clone の中なら、ワーカーが自分で commit できる）。ブランチは `m1-a1` などの専用ブランチ。
  `integration/m1-common`・`integration/types`・`yulang3` へは、ワーカーは push しない（ネットワークが無く、できない）。
- **チェックポイント**: 閉じた補題または定理ごとに、`lake build --wfail` を通してから commit する。進捗を `notes/handoff/<日付>-m1-<目標>-progress.md` に追記し、その commit に含める。
- **終わりの条件を満たすまで、返答して止まらない。** 詰まったら、欠けている補題を正確に書き、別の経路（補助補題、別の分解）へ進む。
  終わりに達したら、最終報告に、定理の名前・量化子と前提を省略しない日本語の主張・ビルドと Audit の末尾・残りを書く。
- 仕様（`spec/`）が黙っていて決められない所は、止まらずに `notes/questions/` へ問いとして積み、場合分けで進む。
- 統合は私（Claude）が行う: ワーカーの先頭を別の場所でビルドと Audit にかけ、通ったものだけ `yulang3` に取り込む。

## 例外の範囲

この例外は、2026-11-07 時点の A1・A2 のワーカーに限る。他の仕事で常駐ループを使う場合は、そのつどユーザーが決める。

## 追記 (2026-11-07 夜): B の割り当てと、追加の規則

ユーザーの決定: 同時に走らせる本数の上限はなし。B を次のように割り当てる。

| 目標 | ワーカー | 内容（statement は `common-demand-and-foundations-results.md` §7 と `core-common-coverage-results.md` §7） |
| --- | --- | --- |
| B5 → B1 | Sol (`gpt-6.1-sol` xhigh) | nominal invariance、ground cast、cast plan、construction site（§7.7）→ list / nominal data / float の共通生成（§7.3） |
| B2 | Sol xhigh | 実 pattern から有限制約を作る共有 allocator、`common_pattern_environment_exact`、`generate_common_case_exact`（§7.4） |
| B3 | Sol xhigh | effect の有限宣言、全称 handler（∃ 外側 ∀ operation-local な型 ∃ arm の量化順）、全 instance の solver（§7.5） |
| B4 | Astra (`gpt-6-astra` xhigh) | role の有限 registry と dictionary、qualified の全 family（§7.6）。K2（再帰型での停止）に当たるので、E2 で終わる可能性がある |
| B6 | 最後に、B1〜B5 の後 | 上の機能を、公開入口 `Core.infer` の一つの型付け判断へ統合する |

追加の規則（並列の衝突を避けるため）:

- **既存の Lean ファイルは変更しない。** 許されるのは、`lean/Yulang.lean` への `import` の追記、`lean/Audit.lean` への `#print axioms` の追記、`lean/README.md` への節の追記だけ。
- **公開入口（`Core.infer`、`Core.CommonSyntax`、`CoreCommonInference` など）は、各ワーカーは書き換えない。** 自分の機能を独立のモジュールで証明し、公開入口への統合を主張する補題は、自分のモジュールに置く（統合は B6 で一度にやる）。
- `.git` は sandbox で読み取り専用。commit は免除。監督者（Claude）が 10 分ごとに外からスナップショットする。チェックポイントの関門は `cd lean && lake build --wfail` が通ること。
- 各ワーカーは、進捗を `notes/handoff/2026-11-07-m1-<目標>-progress.md` に書く。終わりに達したら、`…-results.md` に最終報告を書く。
- Sol のワーカーが、終わり（E1/E2）の前に行き詰まったときは、**欠けている補題を正確な statement で書いて**、その時点の状態を残す。監督者がその残りを Astra に引き継ぐ。止まって報告するだけでは、終わりにならない。

## 追記 (2026-11-07 夜): 「∃ 代入」を含む statement の扱い

B4 の E2 の 4 回目は、head の record tail `..a` を「goal と要求同値になる任意の Common 代入」と読んだモデルの産物だった。実際の solver は、record の引き算を具体的な record が来るまで遅延し、`..'a` を引き算の結果（正準な残り）として決める。この規則は `spec/04-types.md` 4.3 にだけあり、role の照合には書かれていなかった（`spec/06-roles.md` 6.3 に 2026-11-07 に追記）。

ワーカーへの規則:

- statement やモデルに「∃ 代入」「任意の代入」を置くときは、実 solver がその代入を**どう決めるか**（遅延するか、正準な形があるか）が spec に書かれているかを先に確かめる。書かれていなければ、E2 を出す前に `notes/questions/` へ 1 問（Yulang のコードの例つき）として積む。
- E2 の反例が、ソース（型注釈や宣言）から書けない核の型にしか現れないときは、「その形はどの推論の経路で生成されるか」を問いに含める。

## 追記 (2026-11-08): モデルの忠実性の監査を B6 の前に入れる

B4 の role 解決が「点の同値」のモデルで証明されていた件（正しくは不変区間と遅延。B5 の nominal 不変性も同根）を受けて、ユーザーの了承（2026-11-08）で、B6（公開入口への統合）の前に監査を一回入れる。

- 時期: B2・B3・B4r・B5 が、区間モデルの設計メモ（`notes/design/2026-11-08-*-interval-*.md`）を出した後。
- 内容: 各 Lean モデルの定義が、`spec/` と `notes/reference/`（旧世代の role-system、invariant-type-sandwich）に合っているかを、機能ごとに照らして、食い違いを表にする。独立した Codex ワーカー 1 本（または監督）が行う。
- 出力: `notes/handoff/<日付>-m1-model-fidelity-audit.md`。各行は「Lean の定義 / 照らした spec・旧文書の該当箇所 / 一致・不一致・不明 / 影響する定理」。
- 不一致の扱い: 該当ワーカーの目標を、区間モデルなどに合わせて再定義する（statement の変更はユーザーの承認が要る）。B6 は、この表の不一致が片付くまで始めない。

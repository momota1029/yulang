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

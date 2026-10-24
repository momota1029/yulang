# 共起分析と解除の保存：査読・統合記録

Date: 2026-10-24
Sprint: COOCCURRENCE-RELEASE-20261024/r1
Baseline: `6602786c430df75312a2ffb74ebd9561113f3511`
Contract SHA-256: `a30684fdb4c1880810f4e3eb8b521feb68adba43f270c3bed520dda02fb17db8`
Outcome: LOCAL_REPRESENTATION_ACCEPTED; false semantic-choice premise withdrawn; whole-language parent OPEN

## 前後の差

以前は複数入力の `'e?` を `A_all` と入力指定の追加仕様選択として質問していた。ユーザーは、引数の保護が動作原理として先にあり、全く同じ共変位置に現れる対象を共起分析が同じ変数にするので、まとめて解除対象にすることは追加の仕様問題ではない、と訂正した。別途証明は必要という区別も明示した。

[規範的記録](../../../notes/design/2026-10-24-cooccurrence-release-clarification.md)と統合稿・索引・current state を訂正した。原質問は選択肢1の承認として扱わず、質問者 receipt を WITHDRAWN_PREMISE とした。質問ディレクトリは原文を保ったまま未追跡で保持し、通常 checkpoint へ含めない。回答待ちは存在しない。

## 新しい数学と source evidence

[証明稿](../../../notes/theory/2026-10-24-cooccurrence-release-preservation.md)は次を構成した。

1. 実際の正極性 group の表が、変数を含む group 全ての共通部分になる不変式。
2. 相互 membership と非空の位置集合の一致の同値、および商 q について `q⁻¹(q(A_p))=A_p`。
3. 動的 receipt・receiver・scope・route・target と相関を保つ fiber 表示。保護導入、輸送、actual crossing、現在状態の query との可換性。
4. 同じ class に別々の二受領があり、片方の経路だけが crossing するとき、他方の保護が残る識別例。

これは既存の情報を保持する表示に関する局所定理である。共起条件は静的な対象集合の飽和性を与える。全 tuple を保存する構成の可換性を、既存 weight/native がその情報を保存する証明と混同しない。

Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1` の immutable Git object を `/home/momota1029/rust/yulang2-oracle-capture` から読んだ。消失した `/tmp/yulang2-oracle-read` の代わりに可変 checkout の別版を使用していない。正極性 pass の補題を、負極性 pass・interval equality・sandwich・removal が混在した最終 substitution 全体へ拡張していない。

## 独立査読

Producer `/root/astra_cooccurrence_proof` の停止・書込み終了 receipt を受領して凍結後、非共著者 `/root/astra_semantics_review` に read-only 査読を割り当てた。primary は構成前に位置集合の飽和性を含めるよう助言しており、独立査読者として数えない。

| 対象 | 査読した SHA-256 |
| --- | --- |
| 共起・解除の r1 | `5c81d2fb89c25f3ec10ef89560e3b7784d7e88022f52375992036148d3e8b454` |
| 直接訂正の authority | `c9eb9b8d274172f02bc82088896c30dd92e219a02adf6ba22418b2cc34207d12` |
| 統合稿の今回の差分 | `6638c116864e61699c2783eb574682a07c223db10016057788828272ff687f3e` |
| successor contract | `a30684fdb4c1880810f4e3eb8b521feb68adba43f270c3bed520dda02fb17db8` |

判定は **ACCEPTED for the stated local representation theorem; no BLOCKING/MAJOR findings**。特に、同じ actual target での集約、二受領の片方だけの crossing、負極性等の除外範囲、native weight 解釈の未証明性、直接発言と原質問撤回の対応を確認した。primary はこの限定範囲で受理した。査読後の証明稿への変更は、独立査読結果へのリンクを持つ一行の receipt のみであり、数学本文は変更していない。

## 正確に残る義務

- CO-1: collector の group 位置と source の引数保護・出力 recipe の対応。
- CO-2: 負極性、interval、sandwich、removal と併合全体の保存証明。
- CO-3: weight/origin の集約から相関を保つ fiber への解釈と、実際の consumer での保存。
- CO-4: 保護・解除生成、一般化、FreshUse、実際の使用経路を通る対応。

統合稿の finite source edge 対応、全表層展開、foreign continuation、値型証明の独立査読、元の Simple-sub A/B・主型性・停止性も維持する。今回の補題を完了した全言語定理や実装の正しさへ拡張しない。次の証拠は、CO-1/CO-3 の生成 owner と消費 owner を結ぶ同じ寄与の trace であり、ユーザーへの入力選択の再質問ではない。

## 資源・検査・Git

後続の予約は dispatcher 45 秒、producer 195 秒、reviewer 60 秒の計 300 秒。以前の 900 秒と合わせ 1200 秒を保持する。正確な実稼働時間、実行モデル・effort の観測 metadata は UNKNOWN。要求は Astra/medium、同時 child は最大一人。全 child の最終 receipt は停止・書込み終了・子なしを明示した。background execution は存在しない。

実施した検査は固定 hash、関連 source の静的読取り、Markdown のローカルリンク、空白と変更ファイル inventory の確認。compiler/build/tests は実行していない。実装はユーザー指定により対象外。原作業場所の未知 writer の lease は回収せず、copy-back もしない。

この記録を含む commit が統合 locator である。primary は明示した文書・証明・状態ファイルだけを stage し、質問ディレクトリを除外して、専用 branch `research/semantics-proof-20261024` の送信範囲を検査する。push の実結果は最終 handoff と Git 履歴で確かめられる。以前の凍結契約・outcome・大原稿は書き換えていない。

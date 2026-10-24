# Source recipe と scoped join の成果

Date: 2026-10-24
Sprint-ID: COOCCURRENCE-SOURCE-20261024/r1
Baseline: `5fb43a1e61336153496f745e51d6782816561f88`
Contract SHA-256: `f2c29073586fad9ac2ec260505f5b58ac83eab12290de664de51bf8a13073e60`
Status: TWO_LOCAL_CONSTRUCTIONS_ACCEPTED; original whole-language parent OPEN

## 前の未証明前提からの進展

前の共起商の証明は、正しい位置集合と完全な動的証拠を保持する表を使えば保存が成立するという段階だった。今回は次の二点を構成した。

- [Source recipe](../../../notes/theory/2026-10-24-cooccurrence-source-recipes.md): 有限 signed signature graph 上で共変位置の一致を判定し、入力 root と元成分から recipe を生成し、actual lexical receipt 環境から target の表を作る。位置・受領・receiver・経路の照合、潜在使用、新規呼出しの分離、単射改名を証明する。限定された実 collector 対応には row-tail の補助 group も含む。
- [Scoped join](../../../notes/theory/2026-10-24-scoped-weight-join-compatibility.md): 将来の Stamp/Protect/Release に対する観測を三種類に分け、それぞれ intersection-tags/union-protections、極大 antichain、完全状態関係による必要十分条件を導く。完全 tuple を保存するという未分解の前提を、実 consumer と集約の具体的な照合条件へ分解する。

座標別 union の失敗例は抽象例であり、actual source 由来の compiler 反例ではない。既存 `candidate_scope.rs` は三つの生成子と順序付き合成を持つが、今回の parallel summary を実装したとは主張しない。原稿の旧 `A_all` 採用待ちは再開しない。

## 独立査読と適用範囲

source recipe は primary の著作、scoped join は `/root/astra_scoped_join` の著作である。dispatcher は方向付けに参加したので独立査読者ではない。producer の停止 receipt を受領し両成果物を凍結後、非共著者 `/root/astra_semantics_review` が review した。

| 固定対象 | SHA-256 |
| --- | --- |
| source recipes r1 | `7e2acfc321f2ba5e17b522d45c864825122d25fac5483dd90e381dd3d21fc35c` |
| scoped joins r1 | `ebf854a3ed7cd3ca64f2025c01262eb53e79cc35f203b4ba148c672327f86b1b` |
| read-only candidate_scope.rs | `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a` |

判定は **ACCEPTED within the stated mathematical scopes; no BLOCKING/MAJOR findings**。primary はこの範囲で受理した。S1 の有限 signed-node 判定、S3 の actual receipt、S6 の row-tail と ignored/extra-vars 条件、join 定理の単調性・分配・fresh scope による必要性を確認した。有限 support に対し fresh 名を取れるという数学的前提は allocator の無限動作保証ではない。両証明への査読後変更は、結果への一行の receipt のみである。

統合稿 §5.1–5.2 と索引に結果と範囲を反映した。表の要約は査読済みの定理からの説明であり、全 source の規則を承認するものではない。

## 正確に残る義務

1. 元の全 source の生成・compaction・recursive center・非正則 instance と有限 signature/profile の対応。S1–S6 の対象だけへ元の言語を制限しない。
2. 負極性・interval・sandwich・removal を含む簡約全体、任意の型代入、一般化と fresh use の対応。単射改名から自動的には出ない。
3. 実際の P/PF/Eligible query と経路選別が、どの観測言語を使うか。否定を含む query を単独 may 観測へ縮約しない。
4. 重みと origin の具体表現、遅延 replay、同じ fiber への継続作用、共同 freshening を、該当する集約方程式へ接続する。

元の value/source-edge/all-surface/foreign-continuation 義務と Simple-sub A/B・主型性・停止性は OPEN。次の数学上の接続は query の存在・不在条件と filtering の観測を分類して、必要な相関を確定することである。ユーザーへの追加仕様選択ではない。

## 資源、検査、停止、保存

新しい Astra 予約は dispatcher40 + producer190 + reviewer70 =300 秒。以前の1200 秒を保持し累積1500 秒、未観測時間の返却なし。要求 Astra/medium、実行モデル・effort・active duration の観測は UNKNOWN。同時 child は最大一人、全 child が停止・書込み終了・子なしを最終 receipt で明示した。

固定 hash、静的 source、ローカル link、whitespace、明示したファイル inventory を検査。テスト・build・compiler 実行は行わず、実装ファイルを変更していない。元作業場所の未知 writer は引き続き隔離し、copy-back しない。撤回した質問の原文と receipt は未追跡のまま保護する。

この記録を含む commit が統合 locator となる。専用 branch `research/semantics-proof-20261024` へ、primary が明示した path のみを checkpoint し、全送信範囲を点検して non-force push する。Git の実結果は最終 handoff と履歴に残す。

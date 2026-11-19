# dots-main cycle 279 — 据え付けの新規性、子辺の圧縮、有限停止証明書

- 開始 2026-11-19 18:30:04 UTC。報告 2026-11-19T19:20:05Z（50.02 分）。開始時の統合先頭 33add29a、途中の統合先頭 6ffaba4a で standing orders / inbox が同じ blob と確認。ACTIVE、I-51〜53、凍結を保持。private work/dots-main のみに反映。
- 278 の最終報告は中断していた。最後の心拍は開始40分時点。公開9e86871dと手元検証済みbaa676df1は心拍以外まったく同じで、27 Lean モジュールと242宣言は既に公開済みだった。12独立監査を再実行し、報告と集約ログを707497abに復旧した。未追跡の未検証試作は除外し、この結果は279の新規件数に含めない。

## 今回証明したこと

1. **据え付けの効果を二つに分けた。** 任意の current snapshot と整合する effect、任意の全割当について、実 mixed install 後のモデル条件を、旧モデル・元の packet・現在の出力クラス効果・新着要求の効果に正確に分解。新着は実 emitted raw sites に由来し、明示／既定の出力 body と、新着を一方以上に含む同名ペアの整合を、現在・旧・版付き履歴の全効果について検査する。checked source からの実到達状態では、既登録クラスに新たな要求が流入しない既存定理を接続。現在の Frame と registry の一致の下で、**未 committed と「全割当を一つ以上除外する、または未記録の子辺を増やす」の同値**を得た。installable の選択・安全・存在条件は依然必要。
2. **両成分を実 Step で分離。** 実 HeadAlloc の Display→Int では全割当が変わらないが、到達先で Int の子辺が生まれる。逆に旧239/240の任意の install は、公開端点を保つ拡張の存在と子辺の全リストを変えないのに、私有名を変えた全割当を除外する。任意の固定有限テスト列について、十分後のすべての install がテスト列上では完全に見分けられず、それでも各回で別の全割当が落ちることを両例で証明。実 compound 238 では二成分とも変わり、variant の子は固定端点を使う。
3. **子辺を実行可能に圧縮。** 辺のキーは両端の ID、role、引数リスト、出力名と target を含む。全 occurrence に関するキーの単射性、不足辺が実際の書き込みの順序を保った部分列であることを証明。旧 prefix を保って新着だけを登録する更新、全正規化の membership 保存・重複なし・冪等性・反復更新の不変性も検証。実行例で同一IDでも引数の異なる候補を区別し、辺の増分更新で重複を除くことを確認。
4. **実境界での読み戻し。** 現在の辺の membership を保つ任意の置換について、全モデル、任意の生成先、V8 の各 Local 分類（K2・inspection、出力・併合・共有衝突を含む）、証拠木、実 Step の有無、Stable、source EvidenceAt が等しい。既存の legacy/版付き Trusted と cache を再構成し、install・merge・enqueue・refreshの両入口・reobserve・equate の実条件を運べることを個別に確認した。Display の圧縮後も .node 1 [.node 3 []] と EvidenceAt を保持。到着する全 journal の等号や、任意の raw 多段双模倣は主張しない。
5. **停止性の有限証明書。** 固定有限リスト中の「新しく載る辺」か「棄却される指定全割当」を実 install ごとに一つ消費するなら、残量が administrative で増えず install で真に減る。実 finite trace の install 数と全長の上界、Acc を導いた。テストのモデル述語は意味的で、一般の実行可能決定手続ではない。Display の開始点では子辺1本で被覆。旧239開始点では、どの有限の混合証明書も存在しない。
6. **source から辺の有限現物候補へ。** Paterson による有限 owner と宣言節から、任意の元の actual trace 上で全子辺の ID ペアを覆う一つの有限集合を導出。新しい ID ペアを作る Step 数は一様有界。さらに「すべての節引数の正規形の根が変数でない」compiled registry 断片では、入れ子の変数は許したまま、端点が固定の purpose 3/4 を使うことを証明。到達範囲内の ID が full occurrence（全引数と出力を含む）を一意に決め、正確な有限 full-edge basis を得た。この断片では、辺を増やさない実 install に対する有限の全割当テスト被覆だけが、今回の Acc の残りの前提。実 compound 238 でこの断片の辺が空でないことを検証。旧239は同断片でも edge-free の有限テスト被覆を持たない。

## 対象と未達

- I-52後継の部品として、実 install の差分と圧縮した辺台帳を定義。グローバルな source compiler、一般の異なる私的捕捉（特に裸変数の子引数）の正規化、全グラフと履歴 effect snapshot の圧縮同型は未完成。
- 次の候補は (1) 裸変数の子引数を固定公開ポートへ移して意味・V8 readback を保つ補題、(2) 後継の owner 再訪で new full-model obligations を残さない、または有限意味事実で被覆する補題、(3) 正規化した stored effect snapshots を対応させる多段補題。一般 Acc、12の橋の完成、全言語 EvidenceNode は未証明。
- Yulang2 わりあての内部表現そのものは実機未照合。監査の x-oracle.md の X1（名目ラッパーの where 子）および X3・X5（構造パターン界面の限界）を参照。Yulang2 で同じ辺台帳や再ベースが得られたとは主張しない。言語の規則を変更せず、質問ノートなし。

## 検証

- 31新規Libraryモジュール、8独立監査、257宣言。独立再検査は全件PASS、標準3公理のみ。型付き使用例6本と実行テストもPASS。278復旧分を除く今回の差分は65パス。
- 新規 Lean 原本を barrel の追記順に再検査し、各監査ファイルを単独に trust=0・警告エラー化で実行。新規 root import を一度ずつ確認し、凍結ファイルは統合基準と278復旧版基準の両方から不変。
- 両基準の git diff --check・tools/verify-lean.sh --no-build, 閉じた edge-probe 実行を再確認。全 Lake build、全検査スクリプトのビルド部分、CI、Yulang2 実機は未実行。利用枠は不明。
- [設計: 差分](../design/2026-11-19-cycle279-rebase-install-delta.md) / [辺の圧縮](../design/2026-11-19-cycle279-compact-edge-readback.md) / [実ガード](../design/2026-11-19-cycle279-compact-edge-guards.md) / [有限証明書](../design/2026-11-19-cycle279-install-witness-budget.md) / [有限子辺](../design/2026-11-19-cycle279-finite-child-identity-basis.md)
- [監査再検査](../verification/cycle279/independent-recheck.txt) / [新規原本](../verification/cycle279/module-list.txt) / [検証コマンド](../verification/cycle279/commands.txt) / [実行例](../verification/cycle279/edge-probe.lean)

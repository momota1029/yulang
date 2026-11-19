# Cycle 280 — 裸変数の子の固定端点ポート

spec 6.3 の `where 'a: Display` を落とさず扱う。279 の `ClosedArguments` はこの正当な例を除外する。裸変数は捕捉から区間を取り、捕捉を再観測すると raw 名前が変わり得る。一律に ID のみの辺を raw occurrence と同一視したり、古い alias 等式を増やしたりしない。

データ: 実 packet の子 occurrence に、seed・親 ID・宣言 ID・節 ID・位置で固定した既存の purpose 3/4 ポートを与える。子 ID・role・named output targets・実 center をそのまま保存。表示上の同一性は canonical port で、意味は「対応端点の型が全モデルで上下両方向の部分型」。row はこの関係では変更しない。二端点が同じ raw ID かという構文的 point test は保存しない。

宣言的な判断: 個々のモデルで上下各ポートと従来端点の型が同値、全ての実引数に対して interval fit が同値。片方への延長は書き込み対象が互いに素であり、旧意味論の支持・読み出す端点・中心と衝突しないことを明記する。実行版: 裸変数だけに従来端点をコピーする simultaneous write（自己参照を読み直さない）、またはその双方向型不等式。compound は既存のポートと同じで触らない。

定理候補: 任意の roles、checked source と actual trace、任意の実 emitted child の canonical occurrence は元と ID／出力共有を保存する。全 canonical 辺候補は同じ Paterson の有限リストで覆う（raw の全辺が有限とは言わない）。任意の packet/model に対して alias atom の意味は端点同値と一致し、その同値下で site readback が一致。first-use fresh extension と既保持ポートの rebase を分ける。同じポートに旧・新の別の端点を恒久的に足すと制約が強くなるため、ここを無条件の mixed raw Step 対応としない。

既存定理の位置: 279 の full-edge basis は raw descriptor がすでに固定ポートである特殊ケース。279 の full assignment が落ちる旧239/240の反例はこの graph 表現でも残る。一般 Acc に向けて、別途、新しいモデル損失を有限な source 意味事実で捉えるか、後継の再訪で私的な未知割当の反復切り捨てを取り除く必要がある。旧 raw Step を変えないまま後者が成立するとは主張しない。

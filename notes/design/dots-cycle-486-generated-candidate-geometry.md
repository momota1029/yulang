# C486 G05: 元の有限経路の生成と全引数の門

I-99 / I-98 のもとで、G04 は未証明の `G04Entry` のまま。G05 の既存の位置・符号付き局所経路を、候補全体の tape に供給する。現行の問題、宣言順、raw 名と方程式・型商の定義は変えない。

1. 元 Pattern の constructor node budget を実行可能な再帰で定義する。本当に選んだ任意の旧 `Hop` は `Origin` の空でない元 AST path へ降りるので、この budget が減る。記録された `Trail` の長さは元 Pattern の budget 以下で、raw グラフの循環長ではない。
2. 元 Pattern に現れる有限な action と `PhysicalOrigin.children`、実際の旧 immediate successor を使い、既存の `readHop` で確認する。有限な checked checkpoint palette から符号を読み、正の prefix ではその下を読まない。計算結果は独立の旧 `Trail` を反映し、palette が guarded position を被覆している場合は全独立経路を含む。
3. 出所の許可は候補ごと、現在の元 occurrence ごとに別 input とする。型商・位置だけでは許可を作らない。許可を独立判断と照合した gate のもと、proper visit の元引数、action、pose、旧位置列を生成し、同じ palette を使って `TrailWire` を data-only に組む。一候補で真を見つけたことと候補全体の実際の照合を混同しない。
4. `requestRootCheck482` で実際の demand の全 root を順に検査する。安全と確認できないなら、この局所優先入口では none。以前の root diagnosis を定義し直さない。実際の候補役割・prior 責務と visited set の独立な被覆がある場合に限り、正の元候補は選択より優先し、真が無いことから election に進める。候補全体の match/mismatch/defer は G10。
5. I-99 の削除は別の明細で、検証済みの置換・影響範囲・宣言数を明示できる場合だけ。全体統合検査は監督役、手元では影響範囲を確認する。

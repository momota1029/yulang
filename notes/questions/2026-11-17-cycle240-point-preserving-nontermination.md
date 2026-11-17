# Cycle240: I45 の後継でも止まらない経路が残った

## 結論と停止

I45 に従い、すでに一点の descriptor を見直しで文字どおり保持する条件を加えた。
旧239の反復はこの条件で遮断できた。しかし、新しい5slotの原初期状態から、
その条件を毎回満たす別の無限経路が構成できた。偽の停止性目標とその意味修正の研究は停止した。

対象は `GeneralNominalPointSourceBoundary240.boundary`。
`GeneralDictionaryLooseIterationNontermination240.initial_no_acc` は原初期状態の
逆向き実Stepに対する `¬Acc`、`no_saturation` / `no_statement` は任意executorについて
`¬SaturationTotal` / `¬Statement` を、追加の意味的仮定なしで証明する。
これは「すべての実行が発散する」「Stable状態が存在しない」という主張ではない。

## 反例のしくみ

原sourceは5slot。0と1はInt、2と4は独立した `Foo(Int)`、3は同じ区間 `(2,4)` を
二度引数にするPair。2と4は意味は同じでも別のsource名なので、rootのdescriptorは
`PointDescriptor` の構文的条件を満たさない。sourceの形成・GroundRoots・宣言検査・
実モデルはすべて初期境界で検証している。

各段階nで、rootの区間は `(lower_n,4)`。実Installで版つきlowerを割り当て、
Refreshで新しい `Foo(0,1)` を観測し、Reobserveで新しいFooだけを `Foo(0,0)` に
一点化する。同時に非pointのrootを `(lower_(n+1),4)` へ更新する。
既存のpoint descriptorは一切変えないため、I45の追加guardは毎回通る。
一方、rootは非pointのままで、新しいsourceが毎回増える。

`LooseIterationIteration240` はこの3stepを全nで実際に構成する。
Fresh、SafeKnown、フレーム一意性、Installable、未commit、mixed cache、
raw-back、モデル非空、原sourceからの到達性をすべて閉じている。
将来のupperだけをbottomにしたモデルを保存することで未commitを証明し、
必要な経路や未commit結論を仮定に置いていない。

## 監督側で必要な判断

「一点」を同一のsource名という構文的条件ではなく、意味的に幅がない区間も含む
条件として扱う意図なのか。それとも、まだ非pointのdescriptorであっても、
意味を狭めない別名への置換を禁止する別の条件を設けるのか。
現在のI45と実装済みのpoint固定だけでは、有限回という理由は成立しない。

I45で採らないとされた版の正準化は実装していない。新しい停止条件や意味変更も
独断では加えない。次の明示判断を待つ。

## 検証

64新モジュールを個別に `--trust=0 -DwarningAsError=true` で検証し、
`Audit/Cycle240All.lean` で新モジュールの全定義（生成宣言含む）の推移公理を調べる。
許可は `propext`, `Classical.choice`, `Quot.sound` のみ。結果はcycle報告・監査ログ参照。
凍結された `Audit.lean` / `README.md` と既存proofは変更しない。

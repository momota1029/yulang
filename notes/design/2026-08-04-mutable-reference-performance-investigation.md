# 可変参照(`&a`/`$a`)性能調査: 根本原因の特定

日付: 2026-08-04

状態: **調査完了。次段階（Mechanism 1の設計着手可否）はユーザ確認待ち**

著者: Claude (Sonnet 5)（Codex `gpt-5.6-sol` xhigh の調査を統合・記述）

## 0. 背景

RCPF プロジェクト完走後、playground の実測値取得のため
`crates/wasm` にtiming telemetryを配線した（`c11dfc87`）。ブラウザで
実際に計測したところ、RCPFが対象にしていた`std::text::parse`級の
重いlowering経路はplaygroundの通常利用では踏まれておらず
（build時に埋め込んだcompiled prefix artifactにより、std importを
含むコードでも推論コストは数十ミリ秒程度）、RCPFの性能問題は
playgroundの体感速度にはほぼ現れていないことが判明した。

その報告を受けてユーザから「普通に変数処理も重いですよ．最悪って
程ではないけど明らかに不必要に重くなってます．これをもっと
ミリ秒単位で高速化する必要が実はあります」という指摘があり、
続けて「可変参照が遅い訳だけど」と対象を明確化された。

本書はこの指摘を受けた調査（2回のCodex Sol xhigh呼び出し、
read-only）の結果をまとめ、次の設計・実装の出発点とする。

## 1. 調査結果の要約

`&a`/`$a`（可変参照・状態）を使うコードは、同等の不変コードに比べ
**7.7倍〜63倍**遅い。絶対値でも1行程度のスニペットで
**66〜454ミリ秒**かかる。一方、通常の変数束縛（`my x = 1`のような
不変束縛）は既にネイティブで**0.4〜0.9ミリ秒**と十分高速であり、
「変数処理全般」ではなく**可変参照機構に固有の問題**であることが
確定した。

原因は独立した2つのメカニズムに分解される。

## 2. 計測方法

release buildのCLIで、warmな compiled std prefix cache を使い、
`YULANG_INFER_TIMING=files`・`YULANG_CONSTRAINT_EVENT_TIMING`等の
既存instrumentationで phase別・event別に計測した。各ケースは
control-cache/poly-cache命中を避けるため一意なコメントを付けて
5回計測し中央値を取った。

主な計測プログラム:

```yulang
// 定数write×3（比較対象）
{ my $a = 0; &a = 1;  &a = 2;  &a = 3;  $a }

// read-modify-write×3（問題のケース）
{ my $a = 0; &a = $a; &a = $a; &a = $a; $a }
```

| ケース | synthetic act copy | analysis drain | suffix lowering合計 |
|---|---:|---:|---:|
| 定数write×3 | 22.274ms | 72.177ms | 111.428ms |
| read-modify-write×3 | 23.594ms | 360.997ms | 400.512ms |

immutable相当のsuffix loweringは5.7〜8.7msであり、mutable版は
これに対し**7.7倍〜63倍**（ケースにより変動）。

## 3. Mechanism 1: synthetic act copyのオーバーヘッド

### 3.1 現状の実装

`my $a = ...`は`crates/infer/src/module_map/mod.rs:867`で新しい
nominal act宣言として登録される。finalization時
（`crates/infer/src/module_map/finish.rs:340`）に:

1. sourceを`std.control.var.var`へ解決する。
2. 新しいcompanion moduleを作る。
3. テンプレートのoperation signatureと全child宣言をコピー・登録する。
4. コピーした全childを通常のbinding/method loweringで**再度lowering
   する**（`crates/infer/src/lowering/body/act.rs:221`）。

`CopiedSourceInternal`はsource spanとruntime rootを抑制するが、
body inference自体はスキップしない。

### 3.2 コスト

1参照あたり約24ms、束縛数にほぼ線形（2参照で49.3ms）。
`lib/std/control/var.yu`は24行と小さいが、2 operation
（get/set）・`var_ref`（refレコード構築、closure 2つ）・
再帰run（get/setをcatchしてcontinuationをresume）・generic
payload/result変数・effect row・handler subtractionを含み、
コピー1回あたりの内容としては見た目より重い。それでも「ローカル
変数1個をコンパイルするのに約24ms」は不釣り合いである。

### 3.3 根本原因の分類: 実装上の結合であって必然ではない

必要な意味論を切り分けると:

- **束縛ごとに異なるeffect family pathが必要**: 各束縛のhandlerが
  他の束縛のoperationを横取りしないために必須。
- **runtime metadataがそのpathを束縛固有のget/set `DefId`へ
  紐付ける**（`crates/poly/src/expr.rs:120`）。
- 既存test（`crates/infer/src/lowering/tests/case_03.rs:1315`）が、
  異なるact ID・異なる`var_ref`/`run`定義をowner間で要求している。

一方で、**CSTから宣言を再登録し全体をre-inferする必要性は
確認されなかった**——これは現在の表現がidentityを生成するための
手段であって、意味論上の要求ではない。

既存の多相関数再利用機構（`SchemeInstantiator`）は量化された
`TypeVar`/`SubtractId`をfreshenするが、constructor/effect path
自体はそのままcloneする（`crates/infer/src/instantiate.rs:620`、
`Pos::Con`/`Neg::Con`のclone箇所は`instantiate.rs:788`）。つまり
**既存の instantiation機構をそのまま流用することはできない**
——nominal family identityがquantified scheme parameterとして
扱われていないため。単純な「再利用に切り替える」だけでは済まず、
family identityの表現自体に手を入れる設計が必要になる。

## 4. Mechanism 2: subtype replayの増幅

### 4.1 現象

定数write×3回（121ms）に対し、read-modify-write×3回は372ms
（3倍以上）。`probe_select`は2→8、`apply_select`は1→4、
`method_dependency`は1→4と増加する。

### 4.2 トレース結果: 選択解決自体は正しく一回きり

verbose traceで確認した内容:

- 4回の`$a`読み出しは4つの異なる`SelectId`を生成する。
- 各々に`MethodDependencyAdded`は正確に1回だけ発生する。
- 各々`std.control.var.ref.get`へ正確に1回だけ解決される。
- 2量化子の`.get`schemeのinstantiationも各々1回のみ。
- scheme cloneのコストは1回あたり0.015〜0.024msと軽微。

つまり`.get()`の**再解決や重複キャッシュ欠落ではない**。

late no-op probeが解決済み選択ごとに1つ残る（lower-bound
watch listが古いIDを保持しているため）が、これは0〜0.002ms/回
であり、ホットスポットではない。

### 4.3 実際に高コストな箇所: instantiation後のsubtype propagation

- 3回目の`.get`のdrainは、subtype step 126・event 209・
  bounded variable接触279、intrusive tracing下で60.658ms。
- 4回目は subtype step 264・event 477・bounded variable接触281、
  210.379ms。
- いずれも`subtract=0`——コストはrow-subtraction処理ではなく
  subtype propagationそのものにある。
- bounded variableの増分はわずか2個なのに、stepは2.10倍・
  eventは2.28倍に増えている。

selection-bound traceでは、各`.get`のreceiverが同じ
6-lower-bound reference graphへ到達する。新たにinstantiateされた
payload/effect変数はこのgraphへinvariantに制約され、read結果を
`&a = ...`へ渡すことで同じpayload hubへ再接続される。

新しいlower boundが到着すると
（`crates/infer/src/constraints/machine/bounds.rs:4646`）、既存の
全applicable upper recordと組み合わされる。新しいupperも対称的に
既存lowerを走査する（`bounds.rs:4807`）。exact canonical
constraintはprefilterされるが、`.get`のたびに新しい変数を使う
ため、形が同型（isomorphic）であっても**exact IDとしては
局所的に新規**として扱われる。

### 4.4 分類

- **正当**: 各source readにつき1回の`.get`解決とfresh HM
  instantiation。
- **redundantだが無視できる規模**: 選択ごとに残る2個目のstale
  probe。
- **確認された増幅**: fresh invariant read/write制約が密な
  共有hubを拡大させ、対向boundのreplay積が急速に大きくなる。
- **未証明**: このfan-outのうちどれだけがalpha同値のもとで
  除去可能か。既存instrumentationはexact constraintをcountする
  だけで、alpha正規化後の意味論的帰結をcountしていない。

### 4.5 RCPF/CDMとの関係

同じ大きな族（新規到着が蓄積済みフロンティアと結合し続けることで
コストが増える）ではあるが、**同一の具体的バグではない**。

CDMは、新しいcarrierが来るたびにdownstream materializationが
（rootごとにcanonicalであるにもかかわらず）ledger全体を毎回
eagerに再構築していた問題で、admission-local差分処理への置換で
解決した。

本件では:

- `.get`解決は既にcached/one-shot。
- solverは本当にfreshなscheme instanceとlocally novelなboundを
  処理している。
- exact replay dedupは機能している。

再発の原因は「missing selection cache」ではなく、「fresh instance
が高次数のinvariant reference/effect graphへ結合することによる
structural fan-out」である。

さらに、この project の過去の replay-dedup 調査
（`notes/design/2026-07-16-constraint-replay-dedup-investigation.md`）
は、再発見されたtransitive consequenceを安易に「除去可能」と
みなすことへ警告している——過去に類似の簡略化がexported schemeを
変えてしまった前例がある。**このMechanismへの対処は、正しさへの
影響を伴わない形で設計する必要があり、Mechanism 1より慎重な
検討を要する。**

## 5. 環境上の制約

この環境ではallocation/flamegraph attributionが取得できなかった:

- `perf`は`libpython3.10.so.1.0`が無いため起動できない。
- `samply`はインストール済みだが`perf_event_paranoid=2`により
  recordingがブロックされる。
- `valgrind`・`heaptrack`等は存在しない。
- release実行binaryはstripされている。

これらは上記の構造的結論を妨げるものではないが、正確な
allocation attributionと、alpha正規化後のsemantic consequence
countによる「除去可能量」の定量化には、追加のtooling整備または
別環境での計測が必要になる。

## 6. 今後の方向性（本書では未確定・未着手）

1. **Mechanism 1（act-copy）**: 方向性は比較的明確——「束縛ごとに
   fresh identityが必要」という要求を保ったまま、「CST全体を
   毎回re-register・re-inferする」処理を「共有可能な部分は
   共有し、識別子部分だけをfreshenする」形へ置き換える設計が
   有望。ただし既存の`SchemeInstantiator`をそのまま使えないこと
   （§3.3）を踏まえ、family identityの表現自体を含めた設計が
   必要。
2. **Mechanism 2（subtype replay増幅）**: 正しさに関わる領域
   （exported schemeへの影響前例あり）のため、Mechanism 1より
   先に、あるいは独立して慎重に設計する必要がある。まず
   alpha正規化後のsemantic consequence countを取得できる
   instrumentationの追加を検討し、「除去可能な重複」と「本当に
   必要な新規propagation」を定量的に切り分けてから、対処方針
   （例: invariant reference/effect hubの構造自体を見直す、
   fresh instanceの扱いを変える等）を設計するべきである。

いずれのMechanismも、本書は根本原因の特定に留め、具体的な
実装設計・スライス分割はここでは行わない。次の段階として、
まずMechanism 1の設計文書を別途起こすことを想定する。

---

著者: Claude (Sonnet 5)（Codex `gpt-5.6-sol` xhigh の調査を統合）

本書は根本原因調査の記録であり、具体的な実装計画はまだ含まない。
次段階（Mechanism 1の設計着手、Mechanism 2の追加調査着手）は
ユーザへの確認を経てから進める。

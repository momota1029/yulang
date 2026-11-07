# B5/B1: 中心を保存しない不変区間への訂正

状態: **2026-11-08 ユーザー訂正に基づく設計・証明作業の方針。区間版 B5/B1 は未証明。**
この文書を、これ以降の B5/B1 作業の出発点とする。旧点モデルの同名 theorem を区間版の完了として数えない。

## 1. 権威と確定・未確認の境界

確定事項の出典:

- [spec/06-roles.md §6.5](../../spec/06-roles.md): 2026-11-08 の不変区間・宣言時極性の追記、期待型による境界、構築位置の deferred cast と EOF。
- [旧 role-system](../reference/2026-06-02-role-system-yulang2.md)「注意」: 中心なし lower/upper、同じ実引数の merge、交差制約、両側出現変数の等式、具体型への collapse。
- [旧 invariant-type-sandwich](../reference/2026-06-06-invariant-type-sandwich-yulang2.md): 同じ path/slot の bounds の merge、通常の制約機械への返却、全出現を調べる sandwich、再 collect の原因 key。
- [完了契約・最終追記](../handoff/2026-11-07-m1-completion-contract.md): 存在／任意の代入を使う前に、実 solver の代入決定規則を仕様で確認する。未指定の選択による E2 を作らない。

不変引数は `I = (L,U)` であり、中心を data として持たない。実引数 t に対する充足は `L ≤ t ∧ t ≤ U`。
`bool | int | 'a & float & complex` は `(bool | int | 'a, 'a & float & complex)` の表示上の略記である。
実引数 t はモデルを説明するための witness であり、区間に保存する「中心変数」ではない。

同じ実引数 slot に I=(L₁,U₁), J=(L₂,U₂) が来たら、lower に両方を、upper に両方を足す:

```text
merge I J = (L₁ | L₂, U₁ & U₂)
```

upper の `U₂ & U₁` との違いは要求同値までであり、書き順の違いで別の意味にしない。
各元区間の `Lᵢ ≤ Uᵢ` と、merge による `L₁ ≤ U₂`, `L₂ ≤ U₁` を通常の型制約機械へ戻す。
同じ具体型 T に上下から釘付けされる区間は T に畳む。両側共通の変数の等式併合と、全出現に基づく具体 constructor の sandwich は分ける。

型変数の極性は宣言時に決める。入れ子の constructor 引数／effect family 引数／row tail での出現を不変として、通常の関数入力では反転、結果では維持する。
推論器が任意の代入ごとに極性を推測する仕組みは導入しない。role の生 demand、残置 where 引数の反転した読みは旧 role-system の区別を保つ。

**未確認**: すでに確定した `box int` と `box bool` が別々の値として分岐合流するときも、同じ ID の区間を必ず併合して拒否するか。
今回のユーザー訂正が明示的に「未確認」とした帰結なので、次の一問だけを確認中:

```yulang
struct box 'a { value: 'a }
my choose(c: bool, x: box int, y: box bool) =
    if c: x else: y
```

推奨は旧 compact の「同じ path は一 entry」に合わせる区間併合だが、回答前にこの分岐の許否を確定しない。
同じ実引数 slot の明示された merge の代数、および collapsed interval の定理はこの回答に依存しないので先に進める。

## 2. 新 carrier を作らず、既存 machinery に区間を接続する

### 2.1 endpoint と有限制約

新しい点型 carrier や新 demand interpreter を増設しない。
まず既存 `Common.Ty` と `Common.Subtype` を endpoint の意味に使い、区間を lower/upper の有限記述として扱う。
nominal ID・arity・型／行 kind・元 slot の共有は dedicated nominal descriptor の data として保持する。
nominal を structural variant へ翻訳しない。

有限問題は既存 `LayerBoundTemplates.Constraint` の `.lower` / `.upper` / `.flow` / `.check` へ戻す。
一つの元実引数 slot の bounds を複数の独立 point parameter に置き換えない。
二つの元区間を同じ slot に適用した充足と、merge 後の充足の iff を最初の橋にする。
row 引数も下界／上界の向きと共有 ID を保ち、既存 row 制約へ戻す。型 endpoint と row endpoint を混同しない。

再利用する根:

- `CommonBoundCoalescing`: arbitrary Common endpoints の lower/upper、有限 flow、`rigidComparisons`、`expand`、全 parameter 健全性、全モデル回収。
- `DemandBoundPropagation`: 同じ有限 flow の ancestors/lowerBounds/upperBounds、要求根からの到達と反対極性の読み。新しい solver を別に作らない。
- `CommonBoundRef*`: 元 shared node と required/optional/width の固定参照、有限 inspection/worklist、row family、全 parameter・元全 node/row 回収。
- `CommonCanonicalIntervals`: scalar lattice の captured/generalized 区間と実 envelope。scalar での exact code を constructor・相関する複数出力へ無条件に広げない。

`CommonBoundRefPolarity` の lower/upper source grammar と、**宣言時**に求める型変数の variance は別の判定である。
後者を宣言の検証結果として入力 data に焼き込み、前者の generator 閉性・inspection 閉性をそこから証明する必要がある。
「極性を推論する」新しい runtime 制約は足さない。

### 2.2 代入の決め方

固定した有限 bounds/flow に対して、実際に使う family は既存 `CommonBoundCoalescing.expand`:

```text
lower(j) | ⋁(pᵢ & upper(i))   （i は j に到達する元 slot）
```

元の有限 rigid comparisons は solver が検査・分解する。
その成功を実返却 scheme の membership から導き、parameter の条件には残さない。
元の model を parameter に置く既存 retraction で、全元 slot と全元 row を同時に回収する。
これは「都合のよい代入がどこかにある」だけの仕様ではない。

source の弱変数／deferred boundary では、期待型が決まるまで同じ元 slot を保留し、後の利用で確定した型を構築位置へ戻す。
ファイル末尾まで未確定なら、仕様どおり元要素／site 型の cast なし union に確定する。
未指定の任意 substitution を existential に選んで成功／拒否を作らない。
一般 recursive 型・nominal matching・tail の正準な残りなどに別の決定規則が要る場合は、当該 source 規則を確認してから statement を置く。

## 3. nominal invariance の改訂 statement

open interval の比較を、point 型の `Subtype` における引数同値とそのまま同一視しない。
同じ実引数の reconciliation と、区間の instance 集合の包含も別の判断である。

目標 `common_nominal_invariant_exact` の区間版は次を同時に要求する:

```text
任意の検証済み有限 nominal 宣言集合 D、任意 nominal IDs・arity・引数 kind、
任意の元 shared slot/row IDs と、同じ実引数に来た全有限 lower/upper 記述、
任意の独立な元 endpoint/row assignment について、
実 nominal inspector が返す有限 bounds/flow/check の Models
  iff
ID/arity/kind が宣言と一致し、元の全区間・元の共有を満たす独立 interval reconciliation。

inspector は各 slot の lower を union、upper を intersection で蓄積し、
元の整合性・全交差条件を実制約機械へ戻す。
その全元 Models を、実返却 scheme の無制約 parameter 全体で回収し、
任意返却 scheme と任意 parameter は元の全区間 Models を満たす。
旧 Common の順序・typing・実 solver の結果と parameter 契約を保存する。
```

「各実引数」の存在は各区間に別々の witness を与える意味ではない。
同じ元 slot は一つの割当てを共有し、複数の不変 occurrence を同時に満たす。
実装は元 slot と bounds のみを保持し、区間の data に中心を付け足さない。

検証／ID/arity/kind 失敗の扱いと、元制約機械への生成 exactness は、任意の外部 compatibility oracle に依存させない。
recursive nominal が endpoint の内部に現れる場合も、既存 dedicated nominal syntax と shared graph のまま区間を持たせる。
Common endpoint だけの最初の補題を、この全 statement の完了とは呼ばない。

## 4. ground cast の区間版

閉じた ground 引数 T は collapsed interval `(T,T)` として読む。
`CommonGroundNominalCasts` の明示した有限 grammar と computed normalisation image は保存する。
raw 未正規化 `Casts.Ty` の equality を、任意の区間の同値や自由 parameter の選択と同一視しない。

改訂 `common_ground_cast_compatibility_exact`:

```text
任意の明示済み finite ground grammar の source/target descriptions A/B、
宣言 ID/arity/kind が検証され、各 ground argument が (T,T) に collapse しているとき、
実 normalisation/checker の keep compatibility iff、元 Ground の四つの case に応じて:
- scalar/scalar: 元 Common scalar subtype。
- scalar/nominal: source scalar が bottom 以下。
- nominal/scalar: top が target scalar 以下。
- nominal/nominal: dedicated nominal ID/arity が一致し、
  対応する collapsed interval の reconciliation が整合する（元 ground 引数の要求同値）。
```

open interval に期待型が来たときは、区間制約を伝播し、実 solver の決定規則で確定するまで cast の target を保留する。
`∃ T ∈ interval` を任意に選んで cast 成功とする新規則は置かない。
cast の実 search/failure と pure executable plan は、確定した実 endpoint と元 source body へ接続する。
nominal 引数の内部へ cast は通さない。構築位置の deferred cast と、作成済み nominal 値の変換を分ける。

`common_cast_plan_exact_and_pure` は、任意有限 verified registry、実確定した endpoint、元式・環境・row の量化を保つ。
区間解決から得た endpoint を実 keep/search/failure へ渡し、元 body の pure immediate row と arrow の変換後引数での呼出しを証明する。
既存 total PureCasts 表現の局所障害は、区間版全体の E2 ではない。未指定の substitution や未到達の核の型を使って E2 としない。

## 5. list / nominal-data / construction generation の改訂 statement

`common_construction_sites_exact` と `common_data_list_exact` は、次の全量化と義務を保つ:

```text
任意の実署名・検証済み list/nominal 宣言・宣言時に決まった引数極性、
任意の元環境・全 data/nil/cons/nominal-data 式・元結果 interval description、
任意の独立な元 endpoint/row assignment について、
独立共通 IntervalTyping
  iff
実有限生成制約に、全元 bounds/slot/row/site を保持する Models がある。

固定 field と全元 site を保持し、同じ list element／nominal parameter の区間を共有する。
必要な deferred pure cast を同じ構築位置へ戻し、各元 site を一度だけ元順序で評価する。
実返却 scheme の全自由 parameters が元 Models を満たし、元全 Models を回収する。
弱変数の後の利用と EOF の確定を同じ元 slot に接続する。
Float の基底型意味と旧 Common theorem の保存を接続する。
```

nil は「任意の point element でよい」とだけ記述せず、同じ元 element slot の bounds/未解決状態を保持する。
cons/list literal の各 site が別々の element witness を持たないようにする。
construction ごとに始まった弱変数と、すでに確定した nominal 値の collapsed 引数も区別する。
`box int` と `box bool` の分岐の問いが未回答の間は、その二者の branch merge の許否に依存する theorem を確定しない。

## 6. 既存結果の扱い

| 結果群 | 訂正後の位置付け |
| --- | --- |
| `CommonBoundCoalescing`, `DemandBoundPropagation`, `CommonBoundRef*` の既存 theorem | 元の量化・grammar・前提のまま有効。区間の主な再利用先。nominal 拡張／宣言検証／生成閉性が自動で付くわけではない。 |
| `CommonCanonicalIntervals` | scalar captured/generalized interval family として元 statement のまま有効。全 nominal/regular/correlated interface の完了にはならない。 |
| `CommonNominalFinite` / `FullDemand` / `Carrier` / `FullCarrier` の invariance iff、`list_invariant_exact` | その point interpreter 上の数学的 theorem として有効。区間版の一般 invariance の theorem ではない。上下が同じ T に collapse した case に限定して橋を使う。 |
| 旧 nominal head/slot equality solver | collapsed argument の双方向要求同値を解く範囲で有効。open interval merge を全 point equality へ置換する用途では使わない。 |
| `CommonNominal*GroundAdapter` と実 ground checker | 指定した finite ground grammar／collapsed intervals の橋として再利用する。open interval の cast を任意 existential target で決めない。 |
| 旧型埋込み・full-role order 保存・既存 `Core.infer` schemes の像の保存 | それぞれ元の point-model statement として有効。これだけで新 interval solver の conservative extension は出ない。 |
| mixed regular equation closure / graph lowering / AST allocator | 元の syntax equality、元 node/site/order の保持は再利用候補。point-model Models に対する theorem を open interval Models へ無証明で移さない。 |
| point-based construction/data finite generation と family | interval-aware な独立 Typing、cross bounds、宣言時極性、deferred target 確定を含めて言い直す必要がある。 |
| `CommonPureCastTotalityBoundary` 等の局所障害 | 指定した既存表現に対する theorem のまま。区間版 B5/B1 や実 solver の不存在の E2 としない。 |

中断時の `CommonNominalFullTypingReflection.lean` は未完成・未 import。
その未完成 proof の continuation を、今回要求された区間設計より先に進めない。
新 carrier を増設して既存 Common bounds solver を迂回する経路には戻らない。

## 7. 証明・検査の順番

1. 同じ Common endpoint carrier 上で、中心を data として保存しない interval の充足・整合性・merge・collapsed case を証明する。
   lower/upper を既存 finite constraint syntax へ生成し、全交差条件と `CommonBoundCoalescing.expand` の全 parameter / 回収へつなぐ。
2. 宣言で確定した kind/variance と元 nominal ID/arity を参照する finite inspector を作り、同じ実引数 slot の区間制約生成 exactness を証明する。
   一般代入の決定規則が不明な case は問いを一つ残し、既定規則の case を先に進める。
3. interval 由来の制約返却／再 collect の実装では、元の slot/path と原因の有限 key で新規性を判定し、未適用の原因がある場合だけ再 collect する。合算済み lower/upper 全体を key にしない。変数と具体 constructor の除去は主型全体の全出現を調べ、captured/level 保護を保持する。区間両側の変数等式を確定直前に扱う旧規則と混同しない。これらの source/scheme 保存・終了義務が未証明なら interval pipeline 完了としない。
4. ground/collapsed interval へ既存 normalisation/checker を接続する。一般 point theorem を collapsed case の corollary として位置付け直す。
5. 元全 fields/sites を保つ interval-aware generation、実 bounds/worklist solver の全 parameter / 全 model、weak use/EOF を接続する。
6. 必要な B5 の区間基盤が閉じたところから B1 の nil/cons/list/nominal-data を接続し、pure executable cast / runtime order を進める。
7. 各 closed packet の全体 `lake build --wfail`、fresh 独立レビュー、`lake env lean --trust=0 Audit.lean` と公理 allowlist を行う。

進捗は既存 [B5 progress](../handoff/2026-11-07-m1-b5-progress.md) に訂正後の状態を明示し、
今回の結果は [2026-11-08 interval results](../handoff/2026-11-08-m1-b5-interval-results.md) に蓄積する。
部分結果を B5/B1 全体の E1/E2 として報告しない。

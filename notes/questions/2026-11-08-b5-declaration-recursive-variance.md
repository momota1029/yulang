# 宣言時 variance: 「無限に入れ子」の有限な判定規則

状態: 要確認。以下は未承認の定義候補であり、いずれも source 規則として採用していない。
回答待ちで停止せず、任意の宣言 metadata に対する共通の inspector／interval／solver 証明を継続する。

## 確定した部分と、この問いの範囲

[spec/06-roles.md §6.5](../../spec/06-roles.md) の 2026-11-08 の訂正によると、
`box 'a` は共変で、`list 'a` のように際限なく入れ子になる位置は不変である。
向きは式推論中ではなく型宣言時に決める。理由は、構築済みの再帰データの内部へ cast を通すと、
データ全体を作り直す費用がかかることにある。同節は、関数を包む cast の生成時と、
呼び出しごとの内部 cast を区別し、有限 tuple／record／variant には成分ごとの cast を認める。

同節の「再帰的に定義された型が自分自身を通して際限なく深くなる所」は、現在も
**Claude の読みとして要確認**である。再帰宣言の全引数を一律に不変にする規則は確定していない。

[旧 role-system 文書](../reference/2026-06-02-role-system-yulang2.md) は、role method の
signature 上の極性と、従来の保守的な constructor 引数の扱いを区別する。
その古い「data 構造は不変」を、後の `box` 訂正より優先して nominal 全体へ適用しない。
[旧 sandwich 文書](../reference/2026-06-06-invariant-type-sandwich-yulang2.md) は、
不変と決まった位置の中心なし区間、両交差制約、関数位置での極性反転を定めるが、
今回必要な nominal 宣言群からの再帰コスト判定を一意には定めない。

**問い:** 型宣言群から引数ごとの `covariant / contravariant / invariant / unused` を得る際、
どの有限な再帰判定を「無限に入れ子」の意味にするか。
構築済みの値への cast を扱う問いであり、literal の弱変数／構築位置の保留境界／EOF の選択はここで変えない。

## 共通の有限入力と、引数単位の解析

入力は、名前・kind・arity と field／constructor payload が解決された有限の nominal 宣言群とする。
外部の opaque 型については、その module が公開する検証済みの引数 metadata を参照する。
宣言本体の無い `type list 'a` という一行だけから、実装の再帰構造を推測することはしない。
alias の処理と宣言の well-formedness は元の front end の義務であり、この解析で新たな拒否規則を足さない。

三案とも、宣言名だけでなく **`(宣言 ID, 引数番号)` と宣言構文内の有限な出現位置**を頂点にする。
例えば `F 'a 'b` が `G 'b 'a` を含む場合、対応は `F.0 → G.1`、`F.1 → G.0` と記録し、
引数の交換や、具体型への置き換えを失わない。nested な実引数もその有限構文の出現位置を経由して辿る。

最初に、実際の payload まで届く引数の使用を最小不動点で求める。
直接 payload として現れる型変数を起点とし、使用される nominal 引数位置を通って伝播する。
関数の引数・結果に現れる変数も使用に数える。使われない callee 引数の内部には伝播しない。
このため、単に自己参照の実引数に名前が書かれているだけで、値の payload に全く現れない
phantom は `unused` と判定する、という候補になる。これは提案する規則であり、採用済みとはしない。

使用がある位置については通常の正負を有限格子上で伝播する。
関数の引数は反転、結果と通常の data 成分は保持し、callee の既知の向きと合成する。
正だけなら共変、負だけなら反変、両方なら不変である。
以下の再帰コスト判定で選ばれた位置は、正だけ／負だけでも不変にする。
kind／arity の検査は `unused` を含む全位置で保持する。

## 候補 1 — 推奨: 引数ごとの「即時変換が辿る再帰」を判定する

使用を持つ引数の依存 graph に、field／variant payload／tuple など、
cast が値を今その場で辿る辺を入れる。**関数を包む位置で即時走査の path を切る。**
function の内部の使用や極性を消すのではなく、wrapper 作成時とその後の呼び出し時の費用を分ける。

使用される payload へ到達可能な path 上に、任意回数反復できる nominal 展開の cycle がある引数を不変とする。
有限 graph の到達可能性と SCC で判定できる。cycle が無く、すべての path が有限なら、通常の極性を使う。
関数 wrapper の各呼び出しについても、その呼び出しで即時に辿る graph を同じ基準で検査する。
callee の不変位置を通る依存も不変へ伝播し、有限格子の不動点として宣言群全体を解く。

この案は「変換の仕事量がデータの長さに依存しない」という理由と、既存の関数 wrapper の規則を直接結ぶ。
必要な cost theorem は、wrapper 作成一回と呼び出し一回を区別する。総呼び出し回数を定数に制限する主張ではない。
`stream` のような遅延された再帰を共変としてよいかが、この案の主な未決点になる。

## 候補 2 — 引数ごとの再帰 path を判定し、関数でも path を切らない

候補 1 と同じ使用解析・引数対応・SCC を使うが、関数の引数／結果を通る辺も再帰判定に含める。
使用される payload に至る path で nominal 展開を際限なく繰り返せるなら、不変とする。
関数位置では通常の極性を反転／保持するが、再帰 cycle の検査では障壁として扱わない。

`list` と相互再帰を不変にし、phantom や再帰の途中で具体型に置き換わる引数は区別できる。
一方、wrapper ごとに有限の仕事で済む `stream` も不変になる。
「無限に入れ子」を型展開の有限性として読む案であり、既存の cast-cost 規則より保守的になる。

## 候補 3 — 宣言 SCC による保守的な十分条件

phantom の使用解析は共通部分のまま残す。その後、nominal 宣言名の参照 graph の SCC を求め、
自己 cycle または相互 cycle に入る宣言の **使用される引数だけ** を不変にする。
その結果は依存先の不変位置を通る引数へ伝播する。非再帰宣言の残りは通常の極性を使う。

有限実装は最も簡単だが、引数が再帰先で具体型へ置き換わる `reset` まで不変にする。
「再帰宣言だから全引数を不変にする」ことは、phantom にも不変を課すさらに強い規則であり、
この候補にも含めない。この案を採るなら、必要以上の不変性を言語の拒否規則として認める明示的な判断が要る。

## 区別する Yulang の例

以下は判定規則を区別する source 断片であり、現在の parser／checker での実行確認を主張しない。
宣言構文の根拠は [spec/04-types.md §§4.4–4.6](../../spec/04-types.md)。

```yulang
struct user_id(int)
cast(x: user_id): int = x.0

struct box 'a { value: 'a }
struct box2 'a { value: box (box 'a) }

enum chain 'a:
    end
    link 'a (chain 'a)

enum phantom 'a:
    end
    next (phantom 'a)

enum reset 'a:
    value 'a
    next (reset int)

enum left 'a:
    value 'a
    next (right 'a)
enum right 'a:
    next (left 'a)

struct stream 'a { next: () -> ('a, stream 'a) }
```

| 宣言の引数 | 候補 1 | 候補 2 | 候補 3 | 区別する理由 |
| --- | --- | --- | --- | --- |
| `box 'a`、`box2 'a` の `'a` | 共変 | 共変 | 共変 | 有限の nominal 入れ子だけでは不変にしない |
| `chain 'a` の `'a` | 不変 | 不変 | 不変 | 同じ引数の payload が任意の深さで繰り返される |
| `phantom 'a` の `'a` | unused | unused | unused | 名前の自己伝播だけで、実 payload への使用が無いという提案 |
| `reset 'a` の `'a` | 共変 | 共変 | 不変 | 再帰枝は `int` に固定され、元 `'a` を運ばない |
| `left 'a`、`right 'a` の `'a` | 不変 | 不変 | 不変 | 別名を通る cycle でも同じ引数が戻り、payload に届く |
| `stream 'a` の `'a` | 共変 | 不変 | 不変 | 既存値の全深さの走査ではなく、関数 wrapper を作れるか |

```yulang
my widen_box(x: box2 user_id): box2 int = x        // 三案とも許す候補
my widen_chain(x: chain user_id): chain int = x   // 三案とも拒否する候補
my retag(x: phantom user_id): phantom int = x    // unused の提案を採るなら引数制約なし
my widen_reset(x: reset user_id): reset int = x   // 候補 1・2 と候補 3 の差
my widen_stream(x: stream user_id): stream int = x // 候補 1 と候補 2・3 の差
```

`widen_reset` では `value` 枝の一個の値にだけ cast が必要で、`next` 枝の中身は両側とも
`reset int` なので再帰的に作り直す必要が無い。`stream` では、候補 1 は `next` を包み、
各呼び出しで一個の値を変換して次の `stream` の wrapper を作る読みになる。
この挙動を仕様として決めたとは扱わない。

## 選択に依存する正確な証明義務

次の二つは未証明の設計目標であり、既存 theorem 名の置き換えではない。

1. **宣言から表を求める iff。** 任意の有限な解決済み source 宣言群 `D` と任意の表 `V` について、
   実有限 `deriveVariance D` が `some V` を返すことと、元の宣言 well-formedness と
   選択した独立な使用／極性／再帰判断が各元引数位置に `V` を与えることを同値にする。
   手渡しの variance 表を正しいと仮定するだけでは、この義務を満たさない。
2. **その表に従う構造 cast の費用。** 任意の元 source/target instance と、宣言から許可された
   構造 cast plan について、有限の型／plan 構文から定めた構造の走査・再構築・wrapper 作成の
   回数上界を証明する。葉の既存 cast の呼び出しは一回と数え、利用者が書いた cast 本体そのものの
   実行時間や停止をこの命題に混ぜない。
   共変／反変として通す構造変換の上界に、実データの list 長や木の節点数を入れない。
   候補 1 では wrapper 作成と一回の呼び出しを分け、候補 2・3 では拒否される位置を定義どおりに固定する。

その後に、導出した同じ表を full nominal carrier の subtype／construction／cast judgment と
元 source generator に接続する。旧 all-invariant iff を一般 nominal theorem として流用しない。
source-level checker、full carrier、cast cost を閉じる前に、B5/B1 の全体 E1 完了とは呼ばない。

## どの候補でも使える既存の証明

- `CommonDeclaredNominalInspection.inspect_exact` は、任意の有限表を使い、元 ID／arity／kind を検査し、
  その表の方向どおりの比較と実有限 atom 生成を同値にする。表を source から導いたという主張ではない。
- `CommonDeclaredNominalSlots.inspect_all_grammar` は、同じ元共有 slot に生成された atom の
  既存 solver 文法を内部で導く。
- `CommonDeclaredNominalSourceFamily.all_parameters_models` / `generated_models_exact` は、
  表に従う metadata 制約と元 source clause を同じ機械へ入れ、無制約の全 parameter と
  全元 slot の readback を扱う。`generated_core_models_exact` の Core は既存 `principalCore` の範囲である。
- `CommonDeclaredInvariantBounds.inspect_exact` は、表で不変とされた元引数位置だけに
  lower/upper の制約を付け、元 head の実 slot をそのまま使う。どの候補がその位置を不変とするかには依存しない。

これらの表に関する定理を保持したまま、候補ごとの有限 graph 解析や共通の usage/polarity 部分を進められる。
未決の source variance criterion を、solver parameter の support 条件へ移して回避することはしない。

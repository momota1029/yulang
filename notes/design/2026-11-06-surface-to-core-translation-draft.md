# 表の構文から核への翻訳表 (下書き, 2026-11-06)

Rust 実装の中心になる desugar / elaboration の一覧。**下書き**で、ユーザーが 1 つずつ確かめる。
署名: Claude (Sonnet 5.5), 2026-11-06。仕様の正本は `spec/`。この表は仕様を置き換えない。

## 核の式(ターゲット)

旧核は `Inference.Expr` と `RecursiveEffects.Expr`。追加の解決済みcase/handler核は下記の
専用AST・評価器として置き、旧ASTとの全体統合は別の証明義務として残す。
追加した核の形と証明範囲を各行に記す。未決定のsource翻訳は備考と問いへ明記し、
確定の印で拡張しない。pattern defaultのscope・不一致後の評価はQ4・Q5で回答済みであり、
scope付き核へのsource名解決・elaborationの証明を残す。

```text
var i        lit b        lam e        app f a       let v b
branch c t e              pair a b     fst e         snd e
{}  (emptyRecord)         record l h t               field l e
recordDefault l base fallback
variant l e               request op e               boundary(protect|release, mask) e
handler op action ret arm
multiHandler operations action ret arms
partialHandler payloadArms action ret arms
```

旧 `lit` の `b` は base 型の印だけで、整数や文字列の中身を持たない。
内容を持つ `LiteralValues.Literal FloatValue` と独立な比較判断を追加した。旧ASTとの統合は別途必要である。
再帰束縛は核の式の外側(`RecursiveInference` の SCC ブロック)にある。
`recordDefault` は決定44に従って追加済み。型付けと実推論は `PresenceDataInference`、
実評価は `SourceDataRuntime` にある。旧required-field推論器では明示的に未対応と区別する。
`PresenceLegacyBridge` は有限legacy data型の意味と全parameterの一方向の移送を持つ。
`PresenceLayers` と `PresenceRegularLegacyBridge` はrequired/optional/lacksの相関を保ち、
旧regular graphの全有限data観測とblock closureの保存・反映まで接続した。
regularな `SourcePrincipalInference` 全体の主型性・関数/行意味への統合は、
別メモ `2026-11-06-presence-inference-integration.md` の工程3〜5を残す。

## 状態の印

- **確定**: 仕様で翻訳まで決まっている
- **下書き**: 仕様の方針から私が組んだ。ユーザーの確認待ち
- **欠**: 核に対応する形が無い。核を拡張する必要がある(ChatGPT への依頼になる)

## A. 式の骨格

| 表の構文 | 核 | 状態 | 出典・備考 |
| --- | --- | --- | --- |
| 整数・文字列・bool・unit literal | `LiteralValues.Literal` | 確定 | 内容とliteral/range比較を追加。source codecとの対応は未証明 |
| float literal / literal pattern | `Binary64SourceDecimal.convert`、`Binary64.Value`、`LiteralValues.binary64MatchCheck` | 確定 | 回答済みQ2・Q3・Q11。任意decoded tokenの厳密な十進解釈と全grid最近接偶数丸め、有限結果の存在⇔成功・不存在⇔静的overflowを証明。数値Eqは正負zero一致・NaN不一致。literalは網羅性に数えない。lexer・診断/Rust f64との対応は別義務 |
| 名前 `x`、path `a::b` | `var i`(束縛済み)、またはモジュールの宣言への参照 | 確定 | 名前解決は核の前。章3.2 |
| `f x y` / `f(x, y)` / `x.m y` / `f: body` | `app (app f x) y` | 確定 | 章3.3。どれも同じカリー化 |
| `f()` | `app f unit` | 確定 | `unit` は `lit unit` |
| `\x y -> e` | `lam (lam e)` | 確定 | 章3.4 |
| `\(a, b) -> e` | `lam (let a = fst #0 in let b = snd #0 in e)` | 下書き | irrefutable な pattern だけ。pattern の分解は E |
| `a; b`(block の文の列) | `let _ = a in b` | 下書き | 値を使わない式も評価される(決定 43) |
| `my x = e; rest` | `let e rest`(`x` を束縛) | 確定 | 値制限の規則は章4.7 |
| `my f x = e`(再帰しうる) | SCC ブロックの member | 確定 | 核の外。`RecursiveInference` |
| `x with: our h = ...` | `let h ... x` | 下書き | `our` 同士の順不同・値制限の順序は章3.5・2.1 |
| `(a, b)` | `pair a b` | 確定 | |
| `(a, b, c)` | `pair a (pair b c)` | 下書き | 右ネストの pair。`.0` `.1` `.2` は `fst` と `snd` の連鎖 |
| `{x: 1, y: 2}` | `record x 1 (record y 2 {})` | 確定 | 先頭が勝つ(決定 40) |
| `{x: 1, ..rest}` | `record x 1 rest` | 確定 | |
| `{..base, x: 3}` | `recordDefault x base 3` | 確定 | 決定44。核AST・presence-aware data推論・実評価を追加済み。surface翻訳passの証明とは区別する |
| `{x, y}` | `{x: x, y: y}` と同じ | 確定 | 章3.1 |
| `p.x`(field) | `field x p` | 確定 | field か method かは 6.4 の解決で決まる |
| `:tag e` | `variant l e` | 確定 | 構造的なpolyvariant tag |
| `enum::v e` | `NominalDataAssembly.Code.enumeration` → `CaseDataTerms.Expr.nominal typeId ctorId payload` | 確定（解決済み核） | 解決済みenum identityとconstructor tagを保持。source宣言lookup・payload型検査・site抽出はDの別義務 |
| `if c: a else: b` | `branch c a b` | 確定 | |
| `if c: a`(else なし) | `branch c (variant just a) (variant nil ())` | 確定 | 章3.6。`opt` |
| `elsif` | 入れ子の `branch` | 確定 | |
| `x | f` | `app f x` | 確定 | 章3.9 |
| `a + b` | 宣言された本体の展開: `app (app (lam (lam x.add y)) a) b` | 確定 | 章1.5。演算子は `infix` 宣言で決まる |
| `a and b` / `a or b` | `lazy infix` の本体に両辺を thunk として渡す | 確定 | 章1.5。短絡評価 |
| `-x`、`not x` | prefix 宣言の本体の展開 | 確定 | |
| `0..10` / `0..` | suffix/infix 宣言の本体(`std::data::range::...`) | 確定 | 閉区間 |
| `xs[i]` | `app (app (method index) xs) i`、解決済みlist本文は `NominalListIndexError.index` | 確定 | 回答済みQ9・Q10・Q12。任意整数の有効区間、Int/Emptyの具体宣言、無効時の同一operationと原index、wrap/catchと残余行まで証明。source名/宣言identityとrole辞書から本文へのelaborationは残る |
| `"a %{x} b"` | `Display` で `x` を文字列にして連結 | 下書き | 書式指定付きは `fmt` 相当の呼び出し。std 側 |
| `do` | 後続の文を継続 lambda にして、最も内側の呼び出しの引数にする | 確定 | 章3c.7。純粋に構文 |

## B. pattern と case

| 表の構文 | 核 | 状態 | 備考 |
| --- | --- | --- | --- |
| `case e: p1 -> a; p2 -> b` | `ScopedCaseDataProgram.eval`、`ScopedJointCaseCoverage.Typing` と順序付きarm | 確定 | 回答済みQ4のscopeとQ8のjoint被覆を同じ具体caseで型安全性へ接続。旧scope非依存の有限case入れ子は `CaseTree.Expr.caseE` として保持。scope付きCaseTree、effectfulな葉、一般Rust matrix、統一sourceは別義務 |
| `case:`(対象の式なし) | `lam (case #0 ...)`(`\x -> case x:`) | 確定 | 章3.7(2026-11-06)。`catch:` の同形・多引数は要確認 |
| guard `p if g -> a` | pattern成功後にbool guard、偽なら次のarm | 確定 | 実行順と網羅性checkerのguard除外を証明（3b.4）。source guardの名前解決は別義務 |
| 同一polyvariant tagの複数payload arm | `JointCaseCoverage.checkTag/checkRow`、全tag単位の `residual` | 確定 | 回答済みQ8。payload cellを別々のunguarded armが覆える。独立被覆判断・旧受理保存・Q4のscope付き具体caseのprogressへ接続。guard/float literalを被覆に数えない。一般pattern matrixは別義務 |
| or pattern、`as` | `CasePatterns.Pattern.or/as`、`ScopedCasePatterns.run` | 確定 | 回答済みQ6。左の照合成功で枝を確定しguard偽なら次のarmへ進む。失敗枝の束縛は他枝に漏らさない。異なる束縛順のsource整列は未証明 |
| record pattern の既定値 `{x = 1}` | `ScopedCasePatterns.run`、`ScopedJointCaseCoverage`、解決済みpresence検査とunion | 確定 | 回答済みQ4・Q5。先行束縛が外側を隠し、左から右・nested patternへ渡る。具体data型判断とjoint被覆から実評価のprogressを証明。先行missでは後続defaultを省略。Q7の同一経路の重複binderは実行前に拒否。全patternへのpresence検査・effectfulな葉は別義務 |
| 範囲 pattern `0..10` | `LiteralValues.intRangeCheck` | 確定 | 整数の閉区間/片側区間を追加。裸`..`は禁止。区間の合併による一般網羅性は別義務 |
| list pattern `[x, ..rest]` / `[..init, last]` | `CasePatterns.Pattern.cons/snoc` | 確定 | 残りの有限listを実際に渡す。nominal宣言・Fold/Indexのsource辞書への接続は別義務 |
| `~"GET :resource"` | parser 値を入力文字列に適用し、capture を束縛 | 下書き | 章9。後で詳しく |

## C. effect と制御

| 表の構文 | 核 | 状態 | 備考 |
| --- | --- | --- | --- |
| `op args`(operation の呼び出し) | `request op args` | 確定 | 普通の関数呼び出しに見える(章5.1) |
| `catch e: op p, k -> body; v -> ret` | `MultiOperationHandlerTyping.Expr.partialHandler arms target e ret bodies` | 確定 | 回答済みQ1を反映。同一keyの順序付きarm、missの外への伝播、unguarded反駁不能armだけのkey減算を独立型判断・checker・実行安全性へ接続。明示maskは全armを検査し、旧全域表との完全な一致も証明。source patternの束縛・effectful default/guard・mask導出・fresh座標への移送は別義務。追加lambdaで包まない。singleton handlerの入れ子化が意味を変えることも証明済み |
| `catch` の value arm 省略 | `v -> v` と同じ | 確定 | 章5.2 |
| 高階の境界の保護・解除 | `boundary(protect/release, mask) e` | 下書き | 型から elaboration が挿入する。利用者は書かない |
| `for x in xs: body` | `loop::for_in xs (\x -> body)` | 確定 | std の `for_in`(`main:lib/std/control/flow.yu`)。`last`/`next`/`redo` は `loop` の operation。値は常に `()` |
| `last` / `next` / `redo` | `request loop::last ()` など | 確定 | 章3c.2 |
| `for 'outer x in xs: body` | `label_loop::for_in xs (\'outer x -> body)`。label は `last`/`next`/`redo` を field に持つ struct の値 | 確定 | std。label は値として本体に渡される |
| `'outer.last` / `last 'outer` | label の値のメソッド `last` / `next` / `redo`(role `LoopLabel`) | 確定 | 衛生性(callback の effect は内側の handler から守られる)で外側へ届く |
| (旧)`'outer.last` の instance | label で指名した `loop` の操作 | 取消 | label は値(handler の instance を指す)。核に instance の同一性が無い |
| `sub: body` | `sub::sub body`(computation 引数) | 下書き | `sub` は std の `act`。`pub sub(x: [_] 'a) = catch x: return a, _ -> a; a -> a` |
| `return v` | `request sub::return v` | 確定 | |
| `'done.return v` / `sub 'done:` | label 付き `sub` | **欠** | label と同じ |
| `case 'count n: ... 'count.again (n - 1)` | arm 集合全体への再帰 | 下書き | `again` は label の操作。arm 集合を再帰関数にする |
| `my $a = e; rest` | `&a::run e (\&a -> rest)` | 確定 | 章3c.6 |
| `$a` | `&a` の読み出し operation | 確定 | `var` effect |
| `&a = v` | `&a` の更新 operation | 確定 | |
| `x.method`(effect 行の method) | effect 行から選ぶ | 確定 | 章5.8 |
| `if c`(c の行に `junction`) | `if junction::junction c: ...` | 確定 | 章5.9。型に依存して挿入(条件が pure なら何もしない) |

## D. 宣言

| 表の構文 | 核 | 状態 | 備考 |
| --- | --- | --- | --- |
| `struct p {x: int, y: int}` | `NominalDataAssembly.Code.structLiteral` → `CaseDataTerms.Expr.nominal` | 確定（解決済み核） | 保留cast siteから実record payload構築を接続。局所CastContractと独立Code型判断から値型を保存し、隠れるfieldの要求も残す。宣言lookup・固定field/default・source site抽出・cast合成は別義務 |
| `enum e = a | b x` | `NominalDataAssembly.Code.enumeration` → `CaseDataTerms.Expr.nominal` | 確定（解決済み核） | planのidentity/tagを保ち、保留siteから具体payloadへ接続。受理planの全request treeとEOF元値を保持。source宣言検査・site抽出・cast合成は別義務 |
| list literal の構築 | `NominalDataAssembly.Code.list` → `CaseDataTerms.Expr.nil/cons` | 確定（解決済み核） | 保留site実行器と型付きCodeの実list構築を接続。Fold cursorと整数Indexが同じpayloadを観測し、無効indexは任意encodingのerror要求へ接続。source辞書・site抽出・確定error宣言からのelaborationは別義務 |
| `[1, ..xs, 3]`・連続/空spread（有限listに解決済み） | `NominalListSpread.Part` → 実list値・共通Fold/Index観測、`FoldListSpreadFinite` でprotocolへ | 確定（解決済み有限list核） | 独立data型判断・環境・純粋変換契約から、各sourceを記述順に一度読む訪問列と全要素型を証明。任意の旧有限Meaningから同じflatten値・抽象requestへ写した全source traceのprotocol対応も証明。spread要素の新cast境界（Q14）、source site抽出・保留plan生成は別義務 |
| 任意の `Fold` を使うlist spread | `FoldTraversal.Driver`・`FoldListSpread.Engine` | 確定（解決済みprotocol核） | 回答済みQ13。rigid roleの一意辞書plan→供給driver、item型/source行/走査行のunion、局所契約から非停止を許す全有限prefix安全性/progress、走査完了後だけ次sourceへ進む合成。高階source Fold本体の生成・意味保存と全推論器への接続は別義務 |
| `type t = int`(alias) | 展開 | 確定 | 章4.4 |
| `role R 'a: ...` / `impl R T: ...` | 辞書(dictionary)の型と値 | 確定 | 辞書渡しは `RoleDictionaries` に証明がある |
| `where 'a: R` | 辞書引数 | 確定 | 具体化した場所で解く(決定 30) |
| `act a: our op: P -> Q` | operation の署名 | 確定 | `PolySignature` |
| `error e: v1 p; v2 q` | 下の「`error` 宣言の展開」 | 確定 | 章5.7。`wrap` は error effect → `result`、`up` は error effect → 別の error effect。型と非再開は章5.7で確定 |
| `cast(x: A): B = body` | cast 規則の登録 | 確定 | 本体は純粋。境界で挿入 |
| `act copy = source` | 新しい effect family | 確定 | 章5.6 |

## E. 型を見て挿入するもの(elaboration)

| 挿入するもの | 状態 | 備考 |
| --- | --- | --- |
| cast | 確定 | 型が合わないときだけ。関数・tuple・record・payload に通る(決定 16〜25) |
| 辞書引数 | 確定 | `where` の制約ごと |
| 保護・解除の境界 | 下書き | 高階の callback の境界。型から決まる |
| 保留された cast 境界 | 確定 | 不変の型引数を持つ nominal 型の構築(決定 25) |
| `junction::junction` | 確定 | `if` の条件の行に `junction` が出るとき(章5.9) |

## `error` 宣言の展開 (下書き)

```yulang
error path_err:
    not_found path
    denied path
```

作られるもの:

1. `enum path_err = not_found path | denied path` と、同名の operation を持つ `act`(`not_found: path -> never`、`denied: path -> never`)。variant は値の constructor であり operation でもある。期待型が error なら値、effect の位置なら operation
2. `impl Throw path_err`(`e.throw` で、variant に対応する operation を呼ぶ)
3. `impl Display path_err`(variant 名と payload を文字列にする)
4. `path_err::wrap : [path_err] 'a -> result 'a path_err`(確定) — error effect を handle して `result` に戻す。`ok v` か `err e`

`from` 付き(`enum app_err: path from path_err`)では、さらに次が作られる。

5. `app_err::up : [path_err] 'a -> [app_err] 'a`(確定) — `path_err` の operation を handle して、`app_err::path e` として投げ直す(error effect を cast する。継続は再開しない: error の operation は `never` を返す)
6. `app_err::wrap` は、`app_err` と `from` で結んだ `path_err`・`parse_err` の両方を handle する(狭いエラーを同時に捕まえる。章5.7)。狭いエラーは `err (app_err::path e)` のように `app_err` に包まれて `result` に入る(確定, 2026-11-06)

## 核に足りない形(まとめ)

ChatGPT に依頼する核の拡張の候補。

1. 分解するcase形は `CasePatterns` / `CaseEvaluation` に追加済み。保守的網羅性checker・merged残余・具体caseのprogressも追加済み。一般Rust matrix・統一sourceへの接続は別途追跡
2. 複数 operation の核は `MultiOperationHandlerTyping` に追加済み。残るのは source payload-pattern arm の編成、個別署名、多相、mask の elaboration
3. labelの値・methodと衛生的な境界をsourceから核へ対応させるelaboration。labelが値であること自体は章3c.2で確定
4. nominal構築の核と保留site実行は追加済み。source宣言・default/cast・辞書と統一ASTへのelaborationは残る
5. 整数・文字列・bool・unitの中身とbinary64の数値Eq、任意decoded小数tokenの最近接偶数丸め・静的overflowを追加済み。lexer・source診断・旧AST・Rust実装との接続が残る

決定44の `recordDefault` は上記の通り追加済み。`error` と `junction` の要求木helperも
`ErrorEffects` / `JunctionEffects` にあるが、ordinary strict applicationとの接続を含む
source elaborationの証明は別に必要である。

## 確認したいこと(ユーザーへ)

- 書式付き文字列の `fmt` の境界(std 側。`main:web/docs/ja/reference/strings.md` が素材。言語としては `Display` を呼ぶところまで)

`redo` は章3c.2で確定済み。同じ要素について本体の先頭からやり直し、既に起きたeffectや
state変更は巻き戻さない。この意味について再確認は不要である。

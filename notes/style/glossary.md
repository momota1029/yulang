# Yulangドキュメント用語集

本書は、Yulangドキュメントサイトの英語ページと日本語ページの対で使う用語の正本である。
日本語の表記は[Yulang日本語文章作法](./japanese-writing-guide.md)、翻訳対の構成は[Yulangドキュメント文章リズム規範](./writing-rhythm-guide.md)に従う。
用語の選択が本書と既存ページで異なる場合は、本書を優先する。

## 決定手順

新しい項目は、次の順で決める。

1. Yulangの識別子、キーワード、型名、モジュールパス、演算子、effect名は翻訳せず、コード表記にする。
   たとえば、キーワードの`my`、型名の`int`、モジュールパスの`std::data::list`、演算子の`::`、effect名の`flip`は原表記を保つ。
   同じ英単語でも、`error`キーワードは`error`、一般概念のerrorは以下の計測対象として役割を分ける。
2. `web/docs/ja/`以下で、原語のLatin表記と、同じ概念を表す日本語の全表記を行単位で測る。
   コードスパン、コードフェンス、リンク先、HTMLは除外する。
   どちらか一方が他方の4倍以上なら、その側を採る。
   Latin表記が勝った項目は、原語をコード表記にして、ここで決定を終える。
3. どちらも4:1に達しない場合は、多数側を採る。
   同数、または行単位の標本で差が1行しかない場合は、差が小さすぎるものとして原語をコード表記にする。
   Yulangの既存ページが技術語をLatin表記で保つ傾向に沿う、保守的な決め方である。
   多数決でLatin表記が勝った場合も、原語をコード表記にする。
   多数決と同数・1行差のどちらを使った場合も、両側の行数を記録する。
4. 手順2または3で日本語側が勝ち、かつ競合するカタカナ表記がある場合だけ、カタカナ表記を決める。
   一方の綴りが他方の4倍以上なら、その綴りを採る。
   4:1に達しなければ、日本語文章作法の長音規則をtiebreakerとして使う。
   Latin表記をカタカナへ変えるために長音規則を使ってはならない。

サイトに原語も日本語表記もない0:0の候補は、用語集へ入れない。
初出より前に判断が必要な語だけを「初出前に判断する語」へ分け、必要な理由を添える。

## 計測方法と内訳

計測日は2026年7月26日で、対象は`web/docs/ja/`以下の30ページである。
英字は大文字と小文字を区別せず、同じ表記が同じ行に複数回あっても1行と数えた。
複合語が別の候補でもある場合は、概念境界を分けて数えた。
たとえば、一般名詞の`library`と`standard library`、一般概念の`file`と`file` effectは別項目である。

候補は、30組の英語ページの見出し、定義語、技術語と、日本語ページのカタカナ列、対応見出しから作った。
活用形、単数と複数、複合語の重複を一つの概念へまとめ、製品名、ページ移動の語、コード要素を除いた結果、91概念が残った。
再分類では、Rule 2が54項目、Rule 3が33項目、Rule 4が3項目になった。
0:0の`computer`は削除したため、以下の用語集は90項目である。

表の数は、日本語30ページ中の行数である。
0行の競合形も省略しない。

## 言語の構文と表面

| English term | 日本語で使う表記 | 根拠 |
| --- | --- | --- |
| application | `application` | Rule 3（多数）。`application`32行対「適用」16行。 |
| bare application | `bare application` | Rule 3（多数）。`bare application`4行対「裸のapplication」2行。 |
| binding | `binding` | Rule 2（Latin）。`binding`62行対「バインディング」「束縛」0行。 |
| block | `block` | Rule 2（Latin）。`block`30行対「ブロック」5行。 |
| call | 呼び出し | Rule 3（多数）。「呼び出し」42行対`call`32行。 |
| cast | `cast` | Rule 3（多数）。`cast`14行対「キャスト」6行。 |
| colon | `colon` | Rule 3（1行差）。`colon`12行対「コロン」11行なので原語を保つ。 |
| companion module | `companion module` | Rule 2（Latin）。`companion module`15行対日本語表記0行。 |
| constraint | `constraint` | Rule 3（同数）。`constraint`9行対「制約」9行なので原語を保つ。 |
| constructor | `constructor` | Rule 2（Latin）。`constructor`7行対「コンストラクタ」1行。 |
| continuation | `continuation` | Rule 3（1行差）。「継続」5行対`continuation`4行なので原語を保つ。 |
| curry / curried | `curry` / `curried` | Rule 3（多数）。`curry`または`curried`7行対「カリー化」5行。サイトで使われていない`currying`は採用形にしない。 |
| declaration | 宣言 | Rule 2（日本語）。「宣言」42行対`declaration`5行。 |
| default | `default` | Rule 3（多数）。`default`12行対「デフォルト」8行。 |
| dot | `dot` | Rule 3（多数）。`dot`13行対「ドット」6行。 |
| enum | `enum` | Rule 2（Latin）。`enum`9行対「列挙型」0行。 |
| expression | 式 | Rule 2（日本語）。「式」63行対`expression`4行。 |
| field | `field` | Rule 2（Latin）。`field`24行対「フィールド」4行。 |
| function | 関数 | Rule 2（日本語）。「関数」61行対`function`10行。 |
| guard | `guard` | Rule 3（同数）。`guard`6行対「ガード」6行なので原語を保つ。 |
| import | `import` | Rule 2（Latin）。`import`29行対「インポート」0行。 |
| lambda | ラムダ | Rule 3（多数）。「ラムダ」11行対`lambda`5行。 |
| list | `list` | Rule 3（多数）。`list`18行対「リスト」5行。 |
| literal | リテラル | Rule 2（日本語）。「リテラル」7行対`literal`1行。 |
| loop | ループ | Rule 3（多数）。「ループ」9行対`loop`7行。 |
| method | `method` | Rule 2（Latin）。`method`52行対「メソッド」1行。 |
| module | `module` | Rule 2（Latin）。`module`36行対「モジュール」4行。 |
| operator | 演算子 | Rule 3（多数）。「演算子」32行対`operator`26行。 |
| parser pattern | `parser pattern` | Rule 2（Latin）。`parser pattern`5行対日本語表記0行。 |
| path | `path` | Rule 2（Latin）。`path`25行対「パス」4行。 |
| pattern | `pattern` | Rule 3（多数）。`pattern`31行対「パターン」17行。 |
| pattern matching | パターンマッチ | Rule 2（日本語）。「パターンマッチ」6行対`pattern matching`0行。 |
| Pythagorean triple | ピタゴラス数 | Rule 2（日本語）。「ピタゴラス数」2行対`Pythagorean triple`と「ピタゴラス三角形」0行。 |
| prelude | `prelude` | Rule 2（Latin）。`prelude`29行対「プリリュード」0行。 |
| primitive / primitive type | `primitive` / `primitive type` | Rule 2（Latin）。`primitive`8行対日本語表記0行。 |
| record | `record` | Rule 2（Latin）。`record`15行対単独の「レコード」3行。 |
| reference | 参照 | Rule 2（日本語）。「参照」37行対`reference`2行。 |
| role | `role` | Rule 2（Latin）。`role`56行対「ロール」6行。 |
| scope | `scope` | Rule 3（1行差）。「スコープ」6行対`scope`5行なので原語を保つ。 |
| signature | シグネチャ | Rule 4。日本語側はRule 3で「シグネチャ」11行対`signature`3行の多数。カタカナは「シグネチャ」11行対「シグネチャー」0行で4:1以上。 |
| spread | `spread` | Rule 3（多数）。`spread`5行対単独の「スプレッド」2行。 |
| standard library | 標準ライブラリ | Rule 2（日本語）。「標準ライブラリ」18行対`standard library`3行。単独の`library`とは分ける。 |
| struct | `struct` | Rule 3（多数）。`struct`11行対「構造体」8行。 |
| tuple | `tuple` | Rule 2（Latin）。`tuple`11行対単独の「タプル」1行。 |
| variant | `variant` | Rule 2（Latin）。`variant`24行対「バリアント」0行。 |
| visibility | 可視性 | Rule 3（多数）。「可視性」8行対`visibility`3行。 |
| wildcard | `wildcard` | Rule 3（多数）。`wildcard`5行対「ワイルドカード」2行。 |

## 型とeffect

| English term | 日本語で使う表記 | 根拠 |
| --- | --- | --- |
| algebraic effect | `algebraic effect` | Rule 3（1行差）。「代数的エフェクト」2行対`algebraic effect`1行なので原語を保つ。 |
| effect | `effect` | Rule 2（Latin）。単独の`effect`166行対「エフェクト」10行。 |
| effect family | `effect family` | Rule 2（Latin）。`effect family`13行対日本語表記0行。 |
| effect row | `effect row` | Rule 2（Latin）。`effect row`37行対日本語表記0行。 |
| effectful computation | `effectful computation` | Rule 2（Latin）。`effectful computation`2行対日本語表記0行。 |
| handler | `handler` | Rule 2（Latin）。`handler`72行対「ハンドラー」1行。 |
| handler hygiene | `handler hygiene` | Rule 2（Latin）。`handler hygiene`7行対日本語表記0行。 |
| nondeterminism | 非決定性 | Rule 2（日本語）。「非決定性」6行対`nondeterminism`1行。 |
| residual row | `residual row` | Rule 2（Latin）。`residual row`7行対日本語表記0行。 |
| shallow handler | `shallow handler` | Rule 2（Latin）。`shallow handler`1行対日本語表記0行。 |
| subtyping | `subtyping` | Rule 2（Latin）。`subtyping`4行対「部分型付け」0行。 |
| thunk | `thunk` | Rule 2（Latin）。`thunk`8行対「サンク」0行。 |
| type | 型 | Rule 2（日本語）。「型」139行対`type`34行。 |
| type annotation | 型注釈 | Rule 2（日本語）。「型注釈」5行対`type annotation`1行。 |
| ascription | `ascription` | Rule 2（Latin）。`ascription`2行対日本語表記0行。 |
| type inference | 型推論 | Rule 2（日本語）。「型推論」10行対`type inference`0行。 |
| type variable | `type variable` | Rule 3（多数）。`type variable`12行対「型変数」5行。 |
| value | 値 | Rule 2（日本語）。「値」101行対`value`17行。 |

## 内部モデル

公開ページで説明する内部概念にも同じ表記を使う。
これらは識別子ではなく概念名なので、用例数で決める。

| English term | 日本語で使う表記 | 根拠 |
| --- | --- | --- |
| band | `band` | Rule 2（Latin）。`band`17行対「バンド」0行。 |
| directed stack weight | `directed stack weight` | Rule 2（Latin）。`directed stack weight`3行対日本語表記0行。 |
| realm | `realm` | Rule 2（Latin）。`realm`16行対「レルム」0行。 |
| row subtraction | `row subtraction` | Rule 2（Latin）。`row subtraction`1行対日本語表記0行。 |
| stack evidence | `stack evidence` | Rule 2（Latin）。`stack evidence`3行対日本語表記0行。 |

## 一般概念

一般概念にも同じ手順を使う。
日本語文章作法の長音規則は、Rule 4へ進んだ項目にしか適用しない。

| English term | 日本語で使う表記 | 根拠 |
| --- | --- | --- |
| browser | `browser` | Rule 3（1行差）。`browser`2行対「ブラウザ」1行、「ブラウザー」0行なので原語を保つ。 |
| buffer | `buffer` | Rule 2（Latin）。`buffer`7行対「バッファ」「バッファー」0行。 |
| cache | `cache` | Rule 3（多数）。`cache`12行対「キャッシュ」6行。 |
| code | コード | Rule 3（多数）。「コード」8行対`code`4行。 |
| comment | コメント | Rule 3（多数）。「コメント」10行対`comment`8行。 |
| compiler | `compiler` | Rule 2（Latin）。`compiler`13行対「コンパイラ」2行、「コンパイラー」0行。 |
| directory | `directory` | Rule 2（Latin）。`directory`6行対「ディレクトリ」1行、「ディレクトリー」0行。 |
| document | `document` | Rule 3（同数）。`document`2行対「ドキュメント」2行なので原語を保つ。 |
| error | エラー | Rule 3（多数）。一般概念の「エラー」39行対`error`31行。`error`キーワードはRule 1に従う。 |
| file | `file` | Rule 3（多数）。一般概念の`file`21行対「ファイル」19行。`file` effect名はRule 1に従う。 |
| interface | `interface` | Rule 2（Latin）。`interface`3行対「インターフェイス」「インターフェース」0行。 |
| library | ライブラリ | Rule 4。日本語側はRule 2で単独の「ライブラリ」20行対`library`3行の4:1以上。カタカナは「ライブラリ」20行対「ライブラリー」0行で4:1以上。 |
| page | ページ | Rule 2（日本語）。「ページ」27行対`page`0行。 |
| parser | `parser` | Rule 2（Latin）。一般名詞の`parser`15行対「パーサ」「パーサー」0行。`parser pattern`は別項目に従う。 |
| program | プログラム | Rule 3（多数）。「プログラム」8行対`program`6行。 |
| project | `project` | Rule 3（同数）。`project`1行対「プロジェクト」1行なので原語を保つ。 |
| receiver | `receiver` | Rule 3（多数）。`receiver`8行対「レシーバ」6行、「レシーバー」0行。 |
| server | `server` | Rule 2（Latin）。`server`3行対「サーバ」「サーバー」0行。 |
| user | ユーザー | Rule 4。日本語側はRule 2で単独の日本語表記9行対`user`2行の4:1以上。カタカナは「ユーザー」7行対「ユーザ」2行で4:1未満なので、長音規則をtiebreakerにした。 |
| wrapper | `wrapper` | Rule 2（Latin）。`wrapper`9行対「ラッパ」0行、「ラッパー」1行。 |

## 表記が割れている語と残差

ここでは、原語側と日本語側の両方に1行以上ある語、または競合するカタカナ表記がある語を「割れている語」とする。
「残差」は、採用形へそろえる別変更で直す側と、その行数である。
同じ行に複数の項目があり得るため、行数を項目間で合計しない。

| Term | 計測 | 採用形 | 残差 |
| --- | --- | --- | --- |
| application | `application`32対「適用」16 | `application` | 「適用」16 |
| bare application | `bare application`4対「裸のapplication」2 | `bare application` | 「裸のapplication」2 |
| block | `block`30対「ブロック」5 | `block` | 「ブロック」5 |
| call | 「呼び出し」42対`call`32 | 呼び出し | `call`32 |
| cast | `cast`14対「キャスト」6 | `cast` | 「キャスト」6 |
| colon | `colon`12対「コロン」11 | `colon` | 「コロン」11 |
| constraint | `constraint`9対「制約」9 | `constraint` | 「制約」9 |
| constructor | `constructor`7対「コンストラクタ」1 | `constructor` | 「コンストラクタ」1 |
| continuation | 「継続」5対`continuation`4 | `continuation` | 「継続」5 |
| curry / curried | `curry`または`curried`7対「カリー化」5 | `curry` / `curried` | 「カリー化」5 |
| declaration | 「宣言」42対`declaration`5 | 宣言 | `declaration`5 |
| default | `default`12対「デフォルト」8 | `default` | 「デフォルト」8 |
| dot | `dot`13対「ドット」6 | `dot` | 「ドット」6 |
| expression | 「式」63対`expression`4 | 式 | `expression`4 |
| field | `field`24対「フィールド」4 | `field` | 「フィールド」4 |
| function | 「関数」61対`function`10 | 関数 | `function`10 |
| guard | `guard`6対「ガード」6 | `guard` | 「ガード」6 |
| lambda | 「ラムダ」11対`lambda`5 | ラムダ | `lambda`5 |
| list | `list`18対「リスト」5 | `list` | 「リスト」5 |
| literal | 「リテラル」7対`literal`1 | リテラル | `literal`1 |
| loop | 「ループ」9対`loop`7 | ループ | `loop`7 |
| method | `method`52対「メソッド」1 | `method` | 「メソッド」1 |
| module | `module`36対「モジュール」4 | `module` | 「モジュール」4 |
| operator | 「演算子」32対`operator`26 | 演算子 | `operator`26 |
| path | `path`25対「パス」4 | `path` | 「パス」4 |
| pattern | `pattern`31対「パターン」17 | `pattern` | 「パターン」17 |
| record | `record`15対「レコード」3 | `record` | 「レコード」3 |
| reference | 「参照」37対`reference`2 | 参照 | `reference`2 |
| role | `role`56対「ロール」6 | `role` | 「ロール」6 |
| scope | 「スコープ」6対`scope`5 | `scope` | 「スコープ」6 |
| signature | 「シグネチャ」11対`signature`3、長音形0 | シグネチャ | `signature`3 |
| spread | `spread`5対「スプレッド」2 | `spread` | 「スプレッド」2 |
| standard library | 「標準ライブラリ」18対`standard library`3 | 標準ライブラリ | `standard library`3 |
| struct | `struct`11対「構造体」8 | `struct` | 「構造体」8 |
| tuple | `tuple`11対「タプル」1 | `tuple` | 「タプル」1 |
| visibility | 「可視性」8対`visibility`3 | 可視性 | `visibility`3 |
| wildcard | `wildcard`5対「ワイルドカード」2 | `wildcard` | 「ワイルドカード」2 |
| algebraic effect | 「代数的エフェクト」2対`algebraic effect`1 | `algebraic effect` | 「代数的エフェクト」2 |
| effect | `effect`166対「エフェクト」10 | `effect` | 「エフェクト」10 |
| handler | `handler`72対「ハンドラー」1 | `handler` | 「ハンドラー」1 |
| nondeterminism | 「非決定性」6対`nondeterminism`1 | 非決定性 | `nondeterminism`1 |
| type | 「型」139対`type`34 | 型 | `type`34 |
| type annotation | 「型注釈」5対`type annotation`1 | 型注釈 | `type annotation`1 |
| type variable | `type variable`12対「型変数」5 | `type variable` | 「型変数」5 |
| value | 「値」101対`value`17 | 値 | `value`17 |
| browser | `browser`2対「ブラウザ」1、長音形0 | `browser` | 「ブラウザ」1 |
| cache | `cache`12対「キャッシュ」6 | `cache` | 「キャッシュ」6 |
| code | 「コード」8対`code`4 | コード | `code`4 |
| comment | 「コメント」10対`comment`8 | コメント | `comment`8 |
| compiler | `compiler`13対「コンパイラ」2、長音形0 | `compiler` | 「コンパイラ」2 |
| directory | `directory`6対「ディレクトリ」1、長音形0 | `directory` | 「ディレクトリ」1 |
| document | `document`2対「ドキュメント」2 | `document` | 「ドキュメント」2 |
| error | 「エラー」39対`error`31 | エラー | `error`31 |
| file | `file`21対「ファイル」19 | `file` | 「ファイル」19 |
| library | 「ライブラリ」20対`library`3、長音形0 | ライブラリ | `library`3 |
| program | 「プログラム」8対`program`6 | プログラム | `program`6 |
| project | `project`1対「プロジェクト」1 | `project` | 「プロジェクト」1 |
| receiver | `receiver`8対「レシーバ」6、長音形0 | `receiver` | 「レシーバ」6 |
| user | 「ユーザー」7と「ユーザ」2対`user`2 | ユーザー | `user`2、「ユーザ」2 |
| wrapper | `wrapper`9対「ラッパー」1、短音形0 | `wrapper` | 「ラッパー」1 |

## Sanity check

4:1以上の全項目で、採用形は多数側と一致した。
したがって、すでに4:1以上で一貫している語の多数形を非採用にした項目はない。
上表の残差はすべて、各項目の少数形、または4:1未満の語で多数決・同数・1行差規則の結果として非採用になった形である。
既存ページとの不一致行数そのものは、手順の誤作動を示さない。

## 初出前に判断する語

現在は該当なし。
原語も日本語表記も0行だった`computer`は、必要性を示すページがないためここにも置かない。

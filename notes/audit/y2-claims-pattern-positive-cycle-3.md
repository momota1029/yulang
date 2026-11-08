# Cycle 3: 制御・pattern の追加受理候補と境界

旧 Y2 `d4c8bc8fc`、新 spec `816ed8f1d`。source変更・build・公開なし。cycle1/2 の `y2-claims-control-patterns.md`、`y2-claims-pattern-effects-cycle-2.md`、`y2-claims-pattern-order-cycle-2.md`、x-oracle を照合した。OR未統合、括弧なしas結合力、record spread whole/default順序、pipe/catch等の既存行を新発見として重複計上しない。今回は括弧付きOR aliasの左右成功、list remainder、parser capture/full-input境界等を増分とする。

分類の「一致」はこの有限入力で文書/specに整合したという意味であり、一般的完全性・source-to-Lean橋渡しの証明ではない。既存 Lean の解決済み核の定義に対応づけたが、この監査では新しい定理・Lean build はない。

| ID | 出典 | 規則 | 例 | 実機の結果 | 新 spec | Lean | 分類 | 備考 |
|---|---|---|---|---|---|---|---|---|
| C3-POS-OR-AS | 旧patterns.md as alias節 | 括弧付きOR全体へのaliasは左右どちらでも束縛 | normalize `("yes" \| "y") as matched` にyes/y/other | no-prelude check0/dump0/run0、`("yes","y","no")` | 03b.6/.6' と整合 | ScopedCasePatterns.run の .or と .as は解決済み核。parser結合力のsource橋渡し未確認 | 一致 | 旧Y2-PAT-004の括弧なし失敗とは別の成功対照。binder付きOR枝同士の共有を証明しない |
| C3-POS-TUPLE-AS | 旧patterns.md tuple/as節 | 入れ子tupleを分解し同時に全体をalias | `our rearrange (((a,b),c) as whole)=(c,b,a,whole)` | no-prelude check0/dump0/run0、`(true,"two",1,((1,"two"),true))` | 03b.1 tuple/asと整合 | ScopedCasePatterns.run .pair/.as | 一致 | 初期の外側括弧なし関数引数ではwhole未解決。修正版を別ファイル/ログに保存した。初期失敗を消していない |
| C3-POS-RENAMED-DEFAULT | 旧patterns.md 別名とdefault節 | field別名と省略defaultを組み合わせる | `{host:h="localhost",port:p=80}`、{},hostのみ,portのみ | no-prelude check0/dump0/run0、`(("localhost",80),("remote",80),("localhost",443))` | 03b.3 | ScopedCasePatterns.run .defaultField とbinding；source生成未追跡 | 一致 | 既存Y2-PAT-006の依存default順序試験ではなく、別名と独立省略の受理例 |
| C3-POS-ENUM-USE | 旧patterns.md enum pattern節 | wildcard import後の短名をconstructorとして照合 | color red/green/blue、`use color::*` | no-prelude check0/dump0/run0、`("r","g","b")` | 03b.2 ctor名の解決 | ScopedCasePatterns.run .nominal は解決済みtypeId/ctorId照合。import/name-resolution橋渡し未確認 | 一致 | constructor未import時のfresh binding問題を修正したとの主張ではない |
| C3-POS-VARIANT-BOOL | 旧patterns.md polyvariant節 | 同じtagのbool payloadを2armに分けて照合 | `:flag true ->1; :flag false ->0` | no-prelude check0/dump0/run0、`(1,0)` | 03b.4に同じpayload分割の網羅例 | ScopedCasePatterns.run .variant/.literal。網羅性checkerとのsource接続未検証 | 一致 | 実行成功から一般網羅性/完全性は主張しない |
| C3-POS-TUPLE-OR | 旧patterns.md OR/tuple節 | ORの中にbindingを置かず、tupleの別成分を束縛 | `(0 \| 1,y)->y; (_,y)->0` | no-prelude check0/dump0/run0、`(7,8,0)` | 03b.1/.6 | ScopedCasePatterns.run .pair/.or | 一致 | 既存OR binder共有バグを踏む例ではない |
| C3-POS-LIST-ORDER | 旧patterns.md list節 | []、一要素、二要素、head/restの順で最初のarmを選ぶ | classify [],[9],[9,8],[9,8,7] | 標準環境run0 ` (0,1,2,3)`、dump0、checkは8秒timeout | 03b.3/.4 | ScopedCasePatterns.run .nil/.cons；source list sugar未追跡 | 一致 | no-prelude試験ではlist型未解決。標準依存不足をspec上の拒否としない。check通過は主張しない |
| C3-POS-LIST-PREFIX | 旧patterns.md list節 | `[first,..rest]`のrestは残りlist | split [1,2,3]/[]、返り値にrestそのものを含む | 標準check/runとも8秒timeout、dump0 | 03b.3はrecord全体と異なり残りlistを指定 | ScopedCasePatterns.run .cons はrest listを渡す | 未確認 | 時間内に値を得られず成功としない。定義の存在は旧CLIの成功証明ではない |
| C3-POS-LIST-SUFFIX | 旧patterns.md list節 | `[..init,last]`のinitは最後を除いたlist | split [1,2,3]/[] | 標準check8秒timeout、dump0、run1 `unhandled effect request std::control::flow::loop::last` | 03b.3 | ScopedCasePatterns.run .snoc はreverseでinit/lastを分離 | 未確認 | 追補でbodyのlastがbinderではなく標準nullfix last呼出と判明。初期例は名前衝突を含み、matcher失敗の証拠にはしない |
| C3-POS-LIST-MIDDLE | 旧patterns.md list spread1個の一般説明 | 先頭/末尾patternの間にrestを置く探索 | `[first,..middle,last]` に長さ4/2/1 | 標準check8秒timeout、dump0、run1 同じloop::last | 新03b.3は先頭/末尾spreadを明記、中間を本調査だけで設計確定しない | .cons/.snoc合成で表せる核はあるがsurface bridge未確認 | 未確認 | bodyのlastは標準nullfix演算子にlowerされていた。初期失敗はmatcher評価に使わず改名対照を別記。中間をdocの明示的保証と誇張しない |
| C3-POS-PARSER-WORD | 旧parser-dsl.md caseでのマッチ/word capture | word captureは入力全体消費が必要 | `~"GET :resource"`、GET users / GET users now | 標準run0 `("users","no match")`、dump0、check8秒timeout | 09 §9.1/.2、03 §3.10 | parser DSL全体のLean対応を今回特定していない | 一致 | no-prelude+useだけではstd::text::parse::token未解決だった。標準prelude環境でのrun成功と区別 |
| C3-POS-PARSER-REST | 旧parser-dsl.md rest capture | `{tail=..}`は空も含め残り全体を取る | `~"GET /{tail = ..}"`、GET /users/42、GET /、POST / | 標準run0 `("users/42","","no match")`、dump0、check8秒timeout | 09 §9.2 | source DSL/stdlib/Lean橋渡し未確認 | 一致 | prefix一致だけでなく不一致fallbackとempty captureを対照 |

## 失敗した探索と明示差

`qualified-enum-payload-alias` は `enum answer: value (int,bool)` とcaseのtuple aliasで試したが、check/run1 `unsupported pattern syntax: pattern`。dumpはenum constructorが2引数の形に解釈されており、こちらのtuple payloadの記法選択が想定と一致していない。意図したsurfaceを構成できていない可能性を残し、新spec不一致や受理成功には数えない。

旧OR binding非統合と新spec同名共有、旧括弧なしasの結合力と新spec結合力、旧my分割代入網羅性非検査と新spec拒否は、cycle1/2既存表にある明示差。今回はその結論を上書きせず、安全な括弧付きaliasとbinderなしORの成功を別途確認した。parser nested patternは新spec09で一般化を明記するが、この調査はcase arm最上位の例だけであり、入れ子対応を検証済みとはしない。

## ログ

`runtime-cycle-3-pattern-positive.md/json`（初期10入力30 CLI）、`runtime-cycle-3-pattern-positive-extra.md/json`（追加4入力12 CLI）、`runtime-cycle-3-pattern-standard.md/json`（標準環境7入力21 CLI）に出力全文。標準dumpはstdlibを含み約2.8 MBであり、省略していない。全例を標準環境とno-preludeの両方で実施したわけではない。標準各CLI上限8秒、no-prelude上限5秒。Timeoutは終了コードnullとして記録し、run成功をcheck成功に読み替えない。

### list値の表示だけかを分ける追加対照

`runtime-cycle-3-list-observe.md/json` に3件の標準runを追加した。restを直接返さず、内側caseで残りlistを分解して整数tupleだけを返す。prefix/suffixは各8秒timeout、中間rest版は同じ `unhandled std::control::flow::loop::last`。【後続sourceレビューで訂正】この対照にもbodyのlastが残り、標準nullfix last呼出となるため、matcher/表示の独立切り分けとしては不十分だった。prefix/suffixは時間切れのため、matcherの失敗とも断定できない。

全ログ合計66 CLI、exit0 37件、非0 19件、timeout10件、実測command時間合計83.043728秒。exit0件数には診断を含むdumpもある。初期入力の失敗、標準依存の不足、実行上限をすべて保持した。

### C3-POS-LIST-SUFFIX / MIDDLE の訂正と改名対照

`list-source-review.md` にsourceとdumpの追跡を保存。初期bodyのlastはpattern binderでなく標準nullfix演算子だった。新規ファイルでlastをend_itemに変えた4 CLI（各30秒上限）を `runtime-cycle-3-list-renamed.md/json` に保存した。suffix check/run、middle checkはtimeout。middle runだけexit0で `((1,[2,3],4),(1,[],4),(0,[],0))`。したがってC3-POS-LIST-MIDDLEは「改名後の有限runでremainder意味に整合、check未完」、suffixは「名前衝突を除いた再試験は時間切れで未確認」に更新する。初期名前衝突rawは保持。以前の66件集計とは別に4件追加、合計70 CLIとなる。

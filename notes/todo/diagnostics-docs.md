# Diagnostics and Docs TODO

目的: 実装ノートを読まなくても言語を使える状態にする。

## 公開後の優先

公開直後は、診断を「出る」から「直せる」へ寄せる。

優先する情報:

- code: CLI / playground / LSP が同じ原因を同じ分類として扱える安定した識別子。
- primary range: 実際に直すべき式・型・pattern の位置。
- related information: 比較対象になった型、注釈、リテラル、束縛、呼び出し元の位置。
- provenance: expected / actual が注釈、リテラル、関数適用、role/method 解決、
  handler residual のどこから来たか。
- hover: diagnostic range に乗った時、同じ provenance を短く見られること。
- shared payload: CLI / playground / LSP が同じ構造化 diagnostic から表示を作ること。

近い作業:

- 型エラーの comparison に `expected_origin` / `actual_origin` 相当の構造を持たせる。
  - first slice: `SourceDiagnosticRelated.origin` で type annotation / expression を区別する。
- LSP diagnostic の `relatedInformation` を、型比較の両側と注釈位置へ張る。
- diagnostic hover 用に、短い markdown summary を構造化 diagnostic から作る。
- `my a = 1 2` のような最小失敗例で、primary range と related range を固定する。
- playground の blank / missing diagnostic regression を小さい fixture で追う。

## 2026-07-01 weekly target

今週は diagnostics と標準 API 固定を、公開準備の主作業として扱う。

Diagnostics の最初の slice:

- public CLI golden を小さく追加し、現在の `check` で見える代表的な lowering
  diagnostics を固定する。
- 最初に固定するケースは、型注釈 mismatch、未解決 value name、未解決 type name、
  top-level mutable binding、未閉じ delimiter recovery。
- `check` は source diagnostics がある場合、詳細 dump の前に compact な
  `diagnostics:` summary を出す。
- malformed module parse は CLI panic にしない。2026-07-01 時点では未閉じ `(` を
  empty `InvalidToken` として recovery し、`check` が完走するところまで固定した。
  次の改善で user-facing parser diagnostic へ接続する。
- 続けて parser error、role/method error、effect/runtime error を足す。
- 期待値は全文 snapshot にせず、ユーザーが直すために必要な主文言と label だけを
  compact に見る。
- その後、同じ原因を `CheckReport` / LSP / playground で共有できる表示へ移す。
- 2026-07-01 時点で、type mismatch、unresolved value/type、top-level mutable
  binding、unsupported rule lazy quantifier は `SourceDiagnostic.code` から CLI
  summary / LSP diagnostic code / playground diagnostic code へ流れる。
- 同日後続 slice で、型注釈 mismatch は annotation / expression の related 情報を
  `SourceDiagnostic.related` に載せ、CLI note / LSP relatedInformation /
  playground JSON related へ流れる。
- 同日後続 slice で、CLI `check` summary は primary / related range に対して
  1-based line / column と source frame を表示する。std-root で差し込まれる
  implicit prelude は CLI 表示から差し引く。
- 同日後続 slice で、root module の parser recovery `InvalidToken` は
  `yulang.syntax` として CLI / LSP / playground に流れる。未閉じ `(` は
  `syntax error: unexpected end of input` として user source line の末尾を指す。
- 同日後続 slice で、root module parse loop が stop token を捨てて silent success
  していた末尾演算子 `my x = 1 +` を、`yulang.syntax` の unexpected token として
  CLI / LSP / playground に流す。diagnostic range は trailing trivia を含めず、
  実際に直すべき token 本体だけを指す。
- 同日後続 slice で、通常の `run` 経路で処理されない effect request が外へ漏れた
  とき、CLI は `yulang.unhandled-effect` と handler 追加を促す hint を表示する。
  これは runtime evidence VM の内部エラー文言を user-facing contract にしないための
  最初の runtime diagnostic canary とする。
- 同日後続 slice で、文法上は application として valid な `1 2` のような
  not-callable runtime failure は `yulang.not-callable` と call syntax hint を出す。
- 同日後続 slice で、`1.a` と unmatched `case` の normal run runtime failure は
  それぞれ `yulang.not-record` / `yulang.pattern-mismatch` として、field access /
  fallback pattern の hint を出す。
- 同日後続 slice で、特殊化段の `UnsatisfiedSubtype` は
  `compile error [yulang.unsatisfied-subtype]` として、値が要求された field/shape を
  満たしているか見直す hint を出す。
- 同日後続 slice で、`type mismatch` の related payload は
  `SourceDiagnosticRelated.origin` を持ち、expected が type annotation 由来、
  actual が expression 由来であることを CLI / LSP / playground へ同じ message として流す。
- 同日後続 slice で、record literal が expected record consumer の必須 field を
  満たさない `UnsatisfiedSubtype` は `UnsatisfiedSubtypeOrigin::MissingRecordField`
  を持つ。CLI は missing field 名と実際の record field 一覧を出す。source range はまだ
  specialize に来ていないため、次の detailed diagnostics で selection / expected shape
  origin と接続する。
- 同日後続 slice で、`SourceDiagnostic` は optional `hint` を持つ。未解決 value/type
  name は CLI / LSP / playground に同じ修復案を流す。

API 固定の最初の slice:

- filesystem は `spec/2026-07-01-file-resource-api.md` を anchor とする。
- server API は、file session と同じ resource lifetime / scope exit / host capability
  のモデルへ寄せる。
- FFI は標準 API の裏側になりうるが、当面は public ABI ではなく host capability
  boundary として扱う。
- API メモの都合で既存 std surface を compatibility promise にしない。

## Detailed type checker

Simple-sub、`case` / `catch`、role / impl conformance をまとめて扱う計画は
次に置く。

- TODO: `type-checker-diagnostics.md`
- 設計: `../diagnostics/type-checker-plan.md`

この作業では、推論器を別実装に置き換えず、solver / lowering が持つ構造化された
型・制約・origin・expected edge・role fact を `CheckReport` へ集める。
CLI / LSP / playground はその report を読む。

## Diagnostics

ユーザー向け diagnostics は、compiler / runtime の内部実装詳細ではなく、
言語レベルの原因を説明する。

TODO:

- Parser errors:
  - unexpected token
  - expected forms
  - line / column
  - compact source frame
- Type errors:
  - surface expression の名前を出す
  - expected / actual の衝突した形を示す
  - 可能な範囲で raw internal type variable noise を避ける
  - expected / actual の出自を related information へ出す
  - unresolved value/type name は定義または import の hint を出す
  - LSP hover で同じ出自情報を短く見せる
- Role / method errors:
  - missing role impl
  - ambiguous role impl
  - missing method
  - missing field
- Effect errors:
  - unhandled effect
    - first CLI canary: `runtime error [yulang.unhandled-effect]` with a
      handler hint on `run` when `std::control::nondet::each` escapes.
  - handler arm mismatch
  - unsupported host request
- Runtime / lowering errors:
  - 普通の user path で residual polymorphic runtime IR を漏らさない
  - impossible runtime state は recoverable value ではなく trap として説明する
  - not-callable は `runtime-evidence-run not a function` ではなく、call syntax を
    見直せる user-facing message として出す。
  - not-record / pattern-mismatch も同じ normal run formatter を通し、VM 内部文言を
    user-facing contract にしない。
  - specialize の unsatisfied subtype は型/shape 契約違反として compile error code
    を付ける。record literal の missing required field は structured origin を持つ。
    将来的には source range / expected-origin と接続する。

## Examples

現在の examples は CLI と playground から実行できる状態を保つ。

TODO:

- public-facing feature ごとに短い example を保つ。
- ある feature の coverage が巨大 demo だけにならないようにする。
- feature behavior を説明できる程度に安定してから example を追加する。
- 重要な playground example は test にも写す。
- "infers but does not run" は documentation caveat ではなく bug として追う。

## Public docs

TODO:

- README は短く保つ。
- README から playground、examples、design notes へ導線を張る。
- LSP は crates.io install 後に `yulang server` で起動できることを書く。
- Zed extension は公開前でも dev install で使えることを書く。
- filesystem semantics が固まった後に host effects docs を追加する。
- `error` / `result` の方向を実装した後に error handling docs を追加する。
- 現在の実装と一致する known limitations を追加する。
- 古い design notes は historical だと明確に印を付ける。

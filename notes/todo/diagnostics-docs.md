# Diagnostics and Docs TODO

目的: 実装ノートを読まなくても言語を使える状態にする。

## 公開後の優先

公開直後は、診断を「出る」から「直せる」へ寄せる。

優先する情報:

- primary range: 実際に直すべき式・型・pattern の位置。
- related information: 比較対象になった型、注釈、リテラル、束縛、呼び出し元の位置。
- provenance: expected / actual が注釈、リテラル、関数適用、role/method 解決、
  handler residual のどこから来たか。
- hover: diagnostic range に乗った時、同じ provenance を短く見られること。
- shared payload: CLI / playground / LSP が同じ構造化 diagnostic から表示を作ること。

近い作業:

- 型エラーの comparison に `expected_origin` / `actual_origin` 相当の構造を持たせる。
- LSP diagnostic の `relatedInformation` を、型比較の両側と注釈位置へ張る。
- diagnostic hover 用に、短い markdown summary を構造化 diagnostic から作る。
- `my a = 1 2` のような最小失敗例で、primary range と related range を固定する。
- playground の blank / missing diagnostic regression を小さい fixture で追う。

## 2026-07-01 weekly target

今週は diagnostics と標準 API 固定を、公開準備の主作業として扱う。

Diagnostics の最初の slice:

- public CLI golden を小さく追加し、現在の `check` で見える代表的な lowering
  diagnostics を固定する。
- 最初に固定するケースは、型注釈 mismatch と未解決 value name。
- `check` は source diagnostics がある場合、詳細 dump の前に compact な
  `diagnostics:` summary を出す。
- 続けて parser error、role/method error、effect/runtime error を足す。
- 期待値は全文 snapshot にせず、ユーザーが直すために必要な主文言と label だけを
  compact に見る。
- その後、同じ原因を `CheckReport` / LSP / playground で共有できる表示へ移す。

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
  - LSP hover で同じ出自情報を短く見せる
- Role / method errors:
  - missing role impl
  - ambiguous role impl
  - missing method
  - missing field
- Effect errors:
  - unhandled effect
  - handler arm mismatch
  - unsupported host request
- Runtime / lowering errors:
  - 普通の user path で residual polymorphic runtime IR を漏らさない
  - impossible runtime state は recoverable value ではなく trap として説明する

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

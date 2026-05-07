# Diagnostics and Docs TODO

目的: 実装ノートを読まなくても言語を使える状態にする。

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
- filesystem semantics が固まった後に host effects docs を追加する。
- `error` / `result` の方向を実装した後に error handling docs を追加する。
- 現在の実装と一致する known limitations を追加する。
- 古い design notes は historical だと明確に印を付ける。

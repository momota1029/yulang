# Yumark TODO

目的: syntax として読める Yumark を、値・型・lowering・runtime・playground 表示へ接続する。

現状は syntax 側の受け口が先にあり、値モデルはまだ薄い。ここを曖昧にしたまま runtime 側へ流すと、
string なのか document tree なのか、effect を持つ interpolation なのかが後段で割れる。

## 決めること

- Yumark literal / block の AST 表現。
- poly IR での値表現。
  - plain text
  - inline node
  - block node
  - interpolation / splice
  - source span を持つ node
- 型表面。
  - `str` として扱う部分
  - document tree value として扱う部分
  - render / show / serialize の role 境界
- lowering。
  - interpolation が effect を持つ場合の評価順。
  - source span と diagnostics の保持。
  - playground preview へ渡す最小 surface。
- runtime。
  - VM value の shape。
  - host rendering へ渡す serialize contract。
  - `show` と Yumark render の分離。

## First slice

- syntax parse 済みの Yumark example を一つ fixture に置く。
- value model を `notes/design/` へ短く書く。
- `docs/status.md` の「parse できるが value model は未完成」という状態を、次の実装単位へ分解する。
- lowering では string fallback に潰さず、薄くても dedicated node/value を通す。

## やらないこと

- 先に renderer だけ作って compiler/runtime の value model を後追いにしない。
- `show` の見た目で Yumark の semantics を決めない。
- playground preview 専用の構造を core IR に混ぜない。

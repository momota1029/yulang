# Language Surface TODO

目的: 基本機能がまとまりを持って見える程度まで増えたので、言語として見える判断を明示的に保つ。

## Error handling

設計参照:

- `notes/design/error-handling-plan.md`

現在の方向:

- `error` は reserved word にできる。
- `error fs_err:` は enum と act をまとめて定義する。
- error constructor は data constructor と effect operation の両方として使える。
- `Throw` は error value と対応する operation をつなぐ。
- `from` entry は広い error family への cast / wrapper を生成する。
- `io_err::unite` のような aggregation handler は狭い error effect を広いものへ集約する。

TODO:

- `error` の正確な grammar を定義する。
- `Throw` role の正確な形を定義する。
- `Cast` を role、builtin relation、syntax-directed conversion のどれにするか決める。
- constructor-like effect arms の handler syntax を決める。
- `never` が user-facing signature にどう現れるか決める。
- error effects と `result` の関係を決める。

## Result type

- `result 'ok 'err = ok 'ok | err 'err` は error effects が明確になってから追加する。
- `result` は最初の error mechanism ではなく、effectful computation を value に閉じる方法として扱う。
- helper function を決める。
  - `map`
  - `and_then`
  - `unwrap_or`
  - error effects と result values の変換

## Casts

設計参照:

- `notes/design/casts.md`

TODO:

- どの cast を implicit、explicit、forbidden にするか決める。
- error-family `from` cast は、API widening が予想外にならない程度に explicit に保つ。
- ambiguous casts に対して予測しやすい diagnostics を保つ。

## Optional records

設計参照:

- `notes/design/optional-records.md`

TODO:

- default evaluation order を明確にする。
- subtyping との相互作用を明確にする。
- missing fields の runtime behavior を明確にする。
- 悪い optional-record pattern に対して focused diagnostics を追加する。

## References

TODO:

- `&xs[0].field` のような nested projections を明確にする。
- string index update semantics を入れるつもりなら決める。
- `$x` と `&x` を小さな example 付きで文書化する。

## Effects

TODO:

- handler type examples を追加する。
- unhandled effect diagnostics を改善する。
- hygiene / id stack の前提は、user に関係する場合だけ文書化する。
- host effects は call site では普通の function のように見える状態を保つ。

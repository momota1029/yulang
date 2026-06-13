# Runtime guard marker と effect hygiene

日付: 2026-06-13
状態: specialize / runtime-lower 実装前の確定仕様
対象: principal monomorphization 後に必要になる effect hygiene の runtime 表現

## 目的

specialize 後の Yulang では、固定された entrypoint だけを実行するとは限らない。
top-level expression、direct ref、関数値、effectful thunk が first-class value として移動し、
その値を後から呼び出す場所で effect が発生する。

そのため、effect hygiene を「この call spine ではこう挿入する」という runtime-lower 側の推測に
任せてはならない。producer-consumer 境界で必要になった hygiene は、関数 adapter や thunk
boundary と同じく、値と一緒に運ばれる runtime marker として明示する。

旧 runtime IR 由来の `LocalPushId` / `AddId` という名前が残る箇所があるが、実行時意味はこの仕様の
`get_id` / `push` / `pop` / `add_id[n, path, id]` に従う。

## runtime 要素

```text
GuardId      = get_id() で得る runtime fresh id
GuardIdList  = 評価中に push / pop される dynamic list
EffectPath   = effect の exact path

EffectRequest = {
  path: EffectPath,
  guard_ids: [GuardId],
  payload: ...
}
```

`GuardIdList` は set ではなく list / stack として扱う。membership 判定では重複を区別しないが、
push した個数と同じ個数を pop する必要がある。
複数 id を持つ marker は、`push_marker[id0, id1, ...]` のような形から
`push([id0, id1, ...])` と `pop(n)` へ下げてよい。同じ id が複数回入ってもよい。

## effect request を読む条件

handler が effect request を読む条件は次の二つである。

```text
request.path == handler.path
request.guard_ids と current GuardIdList が交差しない
```

`path` の比較は exact path で行う。prefix match や alias 展開はここでは行わない。

`request.guard_ids` のどれかが現在の `GuardIdList` に含まれる場合、その handler は request を読まずに
外側へ素通りさせる。path が一致しない request も通常の effect routing と同じく外側へ送る。

## add_id[n, path, id]

`add_id[n, path, id]` は値に付く runtime marker である。
値を深く走査して全要素を書き換える操作ではない。値が computation として入られる場所まで遅延し、
その場所で effect request と結果値へ作用する。

`add_id[0, path, id]` が active な computation で effect request `r` が発生したとき、
次の条件を満たす場合だけ `id` を `r.guard_ids` に付与する。

```text
r.path != path
r.guard_ids と current GuardIdList が交差しない
```

つまり、現在の dynamic handler 群から見てまだ読める request のうち、指定された exact path 以外の
request だけを blocked にする。すでに別の guard で blocked になっている request は書き換えない。
`r.path == path` の request は、その境界で受け取るべき effect として残す。

`add_id[n, path, id]` は値にも染みこむ。computation が値を返すとき、その値の shape に従って
同じ hygiene を保持する。

- thunk value には `add_id[0, path, id]` を付ける。force された時点で発火する。
- function value には `add_id[1, path, id]` を付ける。1 回関数が起動されると depth が 1 減る。
- array / record / tuple などの構造値には outer marker として保持する。要素取り出し時に、取り出した値へ
  shape-directed に marker を合成する。
- scalar value には実行時に発火する場所がない。実装は marker を保持しても、shape が確定しているなら
  落としてもよい。

関数に付いた `add_id[n > 0, path, id]` は、関数起動時に body 全体へ
`add_id[n - 1, path, id]` として入る。したがって `add_id[1, path, id]` が付いた関数を 1 回起動すると、
その起動中に発生した effect と、その起動が返した値に同じ hygiene が反映される。

thunk force は function execution ではない。`add_id[0, path, id]` が付いた thunk を force した場合、
その suspended computation が depth 0 のまま実行され、そこで effect request への id 付与が発火する。

## stack handler marker frame

stack handler は、handler 関数値そのものではなく、handler が呼び出された後の body に marker frame を持つ。
この frame は handler 自身が `path` の performer でも handler でもあることを表す。

```text
call stack_handler(path, body):
  id = get_id()
  push([id])
  dynamic frame:
    return body
  on frame exit:
    pop(1)
```

frame 内で `path` の request が直接発生しても、`add_id[0, path, id]` はまだ発火していないので
その handler が読める。frame 内で local function / thunk value を取り出した場合は、その値に
`add_id[1, path, id]` または `add_id[0, path, id]` が lazy に付く。

nested handler frame 内で local value を読むときは、innermost active marker だけを値へ付ける。
outer marker も同時に付けると、inner handler から外へ抜けた request を outer handler が読むべき場面で
outer handler まで同じ id によって skip されてしまう。

## function guard marker

producer-consumer 境界で関数値に hygiene が必要な場合、関数値は guard marker を持つ adapter として
表される。この marker は handler かつ performer の境界として振る舞うが、effect request の
`guard_ids` を直接書き換えない。request への id 付与は、引数・戻り値へ付けた `add_id` が
後で computation として実行されるときにだけ行う。

関数起動時の動作は次の形である。

```text
call guarded_function(path, f, args):
  id = get_id()
  push([id])
  dynamic frame:
    args' = mark_arguments(path, id, args)
    result = f(args')
    return mark_result(path, id, result)
  on frame exit:
    pop(1)
```

`mark_arguments` は引数の runtime shape に従う。

- plain thunk 引数には `add_id[0, path, id]` を付ける。
- function 引数には `add_id[1, path, id]` を付ける。
- 構造値には outer marker として保持し、projection / field access / index access で取り出した値へ合成する。

`mark_result` も同じ shape-directed 規則で戻り値に marker を付ける。
戻り値が array なら array 自体が outer marker を持ち、要素を取り出した時点で要素値へ marker が付く。
戻り値が関数なら、その関数を後で起動したときに body と返り値へ marker が入る。

## dynamic unwind

`push([id...])` で入れた marker frame は lexical scope の最後だけで pop してはならない。
control がその frame を横切って外側へ出るすべての場合に pop する。

- 通常 return で frame を出る場合
- effect request の handler search が frame の外側へ抜ける場合
- handler が continuation を resume せず abort する場合
- 将来の例外・早期 return・break などの非局所制御で frame を出る場合

これは `try/finally` ではなく、resumable effect を含む `dynamic-wind` として読む。
effect search が frame の内側にいる間は、その frame の id が `GuardIdList` に見えている。
search が frame を横切って外側の handler へ進む直前に pop し、captured continuation を resume して
frame 内へ戻る直前に同じ id を再 push する。continuation が破棄される場合、pop 済みのまま戻さない。

不変条件:

- push に成功した id は、対応する frame exit でちょうど 1 回 pop される。
- 外側 handler へ抜けた後に、内側 frame の id が `GuardIdList` へ残ってはならない。
- continuation resume で frame 内へ戻るときは、その frame 内で見えていた id が復元される。
- coerce / cast / adapter は value marker を落としてはならない。

## runtime cost model

marker は値に深く eager に書き込まない。実装の目標は、コストをデータサイズではなく
境界イベント数へ寄せることである。

- marker なし値には allocation なしの fast path を持つ。
- array / record / tuple は outer marker を保持し、projection 時にだけ取り出した値へ marker を合成する。
- function call と thunk force は marker を解釈する主要な境界である。
- effect send は exact path 比較と、小さい `guard_ids` / `GuardIdList` の membership 判定だけを行う。
- 複数 id の push / pop は batch 化してよい。
- marker list は small-inline 表現や shared slice で保持し、projection ごとに大きな clone を作らない。

この仕様は correctness を先に固定する。実装時には、空 marker の fast path、marker 個数の上限観測、
effect send 回数、projection 合成回数を計測できるようにして、過剰な runtime overhead を早期に見る。

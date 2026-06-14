# Mono IR から VM / runtime lower への契約

日付: 2026-06-13
状態: VM / runtime lower 実装前の確定契約
対象: `specialize` が作る `mono::Program` を実行表現へ下げる段階

## 目的

`mono` は `poly` より後ろ、runtime lower より前の IR である。
`specialize` は principal type、erased IR、ref / select / effect operation table から、
実行に必要な単相 instance と boundary node を作る。

VM / runtime lower は `mono::Program` を読む段階で、型推論・単一化・impl 探索・effect hygiene 推測を
やり直してはならない。`mono` に残った型は、未解決 placeholder ではなく、runtime boundary を説明する
契約である。

この文書は新世代 pipeline の契約であり、旧 `yulang-vm` の IR を仕様元にしない。
旧実装の `LocalPushId` / `AddId` は oracle として読めるが、実行時意味の定義元は
[`2026-06-13-runtime-guard-markers.md`](2026-06-13-runtime-guard-markers.md) である。

## pipeline 境界

```text
sources -> infer -> poly -> specialize -> mono -> runtime lower -> VM
```

runtime lower の入力は `mono::Program` である。
debug 表示や source map のために別 table を参照してもよいが、意味論は `mono::Program` の構造だけで
決まる。

runtime lower がしてよいこと:

- `mono` node を実行表現へ機械的に変換する。
- `source` / `target` 型を読んで、明示済み boundary node の runtime 処理を選ぶ。
- `FunctionAdapterHygiene` に従って guard marker frame と value marker を作る。
- unsupported な `mono` 形を、構造化された runtime-lower error として止める。

runtime lower がしてはならないこと:

- `poly` / `infer` の内部型グラフを見に戻る。
- `Any` を unknown / fallback として扱う。
- `OpenVar` や unresolved select を、適当な runtime 型へ落とす。
- path / module / fixture / source text の文字列一致で型や runtime 操作を決める。
- function call spine から thunk force や guard marker を推測して挿入する。
- first-class thunk を `ForceThunk` なしに勝手に実行する。
- top-level computed root の RHS を、後続の `catch` や参照のたびに再評価する。

## Program と roots

```text
Program {
  roots: [Root],
  instances: [Instance],
}

Root =
  | Instance(InstanceId)
  | Expr(Expr)

Instance {
  id: InstanceId,
  source: InstanceSource,
  signature: Signature,
  body: Expr,
}
```

`instances` は specialize が到達した単相 instance だけを持つ。
使われない top-level 定義は `mono::Program` に存在しなくてよい。

`roots` は source order の実行需要であり、順序が意味を持つ。

- `Root::Expr(e)` は top-level expression として `e` を評価する。
- `Root::Instance(i)` は top-level computed binding として instance `i` の body を一度評価し、
  その結果を同じ `InstanceId` の runtime value として保持する。

`Root::Instance(i)` を評価した後で `InstanceRef(i)` が出た場合、VM は保存済みの value を参照する。
body を handler の内側や参照箇所で再実行してはならない。

例:

```text
my run = out::say(1)
my handled = catch run: ...
```

この場合、`run` は source order の computed root として先に評価される。
`catch run` は `run` の RHS を handler の内側で再評価せず、すでに計算済みの value を読む。
したがって `run` の effect は外へ逃げる。

## Type の読み方

`mono::Type` は runtime-lower の型推論入力ではなく、境界 node の実行契約である。

- `Any` は Top 型であり、unknown や fallback ではない。
- `Never` は Bottom 型であり、effect 文脈では empty effect row として扱える。
- `OpenVar` は VM-ready ではない。runtime lower に到達したら specialize 側の未解決バグとして止める。
- `Fun` の `arg_effect` / `ret_effect` は原則 pure である。effectful parameter / return は
  `Type::Thunk { effect, value }` として `arg` / `ret` の runtime value shape に畳まれる。
- `Thunk` は first-class suspended computation であり、裸の値ではない。
- `EffectRow` は exact effect path を持つ row item の列であり、path 比較は prefix ではなく exact で行う。
- `Stack` / `Union` / `Intersection` は specialize で解決・境界化されるべき型である。
  VM が実行規則を持たない形で残った場合は runtime-lower error にする。

`Fun` に non-pure `arg_effect` / `ret_effect` が残っている場合、runtime lower はそれを見て
暗黙 thunk を作らない。`specialize` が `Type::Thunk` へ畳み損ねたものとして止める。

## Boundary node

### Coerce

```text
Coerce {
  source: Type,
  target: Type,
  expr: Expr,
}
```

`Coerce` は解決済みの value boundary である。
VM は `expr` を評価し、`source -> target` の cast / representation conversion を実行する。
ここで型を決め直してはならない。

cast の可否は、specialize が読んだ `cast` 宣言と principal type からすでに決まっている。
runtime lower が実行表現をまだ持たない cast は unsupported として止める。
`Coerce` は value marker を落としてはならない。

### MakeThunk

```text
MakeThunk {
  source: ComputationType,
  target: EffectiveThunkType,
  body: Expr,
}
```

`MakeThunk` は plain computation を first-class thunk value に閉じる。
VM は `body` をその場で実行せず、force されたときに実行する suspended computation として保持する。

`source.effect` は `body` が実行時に発生させ得る effect row、`target.effect` は thunk value が持つ
effect row である。両者は `specialize` 済みの boundary であり、VM が effect row を推論し直さない。

### ForceThunk

```text
ForceThunk {
  source: EffectiveThunkType,
  target: ComputationType,
  thunk: Expr,
}
```

`ForceThunk` は first-class thunk value を現在の computation として実行する。
top-level root expression が thunk 型になった場合、specialize は root の出口に `ForceThunk` を入れる。
VM はこの node がある場所だけで thunk を実行する。

record field、tuple element、関数引数、戻り値など first-class value として運ばれる thunk は、
`ForceThunk` なしに勝手に実行してはならない。

### Thunk-to-thunk boundary

`Type::Thunk` から `Type::Thunk` への境界は、`Coerce` ではなく lazy な thunk value として表す。
この境界は、source thunk をその場で評価して target thunk の値を作る処理ではない。

VM は次の形として読む。

```text
make target thunk:
  when forced:
    value = force source thunk
    adapt value from source.value to target.value
    return value
```

`source.effect` と `target.effect` は specialize 済みの effect contract である。
force されるまで effect request は発生しない。

この規則が必要な理由は、handler 引数の thunk を `Coerce { source: thunk, target: thunk }` として
実行すると、`Coerce` が内側式を先に評価し、handler に渡る前に effect が漏れるためである。

### FunctionAdapter

```text
FunctionAdapter {
  source: Type,
  target: Type,
  function: Expr,
  hygiene: FunctionAdapterHygiene,
}
```

`FunctionAdapter` は function value が producer-consumer の関数境界を越えたことを表す。
`source` は内側の関数が実際に持つ runtime function boundary、`target` は外側の文脈へ見せる
runtime function boundary である。

VM は adapter value を作り、呼び出し時に次を行う。

1. caller から受け取った target argument を source argument へ boundary adaptation する。
2. `function` を source argument で呼ぶ。
3. source result を target result へ boundary adaptation する。
4. `hygiene` が空でなければ、同じ call body 全体を guard marker frame で囲む。

この adaptation は `source` / `target` に明示された型を読む処理であり、call spine からの推測ではない。
引数・戻り値に必要な `MakeThunk` / `ForceThunk` / nested adapter / `Coerce` は、この境界の実行として
扱う。

`hygiene` marker frame は、argument / result の boundary adaptation も含む。
target argument は source argument へ変換される前後で marker を保持し、source result は
target result へ変換される前に marker を持つ。
frame の正常 exit で返る target result にも同じ marker を shape-directed に付ける。

これは、boundary adaptation が thunk force / thunk wrap を含む場合に marker が落ちることを防ぐためである。
同じ `(id, path, depth)` の marker が同じ値へ二重に付く場合、VM は一つにまとめてよい。

### FunctionAdapterHygiene

```text
FunctionAdapterHygiene {
  markers: [GuardMarker],
}

GuardMarker {
  path: EffectPath,
  depth: u32,
}
```

`markers` は `specialize` が `source` / `target` runtime shape の差分から作る。
runtime lower は marker を増減・再推測しない。

adapter call 時、VM は marker ごとに runtime fresh `GuardId` を作る。
複数 marker がある場合は、fresh id 群をまとめて `push([id...])` / `pop(n)` してよい。
その dynamic frame の中で、adapter の引数と戻り値へ `add_id[depth, path, id]` を
shape-directed に付ける。

depth の意味は runtime guard marker spec に従う。

- `depth = 0`: thunk force など、その値を computation として入った時点で発火する。
- `depth = 1`: function value を 1 回起動した時点で body / result に入る。
- `depth > 1`: nested function value をその回数だけ起動した先で発火する。

`add_id[depth, path, id]` は `path` を受け取るべき effect として残し、現在読める他 path の request に
id を付けて外側 handler へ素通りさせるための marker である。
詳細な request 判定、dynamic unwind、lazy propagation は
[`2026-06-13-runtime-guard-markers.md`](2026-06-13-runtime-guard-markers.md) に従う。

### MarkerFrame

```text
MarkerFrame {
  path: EffectPath,
  body: Expr,
}
```

`MarkerFrame` は stack handler invocation の body を囲む runtime guard marker frame である。
handler 関数値ではなく、handler が呼び出された後の body に付く。

VM は frame entry で runtime fresh `GuardId` を作り、`push([id])` した状態で `body` を評価する。
この frame は `path` 自体の request を読めるままにし、frame 内で local function / thunk value を読むときに
innermost active marker を shape-directed に付ける。
stack handler frame から値へ染み込ませる marker は、frame entry の guard id をそのまま再利用せず、
値 marker 用の fresh id を持つ。これにより、callback 経由の request は内側 handler を skip しつつ、
外側の元 handler には読める。

- direct `path` request は marker depth が 1 の frame 内で発生するため、handler 自身が読める。
- frame 内で読んだ function value を 1 回起動すると depth が 0 になり、その起動内の別 handler は
  同じ request を読まずに外側へ送る。
- `FunctionAdapterHygiene` 由来の marker は `path` 自身を guard しない。stack handler frame から値へ
  染み込んだ marker は、depth が 0 になった時点で同じ act family の operation も guard する。
- nested handler の中で読んだ local value には innermost marker だけを付ける。
  outer marker も同時に付けると、outer handler まで同じ request を読めなくなる。

`MarkerFrame` は `FunctionAdapterHygiene` と同じ guard marker machinery を使うが、producer-consumer
function boundary ではなく、stack handler の dynamic body boundary を表す。

### EffectOp

```text
EffectOp {
  path: EffectPath,
}
```

`EffectOp` は effect operation value である。
act operation def は body を持たないため、`Local(DefId)` や `InstanceRef` として実行してはならない。

VM は `EffectOp { path }` を、payload を受け取って first-class thunk value を返す function value として扱う。
その thunk を `ForceThunk` で開いた時点で、exact `path` の effect request を送出する。
handler との照合は exact path で行い、prefix match や名前文字列による推測をしない。

## Select と method

```text
Select {
  base: Expr,
  name: String,
  resolution: Option<SelectResolution>,
}

SelectResolution =
  | RecordField
  | Method { instance: InstanceId }
  | TypeclassMethod { member: DefId }
```

`name` は dump / diagnostics の補助であり、runtime 意味を決める根拠ではない。

- `RecordField` は `base` の record field projection である。
- `Method { instance }` は method instance を receiver `base` に適用した結果である。
  追加引数を持つ method では、receiver 適用後の function value が selection result になる。
- `TypeclassMethod { member }` は VM-ready ではない。impl member selection が済んでいないため、
  runtime lower に到達したら specialize 側の未実装として止める。
- `resolution: None` は unresolved select であり、runtime lower error である。

VM は `name == "len"` などの文字列比較で field / method / builtin を決めてはならない。

## Case / pattern

`case` は mono 型で payload / field / item 型がすでに流された後の IR である。
VM は pattern の構造に従って match し、型推論を行わない。

- `Pat::Con(DefId, payloads)` の `DefId` は runtime constructor identity である。
  constructor body の `InstanceId` ではない。
- `Pat::Ref(InstanceId)` は単相 instance が表す runtime value との pattern 参照である。
- record pattern の spread は、すでに mono 型として bind 済みの field 群を受ける。
- list / poly variant pattern は runtime value の shape と tag / arity で照合する。

constructor pattern を `InstanceRef` として呼び出したり、constructor def の body を要求したりしてはならない。

## Catch / effect handler

```text
Catch {
  body: Expr,
  arms: [CatchArm],
}

CatchArm {
  operation_path: Option<EffectPath>,
  pat: Pat,
  continuation: Option<Pat>,
  guard: Option<Expr>,
  body: Expr,
}
```

`operation_path: Some(path)` の arm は exact `path` の effect request だけを扱う。
request を読むかどうかは runtime guard marker spec の `guard_ids` / `GuardIdList` 判定も含めて決まる。

payload pattern と continuation pattern の型は specialize 済みである。
VM は handler payload や continuation 入力型を operation 名から推測しない。

`operation_path: None` は value arm のための形であり、effect operation の exact path と continuation を
持たない。`body` が値として完了したときだけ、value arm の pattern を試す。

shallow handler は「body が最初に出した request を一回だけ見る」ものではない。
handler 対象外の request が body の評価中に発生した場合、その request は外側へ pass-through する。
ただし、その request の continuation は、resume 後に同じ `catch` へ戻る形で包む。
これにより、外側 handler が対象外 request を処理して resume したあと、内側の shallow handler は
body の残りをさらに評価し、次に出てきた対象 path の request を捕まえられる。

対象 path の request を捕まえた場合、arm の continuation pattern に渡す continuation は shallow である。
つまり、その continuation を呼んでも同じ handler は自動では再設置されない。
同じ handler で繰り返し捕まえたい場合は、ユーザー定義の loop / recursive handler として明示する。

handler guard は pattern match 後に、その arm の束縛を見ながら評価される。
guard の評価中に発生した effect も通常の runtime effect routing に従う。

## VM-ready invariants

runtime lower は次を `mono::Program` の前提としてよい。
破られている場合は VM 側で補正せず、specialize / mono のバグとして止める。

- `InstanceId` は `program.instances` 内の実体を指す。
- `Root` は source order の実行需要を保つ。
- root expression の actual が effectful `Type::Thunk` なら、root の出口に `ForceThunk` が入っている。
- first-class thunk は `Type::Thunk` と `MakeThunk` / `ForceThunk` で明示されている。
- effect operation 参照は `EffectOp { path }` に変換済みである。
- effect handler arm は可能な限り exact `operation_path` を持つ。
- function boundary は `FunctionAdapter { source, target, hygiene }` として明示されている。
- guard marker は `FunctionAdapterHygiene` にだけ現れ、runtime lower が後から推測しない。
- method selection は `Method { instance }` へ解決済みである。
- unresolved select、unresolved typeclass method、`OpenVar` は runtime lower に渡さない。

runtime lower / control VM は、実行を始める前に VM-ready validation を行う。
validation は IR を補正しない。参照先、未解決 method / select、未解決型、まだ実行表現を持たない
boundary / node / pattern を構造化エラーとして返す。
この段階で止まったものは、runtime の動的失敗ではなく specialize / mono lower の未完了契約として扱う。

## 実装順序の目安

runtime lower / VM の初期実装は、次の順に増やすと責務が混ざりにくい。

1. `Program.roots` と `InstanceRef` の評価順序を実装し、computed root を再評価しない store を作る。
2. literal / lambda / apply / block / record / tuple / case の純粋な値評価を通す。
3. `EffectOp` と `CatchArm.operation_path` による exact path effect routing を入れる。
4. `MakeThunk` / `ForceThunk` を first-class thunk として入れ、root force だけで実行されることを確認する。
5. `FunctionAdapter` の argument / result boundary adaptation を入れる。
6. `FunctionAdapterHygiene` を runtime guard marker spec に従って入れる。
7. `Coerce` / direct cast の runtime representation を足す。
8. `SelectResolution::Method` と remaining-argument method value を下げる。
9. typeclass method selection など VM-ready でない形は、specialize 側を先に完成させてから扱う。

どの段階でも、未対応 node は fallback 実行ではなく明示的な unsupported error にする。

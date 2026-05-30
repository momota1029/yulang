# 関数型の拡張
通常の関数型`'a -> 'b`を次の様に拡張する。
```
'a ['b] -> ['c] 'd
```
これは具象型としてはeffect thunkを含んだ`thunk['b, 'a] -> thunk['c, 'd]`のことである。

次に、エフェクトの型として反変位置と共変位置に`[handled; 'a]`という型を考える。`handled`は具体的なエフェクト列またはglob `_`が入る。

## 推論手順(注釈あり)
effectを取り出す構文として`catch`を以後採用する。`catch x: arm1, arm2`のように枝が書かれたとする。

### 型変数が介在する場合
関数型には閉じた型のように`'a [handled1] -> [returned] 'b`のように注釈をしてよい(`handled1`は具体的なエフェクト列またはglob)とするが、このとき引数の型は`[handled] 'a`ではなく、単純に`thunk['c, 'a]`のように考えることとし、`'c`に`handled`がbindされているものと考える。次に、`catch`が`handled2`をhandleするとする。このとき、`'c <: [handled1&handled2; 'd]`という制約が足される。また、`effectof arm1 | effectof arm2 | ... | 'd`が`catch`全体の型になる。

次に、高階関数にthunkを渡す場合というのを考える。`x: thunk['a, 'b]`で、`'a`には注釈によって`handled1`がbindされているとする。このとき、`'c [handled2; 'd] -> _`のような関数に入れたとき、`'a <: [handled1&handled2; 'd]`という制約が足されることになる。

### 型変数が介在しない場合
`row <: [handled; 'a]`のような制約が発生した場合、単純に`row-handled <: 'a`という制約がかかる。

### 共変部分に`;`のある注釈が成された場合
注釈された変数はそのままの型`[handled; e]`とする。また、この型は`[handled1; e] <: [handled2; f]`に対して`(handled1 - handled2) | 'e <: 'f`を帰結する。

`row | 'e`の場合には単純に分解してよいとする。

## 単一化時と動作時
単一化の際、`handled`は全て代入ではなく共通部分を取るとする。例えば`let compose(f, g: _ -> [_] _, x) = f(g(x))`すなわち`('a ['b] -> ['c] 'd) -> ('e -> [b&[_;_]] 'a) -> 'e -> ['c] 'd`と`let compose_io(f, g: _ -> [io] _) = compose(f,g)`すなわち`('a ['b] -> ['c] 'd) -> ('e -> [b&[io;_]] 'a) -> 'e -> ['c] 'd`があったとする。このとき、`f: int [io, undet; 'f] -> ['f] int`かつ`g: int -> [io, undet] int`だったとし、`compose_io(f,g)`を単相化するとする。

このとき、`int [io, undet; 'f] -> ['f] int <: 'a ['b] -> ['c] 'd`より`'b <: [io, undet; 'f]`と`'f <: 'c`が、`int -> [io, undet] int <: 'e -> [b&[io;_]] 'a`より`[io, undet] <: 'b&[io;_]`が出てくる。ただし、注意すべきは`&`をただの`&`と見ずに`'b`には`[io;_]`がbindされていて下界が`[io, undet]`であるということである。よって、`[io; undet] <: 'b`とさらに『推論』される。これが特殊な点である。ここから型制約を伝播させれば、`compose_io(f,g)`の型は`('a | int [io, undet; 'c | 'f | undet] -> [undet] 'b & int) -> ('c | int -> [b & [io; undet]] 'd & int) -> 'e & int -> ['c | 'f | undet] 'd | int`となり、これの具体型を取るだけで`(int [io, undet; undet] -> [undet] int) -> (int -> [io; undet] int) -> int -> [undet] int`が復元できる。

`compose`に至って特筆すべきは`[io; undet] <: 'b&[_]`であるが、これは`io`にしか作用しないので、`[io; undet]`のままである(いきなり引き上げられたりしない)。

全ての`effect`は`block_id`を1個以下持つとし、実行環境は`block_ids`と呼ばれる整数の配列を引き回すものとする。全てのhandlerは「effectの`block_id`が環境の`block_ids`にあればhandleしない」という動作を取る。`scope{...}`は`...`の中だけ新しい`block_id`を`block_ids`の一番上に与える。また、`add_id[handled]{...}`は`...`の中身に「`block_id`をまだ持って居らず`handled`にも含まれないeffectに`block_id`として`block_ids`の一番上を与える」という命令である。

単相化された関数`f: int [io; 'e] -> ['e] int`が`compose`の中で起動されたとき、関数全体に`scope{...}`を張り、`f`が起動された瞬間そこに`add_id[io]{f n}`が置かれることになる。これによって、`f n`の`io`以外のeffectは無事保護され、effectのhygieneが成り立つことになる。



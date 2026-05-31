# 透過モードについて
- 透過モードは上界のhandledをcompact-collect時にのみ無視し、All-subtractableな変数である、と定義する。この方が実害が少ない。

# 新規導入変数について
1. `f x`を推論したときに出てくる`f: α [β] → [γ] δ`について: `γ`は「何も引いてはならない型変数」であるので、Emptyをsubtractableとして登録する。`β`は透過モードとする。
2. `my f(x: [handled] α)`など注釈された変数について: `x: [β] α`と登録し、`β`には`handled`をsubtractableとして登録する。`handled`が`_`だった場合はAllにする。
3. `my f(g: α [β] -> [handled] γ)`と注釈された関数について: `f: α [β] -> [δ] γ`として登録し、`δ`には`handled`をsubtractableとして登録する。`β`に`handled2; ε`などと書いてあった場合はそのまま登録してよく、`ε`はAll-subtractableな変数とする。
4. 実際に値の定まった型を引いてくる場合: extractable classを参照。

# extractable class
量化のとき、その型のextractableを型クラスのように別テーブルで保存する。単相化のときはこれをまず参照する。

# extractableを2度適用するとき
- 共通部分を取ること。

# `α <: [handled1; β]` の正確な処理
1. `α`が`handled2`についてsubtractableである場合: `handled1∩handled2`を計算し、空でなければ`α <: [handled1∩handled2; β]`を登録する。空であれば`α <: β`を登録する。`β`には`handled2`をsubtractableとして継承する。

# `catch`のscrutinee/`k`/catch全体effectの制約
1. scrutineeの型を`[α] β`と仮定する(これは新しい型を作るわけではなく、ただのassume)。
2. まず、catchの中で引かれているエフェクトを`handled`とし、`α <: [handled; γ]`を要請する。このとき新しく立てた`γ`のsubtractableはNoneである(要請時に登録されるため)
3. `k`のeffectは`α`とする。
4. 新しく型`δ`を立て、透過モードとする。次に、各枝のエフェクト型`ε_1,...,ε_n`に対して`ε_1 <: δ, ... ε_n <: δ`を要請する。
5. catchの中で引かれているエフェクトが完全であれば`γ <: δ`を、1つでも欠けているものがあれば`γ <: δ`かつ`α <: δ`を要請する。

## 注意
完全なエフェクトハンドルと不完全なエフェクトハンドルを混ぜたときに、完全なエフェクトハンドルまでαとして漏れ出すのは**仕様**である。これは、エフェクトを分離してハンドルしたときに意味が変わってしまうため。言語上の限界でもある。

# shallowとrecursive/deepの期待型が分岐する理由
1. Shallowについて: All subtractable scrutinee`[α] β`を引数としてとり、またエフェクトをそのまま起動するだけのshallow handlerがbodyである関数を考える。このとき、全体の型は`β [α] → [δ] β`である。ただし各枝はエフェクトを起動するので`α <: δ`である。また、`catch`の特性により`α <: [handled; γ]`かつ`γ <: δ`である。ここでcompact型に全て展開すると、`β [α&[handled;γ]] → [γ|α|δ] β`が成立する。ここで極性を判定すると`δ`が消え、共起分析では共変位置で常に共起する`α`と`γ`が統合で結ばれる。このとき、全体の型は`β [α&[handled;α]] → [α] β`と推論される。これがshallow handlerの推論手順である。
2. recursive/deepについて: ある関数`f`がall subtractable scrutinee`[α] β`を引数としてとり、継続の値をそのまま自分自身に投射する枝しか持たないrecursive handlerをbodyとして持つとする。このとき、全体の型は同じく`β [α] → [δ] β`である。ただし、`k`の出力を自分自身に代入したことにより`α <: α`のみが成立し、`δ`に`α`がかかることはない。よって展開は`β [α&[handled;γ]] → [γ|δ] β`である。このとき、極性を判定すると、`α`が反変位置にしかないので消え去り、同様に共変位置の`δ`も消え去る。よって`β [handled;γ] → [γ] β`が最終的に推論される。
3. 足りない枝がある場合: ある関数`f`がall subtractable scrutinee`[α] β`を引数としてとり、継続の値をそのまま自分自身に投射する枝しか持たないrecursive handlerをbodyとして持つとする。ただし、足りない枝があるとする。このとき、`catch`の特性により`α <: [handled; γ]`かつ`α <: δ`かつ`γ <: δ`である。よって`β [α&[handled;γ]] → [α|γ|δ] β`が展開され、shallow handlerと同じ状態になる。

# `outer/local/repeat` の衛生性で何を残して何を消すべきか
```yu
act outer:
    our redo: () -> never
    my act local:
        our break: () -> never
        our judge(x: [_] _) = catch x:
            break(), _ -> true
            _ -> false
        our sub(x: [_] _) = catch x:
            break(), _ -> ()
            _ -> ()
        my act repeat = local
        our run(f: () -> [outer] _) = local::sub: loop true with:
            our loop b = if b:
                loop (repeat::judge:catch f():
                    redo(), _ -> repeat::break()
                    _ -> local::break()
                )
                else ()

pub r = outer::run
```
を仮定する。
1. 通常の推論手順により、`repeat::judge: ⊤ [repeat; ε] → [ε] bool`、`local::sub: ⊤ [local; ζ] → [ζ] ()`となる(また、`ε`と`ζ`はall extractableである)ことに注意する。また、1回しか用いないため、単相化した状態の型がこれであると簡単のため仮定する。
2. まず`run`の中の`f`の型は始めに`() -> [α] β`と推論され、`α`のsubtractableは`outer`に確定する。
3. 次に`f()`の起動が`catch`され、`α <: [outer; γ]`が要請される。この場合は素直に`α <: [outer; γ]`が登録され、`catch`全体の型`δ`には`repeat <: δ`, `local <: δ`, `γ <: δ`が登録されることになる。`γ`は`outer`-extractableである。
4. 次に`repeat, local, γ <: δ <: [repeat; ε]`が登録される。このとき、具体的な型については`repeat <: [repeat; ε] ⇒ [] <: ε`、`local <: [repeat; ε] ⇒ local <: ε`、`γ <: [repeat; ε] ⇒ γ <: ε`が成立する。これを合わせると、`local, γ <: ε`であり、`ε`は`outer`-extractableである。
5. loopの型は`bool → [ε] ()`であり(これは`loop`が純粋関数であることによる)、展開すると`bool → [local, γ, ε]`である。これらの型はレベルが全て低くなっているので、`loop`の型は簡約されず、`bool → [local, γ, ε] ()`のままである。
6. これにtrueが代入され、単一化はやはり1回限りの展開であるし簡単のために省略するが、`local::sub`によってあたらしく`local, γ, ε <: [local; ζ]`が推論され、仮定は同じなので省くが、`γ, ε <: ζ`が結論され、さらに`ζ`は`outer`-extractableである。
7. 最終的な型は`(() -> [α] β) → [ζ] ()`であり、これを展開すると、`(() -> [α&[outer; γ&ε&ζ]] β) → [ζ|γ|ε] ()`である。`α`と`β`は反変位置にしかなく、また共起分析で`γ=ε=ζ`なので、最終的に`(() -> [outer; γ] ⊤) → [γ] ()`が推論される。


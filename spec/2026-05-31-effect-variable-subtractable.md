# effect subtraction（stack/filter 重み）

effect subtraction の寿命境界と、共変位置の効果注釈による上限検査を、
型の外に浮く制約ではなく `stack(T, @S)` 型と不等式の重みで表す仕様。
型推論コアの一部。不変区間まわりの規則は `2026-06-02-role-system.md`、compact 表現は
`2026-06-06-invariant-type-sandwich.md` を参照。

このファイルは前半が規則の定義、後半が手計算による検証（規則そのものではなく、規則が期待どおり
動くことの確認）になっている。

## 目次

規則（定義）:

- `stack(T, @S)` と stack 重みについて
- floor について
- filter について
- 型の不等号の重みについて
- `α @L <: @R [S; β]` が制約として要求されたときの正確な処理
- `effect<α> @L <: @R [handled; β]`
- 新規導入変数について
- まとめ上げと自己型の下界
- 型注釈の上下分解
- stack id の量化とcleanup
- `catch` の scrutinee / `k` / catch 全体 effect の制約
- `AllExcept(ref_update _)` stack と変数表現（節の前半が定義）
- 実際の表現について
- 変数展開について

手計算による検証（worked examples）:

- 重み付き手計算の記法
- shallow と recursive/deep の期待型が分岐する理由
- `outer/local/repeat` の衛生性で何を残して何を消すべきか
- 補足: `m`/`j` は巡回を生まない
- `AllExcept(ref_update _)` 節後半「実際に推論されるもの」（`ref::update` の推論）

---

# `stack(T, @S)` と stack 重みについて
`S-subtract(α,#a)`と`non-subtract(T,#A)`は、型の外側に浮いたrole-like constraintとしては扱わない。
代わりに、effect subtractionの寿命境界を型そのものと不等式の重みで表す。

- `stack(T, @S)` は型であり、`T`にstack重み`@S`を付けた型である。
- `@S` は filter と、`#id` からstack entryへの写像である。
- filter は重み全体に対する effect family 集合の上限検査であり、既定値は `All` である。
  `filter[All]` は省略する。
- stack entryは常に `floor[F] pop(p)[H1, ..., Hn]` の形に正規化する。
- `H` と `F` は effect family 集合である。effect family は `path(args...)` の形を持ち、
  同じ `path` について高々1つの引数列を持つ map として正規化する。
  引数列はその effect 宣言の型引数であり、stack 集合演算では path だけで捨てない。
- `F` は高々1つであり、`F = All` のときは空のfloorと同一視して `pop(p)[H1, ..., Hn]` と略記する。floorの意味と合成規則は後述する。

```text
@S = filter[A] { #id -> floor[F] pop(p)[H1, ..., Hn], ... }
```

旧記法で書けば、次は糖衣として読める。

```text
push(T, H, #id) = stack(T, { #id -> pop(0)[H] })
pop(T, #id)     = stack(T, { #id -> pop(1)[] })
```

この糖衣の直感は、`stack(stack(T, { #id -> pop(0)[H] }), { #id -> pop(1)[] }) = T` である。
この等式は、型の局所正規化の直感である。
ただし、不等式の重みとして見た場合、過去の未対応`pop`は後ろから来たstack要素で消さない。
順序を保存するために、重みは`#id`ごとの正規形として持つ。

```text
Weight(#id) = floor[F] pop(p)[H1, ..., Hn]
```

空の重み`@0`は`filter[All] {}`である。
このとき全ての`#id`が`floor[All] pop(0)[]`（略記で`pop(0)[]`）である。

## 非 effect 具象型の terminal edge

stack 重みが観測されるのは effect family の行分解・subtraction・残差生成に到達する経路である。
したがって、effect family ではない具象型に対する terminal subtype edge では重みを消してよい。

```text
C @W <: α      ≡ C <: α      if C is a non-effect concrete terminal
α @W <: C      ≡ α <: C      if C is a non-effect concrete terminal
C @W <: C      ≡ C <: C      if C is a non-effect concrete terminal
```

ここで non-effect concrete terminal とは、解決先の型宣言が effect family ではなく、かつその edge から
子制約へ重みを伝播しない具象型である。`int`、`bool`、0引数の通常struct/enumなどがこれに当たる。
effect family として宣言された型は、同じ `Con(path, args)` 表現を持っていてもこの消去対象ではない。

型引数を持つ通常コンストラクタでは、親の terminal edge で重みを捨ててから分解してはいけない。
`box<α [e] -> β>` のような引数内部に effect row がある場合、その引数へ向かう不変制約には
重みを伝播する必要がある。重みを消せるのは、具象型そのものの照合で計算が止まり、
effect row subtraction に到達しない終端 edge に限る。

stack entryの合成は、左の後ろに右を積む操作である。

```text
pop(p)[H1, ..., Ha] + pop(q)[K1, ..., Kb]
= pop(p)[H1, ..., H_{a - q}, K1, ..., Kb]  if q <= a

pop(p)[H1, ..., Ha] + pop(q)[K1, ..., Kb]
= pop(sat(p + q - a))[K1, ..., Kb]          if q > a
```

pop countは飽和カウンタとして扱う。
pop countが`u32::MAX`のときにさらに`pop`を積んでも`pop(u32::MAX)`のままであり、オーバーフローさせない。
`u32::MAX`は「十分大きい未対応pop」の番兵であり、多段の`pop`へ展開しない。

したがって、`pop(1)[]`に後から`pop(0)[H]`を積むと
`pop(1)[H]`になる。
先頭の`pop(1)`は消えない。
一方、`pop(0)[H1, H2]`に後から`pop(1)[]`を積むと`pop(0)[H1]`へ減る。

重みの合成`@A + @B`は、各`#id`について`@A`の後ろに`@B`を順に積む操作である。
すなわち、`@B`側の`pop(n)`を先に`@A`のstackへ作用させ、その後で`@B`側のstack要素を末尾へ追加する。
`@B`側に非自明なfilterがある場合は、合成の前に`@A`側のactive stack要素へfilter検査を課す。
この検査を課した後、`@B`側のfilterは合成結果へ残さない。
合成結果に残るfilterは`@A`側のfilterである。
この合成は順序を持ち、可換ではない。

入れ子のstack型は、重みを合成して正規化する。

```text
stack(stack(T, @A), @B) = stack(T, @A + @B)
```

## floor について
floorは「全ての未対応popの下に残る、まだ引けるeffect集合」である。
残差規則（後述）が`@W`から`U`を引いたという事実を、popで消えない位置に覚えるためのものである。

- floorはstack要素と違い、順序と多重度を持たない。順序付きの寿命はstack列だけが担う。
- floorは`pop(n)`で消えない。`pop(n)`が後ろから消すのはstack要素だけである。
- 同じ`#id`のfloorの合成は共通部分で正規化する。
  ```text
  floor[F1] + floor[F2] = floor[F1 ∩ F2]
  ```
- 合成の結果`F = All`になったfloorは、空のfloorと同一視して消す。
- floor込みのentry合成は、floor同士を共通部分で畳む。
  右側のfloorは「右側へ来るまでにすでに引かれたもの」の痕跡なので、
  右側の`pop`で消えずに残る左側stack要素にも作用する。
  右側自身のstack要素は、すでにそのfloorを反映したものとして追加される。
  ```text
  floor[F1] pop(p)[H1, ..., Ha] + floor[F2] pop(q)[K1, ..., Kb]
  = floor[F1 ∩ F2] pop(p)[H1∩F2, ..., H_{a-q}∩F2, K1, ..., Kb]  if q <= a

  floor[F1] pop(p)[H1, ..., Ha] + floor[F2] pop(q)[K1, ..., Kb]
  = floor[F1 ∩ F2] pop(sat(p + q - a))[K1, ..., Kb]             if q > a
  ```
- `common_stack(W)`の計算では、floorはstackに残った`H`と同格の一要素として共通部分に参加する。

共通部分での正規化は新しい型規則ではなく、pop countの飽和と対になる実装上の正規化である。
bounds replayの循環で同じ重みが自分自身と合成されるとき、floorを列として連結すると
`[F] + [F] = [F, F]`のように毎回異なる重みが生まれ、constraint machineの重複検出（hash-cons）が永遠に外れて停止しなくなる。
共通部分で畳めば`F ∩ F = F`の不動点になる。
floorの消費は常に共通部分（`common_stack`）と要素ごとの引き算であり、引き算は共通部分に分配する
（`(A ∩ B) - U = (A - U) ∩ (B - U)`）ので、列表現と単一要素表現は観測上同値であり、情報は失われない。

再帰呼び出しで同じ重みが合成されるだけなら`F ∩ F = F`で安定する。
別のハンドラで新たに`U'`を引いたときは`AllExcept(U) ∩ AllExcept(U') = AllExcept(U ∪ U')`として単調に蓄積され、
「すでに引いたものはもう引けない、それ以外はまだ引ける」が保たれる。
別のcatch・別のinstantiate由来のハンドラは`#id`がfreshに分かれるため、そもそも同じentryのfloorとは合成されない。

floorの値域は有限個のeffect familyから作られる`AllExcept`系に閉じ、合成で除外集合が単調にしか増えないため、
floorを通る制約の列は必ず有限回で安定する。

## filter について
filterは、共変位置に書かれたeffect注釈を「そこから外へ出てよいeffect familyの上限」として読むための装置である。
これはstack要素ではなく、`#id`にも属さない。`common_stack(W)`にも参加しない。

```text
filter[A] { #m -> floor[B] pop(n)[C, D] }
```

という重みは、内部で扱うstack subtractionとは別に、外へ出ようとする具体effect familyや
左から右へ渡されるactive stack要素が`A`に収まることを要求する。

- `filter[All]` は検査しない。注釈がない効果行や、効果注釈を固定しない位置ではこれを使う。
- `filter[Empty]` は何も外へ出さない。表面構文で明示的に `[]` と書いた共変位置はこれを使う。
- `filter[A]` は残差を作らない。検査が成功しても失敗しても、`floor` や stack entry に変換しない。
- `filter[A]` が具体effect family `L` に当たったら、`L <: A` を課す。
  `A` は具体集合でもeffect family型変数でもよい。
  `A` が `Set(...)` の場合は同じpathのfamilyが含まれる必要があり、引数列は通常の不変引数制約で照合する。
  `A = Empty` であれば常に失敗し、`A = All` であれば常に成功する。

重みの合成では、右側のfilterは「右側の文脈へ入る直前」の検査として働く。
そのため、`@L + @R`を作る前に、`@L`の各entryに残っているactive stack要素を`@R`のfilterへ通す。
この検査は、後で`@R`の`pop`に消されるstack要素にも課される。
filterは境界を通過すると消費されるため、合成結果のfilterは左側のものだけである。

例えば、行`[F; 'a]`へ作用した後の右重みを次とする。

```text
@R = filter[A] { #m -> floor[B-F] pop(1)[C-F, D-F, E-F] }
```

これを左重みへ右から足す。

```text
@L = filter[G] { #m -> floor[H] pop(n)[I, J, K] }
```

まず、右側filterの検査として次を課す。

```text
I <: A
J <: A
K <: A
```

その後で、`floor[B-F]`を左側のfloorと、右側`pop(1)`で消えずに残る左側stack要素へ合成する。

```text
@L + @R
= filter[G] {
    #m -> floor[H ∩ (B-F)] pop(n)[I ∩ (B-F), J ∩ (B-F), C-F, D-F, E-F]
  }
```

ここで`K`は`pop(1)`に消されるが、消される前に右側filterへ入るので`K <: A`の検査は残る。
一方、右側の`filter[A]`は合成結果へ残らない。

# 型の不等号の重みについて
型の不等号について`T <: U`ではなく、左右にstack重みを持つ
`T @L <: @R U`として型の比較を行う。
通常の意味で型の分解が行われ、例えば
`T -> S @L <: @R U -> V`であれば、
反変位置では左右が反転するので`U @R <: @L T`、
共変位置ではそのまま`S @L <: @R V`が成立する。

`stack(T, @S)`に当たったときは、型を剥がして重みへ移す。

```text
stack(T, @S) @L <: @R U
=> T @(@S + @L) <: @R U

T @L <: @R stack(U, @S)
=> T @L <: @(@S + @R) U
```

不変位置では、共変方向と反変方向の両方を生成する。
ADT、レコード、タプル、行型、エフェクトatom引数も、それぞれの宣言された分散に従って同じ規則で分解する。

変数に到達したときは、これまで通り境界へ伝播する。
ただし、旧仕様のように`non-subtract`境界を作るのではなく、重み付き境界として保存する。

- `α @L <: @R T`であれば、`α`の上界に`T`を重み`@L/@R`つきで登録し、既存の下界`S`に対して`S @L <: @R T`を追加する。
- `T @L <: @R β`であれば、`β`の下界に`T`を重み`@L/@R`つきで登録し、既存の上界`S`に対して`T @L <: @R S`を追加する。
- `α @L <: @R β`であれば、`α`の既存下界`T`と`β`の既存上界`U`に対して`T @L <: @R U`を追加し、`α`の上界と`β`の下界にこの重み付き境界を保存する。

# `α @L <: @R [S; β]`が制約として要求されたときの正確な処理
0. `@L = @R = @0`であれば、新しい残差変数`γ`を立てない。
   この場合は重み付きsubtractionの情報がないので、`α <: [S; β]`をそのまま通常の境界として登録して終わる。
1. `@W = @L + @R`を作る。
   このとき、右側のfilterが非自明であれば、合成前の`@L`に残るactive stack要素へfilter検査を課す。
   合成結果に残るfilterは`@L`側のfilterである。
2. `@W`に現れる全ての`#id`について、stackに残っている全ての`H`とfloorを集める。
3. `pop(m)`は`U`の計算には使わない。使うのはstackに残った`H`とfloorだけである。
4. 集めた`H`もfloorも一つもなければ、共通部分は`All`として扱う。
5. 集めた`H`とfloor全ての共通部分と`S`の共通部分を取り、これを`U`と置く。
   この共通部分は effect family の引数列もすり合わせる。すり合わせで同じ `path` の
   `effect<A...>` と `effect<B...>` が出会ったら、対応する引数を不変区間として併合する。
   併合は `spec/2026-06-02-role-system.md` の不変区間規則に従い、両側の lower / upper を単に足す。
   同時に、同じ実引数が両方の区間を満たすための交差条件として
   `A.lower <: B.upper` と `B.lower <: A.upper` を生成する。
   path が一致しない family 同士は交わらない。
6. `U`が空でなければ、新しい残差変数`γ`を立てて`α`の上界に`[U; γ]`を登録する。さらに`@W`から`U`を引いた`@W' = @W - U`を作成し、`γ @W' <: @0 β`を登録する。
7. `U`が空であれば、残差変数を立てずに`α @W <: @0 β`を登録する。
8. **注意**: `@L`と`@R`の少なくとも一方が非空なら、`α @L <: @R [S; β]`をそのまま登録しては**いけない**。登録の前に必ず上の処理へ分解する。

`@W - U`は各entryについて次のように定める。

- filterは変更しない。`@W - U`はstack subtractionの痕跡を残す操作であり、
  共変注釈由来の上限検査を広げたり狭めたりしない。
- stack要素`H`それぞれを`H ∩ AllExcept(U)`に置き換える。このとき `H` と `U` に
  同じ path の family があれば、共通部分の場合と同じ不変区間併合と交差条件を生成してから
  その family を除外する。
- floor `F`を`F ∩ AllExcept(U)`に置き換える。ここでも除外対象と同じ path の family は
  引数列をすり合わせ、同じ不変区間併合と交差条件を生成する。
- floorもstack要素も持たないpopだけのentryには、`All ∩ AllExcept(U) = AllExcept(U)`をfloorとして置く。
- さらに、そのentryに残るfloorとstack要素の共通部分をfloorとしても保存する。
  これはstack要素が後続の`pop`で消えても、「このentryではすでに`U`を引いた」という下限が失われないようにするためである。

最後の規則が、述部由来の`pop(u32::MAX)[]`番兵を通った後でも「`U`はすでに引いた」を残す要である。
これが無いと、同じ`S`への分解が`U = S ∩ All = S`として何度でも成立し、残差変数の連鎖が止まらない。

同じconstraint machine内で、同じ`α`、同じ`U`のeffect family集合、同じ`@W' = @W - U`からこの分解を複数回行う場合は、同じ残差変数`γ`を再利用する。
この key に含める `U` と `@W'` は path だけでなく effect family 引数列も含む。
これは新しい型規則ではなく、`α`から`U`を引いた後に残るslotをhash-consするための実装上の正規化である。
`β`はslotの行き先であり、slotの同一性には含めない。
別の`β`へ流す必要がある場合は、同じ`γ`に対して`γ @W' <: @0 β`を追加する。
`β`ごとに別の`γ`を立てると、bounds replayで`α`自身の`[U; γ]`上界が再び分解され、再帰的なeffect rowではfreshなtailと残差変数が増え続ける。

`γ @L <: @R [S; γ]`のように、残差を作っても同じ変数へ戻るだけの制約はno-opにしてよい。
自分から引いて自分がtailに戻るだけの制約は、境界情報を増やさず、無限ループの燃料になりやすい。

# `effect<α> @L <: @R [handled; β]`
- `effect`が`handled`に`effect<γ>`の形で含まれるなら`α+ @L <: @R γ-`かつ`γ+ @R <: @L α-`。
- そうでなければ`effect<α> @L <: @R β`。

# 新規導入変数について
この節で「登場する関数の述部に`pop(1)`を置く」と言うとき、裸の`pop(1)`ではなく、
その述部が外へ見せるeffect row slot `ω` に対して
`stack(ω, filter[A] { #id -> pop(1)[] })`を置く。
ここで大文字`A`は、その述部popが戻る共変位置のeffect上限集合である。
共変位置に注釈`[A]`があればその具体集合を使い、注釈が無ければ`A = All`とする。
さらに注釈`[A]`があれば、通常の注釈分解として`ω <: A`も課す。
これにより、`pop(1)`でstack要素を消す前に、消されるeffect familyが`A`へ収まることを検査できる。
このfilterがないと、述部側の`pop(1)`がcallback由来のeffectを先に消してしまい、
外側の返りeffect注釈がそれを観測できなくなる。

1. 返りエフェクトが注釈されていない引数の`f`に対して`f x`を推論したときに出てくる`f: α [β] → [γ] δ`について: `γ`は「何も引いてはならない型変数」であるので、新しく`#a`を立て、返りエフェクトを`stack(γ, { #a -> pop(0)[Empty] })`として扱う。これの登場する関数の述部には新しく変数を立て、その述部popが戻る共変位置の上限集合`A`と合わせて`stack([ε] ζ, filter[A] { #a -> pop(1)[] })`を置く。
2. `my f(x: [handled] α)`など注釈された変数について: `x: [stack(β, { #b -> pop(0)[handled] })] α`と登録する。`handled`が`_`だった場合は`stack(β, { #b -> pop(0)[All] })`にする。これの登場する関数の述部には新しく変数を立て、その述部popが戻る共変位置の上限集合`A`と合わせて`stack([γ] δ, filter[A] { #b -> pop(1)[] })`を置く。
3. `my f(g: α [β] -> [handled] γ)`と注釈された関数について: `f: α [β] -> [stack(δ, { #c -> pop(0)[handled] })] γ`として登録する。`β`に`io`などと書いてあった場合はそのまま登録してよく、`[io] <: β`とする。`α [β] -> [handled; δ] γ`と書いてあった場合は`η`を立て、`stack(η, { #c -> pop(0)[handled] })`を使い、`f`の述部には、その述部popが戻る共変位置の上限集合`A`と合わせて`stack([ζ] η, filter[A] { #c -> pop(1)[] })`を置く。
4. `xs: list(α [A] → [B] β)`のように不変に注釈された変数について、変数`γ`と`δ`を定める。同時に`stack(γ, filter[A] { #a -> pop(0)[A] })`、`stack(δ, filter[B]{ #b -> pop(0)[B] })`を使う。不変位置に書けるのは具体effectのみであり、effect変数、wildcard、具体effectと変数の混合はここでは受け付けない。
5. 実際に値は定まっていないが、量化されていない値`f`に対して`f x`を推論したときに出てくる`f: α [β] → [γ] δ`について: なんの情報も付けない。
6. `\x -> y`について: どちらもなんの情報も付けない。

## まとめ上げと自己型の下界
上の規則で導入したstack付きの引数型と述部は、個別に境界へ置くだけでは足りない。
これらをまとめ上げて関数自身の骨格型を作り、本体の型集めを始める**前に**、関数自身の型変数を**下から**抑える。

例えば`my f(x: [handled] _)`であれば、local変数`x`は`stack(β, { #b -> pop(0)[handled] })`というeffect viewを持つ。
一方、関数自身の骨格で外に見せる引数effect slotは、その内側の`β`である。
規則2の導入物を組み上げた骨格は次になる。

```text
α [β] -> [stack(ζ, filter[A] { #b -> pop(1)[] })] δ
```

を作り、`skeleton <: f`を本体の型集めより先に登録する。
ここで`α`/`β`/`ζ`/`δ`は本体の推論が使うのと同じ変数である。
規則1や規則3が置くfilter付き述部popも、同じ骨格の返り側に合流する。
継続`k`などの扱い自体は自由であり、その整合性は骨格の述部popが取る。

body内で`x`を`catch`のscrutineeとして使うときだけ、このeffect viewから
`stack(β, { #b -> pop(0)[handled] }) <: [handled; ρ]`を張る。
通常の関数適用など、scrutineeではない位置では内側の`β`だけが見える。
local用のouter変数を共有して`stack(β, @b) <: outer`と`outer <: [handled; ρ]`を溜めると、
catchのraw row upperが関数境界や再帰呼び出しへ漏れて、別のhandlerが同じ残差からeffectを引けてしまう。

こうすると、本体内での`f`自身の使用（再帰呼び出し）も、外部の呼び出しと同じ境界横断として処理される。
body内の`catch x`がscrutinee viewから`pop(0)[handled]`を供給し、関数の返り側述部には`filter[A] pop(1)`が合成される。
`@W - U`で残ったfloorにより、catchで消費済みになった残差保護は述部popの後にも残る。
そのため、内側のcatchが消費できるのは自分のscrutinee viewが積んだ予算だけになり、
外側の残差の保護（`floor[Empty]`）が自関数の述部popで消えて`All`へ戻ることはない。
`#id`は引数ごとに別なので、周回で釣り合わない経路が際限なく太ることもない。

この登録とfloor保存が無い場合、消費済み予算`pop(0)[Empty]`がpopに食われて重みがpopだけになり、
「stackに残った`H`もfloorも無ければ共通部分は`All`」の規則に落ちて、
注釈が許していないeffectまで残差から引けてしまう。

```yu
act tick:
    our out: int -> ()
act flip:
    our coin: () -> bool

our pick(action: [flip] _) = catch action:
    flip::coin(), k -> pick(k true)
    v -> v

our loop(x: [tick] _) = catch x:
    tick::out _, k -> pick(loop(k ()))
    v -> v
```

骨格の下界がある場合、`loop`の残差の重みは次のように釣り合う。

```text
深さ0の予算:          β @ [tick]
catchがtickを消費:     残差 @ floor[Empty] [Empty]
再帰から出る(pop(1)):  残差 @ floor[Empty]
pickがflipを要求:      U = flip ∩ Empty = Empty → 引けない
```

期待される型は`'a [tick; 'b] -> ['b] 'a`であり、`'b`の上界に`[flip; ...]`が現れてはならない。
骨格の下界が無いと、この例は`'a [tick; 'b & [flip; 'b]] -> ...`となり、
注釈`[tick]`の保護を破ってflipが引けてしまう。

# 型注釈の上下分解
型注釈は、注釈に書かれた型そのものをそのまま上下界へ置くものではない。
注釈`T`は、型の極性に従って「下から抑える型」と「上から抑える型」に分解される。

`x: T`を接続するときは、注釈としてはexactである。
すなわち、`T`から作った下側制約と上側制約の両方を登録する。
ただし`x`が値であり、Simple-subの簡約によって片側だけが観測可能になる場合がある。
この場合でも、注釈自体が片側注釈になったわけではない。

エフェクト行注釈は、通常の型注釈よりも位置の影響を強く受ける。
ユーザが`[io]`と書いたからといって、全ての位置で「ちょうど`io`」を意味するわけではない。
具体的なエフェクト行は、現在の極性に応じて次のように特殊な型へ展開する。

- 共変位置では、書かれた具体エフェクトを`filter[A]`として重みへ置く。
  これは「出力側へ出ていくeffect familyは`A`に収まらなければならない」という上限検査である。
  旧仕様のように、書かれた具体rowを単に下から置くだけでは注釈にならないので採用しない。
- 普通の反変位置では、書かれた具体エフェクトを直接境界に固定せず、新しいエフェクト変数を立て、その変数を`stack(ρ, { #id -> pop(0)[A] })`で包む。
  この位置のfilterは通常`All`である。
- 不変位置では、下からは具体rowで抑え、同時に同じ具体effect集合を持つstack tailを入れる。書けるのは具体effectのみであり、effect変数、wildcard、具体effectと変数の混合はここでは受け付けない。

効果注釈が省略された共変位置は`filter[All]`であり、余計なエラーを出さない。
明示的な空行注釈`[]`だけは`filter[Empty]`であり、その位置から具体effect familyが外へ出ると失敗する。

例えば次の注釈を考える。
```yu
value: (a [b] -> [c] d) -> [e] list(f -> [g] h)
```

この注釈は、下からは次の型で抑えられる。
```yu
@e0 = filter[[e]] {}
@g1 = { #1 -> pop(0)[[g]] }
(a [b] -> ['eff0] d) -> [stack('eff_e, @e0)] list(f -> [g; stack('eff1, @g1)] h)
```

また、上からは次の型で抑えられる。
```yu
@c2 = filter[[c]] {}
@g1 = { #1 -> pop(0)[[g]] }
(a ['eff_in] -> [stack('eff2, @c2)] d) -> ['eff_out] list(f -> [g; stack('eff1, @g1)] h)
```

ここで`'eff0`や`'eff_out`には省略された`filter[All]`が付いている。
これは「不明だから逃がす」型ではなく、注釈分解によってその位置では具体エフェクトを固定しないことを表す特殊な上限側の行である。
未確定型を表す`Unknown`とは別物である。

型コンストラクタの不変引数など、不変位置で関数型が現れる場合は、上下の両側から同時に抑えるため、具体effectは具体rowとstack tailのsandwichとして現れることがある。
上の例の`list(f -> [g] h)`では、`g`そのものと`stack('eff1, @g1)`を組み合わせて、`list(f -> [g; stack('eff1, @g1)] h)`として上下の両側に現れる。
ただし、不変位置に書けるeffectは具体effectだけであり、effect変数やwildcardをそのまま書くことはできない。

`ref '[file] str` のように、effect row 型そのものが型コンストラクタの引数として現れる場合、
その引数は `['e]` / `[ref_update a; 'e]` の tail に入る effect-kind 型として読む。
したがって下側には `Pos::Row([file])` ではなく、row item / tail を ordinary effect 型として
合流した `file`（tail があれば `file | tail`）を置く。上側は具体 effect 集合を引ける
stack 付き proxy として置く。ここで `Pos::Row([file])` をそのまま型引数に入れると、
body から来る裸の `file` と注釈由来の ` '[file]` が別成分として残り、
`ref(file | '[file], str)` のような二重 row になる。

また、同じ関数型
```yu
a [b] -> [c] d
```
を関数定義の引数注釈として書いた場合は、外側の関数型に含まれる引数型部分として書いたときとは、上下から見る側が逆に見える。
下からは次のように抑えられる。
```yu
@c1 = filter[[c]] {}
a ['eff_in] -> [stack('eff, @c1)] d
```

上からは次のように抑えられる。
```yu
a [b] -> ['eff_out] d
```

このため、エフェクト注釈について「反変位置ではstack wrapperを作らない」「共変位置ではstack wrapperを作る」といった単純な読み替えは誤りである。
普通の反変位置ではstack wrapperを作り、共変位置ではfilterを作る。
関数型の内部では、関数引数・引数effectが反変、返りeffect・返り値が共変であるため、外側の極性と合成してからこの規則を適用する。

例えば、次のような返りeffect注釈を考える。

```yu
my write(f: () -> [write] ()): [io] () = f()
```

返りeffectの`[io]`は共変位置なので、外へ出るeffectに`filter[[io]]`を課す。
同時に、引数`f`の返りeffect注釈`[write]`から述部側`pop(1)`が導入される。
このpopが戻る共変位置の上限集合を`B = [io]`と置くと、述部側には`filter[B] pop(1)`が付く。
`f()`が`write`を外へ出すだけなら、`pop(1)`で`write`を消す前に`write <: B`、
つまり`write <: io`が要求される。
`write`が`io`に含まれないなら失敗する。
本体の中で`write`をhandleしてから返す場合は、外へ出る具体effectが`io`のfilterに当たらないので、この注釈には反しない。

# stack id の量化とcleanup
量化の際には、型変数と同じように`#id`もschemeに保存する。
`instantiate`のときは、型変数と同じように`#id`もfreshにする。
量化された値のschemeに`stack(T, @S)`が含まれていたら、
同じscheme内の同じ古い`#id`は同じfresh idへ置き換え、別のinstantiateとは共有しない。

さらに、各fresh idについて、instantiate後の共変側に非空stack entryが残るかを見る。
ここで非空stack entryとは、stack要素を1つ以上持つ（`pop(p)[H1, ..., Hn]`で`n > 0`）か、floorを持つentryである。
非空stack entryが一つでも残るなら、量化値の述部側には同じidの`pop(u32::MAX)[]`を一つ付与する。
非空stack entryが一つも残らないなら述部へ`pop`を付与しない。
これは、量化値の内部で導入された共変側のstack寿命を、呼び出し側の述部で対応する`pop`へ戻すための規則である。
共変側のstack要素数を正確に数えてその回数だけ`pop`を作ると、型の共有や展開の仕方によって大きな型を意図せず生成できる。
そのため、実装上は`u32::MAX`を飽和した番兵として扱い、`pop`を多段に展開しない。

述部側の多重popは、同じ出力slotへ戻るなら
`stack(T, filter[A] { #1 -> pop(1)[], #2 -> pop(1)[] })`のように保存してよい。
異なる出力slotへ戻るfilter付きpopは、同じweightへ無理に畳まず、別の`stack` wrapperとして残してよい。
同じ`#id`に対する多段の`pop`は、entry合成で`pop(n)[]`へまとめる。

cleanupでは、共変側にある`#id`を基準にする。
ある`#id`が共変側に一つも残っていない場合、その`#id`に対応する反変側のstack entryも消してよい。
これは、旧仕様の「使い切られた寿命境界は表示から消える」という規則を、型構造側のcleanupとして言い換えたものである。

`pop(0)[Empty]`だけを持つentryは、未注釈callback呼び出しの内部境界として導入される。
同じscheme内で、そのentryが付いた型変数が反変側にstackなしで普通に現れているなら、
callerが渡したcallbackの返りeffectをそのまま外へ返しているだけなので、その`Empty` entryはsurfaceへ残す根拠を持たない。
この場合は、`#id`量化の前にその `(型変数, #id)` のentryを落としてよい。
これは具体effectの引き算ではなく、同じ境界のpush/popが一般化前に相殺されなかったときの極性消去に近いcleanupである。

また、Pos/Negへ置き換える時点で、対応する非空stack entryがどちらの極にも存在しない、popだけの（floorもstack要素も持たない）entryは消してよい。
その`pop(n)[]`は境界を戻す相手を持たず、後から来る非空stack entryで相殺してはならない先頭`pop`として残す意味もない。
floorを持つentryは「すでに引いた」という境界情報そのものなので、このcleanupでは消さない。

stackに積まれたeffect集合の共通部分は次の代数で計算する。
- `Empty ∩ X = Empty`
- `All ∩ X = X`
- `Set(A) ∩ Set(B) = Set(A ∩ B)`。同じ path の family は引数列を
  不変区間として併合し、同じ実引数を持つための交差条件を生成する。
- `Set(A) ∩ AllExcept(B) = Set(A - B)`。`A` と `B` に同じ path の family があれば、
  除外される前に引数列を不変区間として併合し、交差条件を生成する。
- `AllExcept(A) ∩ AllExcept(B) = AllExcept(A ∪ B)`。同じ path の family を union するときも
  引数列を不変区間として併合し、交差条件を生成する。

ここで `A` や `B` はeffect atom familyの集合である。
`ref_update _` のような引数付きeffectは path だけで同じ family とみなすが、引数を捨ててはいけない。
同じ path の family を共通部分・差分・除外集合の union で突き合わせるたびに、対応する引数から
ordinary type constraint を生成する。stack 集合演算はどの family が残るかを決め、
引数の同一性は通常の型制約で決める。
この制約生成は、明示的な subtraction だけでなく、effect row の展開で同じ path の family が
1つの stack 集合へ集まる場合にも発生する。
同じ family map に重複 path を正規化して押し込む操作は、不変引数の併合と交差条件の生成を伴う。
実装上は `FxHashMap<path, entry-index>` などで最初の entry を代表として残し、2回目以降の同じ
path の代入時に代表 entry の引数列と新しい引数列の間へ制約を生成してから、最後に entries へ
collect してよい。

# `catch`のscrutinee/`k`/catch全体effectの制約
1. scrutineeの型を`[α] β`と仮定する(これは新しい型を作るわけではなく、ただのassume)。
2. まず、catchの中で引かれているエフェクトを`handled`とし、`α <: [handled; γ]`を要請する。このとき新しく立てた`γ`には別の保護情報を直接付けない。必要な情報は`α @L <: @R [handled; γ]`の処理で`@L + @R`から伝播する。
3. `k`のeffectは`α`とする。
4. 新しく型`δ`を立てる。次に、各枝のエフェクト型`ε_1,...,ε_n`に対して`ε_1 <: δ, ... ε_n <: δ`を要請する。
5. catchの中で引かれているエフェクトが完全であれば`γ <: δ`を、1つでも欠けているものがあれば`α <: δ`を要請する。

## 注意
完全なエフェクトハンドルと不完全なエフェクトハンドルを混ぜたときに、完全なエフェクトハンドルまでαとして漏れ出すのは**仕様**である。これは、エフェクトを分離してハンドルしたときに意味が変わってしまうため。言語上の限界でもある。

# 重み付き手計算の記法
以下の手計算では、空重みを`@0`と書く。
`#id`だけに`pop(0)[H]`を持つ重みを`@#id[H]`と書く。
例えば`stack(α, @#run[[outer]]) @0 <: @0 T`を剥がした後の重みは
`α @#run[[outer]] <: @0 T`である。
以下では読みやすさのため、`@#run[[outer]]`を`@run`のように略記する。

`α @W <: @0 [S; β]`を処理するときは、必ず次の形を一度書く。

```text
if W = @0:
  α upper += [S; β]
  stop

W = @W
U = S ∩ common_stack(W)
if U is not Empty:
  W' = W - U
  α upper += [U; γ]
  γ @W' <: @0 β
if U is Empty:
  α @W <: @0 β
```

ここで`common_stack(W)`は、`W`に残ったstack要素とfloor全ての共通部分である。
`pop(m)`は`U`の計算に使わない。

# shallowとrecursive/deepの期待型が分岐する理由
Shallowについて。
`[_]`で導入されたscrutineeを`[stack(α, @h)] β`とし、`@h = @#h[All]`と置く。

1. catchが`handled`を処理するので、まず次を要請する。
   ```text
   stack(α, @h) @0 <: @0 [handled; ρ]
   ```
2. `stack`を剥がして重みに移す。
   ```text
   α @h <: @0 [handled; ρ]
   ```
3. stackの共通部分は`All`なので、引ける具体effectは次になる。
   ```text
   U = handled ∩ All = handled
   ```
4. したがって、次の境界と残差制約を登録する。
   ```text
   α upper += [handled; γ]
   γ @h <: @0 ρ
   ```
5. shallow handlerの枝はエフェクトをそのまま起動するので、枝effect`δ`には次が入る。
   ```text
   α @0 <: @0 δ
   ρ @0 <: @0 δ
   ```
6. 関数全体は一旦次の形になる。
   ```text
   β [α] -> [δ] β
   constraints:
     α upper += [handled; γ]
     γ @h <: @0 ρ
     α @0 <: @0 δ
     ρ @0 <: @0 δ
   ```
7. compact展開では次の形になる。
   ```text
   β [α & [handled; γ]] -> [γ | ρ | α | δ] β
   ```
8. 極性消去で`δ`は落ち、共起分析で共変位置に一緒に出る`α`と`γ`が結ばれる。
   最終的に次を得る。
   ```text
   β [α & [handled; α]] -> [α] β
   ```

recursive/deepについて。
同じくscrutineeを`[stack(α, @h)] β`とし、`@h = @#h[All]`と置く。

1. catchの処理自体はshallowと同じである。
   ```text
   stack(α, @h) @0 <: @0 [handled; ρ]
   => α @h <: @0 [handled; ρ]
   U = handled ∩ All = handled
   α upper += [handled; γ]
   γ @h <: @0 ρ
   ```
2. recursive/deepでは、継続の値を自分自身に投射するだけなので、枝effect`δ`へ`α`は流れない。
   生じるのは次だけである。
   ```text
   ρ @0 <: @0 δ
   ```
3. 関数全体は一旦次の形になる。
   ```text
   β [α] -> [δ] β
   constraints:
     α upper += [handled; γ]
     γ @h <: @0 ρ
     ρ @0 <: @0 δ
   ```
4. compact展開では次になる。
   ```text
   β [α & [handled; γ]] -> [γ | ρ | δ] β
   ```
5. `α`は反変位置にしか残らないので極性消去で落ちる。
   `δ`も共変位置だけなので落ち、最終的に次を得る。
   ```text
   β [handled; γ] -> [γ] β
   ```

足りない枝がある場合。
完全に処理できないeffectがあると、catch全体のeffectへscrutinee effectそのものを流す。

```text
α @0 <: @0 δ
ρ @0 <: @0 δ
```

このため展開はshallowと同じく次になる。

```text
β [α & [handled; γ]] -> [α | γ | ρ | δ] β
```

したがって、足りない枝があるrecursive/deepはshallowと同じ状態になる。

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
        my act repeat = local   // 内部のみ同じ別エフェクト
        our run(f: () -> [outer] _) = local::sub: loop true with:
            our loop b = if b:
                loop:repeat::judge:catch f():
                    redo(), _ -> repeat::break()
                    _ -> local::break()

pub r = outer::run
```
を仮定する。
通常の推論手順により、単相化した状態で次を仮定する。

```text
repeat::judge : ⊤ [repeat; ε] -> [ε] bool
local::sub    : ⊤ [local; ζ]  -> [ζ] ()
```

1. `run`の引数注釈`f: () -> [outer] _`から、`f`のeffect変数は次のように導入される。
   ```text
   f : () -> [stack(α, @run)] β
   @run = @#run[[outer]]
   ```
2. `f()`をcatchするので、まずhandled `outer`を要求する。
   ```text
   stack(α, @run) @0 <: @0 [outer; ρ]
   ```
3. `stack`を剥がす。
   ```text
   α @run <: @0 [outer; ρ]
   ```
4. stackの共通部分は`[outer]`なので、次になる。
   ```text
   U = [outer] ∩ [outer] = [outer]
   α upper += [outer; γ]
   γ @run <: @0 ρ
   ```
5. catchの枝では`repeat::break`、`local::break`、未処理残差がcatch全体effect`δ`へ流れる。
   ```text
   repeat @0 <: @0 δ
   local  @0 <: @0 δ
   ρ      @0 <: @0 δ
   ```
6. `repeat::judge`へcatch結果を渡すので、`δ <: [repeat; ε]`が必要になる。
   `δ`の下界を一つずつ流す。
   ```text
   repeat @0 <: @0 [repeat; ε]
   => [] @0 <: @0 ε

   local @0 <: @0 [repeat; ε]
   => local @0 <: @0 ε

   ρ @0 <: @0 [repeat; ε]
   ```
7. `ρ`には`γ @run <: @0 ρ`があるので、推移で次も流れる。
   ```text
   γ @run <: @0 [repeat; ε]
   ```
8. この制約ではstackの共通部分が`[outer]`で、handledが`[repeat]`なので、引ける部分は空である。
   ```text
   U = [outer] ∩ [repeat] = Empty
   γ upper += η
   η @run <: @0 ε
   ```
9. したがって`repeat::judge`適用後の残差は次の形である。
   ```text
   local @0 <: @0 ε
   η @run <: @0 ε
   ```
10. `loop`は純粋関数なので、ここまでのeffectをそのまま返りeffectへ持つ。
    ```text
    loop : bool -> [ε] ()
    expanded as bool -> [local | η@run | ε] ()
    ```
11. これを`local::sub`へ渡すので、今度は`local, η, ε <: [local; ζ]`を一つずつ処理する。
    ```text
    local @0 <: @0 [local; ζ]
    => [] @0 <: @0 ζ

    η @run <: @0 [local; ζ]
    U = [outer] ∩ [local] = Empty
    η upper += θ
    θ @run <: @0 ζ

    ε @0 <: @0 [local; ζ]
    ```
12. `ε @0 <: @0 [local; ζ]`は空重みなので、`local`をそのまま引ける。
    ```text
    U = [local] ∩ All = [local]
    ε upper += [local; κ]
    κ @0 <: @0 ζ
    ```
13. `ε`には`η @run <: @0 ε`があるので、推移で次も得る。
    ```text
    η @run <: @0 [local; ζ]
    => θ @run <: @0 ζ
    ```
14. 最終的な型は次から始まる。
    ```text
    (() -> [stack(α, @run)] β) -> [ζ] ()
    ```
15. compact展開では、`α`の上界と`ζ`へ流れた`@run`付き残差を合わせて次になる。
    ```text
    (() -> [α & [outer; γ & η & θ & κ & ζ]] β) -> [ζ | γ | η | θ | κ] ()
    ```
16. `α`と`β`は反変位置にしかないので落ちる。
    共起分析で`γ, η, θ, κ, ζ`は同じ残差に畳まれる。
    最終的に次を得る。
    ```text
    (() -> [outer; γ] ⊤) -> [γ] ()
    ```

# 補足: `m`/`j`は巡回を生まない
```yu
act io:
    our read: () -> int
my j(x: [_] _) = catch x:
    io::read(), k -> j(k 0)
my m(x: [io; e] _) = catch x:
    io::read(), k -> j(k 0)
```
を仮定する。
`j`は通常の解析によって次の型を持つとする。

```text
j : α [io; β] -> [β] α
```

`β`は`[_]`由来の残差だが、この例では1回しか使わないため、instantiate後のfreshなidを省略する。

`m`の内部を追う。

1. `x: [io; e] _`の反変注釈から、scrutinee effectを次の形で置く。
   ```text
   x : [stack(γ, @m)] δ
   @m = @#m[[io]]
   ```
2. catchが`io`を処理する。
   ```text
   stack(γ, @m) @0 <: @0 [io; ε0]
   => γ @m <: @0 [io; ε0]
   ```
3. stackの共通部分は`[io]`なので、次になる。
   ```text
   U = [io] ∩ [io] = [io]
   γ upper += [io; ε]
   ε @m <: @0 ε0
   ```
4. 枝の中で`k 0`を作る。
   ```text
   δ @0 <: @0 α
   γ @0 <: @0 effect(k 0)
   ```
5. その`k 0`を`j`へ渡すので、`j`の引数effectに合わせて次が必要になる。
   ```text
   γ @m <: @0 [io; β]
   ```
6. この制約も同じ重みで処理する。
   ```text
   U = [io] ∩ [io] = [io]
   γ upper += [io; β1]
   β1 @m <: @0 β
   ```
7. 枝のeffectは`β`である。
   catch全体のeffect`ζ`には、枝effectとcatch残差が入る。
   ```text
   β  @0 <: @0 ζ
   ε0 @0 <: @0 ζ
   ```
8. 全体の関数型は一旦次になる。
   ```text
   δ [stack(γ, @m)] -> [ζ] α
   ```
9. compact展開で上界を入れる。
   ```text
   δ & α [γ & [io; ε & ζ] & [io; β1 & β & ζ]] -> [ζ | β | ε0] α | δ
   ```
10. 同じ`[io; ...]`をまとめる。
    ```text
    δ & α [γ & [io; ε & ζ & β1 & β]] -> [ζ | β | ε0] α | δ
    ```
11. 極性消去と共起分析後、`j`と同じ形へ戻る。
    ```text
    α [io; β] -> [β] α
    ```

重みは常に`γ @m <: @0 [io; ...]`から前向きに残差へ渡る。
右側のtailから`γ`へ戻る制約は作らないので、巡回が発生する余地はない。

# `AllExcept(ref_update _)` stack と変数表現
データ型を定義する際には、反変表現として保存する。これにより次の様なデータが作成できる:
```yu
struct ref 'e 'a {
    get: () -> ['e] 'a
    update_effect: () -> [ref_update 'a; 'e] ()
}
```
このとき、
```yu
ref: {
    get: () -> ['e] 'a
    update_effect: () -> [ref_update 'a; 'e] ()
} -> ref 'e 'a
```
が定義されるが、また同じように`update_effect: ref 'e 'a → () -> [ref_update 'a, 'e] ()`も定義される必要がある。このとき、`'e`は何か？　`stack('e, @ref)`で保護された残差であるとするのが妥当であろう。ただし`@ref = { #ref -> pop(0)[AllExcept(ref_update _)] }`である。この後、`catch`で`[ref_update 'a; 'e]`を取り去るのであるから当然であり、分離とはそのように成される。

## 実際に推論されるもの
```yu
pub act ref_update 'a:
    pub update: 'a -> 'a

pub type ref 'e 'a with:
    struct self:
        get: () -> ['e] 'a
        update_effect: () -> [ref_update 'a; 'e] ()
    pub r.update f =
        my loop(x: [_] _) = catch x:
            ref_update::update v, k -> loop:k:f v
        loop:r.update_effect()
```
に対して`ref::update`を推論してみよう。最初は引数の型から。便宜上型変数名を数字、レベルも数字で置こう。`r: ref '1(1) '2(1)`と`f: '3(1)`だ。

次にloopを見よう。
1. `x: [_] _`から、scrutinee effectを次の形で置く。
   ```text
   x : [stack('4(2), @loop)] '5(2)
   @loop = @#1[All]
   ```
2. catchが`ref_update`を処理する。
   ```text
   stack('4(2), @loop) @0 <: @0 [ref_update '6(2); '7tail(2)]
   => '4(2) @loop <: @0 [ref_update '6(2); '7tail(2)]
   ```
3. stackの共通部分は`All`なので、引ける部分は`ref_update`そのものである。
   ```text
   U = ref_update ∩ All = ref_update
   '4(2) upper += [ref_update '6(2); '7(2)]
   '7(2) @loop <: @0 '7tail(2)
   ```
4. handler armのoperation patternから、operation引数と継続型を置く。
   ```text
   '6(2) @0 <: @0 '8(2)
   '6(2) -> ['4(2)] '5(2) @0 <: @0 '9(2)
   ```
5. `f v`のために`f`を関数型へ下から押し込む。
   返りeffectは注釈されていないので、`stack`を剥がした後に`@fv = @#fv[Empty]`として伝播する。
   ```text
   @fv = @#fv[Empty]
   '3(1) @0 <: @0 '8(2) -> [stack('10(2), @fv)] '11(2)
   ```
6. level extrude後は次である。
   ```text
   '3(1) @0 <: @0 '8(1) -> [stack('10(1), @fv)] '11(1)
   ```
7. `k : '9(2)`へ`f v`を渡すので、次の比較を作る。
   ```text
   '9(2) @0 <: @0 '11(1) [stack('10(1), @fv)] -> ['12(2)] '13(2)
   ```
8. 既に`'6(2) -> ['4(2)] '5(2) @0 <: @0 '9(2)`があるので、推移で関数型同士を比較する。
   ```text
   '6(2) -> ['4(2)] '5(2)
     @0 <: @0
   '11(1) [stack('10(1), @fv)] -> ['12(2)] '13(2)
   ```
9. 関数型を分解する。
   ```text
   '11(1) @0 <: @0 '6(2)
   '4(2)  @0 <: @0 '12(2)
   stack('10(1), @fv) @0 <: @0 '12(2)
   '5(2)  @0 <: @0 '13(2)
   ```
10. `stack`を剥がす。
    ```text
    '10(1) @fv <: @0 '12(2)
    ```
11. `loop`の型変数を`'14(2)`、catch本体の型を`['15(2)] '16(2)`と置く。
    recursive bindingの下側から次を登録する。
    ```text
    '5(2) ['4(2)] -> ['15(2)] '16(2) @0 <: @0 '14(2)
    ```
12. recursive call `loop:k:f v`から、`loop`の上側に次を要求する。
    ```text
    '14(2) @0 <: @0 '13(2) ['12(2)] -> ['17(2)] '18(2)
    ```
13. catch全体のeffect/valueは、未処理残差とhandler armの式から下から抑えられる。
    ```text
    '7(2)  @loop <: @0 '15(2)
    '17(2) @0 <: @0 '15(2)
    '5(2)  @0 <: @0 '16(2)
    '18(2) @0 <: @0 '16(2)
    ```
14. `loop`の下界と上界を推移でつなぐ。
    ```text
    '5(2) ['4(2)] -> ['15(2)] '16(2)
      @0 <: @0
    '13(2) ['12(2)] -> ['17(2)] '18(2)
    ```
15. 関数型を分解する。
    ```text
    '13(2) @0 <: @0 '5(2)
    '12(2) @0 <: @0 '4(2)
    '15(2) @0 <: @0 '17(2)
    '16(2) @0 <: @0 '18(2)
    ```
16. `f v`由来の`@fv`重みは、次の推移で`'4(2)`の上界へ届く。
    ```text
    '10(1) @fv <: @0 '12(2)
    '12(2) @0  <: @0 '4(2)
    '4(2) upper includes [ref_update '6(2); '7(2)]

    therefore:
    '10(1) @fv <: @0 [ref_update '6(2); '7(2)]
    ```
17. この行をrow規則で処理する。
    ```text
    W = @fv
    U = ref_update ∩ Empty = Empty
    '10(1) upper += '10r(1)
    '10r(1) @fv <: @0 '7(2)
    ```
    ここで`@fv`重みが`'10r(1) @fv <: @0 '7(2)`として`'7(2)`側へ伝播する。

展開して見よう。
```
'14(2)
= ('5(2) ['4(2)] -> ['15(2)] '16(2)) | '14(2)
  constraints:
    '4(2) upper += [ref_update '6(2); '7(2)]
    '7(2) @loop <: @0 '7tail(2)
= ('5(2) & '16(2) & '18(2) ['4(2) & [ref_update('11(1) | '6(2) & '8(1)); '7(2)@loop & '10r(1)@fv]] -> ['7(2)@loop | '10r(1)@fv | '17(2) | '15(2)] '13(2) | '5(2) | '18(2) | '16(2)) | '14(2)
  constraints:
    '7(2) @loop <: @0 '15(2)
    '10r(1) @fv <: @0 '7(2)
= '5(2) [ref_update('11(1) | '6(2) & '8(1)); '7(2)@loop & '10r(1)@fv] -> ['10r(1)@fv | '7(2)@loop] '5(2)
  constraints:
    '10r(1) @fv <: @0 '7(2)
    '7(2) @loop <: @0 '15(2)
= '5(2) [ref_update('11(1) | '6(2) & '8(1)); '7(2)] -> ['10(1) | '7(2)] '5(2)
= forall '5, '6 '7. '5 [ref_update('11(1) | '6 & '8(1)); '7] -> ['10(1), '7] '5
```

とても分かりやすくなった。でもこれはまだloopの型。
これに`r.update_effect()`、つまり`[ref_update '2(1), '1(1)] ()`を代入する。
`'1(1)`は`stack('1(1), @ref)`で保護された残差である。

1. loopの型をlevel 1へinstantiateしたものを使う。
   ```text
   '5(1) [ref_update('11(1) | '6(1) & '8(1)); '7(1)]
     -> ['10(1), '7(1)] '5(1)
   ```
2. `r.update_effect()`の型は次である。
   ```text
   () [ref_update '2(1); stack('1(1), @ref)] ()
   @ref = @#ref[AllExcept(ref_update _)]
   ```
3. 関数適用で次を比較する。
   ```text
   '5(1) [ref_update('11(1) | '6(1) & '8(1)); '7(1)]
     -> ['10(1), '7(1)] '5(1)
       @0 <: @0
   () [ref_update '2(1); stack('1(1), @ref)]
     -> ['19(1)] '20(1)
   ```
4. 関数型を分解する。
   ```text
   () @0 <: @0 '5(1)

   ref_update '2(1) @0
     <: @0
   ref_update('11(1) | '6(1) & '8(1))

   stack('1(1), @ref) @0 <: @0 '7(1)

   '10(1) @0 <: @0 '19(1)
   '7(1)  @0 <: @0 '19(1)
   '5(1)  @0 <: @0 '20(1)
   ```
5. `ref_update`の引数を分解する。
   ```text
   '11(1) | '6(1) @0 <: @0 '2(1)
   '2(1) @0 <: @0 '6(1) & '8(1)
   ```
6. 残差側の`stack`を剥がす。
   ```text
   '1(1) @ref <: @0 '7(1)
   ```
7. これにより`'1(1) @ref <: @0 '7(1)`として、`@ref`重みが`'7(1)`側へ伝播する。
   返りeffectは次で抑えられる。
   ```text
   '10(1) @0 <: @0 '19(1)
   '7(1)  @0 <: @0 '19(1)
   ```
8. 全体の型を`'21(1)`と置く。
   ```text
   ref '1(1) '2(1) -> '3(1) -> ['19(1)] '20(1) @0 <: @0 '21(1)
   ```

展開して見よう:
```
21(1)
= (ref('7(1) | '1(1)@ref & '7(1) & '19(1), '11(1) | '6(1) | '2(1) & '6(1) & '8(1)) -> '3(1) & ('11(1) | '5(1) | '2(1) | '8(1) -> ['10r(1)@fv & '19(1)] 11(1)) -> ['10r(1)@fv | '1(1)@ref | '7(1) | '19(1)] () | '5(1) | '20(1)) | 21(1)
  constraints:
    '1(1) @ref <: @0 '7(1)
    '10r(1) @fv <: @0 '7(1)
    '10(1) @0 <: @0 '19(1)
    '7(1) @0 <: @0 '19(1)
= ref('1(1)@ref & '19(1), '11(1)) -> ('11(1) -> ['19(1)] 11(1)) -> ['1(1)@ref | '19(1)] ()
  constraints:
    '10r(1) @fv <: @0 '19(1)
    '1(1) @ref <: @0 '19(1)
= ref('1(1) & '19(1), '11(1)) -> ('11(1) -> ['19(1)] 11(1)) -> ['1(1) | '19(1)] ()
= forall 'a 'b 'c. ref('a&'b, 'c) -> ('c -> ['b] 'c) -> ['a, 'b] ()
```

# 実際の表現について
compact collect型については、通常の共変型が`変数 + record + ...`であるように、effect row側も共変部分は`変数 + 行`として持つ。
反変部分は、具体rowを直接増やすのではなく、stack付きの境界として保存する。

CompactTypeからPos/Negへ移す段階では、`stack(T, @S)`を両極の型に入れるのが一番扱いやすい。
`@S`は常に`{ #id -> pop(p)[H1, ..., Hn], ... }`の正規形で持つ。
旧記法の`push(T, H, #id)`と`pop(T, #id)`は、この`stack(T, @S)`の特殊ケースとしてだけ扱う。
この表現にしておくと、CompactTypeからPos/Negへ移すときに、片方の極だけに特別なproxy型を作らなくてよい。

cleanupでは、共変側に`#id`が一つも残っていないなら、反変側に残った同じ`#id`のstackも消し去る。
また、Pos/Negへ置き換える時点で、対応する非空stack entryがどちらの極にも存在しない、popだけの（floorもstack要素も持たない）entryは消してよい。
その`pop(n)[]`は境界を戻す相手を持たず、後から来る非空stack entryで相殺してはならない先頭`pop`として残す意味もない。
通常のhandlerで使い切られるものはこのcleanupで消えるので、表示型は既存の表記から大きくは変わらない。

# 変数展開について
変数展開は、裸の変数ではなく重み付きの変数出現に対して行う。
`'a@R`を展開するときは、展開結果に現れる全ての変数出現へ`@R`を後から足す。
すでに変数出現が`ρ@Q`の重みを持っている場合は、`ρ@(@Q + @R)`にする。
これは`@R`が「`'a`へ到達するまでに通ってきた文脈」であり、その文脈を展開結果の各変数へ引き継ぐためである。

1. `α [β] → [γ] δ`という型をcompact表現に展開するとする。ただし、`β`の上界は`ε, [undet; ζ]`、`ε`の上界は`[io; η]`、`ζ`の上界は`[flip; γ]`とする。`α`や`γ`、`δ`は今回上下界を持たないとする。
2. `α [β & ε & [undet; ζ]] → [γ] δ`と展開する。
3. 次に見るのは`ε`だが、このとき`β`から直接出てきた上界なので、さらに上は展開しない。代わりに次の`ζ`を見る。
4. `α [β & ε & [undet; ζ & [flip; γ]]] → [γ] δ`と展開する。
5. 極性消去によって`α [[undet; [flip; γ]]] → [γ] δ`と展開される。終わり

ここで注意すべきは**変数を展開して出てきた変数は、上界を展開しない**ことである。これによって、本来推移律の成立しない世界を上手くコンパクト化している。

`stack(ρ, @S)` はordinary row boundではない。
compact表示ではordinary row boundを従来どおり展開し、残ったstack境界だけを型構造として扱う。

うん、まだあるよ〜。ただ、今の状態だと **制御フロー上の小技より、データ表現と同じ型グラフの再走査を減らす段階** に入ってるねぇ。

`showcase` では instantiate predicate が `Fun` 853件、`Con` 43件、`Stack` 4件で、direct lower-bound 化後も instantiate の制約投入が約44〜49ms残ってる。一方、SCC routing では `QuantifyComponent` が約129msと一番太い。かなり絞れてきてるよ〜。

## 1. `SchemeInstantiator` に source node ID のメモ化を入れる

私なら、まずこれを試すねぇ。

`TypeArena` はすでに hash-cons arena で、同じ構造は `PosId` / `NegId` / `NeuId` として共有されている。
ところが `SchemeInstantiator` が持つ対応表は `TypeVar` と `SubtractId` だけで、型node IDの対応表はない。

そのため、scheme内で同じ source node が複数箇所から参照されると、

* source nodeを再び再帰走査
* pathやfield名をclone
* 一時的な`Vec`を再構築
* target arenaで同じ構造を再hash

という処理が発生する。実際、`clone_pos` / `clone_neg` / `clone_neu` は毎回再帰的に組み立て直している。

```rust
struct SchemeInstantiator<'a> {
    // 既存
    vars: FxHashMap<TypeVar, TypeVar>,
    subtracts: FxHashMap<SubtractId, SubtractId>,

    // 追加候補
    pos: FxHashMap<PosId, PosId>,
    neg: FxHashMap<NegId, NegId>,
    neu: FxHashMap<NeuId, NeuId>,
}
```

これは**単一instantiation内だけ**のcacheなら安全だと思うよ〜。fresh variable対応はそのinstantiation中は固定だからねぇ。

最初は次だけ計測すると勝敗がすぐ分かる。

```text
instantiate.clone_pos_calls / hits
instantiate.clone_neg_calls / hits
instantiate.clone_neu_calls / hits
instantiate.cloned_nodes
```

hit率が高ければ、`FxHashMap`よりsource IDの`.0`で引く`Vec<Option<Id>>`へ進むとよさそうだねぇ。

---

## 2. `TypeVar` をkeyにするhot tableをdense vectorへ移す

これは期待値がかなり高い構造変更だと思う。

`TypeVar`はarena-localな連番`u32`として発行されている。
それなのにconstraint machineでは、次のような状態が`FxHashMap<TypeVar, ...>`になっている。

* type level
* bounds
* variable adjacency
* subtract facts
* pre-pop effect families

特に`add_lower_bound` / `add_upper_bound`は毎回level lookup、bounds lookup、dedup、neighbor更新、replayを行う。

段階的には、

1. `TypeLevels`を`Vec<LevelInfo>`へ
2. `TypeBounds`を`Vec<Option<VarBounds>>`へ
3. `pre_pop_effect_families`とsubtract factsをvectorへ
4. adjacencyは最後

という順が安全かなぁ。

現在は3万件台のconstraint workとbound追加があるので、hash lookupを数回ずつ除けるだけでも効く可能性がある。

---

## 3. hash-cons nodeごとに「含まれる型変数」をcacheする

今のneighbor登録は、単純な`Var`や引数なしconstructor以外だと、毎回新しい`FxHashSet`を作って型nodeを再帰走査している。

extrusionでも、

* `visited`
* `visited_pos`
* `visited_neg`
* `visited_neu`

の4つのsetを毎回作り、構造を再帰走査している。

型nodeはimmutableかつhash-cons済みなので、次のside cacheを持てるはずだよ〜。

```text
PosId -> Arc<[TypeVar]>
NegId -> Arc<[TypeVar]>
NeuId -> Arc<[TypeVar]>
```

これで、

* neighbor登録はcached sliceを列挙するだけ
* extrusionは含有変数を直接`extrude_type_var`へ渡す
* node traversal用のvisited setをかなり減らせる

という形になる。

さらに各nodeに「含有変数の最大level」相当をcacheしたくなるけど、levelは後から浅くなるので、その部分はepoch管理か保守的判定が必要だねぇ。まずは変数集合だけが安全。

---

## 4. `ConstraintWeights`をID化、またはempty特化する

今の`ConstraintWeights`は2本の`StackWeight`を所有し、それぞれが`Vec<StackWeightEntry>`を持つ。cloneやreplay compositionで実データを複製する構造になっている。

さらに、

* subtype constraintは`seen`用にcloneしてからqueueへ入る
* weighted boundは`HashSet`と`Vec`の双方へ保持する

という二重所有がある。

まず、

```text
constraint.empty_weight_work_items
constraint.nonempty_weight_work_items
bounds.empty_weight_count
bounds.nonempty_weight_count
```

を取るのがよさそう。

emptyが圧倒的なら、

```rust
enum ConstraintWeights {
    Empty,
    Weighted(WeightId),
}
```

くらいの表現でもかなり軽くなる。

より本格的には、`StackWeight` / `ConstraintWeights`をarenaにinternして、constraintやboundには`WeightId`だけ保存する形だねぇ。`seen` keyもほぼCopyになり、queueとboundsのcache localityも改善する。

これは効きそうだけど意味論への接触面が広いので、dense tableやnode-var cacheのあとがよさそうかなぁ。

---

## 5. generalize開始時の「適用済みrole集合」全cloneをやめる

`generalize_root_with_prepasses`はdefごとに、session全体の`applied_method_role_resolutions`を丸ごとcloneし、さらにdemand集合もclone構築している。

ループ終了後にはcandidate集合も改めてcloneしている。

ここは、

* session共通のbase setはborrow
* 当該generalize中に増えた分だけlocal delta set
* membershipは`base.contains(x) || delta.contains(x)`
* reachable roleが空なら、そもそも集合を作らない

という形にできそう。

今の`quantify_generalize`はwarm sampleでも91〜95ms付近なので、こうしたdefごとの固定費を切る価値がある。

---

## 6. recursive boundsの即時drainをまとめる

scheme instantiation中の`clone_recursive_bounds`は、recursive bound 1件につき`subtype`を2回呼ぶ。各`subtype`はその場でdrainする。

最終predicateはすでにbatch投入するようになっているけど、recursive boundsはbatchの外側に残っている。

なので、

```rust
let mut recursive_constraints = Vec::new();
// 2本ずつpush
target.subtypes(recursive_constraints);
```

と、まずscheme単位でまとめられそう。

showcaseでrecursive boundsが少なければ効かないので、

```text
instantiate.recursive_bound_count
instantiate.recursive_bound_drains
```

を先に足すのがよさそうだねぇ。

---

## 7. warm pathの最大勝ちは、やはりtyped SCC import

これは推論器内部のmicro optimizationではないけど、ユーザー体感では一番大きくなりうる。

すでにloaded-prefix cacheでparseはかなり飛ばせている一方、build全体にはinferが残っている。次の設計として「unchanged dependency SCCのlowering / inferenceをtyped surface importで飛ばす」と明記されている。

つまり長期的には、

```text
source SCC
  ├─ syntax surface
  ├─ typed exports / schemes
  ├─ role + impl + effect surface
  └─ runtime surface
```

をcache単位にして、変更されたSCCと依存先だけ再推論するのが最大の勝ちだと思うよ〜。

---

## 私ならこの順で試す

1. **scheme node-ID memo**
2. **`TypeLevels`のdense vector化**
3. **node free-variable cache**
4. **recursive boundsのbatch化**
5. **applied role setのbase + delta化**
6. **weightのempty特化／intern化**
7. **typed dependency SCC import**

逆に、単純なdrain batchingをさらに広げるのは避けたいねぇ。既にqueueが太って悪化した実験があり、var-only intervalを全面的にdirect化する案もwork件数は減ったものの正しさのテストを壊している。

一番「小さい変更で未知の削減を拾えそう」なのは、やっぱり **`SchemeInstantiator`の`PosId` / `NegId` / `NeuId` memo** だと思うよ〜。

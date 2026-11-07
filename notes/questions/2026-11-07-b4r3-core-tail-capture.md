# B4r3: verified core 宣言に未知の record tail を許す範囲

状態: **列挙された core 前提への E2 証明済み。以下の修正は未承認**。
主定理は `CommonRoleFiniteTailObstruction.normalized_registry_undecidable`。
既存の E2、承認済み N、K2 は変更しない。

## 一問

**推奨: B4 の宣言量化を、実 source checker/elaborator が生成する head に明示的につなぎ、
record head の tail は閉じた rigid spine に限られることを独立 lemma で保証する。**
現在の surface から書けない未知 tail を持つ任意 core impl まで、全域 resolver の契約に含めるか。

現在の surface で書ける、payload の変数と where の例は次である。

```yulang
role R 't:
    type value

impl R ({x: 'a}):
    where 'a: R
    type value = int
```

ここで 'a は field payload であり、head からその意味が決まる。
反例はこれとは別の core 型 `R {x:int,..a} requires R a` で、a は未知の record tail にある。
この反例を source impl の code block にはしない。
[現在の named-record type grammar](../../syntax-reference/ja/src/types/named-record-type.md) は spread を含まない。

1. **推奨案: source との bridge を契約に含める。** 任意有限 source 宣言表 S と実 elaboration D=elaborate(S) を量化し、
   head の閉 spine 性を source checker から証明する。任意確定 regular goal の量化は維持する。
   既存 `VerifiedDeclaration` はこの条件を保証しないため、名前だけで source 検証済みとは扱わない。
2. **任意 core 宣言を維持する案。** head の意味から where 各引数の意味が一つに決まる
   `HeadDeterminesRequirements` を新たに宣言検査へ入れるか、tail の捕捉を canonical residual に限定して
   独立 evidence を変更する。このいずれも既存の任意 Common head-match evidence の契約を変えるので、別の承認が必要。

どちらも、今回の E2 を除くための statement/semantics の変更案である。
どちらかで full B4 の E1 が成立することを先取りしない。RoleRank、fuel、深さ上限、無限辞書は提案しない。

## 最小 core 反例

```text
head  R {x:int, ..a}
where R a
associated value = int
```

role 一つ、impl 一つ、変数一つ、recursive graph なし。head の x は一度だけなので N で変わらず、
normalized head/child サイズは 3/1。
既存 `CommonRoleHeadDetermination.verify` も新 normalized checker も受理する。
有限 goal C={x:int} に対し、a:=C と捕まえると head は C と Common 同値、child は C そのものになる。
a:=emptyRecord でも head は同じだが、child は C と同値でない。
関連型は定数 int なので HDA は満たすが、where の意味は head から決まらない。

`old_verified_api_accepts` / `normalized_checked` / `declaration_fixed` / `declaration_sizes` /
`head_matches` / `child_returns` / `requirements_not_determined` がこれを実 fields で示す。
`normalization_does_not_commute_with_capture` と `post_capture_sizes` は、捕捉後に初めて field が隠れ、
N後の両実型サイズが 3/3 になることを示す。

同一 goal のループだけでは全算法不可能とはしない。
主 E2 は、この有限 C を独立した pair slot に必要な数だけ並べ、各 slot の head を `{x:int,..fresh}`、
child を fresh として、任意有限線形 program の停止を実有限辞書の存在へ還元したもの。
全 stored head/where は N 固定で、全実 goal は有限木。両 K2 規則も働かない。
任意 Common 代入の上位 evidence に広げても成功集合は変わらない。

## amended statement の正確な提案

推奨案は、任意 core D の量化を、任意 source 宣言表 S とその実検証・elaboration の出力 D へ変える。
新しく必要な bridge は、少なくとも次である。

```text
任意有限 source 宣言表 S、任意成功結果 D について、
  checkAndElaborateImpls S = success D
なら、D の全 head/where が対応する正しい core grammar を持ち、
  source 表記で head の record spine は型変数の tail を持たず、
  正規化 N は Common 意味を保ち、normalized WellFormed と HDA が成り立つ。
```

その上で、任意 finite regular goal g に対する両 K2 と作業上の拒否先行を含む全域実 resolver と、
独立 selection/rejection/ambiguity および全実辞書との iff を要求する。
未解決 qualified constraints の任意 Common 代入の量化は変えない。
この source checker/elaborator の実装・bridge・full E1 は未証明。
承認前に source-generated 条件を元の theorem の暗黙の前提にしていない。

任意 core 宣言を維持する場合の追加条件候補は次である。

```text
HeadDeterminesRequirements D :=
  ∀ impl∈D, ∀ Common substitutions σ τ,
    pointwiseEquivalent (interpret impl.head σ) (interpret impl.head τ) →
    ∀ child∈impl.where, pointwiseEquivalent (interpret child.args σ) (interpret child.args τ)
```

この条件だけで全体の停止が得られるとも、全言語で decidable な完全検査があるとも主張しない。
一般 union の冗長性などは別の問題であり、surface で許される head grammar と分けて扱う。

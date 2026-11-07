# B4: head に隠れた変数が where 辞書を変える場合

状態: 全辞書 plan の保存と Common 同値での plan 一意性の非両立性を Lean で検証。
この強い plan 契約が修正後 B4 に必須かは未確認であり、現在の E2 完了とはしない。以下の追加修正案は未承認。
承認済みの `HeadDeterminesAssociated` と別の条件であり、K2 の回答ではない。

出典: `spec/04-types.md` §4.3 の隠れた同名 field の型同値、`spec/06-roles.md` §6.2–6.3 の
同じ呼出側 visible 集合での nested where 解決、B4 §7.6 の実 dictionary 対応、
`RoleDictionaries.elaborate_success_iff` / `Dictionary.erase_unique`。

## 承認済み条件を満たす反例

```yulang
role R 't:
    type value

role S 't:
    type value

impl R ({x: int, x: 'a}):
    where 'a: S
    type value = int

impl S int:
    type value = int

impl S bool:
    type value = int
```

関連型 RHS は三つとも定数 int。任意の Common 代入に対して `HeadDeterminesAssociated` が成立する。
root の head/where サイズは 5/1、変数 a の出現回数は 1/1 で、現在の Paterson checker も受理する。
関連型の scope、署名 arity、必須名の実装、未宣言名の排除も実 `Roles.AssocWellFormed` で確認する。

同じ visible 集合で、実 resolver の成功時の辞書は次のようになる。

```text
R {x:int,x:int}  → node root [node S-int []]
R {x:int,x:bool} → node root [node S-bool []]
```

両 goal は Common の型同値では同じであるが、選ばれる子 impl identity が違う。
これは別の caller scope の証拠を渡した場合ではない。
`RoleDictionaries.elaborate_success_iff` は任意 plan に対して実返却 iff 独立した辞書の存在を要求し、
`Dictionary.erase_unique` は同じ visible 集合・同じ goal の完全な木の一意性を示す。
この実辞書を保存し、Common 同値な goal に同じ辞書を選ぶ extension は存在しない。

ただし旧 `Dictionary.erase_unique` が固定するのは構文的に同一の goal である。
B4 を「成功 iff 証拠の存在、成功時に有効な辞書を一つ返す」と読む場合、全 plan の等号まで必要とは限らない。
fresh review はこの契約上の差を指摘した。監督者へ契約の解釈を質問し、K2 の証明作業を継続する。

Bool の成功／失敗だけなら両方を成功とする余地があるため、それを不可能性とは扱わない。
関連型 RHS の相違でもない。三宣言すべての関連型は同じ int である。

## 提案する追加 statement

関連型だけでなく、where の各引数も head の意味から決まる条件を候補とする。

```text
HeadDeterminesRequirements(D) :=
  ∀ impl ∈ D, ∀ Common substitutions σ τ,
    (∀ h ∈ impl.head, interpret h σ ≈ interpret h τ) →
    ∀ child ∈ impl.where, ∀ argument ∈ child.args,
      interpret argument σ ≈ interpret argument τ
```

追加案は registry の宣言前提を
`WellFormed D ∧ HeadDeterminesAssociated D ∧ HeadDeterminesRequirements D` にすること。
role ID は各 child 宣言に固定されており、この条件では変更しない。
goal / 式 / 任意 Common 代入の量化は変えない。
この条件の最小性、全言語での decidable checker の完全性、regular 解決の停止は証明していない。

具体案として head の隠れた field を除去してから where の変数出現回数を検査すれば、この例は拒否される。
ただし、現在の raw な `Roles.WellFormed` に対してそれを先に行う pipeline は、今回の承認内容ではない。
承認済みなのは関連型の意味的条件であり、where 条件まで正規化後の scope check に変更したとは扱わない。

別案は、同じ root impl 内の異なる照合代入から異なる where 辞書が得られる場合を曖昧性として扱うこと。
これは現在の head-overlap / evidence の意味を変えるので、同様にユーザー判断が必要となる。
どちらの案も、旧 K2 の正則 clock chain や決定不能性を解決したものではない。

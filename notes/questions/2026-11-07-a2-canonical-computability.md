# A2: 全有限 interface の表示 code に要求する完全性

状態: **解消(2026-11-08, ユーザーの回答): 案1を採用する。** 「証明の契約としては、外したほうが楽なら外してよい」。計算可能 code の完全性（`PublicEquivalent I J → encode I = encode J`）を外し、`encode I = encode J → PublicEquivalent I J` と、表示・readback の契約を残す。以下は提案時の記録。

問いは一つ：全有限公開文法と既存の公開 instance 意味を維持し、code 等号の契約を下記の案1へ変更するか。

利用者に見える論点の例：

```yulang
my id(x: 'a): 'a = x
my id2(y: 'b): 'b = y
```

このような表示上の改名をまとめる個別の正規化は引き続き可能である。
問いは、それを一般行式・正負共有・再帰行を含む**任意の有限 interface**へ拡張し、
意味が等しいものを必ず同じ表示 code にすることまで要求するか、という契約である。
上の例自体を決定不能性の反例とはしていない。今回の帰着族が実 source inference の像に入ることも主張しない。

## Lean で閉じた障害

`CommonCanonicalUndecidability.no_computable_canonical_encoding_at_theory`：
任意の固定 `theory : RoleConstraints.Theory Common.model.toModel` に対し、
次の二条件を同時に満たす関数 `encoding : CommonCanonicalRowSyntax.Interface → Nat` と
有限 counter program `machine` は存在しない。

1. 任意有限 symbolic interface `I` で、`Runs machine (interfaceCode I) (encoding I)`。
2. 任意二 interface `I/J` で、全 `target : Inference.Comp Common.model.toModel` に対する
   既存 `QualifiedInference.BindingTyping model theory I.binding target` と
   `QualifiedInference.BindingTyping model theory J.binding target` の同値が、
   `encoding I = encoding J` と同値。

計算可能性は有限 instruction table の counter machine（increment、zero-test/decrement、goto、halt）で形式化した。
全自然数上の停止は要求せず、有限 interface の正しい構文符号上の停止だけを要求する。
有限 code は固定 token alphabet の自然数符号であり、`Common.Row = Occurrence → Prop` の述語を入力にしていない。
外部の compiler 実現可能性、oracle、solver 成功、有限 support は仮定していない。

帰着は任意有限 counter program `P` と自然数 `x` に対し、有限 symbolic interface
`I(P,x)` / `J(P,x)` を作り、元の public-instance 意味で

```text
I(P,x) と J(P,x) が等価  ↔  ¬ Halts P x
```

を示す。さらに二つの固定有限 Program が `programCode P` から
`interfaceCode I(P,programCode P)` と `interfaceCode J(P,programCode P)` を実際に返す。
仮の canonicalizer を両方に実行し、その出力が等しい時だけ停止する一つの有限 Program を構成すると、
その Program 自身の入力で停止と非停止が同値となり矛盾する。

必要な構文は unit/pair/union/general-arrow、有限 row head/union/protect/release、
有限 `only []` mask、有限 `AsRow` body で記述した grid/zero-plane、無制約の row parameters の正負共有。
型 parameter の全単射や同数条件は使わない。比較する二 family の row parameter 数は0と `2 * P.states`。
role obligations は空であり、record/default、nominal、weak/captured は帰着に不要。
この断片を含む全目標の計算可能な完全 code を否定する障害であって、部分文法版の A2 を完成と呼ぶものではない。

文法上、ここでの general-arrow domain は既存の producer `Common.Ty` の子であり、
union constructor のない `CommonFinite.Demand` に union を追加していない。
既存 `CommonCanonicalInterface.Form.arrow` も union を含む scalar expression を domain に許し、
[recovery results §2](../handoff/2026-11-07-m1-common-recovery-results.md) は任意の負の arrow 子を除外していない。
source 生成時の極性制限や「実推論器の像だけ」を別の `Admitted` 条件として採用する場合は案2に属する。
その像への所属、または union-free な負位置文法への変換を今回証明したとはしない。

## 選択肢

1. **推奨：全文法と元の意味を維持し、計算可能 code の完全性を外す。**
   修正するのは `PublicEquivalent I J → encode I = encode J` の方向だけ。
   全有限 interface の量化、自由 parameter の無制約性、共有、weak/captured、role、regular graph を変更しない。
   提案する主張は正確には次である。

   ```text
   ∃ computableEncoding,
     ∀ finite public interfaces I J,
       computableEncoding I = computableEncoding J → PublicEquivalent I J
   ```

   表示・readback には別途、任意 `I` について decoded/exported 表現の public-instance 意味が `I` と一致する契約を残す。
   実 inference scheme、全 ambient/row/generalized assignments、全 target、実 EOF の成功・失敗、raw support を
   そのまま保存する義務も残す。これらの全文法版が今回証明済みであるとはしない。
   個別の変形には意味保存を証明し、code が異なることから意味の相違は推論しない。

2. **完全な iff を維持する場合は、量化する interface を明示した決定可能断片へ制限する。**
   変更後は `∀ I J, Admitted I → Admitted J → (PublicEquivalent I J ↔ encode I = encode J)`。
   `Admitted` の具体的な文法・有限 checker・完全性、および実 inference/export の出力がその文法に入ることは新しい証明義務。
   正負共有・再帰行・unrestricted row assignment の組合せによる今回の帰着族を除く必要がある。
   どの制限で決定可能になるかはこの障害定理からは導けず、未証明の文法条件を採用済みとは扱わない。

案1の推奨理由は、一般の interface を拒否したり既存 instance 意味を変えたりせず、
不可能性が示された計算上の完全性だけを契約から外せるためである。
ユーザーの承認前に案1/案2を元の `public_interface_canonical_exact` の代わりに採用しない。

証明と検証結果の一覧は [A2 results](../handoff/2026-11-07-m1-a2-results.md)、
各補題の量化・前提・checkpoint は [A2 progress](../handoff/2026-11-07-m1-a2-progress.md) を参照。

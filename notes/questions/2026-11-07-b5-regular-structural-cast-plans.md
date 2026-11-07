# B5: 正則な構造型の cast と「データの大きさに依らない」の両立

状態: **未決。仕様変更は提案のみ。B5 全体の E2 としては未認定。**

## 問い

有限 graph で表した再帰的な構造型に、component ごとの暗黙 cast を再帰的に通すか。
通す場合、spec 6.5 の「変換の量は型の大きさで決まり、データの大きさには依らない」は、非再帰の structural traversal に限定する必要がある。

出典:

- `spec/06-roles.md` 6.5: tuple/record/variant payload への共変な cast、上記の量の条件。
- `spec/04-types.md` 4.7b: 再帰型にも同じ要求順序を適用する。
- `notes/design/2026-11-07-common-effect-role-nominal-contracts.md` 6.3: 任意の有限 boundary description と、ground adapter だけではない全実生成 description への接続。

利用者が書く形の例（この例そのものの parser / source inference は未検証）:

```yulang
struct user_id { raw: int }
cast(x: user_id): int = x.raw

my make(n: int) =
    if n == 0: :nil
    else: :cons (user_id { raw: n }, make(n - 1))

my use_int(x: int) = x

my sum(xs) =
    case xs:
        :nil -> 0
        :cons (x, tail) -> use_int x + sum tail

sum (make 100)
```

`use_int` の注釈を介して int の期待を明示した。未知 payload の `.add` を role 制約へ freeze するだけで int が決まるとは仮定しない。

想定する regular graph は次の二つで、いずれも graph の節点数は固定である。

```text
S = :nil () | :cons (user_id, S)
T = :nil () | :cons (int, T)
```

この境界で全 cons payload に cast を通すなら、長さ n の値では user_id→int の変換が n 回要る。

## Lean で確認した正確な障害

`lean/Yulang/CommonRegularCastObstruction.lean` は、実内容付き `CaseValues.Value Empty`、opaque な nominal user_id、
純粋な唯一の直接変換 `user_id { raw: n } → n`、keep / composition / pair / variant / tag branch からなる
有限 structural plan とその独立な実行関係を定義する。

- `chain_requires_each_conversion`: 任意有限 plan、任意 length / output / count に対し、length 個の source nominal を持つ chain の実行が TargetChain を返すなら、count = length。
- `plan_fails_at_successor_budget`: 任意有限 plan について、length = plan.budget + 1 の具体的な source chain を TargetChain に変換できない。
- `no_finite_structural_plan_for_all_chains`: 全 length の source を TargetChain に変換する一つの有限非再帰 structural plan は存在しない。
- `no_data_independent_conversion_bound`: length ごとに別 plan を選んでも、全 length の型付き変換を覆う一定の直接変換回数 bound は存在しない。
- `each_length_converts` / `each_target_typed`: 任意 length について、その length を有限に展開した plan は正しく length 回で変換する。単なる変換不能例ではない。
- `sourceType` / `targetType` は、専用 nominal を保った new Common carrier 内に上記の固定 2-state graph を実際に構成する。

**未証明の接続を省略しない**: この module の有限 data-plan 実行関係と、将来の全 Common cast plan の完全一致、および上記 Yulang source からこの graph/boundary が実際に生成されることは未証明。
したがって、この障害 theorem だけで元の `common_cast_plan_exact_and_pure` や B5 全体が偽だとは報告しない。

## 選択肢と正確な修正案

1. **推奨: 正則 graph を巡る再帰 plan を許し、その場合だけデータ依存の走査を認める。**
   元の全有限 regular description の量化は保持する。amended statement:

   ```text
   任意有限 verified registry / source-target regular descriptions / 元環境 / 元式 / 元 row に対し、
   実 keep/search/failure と、有限 graph で表現した型付き（再帰を許す）executable plan の存在が iff。
   plan の immediate row は pure。実行の各有限 prefix の request tree を保持し、
   arrow は入力変換後の引数で元関数を呼ぶ。正常返却時には target 型を満たす。
   非再帰 structural traversal は型サイズによる bound を保つ。
   再帰 structural traversal の変換回数・停止は値に依存してよく、型付けから停止を主張しない。
   ```

   変更理由: 全 length に一定 bound を課す部分を除き、pure / 型 / order / request tree の条件を保つ。
   well-founded `Directed.Computation` のみで全 source の divergence を表したとは扱わず、部分実行の意味を別途必要とする。

2. **型の大きさだけの有限 plan を保ち、非自明な変換が recursive cycle を横切る境界は暗黙には通さない。**
   amended statement:

   ```text
   任意有限 description を入力にできるが、ordinary compatibility による keep 以外の
   structural lifting は有限非再帰の変換依存 graph を持つ場合に限る。
   実 synthesize の成功 iff その有限 lifting による独立 Boundary。
   cycle を巡る変換は明示関数で書く。既存 ground / acyclic theorem は保つ。
   ```

   元契約の「全実生成 boundary」の許される conversion relation を狭める選択である。
   ユーザーの承認なしにこの制限を追加しない。

## 承認待ちでも進める範囲

既存 finite ground cast、有限 source registry の純粋な body 合成、元全 site の順序評価、
nominal invariance / 旧 Common 保存 / 共有 slot family を進める。
再帰 plan の許可・拒否はまだ実装に固定しない。

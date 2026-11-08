# M1 B3: mixed 宣言表の全再帰と family slot の実割当て (2026-11-08)

状態: **部分。B3 全体の E1 は未完了**。前回の
[B3 継続結果](2026-11-08-m1-b3-continuation.md) §5 を出発点として、
解決済み source の範囲で mixed 型・行 local 宣言表の全再帰を閉じた。
family の不変区間についても、外部 `actual : Slot → RowExpr` を必要としない
実際の有限割当てと、型・行の両方の区間生成を追加した。

既存の `Common` carrier、元の再帰 source `Expr`、signed row 解釈、kinded formula を使う。
旧 value-local の定理は変更せず、新しい Lean モジュールだけを追加した。
公開 `Core.infer` と B6 は変更していない。

## 1. 仕様との対応

- `spec/05-effects.md` 5.1: operation の呼出し側では local を具体化し、handler 側では
  local が外へ逃げない rigid な引数として扱う。新しい generator の request は
  `existsLocals types rows`、全 handler arm は `forallLocals types rows` を生成する。
- 同 5.3: 継続は shallow である。継続の戻り先には、handler の元の `input` の
  型と行をそのまま残す。handler 済みの行へ変更していない。
- 同 5.4–5.5: signed boundary と有限 permission の既存規則を再帰の全域で保持する。
  ただし、ソースの可視性からそれらを取り出す lowering は今回の定理に含めない。
- `spec/04-types.md` 4.6: local の型 kind と行 kind は別である。
  新しい captured name checker は、元の有限名前表での存在と kind を実際に調べる。
- `notes/reference/2026-06-02-role-system-yulang2.md` の中心なし区間、
  `2026-06-06-invariant-type-sandwich-yulang2.md` の「CompactType の nominal / row 成分」:
  同じ row/family/argument 位置に集まった不変引数だけを共有し、両方向の交差比較を生成する。
  family 名が同じだけの異なる row 位置は統一しない。
- nominal の共変引数に不変区間を適用する規則は追加していない。
  family モジュールの入力は、既に不変位置として区別された引数出現である。

区間の `∃ actual` は「同一の不変引数が全上下界を満たす」という解釈であり、
role の照合時に任意代入を探索する規則ではない。実 slot は有限入力から計算し、
任意 semantic assignment は証明の soundness/completeness の量化子にだけ使う。
一般 solver が返す自由 parameter family は、この存在量化からは導いていない。

## 2. 宣言の解釈と独立した typing

`CommonEffectMixedDeclarations.Declaration` は既存の
`CommonEffectKindedHandler.Declaration` を使う。
型 local 数、行 local 数、元 key、追加 effect key 列、有限 input/output 型構文を保存する。
captured 名前と二つの local 名前空間は `α ⊕ (Fin types ⊕ Fin rows)` で区別する。

`SemanticSignature` はこの有限構文を任意 captured assignment `ρ` と
`Locals types rows` で解釈する。`interpret_rename` と `interpretAll_rename` は、
全ての捕捉と local の区別が再帰中の rename で保たれることを示す。
`lookup_interpretAll` は、元の有限位置での成功と欠番の両方を保持する。

`CommonEffectMixedSource` は、元の `CommonEffectRecursiveSource.Expr` を再利用する。
新たな実行式や別 carrier へ移していない。独立した inductive `Typing` は、
生成関数も生成 formula も参照しない。

対象は変数、literal、lambda、application、value/computed let、条件分岐、pair と射影、
empty record、record、strict record default、field、variant、request、signed boundary、
single/multiple/partial handler の全 constructor である。
record の隠れる field/default も、元規則と同じく評価・effect に寄与する。

operation-local の型と行は、request ごとに新しく具体化する。
handler は外側の環境、action の `input`、return arm の `returned`、全体の `out` を
固定した後、各 operation の **全ての型 local と全ての行 local** を検査する。
arm 自身の結果だけは各 local assignment に依存できる。
通常の inferred binding の行を、この operation-local の規則で再一般化してはいない。

## 3. 全再帰 generator の exactness

### `CommonEffectMixedExact.generate_recursive_mixed_exact`

任意の `scopes : Nat`、名前型 `α`、有限 mixed 宣言表 `D`、
有限 semantic signature 表 `S`、元の再帰式 `e : Expr scopes`、
有限 symbolic 環境 `sΓ`、独立 binding 環境 `Γ`、
任意 `ρ : α → Computation`、有限結果記述 `out : CompTerm α` について、
次の **二つだけ**からなる `ContextRel S D ρ sΓ Γ` を前提とする。

1. `interpretAll ρ D = S`。
2. 任意の元環境 index と computation `c` に対し、入力 scheme の充足と
   入力 binding の `BindingTyping S` が同値であること。

このとき、

```text
Holds ρ (CommonEffectMixedGeneration.generate D sΓ e out)
  ↔ CommonEffectMixedSource.Typing S Γ e (out.eval Common.model ρ)
```

が成立する。source の全 constructor に対する induction で証明した。
nested request の payload、handler の action/return/operation arm、stored polymorphic
value の内部まで、**同じ mixed 宣言表を保って**再帰する。
zero-arm の multiple/partial handler も含む。

成功した solver、support、fuel、外部の body exactness を前提にしない。
`ContextRel` は指定された入力環境の意味対応であり、求解済み条件ではない。
raw theorem は有限宣言を任意に量化するので、kind admission は次節で別途計算する。

## 4. captured 名前と両 local kind の admission

### `CommonEffectMixedKinds.check_declarations_exact`

任意の有限 `captured : List Kind` と有限 mixed `D : Declarations Nat` に対し、

```text
checkDeclarations captured D = true
  ↔ DeclarationsKinded captured D
```

右辺の `TypeKinded` / `RowKinded` は独立した inductive 判断であり、Boolean checker を
参照しない。各型変数・行変数の出現を検査し、arrow の input/output 型と
incoming/outgoing 行の中も再帰する。

- captured 名前は `captured[name]?` の元位置で存在し、期待する kind を持つ必要がある。
- local の型名前と行名前は別々の `Fin` 名前空間で検査する。
- captured 欠番、captured kind の相違、local 型を行として使う出現、
  local 行を型として使う出現は拒否する。

### `CommonEffectMixedChecked.generate_checked_exact`

任意の finite captured kind 表、`D : Declarations Nat`、`sΓ,Γ`、
任意 `ρ : Nat → Computation`、元の `e` と有限 `out` に対し、
入力だけの `EnvRel (interpretAll ρ D) ρ sΓ Γ` を前提に、

```text
Holds ρ (generateChecked captured D sΓ e out)
  ↔ DeclarationsKinded captured D
     ∧ Typing (interpretAll ρ D) Γ e (out.eval Common.model ρ)
```

を示す。宣言表の意味は `D,ρ` から計算し、kind admission は
**結論の一部**として生成する。検査成功を利用者に要求する形ではない。

### `CommonEffectMixedChecked.generate_closed_checked_exact`

上と同じ任意 captured kind 表、有限 `D`、`ρ,e,out` について、
`sΓ=Γ=[]` の場合は `EnvRel` も不要である。

```text
Holds ρ (generateChecked captured D [] e out)
  ↔ DeclarationsKinded captured D
     ∧ Typing (interpretAll ρ D) [] e (out.eval Common.model ρ)
```

これは元の閉じた再帰式に対する定理であり、capture が空であるという条件ではない。

## 5. mixed family 引数の実有限割当て

`CommonEffectMixedFamilyAllocation.Occurrence` は、
元の `Slot = (row, family, argument)`、元出現 `origin`、
型区間または行区間の有限構文を保存する。
型区間は有限 `TyTerm` の二端点、行区間は既存 signed `RowExpr` の上下 endpoint 列である。
行の upper を表すために、既存の構文にない meet/top constructor は追加していない。

`slots kind occurrences` は元の列から該当 kind の slot を集めて重複を取り除く。
二つの finite pool にそれぞれ `Fin length` の index を付ける。
外部から `Slot → RowExpr` や同等の source-to-slot callback を受け取らない。

- `reference_eq_iff`: 任意 finite pool と、そこに含まれる任意の二つの元 slot について、
  計算した index が等しい iff 元の `(row,family,argument)` が等しい。
  source の別 row・別 family・別 argument を勝手に統一しない。
- `valueAt_encode` / `rowAt_encode`: 任意の型・行 semantic assignment を finite locals へ
  encode すると、全ての実際に出現する元 slot で同じ型・同じ行を回収する。
  assignment に support 条件や整合性条件を課さない。
- `encode_decode`: 任意の unrestricted finite local assignment について、
  decode した後の encode は文字通り元の assignment に戻る。
  存在しない source slot に対して未使用 local を余分に割り当てていない。

この結果は上記の **解決済み occurrence 列からの allocation** である。
raw source/annotation/stack の全出現を正しい row slot へ集める producer の完全性は別義務である。

## 6. mixed family 区間の実生成と独立 realization

### `CommonEffectMixedFamilyConstraints.generate_exact`

任意の有限 resolved invariant family kind 表 `F : List (List Kind)`、
任意の元 mixed 引数出現列 `os : List (Occurrence scopes α)`、
任意 captured `ρ : α → Computation` に対し、

```text
Holds ρ (generate F os) ↔ Reconciles F os ρ
```

が成立する。右辺は allocator/generator を参照せず、次を要求する。

```text
∃ values : Slot → Common.Ty, ∃ rows : Slot → Common.Row,
  ∀ o ∈ os,
    Declared F o
    ∧ o の元区間が同じ values(o.slot) / rows(o.slot) を含む
```

`Declared` は元 family index から有限表を引き、その signature の元 argument index に
ちょうど同じ kind があるという独立判断である。
未知 family、引数位置の欠番、型/行 kind の相違は実 checker により拒否する。
family を制約が通るまで選び直す検索は行わない。

生成側は、計算した二つの finite pool を `existsLocals` で束縛する。
全元出現の自己区間検査と、同一 allocated actual への全上下界比較を生成する。
さらに、元出現の全順序対から、slot が同じものの lower-to-upper 交差比較を生成する。
したがって異なる二出現間の両方向比較も落とさない。
全比較は通常の有限 formula constructor であり、semantic predicate の atom は追加していない。

この定理は任意の原始 endpoint を解釈する。endpoint 内の captured 名前の kind 検査、
raw family application が指定 arity の引数を全て持つこと、
source 全体からの出現列生成、宣言表と式中の family reference への接続は、この定理だけでは示さない。
`F` は既に不変位置として区別された family 引数の kind metadata であり、
nominal 全引数を不変と仮定する新しい規則ではない。

## 7. 検証と commit

基準 `a019f8e09` で、監督側が最初に全 build と trust-zero Audit を実行し、
`Build completed successfully (1037 jobs)` と
`Axiom allowlist passed for 75447 declarations` を確認してから作業を開始した。

各 packet を `lake build --wfail Yulang.<対象モジュール>` で検査した。
最後の二つの主要対象の focused build は次のとおりである。

```text
lake build --wfail Yulang.CommonEffectMixedChecked
Build completed successfully (90 jobs).

lake build --wfail Yulang.CommonEffectMixedFamilyConstraints
Build completed successfully (97 jobs).
```

独立した監査ファイルを `lake env lean --trust=0 <監査ファイル>` で実行し、
宣言解釈、全再帰 exactness、captured kind check、checked source exactness、
有限 slot recovery、family generation の主要 theorem を `#print axioms` で検査した。
全て `{propext, Classical.choice, Quot.sound}` の部分集合である。
family の `generate_exact` は `[propext, Quot.sound]` だけに依存する。
`sorry`、追加公理、`native_decide`、warning 抑止は追加していない。

共有 `Yulang.lean` / `Audit.lean` / `README.md` の追記と統合ブランチの全 gate は監督側が行う。
Rust/runtime の検査は今回の Lean-only 変更に対して実行していない。

下表の SHA は detached 作業 worktree のもの。統合時の cherry-pick で公開 SHA は変わり得る。

| commit | 内容 |
| --- | --- |
| `0897cc169` | captured/local の区別を保った mixed 宣言の有限解釈 |
| `bf4bcf23e` | 元の再帰 source 全体に対する独立 mixed typing |
| `1ea0ef654` | stored scheme の capture-avoiding な mixed formula 操作 |
| `b6d80fe5a` | 一つの mixed 宣言表を保つ全再帰 generator |
| `c50279e55` | 全 constructor の generator iff typing |
| `4d5864729` | 元 captured 名と両 local kind の有限 checker iff 独立判断 |
| `cb7575cc4` | kind admission を前提にしない checked source exactness |
| `61fd6726f` | 元 family slot の実 finite allocation と全割当て回収 |
| `c0ad30363` | mixed family 引数の全元区間・交差制約の実生成 exactness |

## 8. E1 までの正確な残り

1. **raw source 宣言/式からの lowering 全体。** 元の再帰 `Expr` は再利用したが、
   operation/family key は解決済み自然数、permission は有限 metadata、partial handler の
   coverage は解決済み metadata である。名前解決、可視性、permission 抽出、
   hygiene boundary の配置、正しい SCC snapshot の生成を含む whole-source iff は未完。
2. **family allocation への source 接続。** 任意の mixed resolved occurrence 列から
   実 allocator と制約生成は閉じた。raw family application の完全な arity/kind 検査、
   全出現の収集、pop 前の family 出現の保存、正しい元 row 位置への照合、
   生成した shared index と operation 宣言/body の captured 引数との接続が残る。
   型 kind を含む allocator 自体を、今後「未実装」と重複して扱う必要はない。
3. **実 solver の全 family。** 実生成問題の任意 independent rows と全 compiled node values に対し、
   `Models` iff 実返却 scheme と無制約 parameter による同一 rows・全 node の要求同値回収、
   および任意返却 scheme/parameter の soundness を閉じる必要がある。
   今回の `existsLocals` は未求解 formula に残る。自由 parameter の条件へ移していない。
4. **一般 mixed 全称の求解。** 固定外側 Γ/input/returned/out の下で、型・行 locals の
   一般 `forallLocals` を解く必要がある。現在は構文生成とその独立 typing の意味同値である。
5. **arrow inspection の有限 family。** 元 `Realizes` と全 ID を保った domain cover / result inter の
   一般求解が残る。depth ごとの cover を全 depth に共通する一つの branch に替えてはいけない。
6. **rank-2 field の source 接続。** 既存 `CommonEffectFieldTable` は依然として
   value-local operation 表を用いる。mixed operation 表との接続、実 nominal source、
   strict construction effect、field captured 名前の検査は残る。
7. **仕様が未決の箇所。** 一般 rank-2 struct 同士の部分型・role 等の相互作用を
   今回決めていない。新しい `notes/questions/` は作成していない。

以上の局所結果を B3 全体の E1、あるいは B6 入口の完成として扱わない。

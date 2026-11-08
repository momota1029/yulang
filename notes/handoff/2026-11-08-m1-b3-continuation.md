# M1 B3: rank-2 field と effect-family 行区間の継続結果 (2026-11-08)

状態: **部分。B3 の E1/E2 には未到達**。元の B3 の量化子・前提・完了条件は変更していない。
作業 0 のモデル監査と初期 build/Audit の成功後、独立した新モジュールだけを追加した。
公開 `Core.infer` への B6 統合は行っていない。

## 1. 正本と、今回閉じた範囲

- `spec/04-types.md` 4.6: struct の field-local 変数は、構築時に rigid、使用時に毎回具体化する。
  `ref.run` の `'f` は **行 kind** である。`'a` と `'e` は捕捉する nominal 引数である。
- `notes/reference/2026-06-02-role-system-yulang2.md`「注意」:
  不変区間は中心を保存せず、同じ実引数の merge は lower の和と upper の共通部分、
  `loA <= upB` と `loB <= upA` の両交差条件を要求する。
- `notes/reference/2026-06-06-invariant-type-sandwich-yulang2.md`「CompactType の nominal / row 成分」:
  effect-family 引数も同じ row slot の同じ family に集まったときにすり合わせる。
  family 名が同じというだけで、別々の row slot の引数を一律に併合する規則ではない。

今回の結果は次の二つである。

1. 型・行を区別する既存 binder を使い、pure な field の検査、有限 field 表の保存、
   解決済み位置からの新鮮な具体化、元の source body によるその使用の正当化を接続した。
   `ref.run` の実際の有限署名をこの表に格納した。
2. effect-family の **行 kind の引数**について、有限 endpoint 列を中心なし区間として保存し、
   同一の `(元 row 位置, family ID, 引数位置)` にある全出現を集約し、
   全交差制約と共有された実引数の上下界を、実際の有限 `Formula` に生成した。

## 2. field に関する定理

以下で `scopes : Nat` と名前型 `α : Type` は任意。
`D` は既存の **value-local** な有限 `CommonEffectRequestGeneration.Declarations α`、
`S` は独立した semantic signature 表、`sΓ` は有限 symbolic 環境、`Γ` は semantic binding 環境、
`ρ : α → Computation` は任意の捕捉割当てである。
構築側の定理は明記する `ContextRel S D ρ sΓ Γ` を前提とする。
これは検証済み source 宣言の lowering が完了したという前提ではない。

### 2.1 `CommonEffectFieldInstances.construct_use_sound`

任意の上記 `S,D,sΓ,Γ,ρ` と `ContextRel`、任意の有限 `FieldScheme F`、
任意の再帰的 effect source body `e : CommonEffectRecursiveSource.Expr scopes`、任意の有限 `out` に対し、

- `constructCheckedField D sΓ F e` が `ρ` で成立し、
- `useCheckedField F out` が同じ `ρ` で成立するなら、

`Typing S Γ e (out.eval ρ)` が成り立つ。
構築時の同じ `e` と捕捉環境 `Γ` が、使用時に選ばれた任意の型・行 local に対して使われる。
構築時に一つの local assignment を固定したり、複数の使用で共有したりしない。

### 2.2 `CommonEffectFieldTable.construct_fields_exact`

任意の上記 `S,D,sΓ,Γ,ρ` と `ContextRel`、任意の有限 field 列 `fields`、
任意の元 source body 列 `bodies` に対し、

`constructFields D sΓ fields bodies` の `ρ` での充足は、
各同一位置の field/body が kind 検査に通り、その field 独自の **全ての型・行 locals** に対して
同じ `Typing S Γ` で pure な field 型を持つという `FieldsTyping` と同値である。
列の長さが違えば拒否し、元の field/body を捨てない。

### 2.3 `CommonEffectFieldTable.project_exact`

任意の `ρ`、任意の有限解決済み `Declaration`、任意の自然数位置 `i`、任意の有限 `out` に対し、
`project declaration i out` の充足は、

1. ちょうど位置 `i` に field `F` が存在し、
2. `F` の local kind 検査が成功し、
3. ある新鮮な型・行 local assignment による pure な field 型が `out.eval ρ` 以下になる
   `FieldUse ρ F (out.eval ρ)` が成立すること

と同値である。位置がなければ拒否する。具体化した結果を declaration に書き戻さない。
ここでの存在量化は spec 4.6 が指定する使用時具体化であり、role 照合の任意代入ではない。

### 2.4 `CommonEffectFieldTable.constructed_projection_sound`

任意の上記 `S,D,sΓ,Γ,ρ` と `ContextRel`、任意の declaration、元 body 列、位置 `i`、有限 `out` に対し、
その表全体の `constructFields` と同じ表の `project i out` が成立すれば、
元 body 列の **同じ位置 `i`** に body `e` があり、`Typing S Γ e (out.eval ρ)` が成立する。
補助 `FieldsTyping.lookup` は body の存在と位置を、完全な構築の検査結果から導く。
これは元 field body に関する定理で、未実装の nominal runtime に対する射影定理とは呼ばない。

### 2.5 `CommonEffectRefRunField`

`refRun a e` は、型 local が 0 個、行 local が 1 個の有限 `FieldScheme` で、
`∀f. (a → [f] a) → [e,f] ()` を保存する。`refRun_wellKinded` と `refRun_eval` が kind と解釈を確認する。

- `construct_ref_run_exact`: 任意の `S,D,sΓ,Γ,ρ,ContextRel`、捕捉名 `a,e`、元 source body `body` に対し、
  checked 構築の充足は、**全ての `f : Common.Row`** について、同じ body が
  `pure ((ρ(a).ty → [f] ρ(a).ty) → [ρ(e).row,f] ())` を持つことと同値である。
  `Common.Row` には無限集合も任意の signed coordinate 長も許す。
- `use_ref_run_exact`: 任意の `ρ,a,e,out` に対し、checked 使用の充足は、**ある `f : Common.Row`** で
  上記の pure な関数型が `out.eval ρ` 以下になることと同値である。
- `project_ref_run_exact`: 任意の `ρ,a,e`、nominal ID、field ID、`out` に対し、
  `run` 一つだけを持つ実有限 declaration の位置 0 の射影について、同じ存在具体化の iff が成立する。

## 3. 行区間と family slot の定理

以下で `scopes : Nat`、名前型 `α : Type`、`ρ : α → Computation` は任意。
endpoint は、変数・空行・head・union・protect・release・residual を持つ既存の有限 `RowExpr scopes α`。
`Bounds` は lower/upper の有限列だけを保存する。
lower の意味は全 lower の union、upper の意味は全 upper の intersection。
空の lower は空行、空の upper は全行である。
`RowExpr` に存在しない meet/top constructor を捏造せず、この列を使って実比較を生成する。

- `CommonEffectRowIntervalConstraints.cross_checks_exact`: 任意の区間 `A,B` と任意の `ρ` に対し、
  実有限 `crossChecks A B` の充足は `eval(A).lower <= eval(B).upper` と同値。
  `check_exact` は `A=B` の場合で、自己整合性との iff。
- `Bounds.eval_merge`: 任意の `A,B,ρ` に対し、endpoint 列を連結する `merge` の評価は、
  semantic `EffectRow.merge` と文字通り等しい。
- `merge_check_exact`: 任意の `A,B,ρ` に対し、merge の実生成 check は、
  `check A ∧ check B ∧ crossChecks A B ∧ crossChecks B A` と同値。
  元区間の整合性は前提ではない。
- `contains_exact`: 任意の `A`、既に割り当てられた shared actual の有限 `RowExpr t`、任意の `ρ` に対し、
  実有限 `contains A t` は `eval(A).lower <= eval(t) <= eval(A).upper` と同値。
  actual を照合のために任意に選び直さない。
- `merge_contains_exact`: 任意の `A,B,t,ρ` に対し、同じ `t` が merge に属する実制約は、
  `contains A t ∧ contains B t` と同値。

`CommonEffectFamilyRowSlots.Slot` は **元 row 位置、family ID、argument 位置**を全て保存する。
`Occurrence` はその slot、元出現 ID、有限区間を保存する。

- `collect_member_exact`: 任意の slot `s`、元出現の有限列 `os`、任意の `ρ` と任意の実際の行 `r : Common.Row` に対し、
  `r` が集約後の区間に属することは、`os` に含まれ slot が **ちょうど `s`** である全出現の区間に
  同じ `r` が属することと同値。
- `collect_contains_exact`: 任意の上記 `s,os,ρ` と有限 actual term に対する、同じ主張の実生成制約版。
- `generate_exact`: 任意の元出現の有限列 `os`、syntax が供給する shared actual の対応
  `actual : Slot → RowExpr scopes α`、任意の `ρ` に対し、実有限 `generate os actual` の充足は、
  **全ての元出現 `o ∈ os`** の区間が、同じ `actual(o.slot).eval ρ` を含むことと同値。
  generator は出現する有限 slot だけを `eraseDups` で一度ずつ処理し、
  全交差比較と actual の上下界制約を生成する。外部の Models/support/fuel 条件は前提にしない。

これらは制約生成と局所意味の iff である。未解決の式を solver の自由 parameter 条件へ移して
「解けた」と呼んでいない。source の actual allocator の完全性、family key の解決、
型 kind の family 引数を含む mixed な表全体の接続、一般全称求解は未完である。

## 4. 検証と commit

各 packet を `lake build --wfail Yulang.<対象モジュール>` で検査し、
独立した `--trust=0` の監査ファイルで全主要 theorem の `#print axioms` を確認した。
最後に今回の 5 モジュールを同時に指定した build を実行した。

```text
lake build --wfail Yulang.CommonEffectFieldInstances Yulang.CommonEffectFieldTable \
  Yulang.CommonEffectRefRunField Yulang.CommonEffectRowIntervalConstraints \
  Yulang.CommonEffectFamilyRowSlots
Build completed successfully (96 jobs).

'Yulang.CommonEffectFamilyRowSlots.collect_member_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonEffectFamilyRowSlots.collect_contains_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonEffectFamilyRowSlots.generate_exact' depends on axioms: [propext, Quot.sound]
```

全監査結果の公理は `{propext, Classical.choice, Quot.sound}` の部分集合である。
`sorry`、追加公理、`native_decide` は追加していない。
共有 import / `Audit.lean` / README の変更と統合ブランチでの全 gate は監督側が行う。

下表は detached 作業 clone の commit ID。統合時に cherry-pick するため、公開 commit ID は変わり得る。

| commit | 内容 |
| --- | --- |
| `076b7a794` | checked field の構築から使用への soundness |
| `4a5dc0e5c` | 全有限 field 表の rigid 構築の exactness |
| `97d43f5bf` | 解決済み field 位置からの fresh projection exactness |
| `f952bc1d0` | 元 source body と同じ位置に戻る projection soundness |
| `8e8683342` | `ref.run` の有限署名と全行 rigid 構築 |
| `df73fae50` | `ref.run` の新鮮な行具体化と表からの射影 |
| `4686f21ca` | 行区間の有限 endpoint 比較の生成 |
| `5c1ef3481` | merge での両交差条件の保持 |
| `733e9d4fe` | shared actual の上下界制約と merge |
| `55c70bf91` | 同一 row/family/argument slot の区間集約 |
| `57f531d3d` | 全元出現に対する有限 family row-slot 制約生成の exactness |

## 5. 正確な残り

1. 任意の有限検証済み source operation 宣言 `D`、関連する環境 `sΓ,Γ`、任意の `ρ`、
   対象 Core 式 `e` と有限 `out` について、
   `Holds ρ (generateFinite D sΓ e out) ↔ CommonEffectTyping D Γ e (out.eval ρ)` を閉じること。
   旧 value-local 表だけでなく mixed 型・行 local 表全体の再帰、family 引数の区間照合、
   visible effect / permission / hygiene の lowering を含める必要がある。
2. 上記の **実生成問題** `p` の任意の独立 rows と全 compiled node values について、
   `(compileEffect D p).Models rows values` と、実返却 scheme と無制約 parameters による
   同一 rows・全 node の要求同値な values の回収との iff を閉じること。
   任意返却 scheme・任意 parameters の soundness も必要である。
3. `CommonEffectArrowInspection` の有限 Output の domain cover と result inter 比較を、
   元 `Realizes` と全 ID を保った実有限 family に解くこと。
   depth ごとの cover を、全 depth に共通する一つの branch に置き換える経路は既存反例で不正。
4. 固定した外側 Γ/input/returned/out の下で、mixed local 全称を一般に求解すること。
   operation-local 型・行を外側の parameter 条件へ移さない。
5. rank-2 field の保存・射影を、実 nominal source と strict construction effect の生成に接続すること。
   今回の表は **pure な各 field body、既に解決された field 位置**の橋である。
   captured 名前の kind/name 検査は source lowering の別義務として残る。
6. `∀field` を含む struct 同士の部分型・一般化・role の相互作用など、spec 4.6 で未決の意味論を
   勝手に補わない。今回その statement を変更する提案や新しい未回答質問は追加していない。

元の B3 E1/E2 を完了とは扱わず、B6 の入口も変更していない。

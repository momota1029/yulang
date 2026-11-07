# Common への effect・role・nominal 統合: 残る契約

日付: 2026-11-07。状態: **Draft — B3/B4/B5 の設計と未完補題の記録**。

`Core.infer` の全構文への拡張に向け、既存の別モデルと Common の実生成 solver の接点を確認した。B3 の有限 occurrence 定数を持つ row flow は、この記録に先行する `CommonRowHeadFlow` / `CommonRowHeadSolver` で閉じた。request、handler、method、nominal、cast、construction の公開入口への統合は、この row 補題からは従わない。

以下の未実装契約名は設計上の名前であり、同名の Lean 宣言が実装済みであることを意味しない。A1/A2 の残りは別記録に委ねる。今回、新しい利用者向けの仕様質問は生じていない。

## 1. 全段階で保つ完了条件

有限な実宣言環境 `D` と対象構文について、同じ Common carrier の独立した constructor judgment を先に定義する。その定義に generator、solver、`Formula.Holds` を使わない。

公開入口の必要条件は、任意の検証済み有限実宣言 `D`、任意の対象閉式 `e`、任意の結果計算型 `c` に対する次の形である。ここでは返却 scheme 列を `schemes D e`、公開分類を `classify D e` と書き分ける。

```text
Typing D [] e c
  ↔ ∃ S ∈ schemes D e, ∃ p, S.instantiate p ≤ c

∀ S ∈ schemes D e, ∀ p,
  Typing D [] e (S.instantiate p)

classify D e = rejected ↔ ¬ ∃ c, Typing D [] e c
```

`p` に `Models`、`ResidualHolds`、support、fuel、solver 成功、closed cache の条件を残さない。別モデルの成功をそのまま Common の成功と呼ばない。対象断片の構文条件は、実生成器が必要な内部 grammar を満たすことの証明に使い、公開 principal theorem の成功前提にはしない。

宣言の well-formedness は、仕様に従い、solver から独立に定義する宣言検査である。内部定理は `D.Valid` を明示してよいが、raw declarations を受ける公開入口はその検査を実行する。solver の成功を `CheckedDeclarations` の証明欄に隠す設計にはしない。

## 2. 採用する入力の表現

### 2.1 有限な実宣言と、任意の意味関数を区別する

`Core.EffectTyping.LocalSignature`（`CoreEffectTyping.lean`）の現在の `input` / `output` は、任意の関数 `(Fin locals → m.Ty) → m.Ty` である。`Contract.permission` も `Core.Expr s → s.Key → Bool` として与えられる。この任意関数を受け取る semantic judgment の一般性は保つが、任意関数から有限型構文を計算で取り出せるとは仮定しない。

同様に、`RoleConstraints.Theory m` は `Predicate m.Ty → Prop` である。任意の述語を受け取る theorem と、有限な実 `impl` 宣言を入力にして解決する算法は別の契約である。

**採用方針**: 実推論の入力には、有限な operation/method/role/nominal/cast declaration syntax を使う。名前、型本体、parameter の数と種別、qualifier、constructor signature、scope と可視性を有限データとして保持し、その意味を既存の semantic interface へ写す。意味関数そのものを opaque な formula leaf として格納する案は採用しない。

この選択により、有限生成・停止・export に同じ declaration identity を使える。既存の任意モデル上の exactness theorem は、有限宣言の解釈を代入する先として再利用する。

### 2.2 signature を空のままにして一般の effect/atom を閉じない

現在の `Core.Required.Term` は `Core.Expr Signature.empty` である。`Signature.empty` では `Op`、`Key`、`Scope`、`Float`、`Atom` がすべて `Empty`。一般の request/atom を表す入力には、実宣言を反映する非空の signature が必要である。

空 carrier のため構築不能な構成子と、同じ syntax には存在するがまだ規則のない構成子を区別する。opaque atom を unit に下げたり、effect signature の入力を空で固定したまま一般の B3 を完了としたりしない。

## 3. B3: effect と handler

### 3.1 既存の接点と、その範囲

| 接点 | 実装済みの性質 | Common 統合に残るもの |
| --- | --- | --- |
| `CoreEffectTyping.lean` | 独立した request/boundary/handler/multiHandler/partialHandler 規則 | 基礎規則は旧 required-field 型付け。exact empty/optional/default と同じ judgment には未統合 |
| `CoreEffectGeneration.lean` | syntax に沿って再帰する `generate : ... → Prop` | model-independent な有限 formula への reification |
| `Core.EffectTyping.generate_models_iff_typing` / `principal_exact`（`CoreEffectExactness.lean`） | 上の semantic generation と独立 judgment の同値 | 有限 solved scheme 列・全 parameter soundness |
| `RecursiveEffects.Formula` | 再帰的 effect syntax の有限 formula | signature は monomorphic、型文法は旧 required-field |
| `RowInference.Constraint` / `poly_request_constraints_exact` / `poly_handler_constraints_exact` | finite exists/forall type quantification、signed row expression | Common の全 source generation / compiled graph / solver への接続 |
| `MultiOperationPayloadHandlers` | 解決済み pure payload test/guard の順序付き dispatch と正しい減算 key | source pattern/default/guard の生成、effects と bindings の統合 |

spec 5.1 の operation-local type は、呼び出しで自由に具体化し、handler では抽象的に扱う。spec 5.3 の shallow resumption は元の action row を持つ。spec 5.5 の permission にない arm は静的に拒否する。これらは新しい仕様選択ではなく、保つべき既存条件である。

### 3.2 `common_effect_row_interpretation_exact`〔未実装〕

**対象と量化**: 任意の有限 scope 数 `n`、任意の `Directed.Row n Nat` の `r/s`、任意の scope `k : Fin n`、permission `M : Nat → Bool`、handled key 列 `H`。

**必要な結論**: 同一の occurrence encoding と row embedding を用い、次を示す。

```text
SignedStructural.RowLe r s
  ↔ Common.rowLe (embedRow r) (embedRow s)

embedRow (r.map (Directed.protect k M))
  = commonProtect k M (embedRow r)
embedRow (r.map (Directed.release k M))
  = commonRelease k M (embedRow r)
embedRow (Directed.residual H r)
  = commonResidual H (embedRow r)
```

`commonProtect` / `commonRelease` / `commonResidual` は任意の Common row に意味を持つ必要がある。自由な row parameter に「有限 list として表現できる」という条件を加えない。任意の `r : Common.Row` について、同じ scope/permission の protect と release が両側で打ち消し合うことも別に示す。`Directed.Capturable` の条件は「handled key で、全重みが0」であり、負の重みも残余に保持する。

Common の `Occurrence = Nat × List Int` は符号と各座標を保持し、`Row = Occurrence → Prop` は任意の集合を許す。一方、`RowInference.signedAlgebra n Key` は `Directed.Occurrence n Key` の有限 list を使う。両者が同じものだと仮定して `RowView` を置いてはいけない。

**表現の決定**: scope identity と座標の対応を有限宣言側で保持し、embedding の可換性を証明してから row solver に接続する。重み列への無証明な padding は採用しない。例えば末尾0を足した列は現在の Common occurrence と文字通り同じではなく、protect/release の往復や row retraction の等号を壊し得る。固定長の範囲での embedding と、任意 Common row 上の全域な演算の設計を明示的に分ける。

### 3.3 `generate_common_effect_finite_exact`〔未実装〕

**対象と量化**: 任意の有限 effect declaration `D` と独立した宣言検証 `D.Valid`、任意の symbolic environment `sΓ`、任意の semantic environment `Γ`、任意の ambient assignment `ρ`、任意の対象 Core 式 `e`、任意の symbolic result `out`。

**前提**: 宣言 syntax と semantic contract の解釈の一致、および `EnvRel ρ sΓ Γ`。どちらも solver 成功条件ではない。実宣言から permission を計算し、その静的規則との一致も証明する。任意の permission 関数を外から仮定した exactness だけでは公開入口を閉じない。

**結論**:

```text
Holds ρ (generateFinite D sΓ e out)
  ↔ CommonEffectTyping D Γ e (out.eval ρ)
```

`generateFinite` は inductive な有限構文を返す。source typing、任意の `Comp → Prop`、求解の成功を formula の leaf に持たせない。Common の exact empty、required field、optional/default を保つ生成規則を使う。

#### handler の量化順

単一 operation について、外側の `Γ`、結果 `c`、action result、return result は operation-local assignment の外に置く。必要な形は次である。

```text
permission(handler, operation.key) = true
∧ ∃ input returned,
  ActionTyping Γ action input
  ∧ ReturnTyping (pure input.value :: Γ) onReturn returned
  ∧ ∀ ι : Fin operation.locals → Common.Ty,
      ∃ operated,
        ArmTyping (payload(ι) :: resumption(response(ι), input) :: Γ)
          onOperation operated
        ∧ union returned.value operated.value ≤ c.value
        ∧ residual operation.key input.row
            ∪ returned.row ∪ operated.row ≤ c.row
```

resumption の出力は元の `input`。handler の減算済み row に差し替えない。`operated` は local assignment ごとに変わってよい。`∃ operated, ∀ ι` として一つの固定結果を要求する案は、既存判断を強めるため採用しない。

複数 arm では `ι : (i : Fin count) → Fin locals[i] → Common.Ty` を全称化し、その内側で arm 結果列を存在量化する。`Γ`、input、returned、最終結果は同じく外側に保持する。現行 judgment の「結果関数を存在量化してから全 local を検査する」形とは、関数を構成する選択の証明を通して対応させる。

partial handler が引く key は、既存 `removedKeys` のとおり unguarded irrefutable arm があるものだけである。refutable test の和や常に true な guard を勝手に total とみなさない。source の effectful guard/default はこの resolved pure test 層とは別に生成する。

#### 境界情報の確定時点

任意の実 binding（相互再帰では SCC）、任意のそこで一般化する interface に対して、共変の effect 注釈が検査する occurrence は、その binding/SCC の推論終了時に具体的に見えるものと一致しなければならない（spec 5.5b）。後の呼び出し側の任意 parameter による具体化で再検査しない。反変 permission の抽出と、共変側のこの検査時点の theorem は、単に `Contract.permission` を供給した effect exactness からは出ない。

### 3.4 `solve_common_effect_all_instances_exact`〔未実装〕

**対象と量化**: 任意の検証済み有限宣言 `D`、任意の対象式から実生成した packed problem `p`、任意の独立 row assignment `rows`、任意の compiled node assignment `values`。

**結論**:

```text
(compileEffect D p).Models rows values
  ↔ ∃ S ∈ solveEffectAll D p,
      ∃ rowParameters, ∃ valueParameters,
        S.instantiateRows rowParameters = rows
        ∧ ∀ i,
          S.instantiateValues rowParameters valueParameters i ≈ values i

∀ S ∈ solveEffectAll D p,
  ∀ rowParameters, ∀ valueParameters,
    (compileEffect D p).Models
      (S.instantiateRows rowParameters)
      (S.instantiateValues rowParameters valueParameters)
```

元の全 row ID を同じまま回収し、literal equality を保つ。local universal check や変換後の row 条件を parameter の前提に残さない。実生成 grammar の閉性は generator 側の定理で供給する。

有限の source syntax だからといって、変換後の occurrence 集合を有限列挙できるとは限らない。新しい row 制約文法に `head(k) ⊆ r` と `protect(scope, denied, r) ⊆ r` の循環を許す場合、0から始めて任意回数だけ重みを増やした occurrence が必要になる。その場合は有限な記号表現で変換閉包を表すか、実生成器がその形を生成しないことを証明する。既存の flow ID の有限性だけで閉じたことにはしない。

## 4. 実装済みの B3 部分: head 定数付き row flow

`CommonRowHeadFlow.Problem n` の入力は、有限な `RowFlowSchemes.FlatProblem n` と有限な `(slot, occurrence)` の列である。flat problem は flow と pure sink を含む。`Models` は、元の row assignment が全 flow/pure 条件と全 occurrence 所属条件を満たすことを独立に定義する。

`CommonRowHeadFlow.Scheme` は伝播済み occurrence の有限列と、既存 `RowFlowSchemes.Scheme` の有限 row term を持つ。具体化はその定数 row と既存 flow family の union。`Fin n → Common.Row` の全 parameter を許し、無限集合の row も除外しない。

### 閉じた定理

| 定理 | 量化・前提・結論 |
| --- | --- |
| `CommonRowHeadFlow.coalesce_retraction` | 任意の `n/problem/rows`、`Models problem rows` の下で、元の `rows` 自身を parameter にすると `instantiate rows = rows` |
| `CommonRowHeadFlow.no_heads_instantiate` | 任意の旧 flat problem と全 row parameters について、head なしの新 family は旧 `RowFlowSchemes.coalesce` の具体化と等しい |
| `CommonRowHeadSolver.solve_all_instances_exact` | 任意の有限 problem と任意の独立 rows について、`Models problem rows ↔ ∃ S ∈ solve problem, ∃ p, S.instantiate p = rows`。`p` に条件なし |
| `CommonRowHeadSolver.all_parameters_models` | 任意の problem、返した任意の S、任意の row parameters について Models。前提は S の membership のみ |
| `CommonRowHeadSolver.rejected_iff` | 任意の problem について、返却リストが空であることと Models が存在しないことが同値 |
| `CommonRowHeadSolver.rejected_iff_head_reaches_pure` | 任意の problem について、拒否と「要求されたある occurrence が flow を通して pure sink に届くこと」が同値 |

`solve` は0個または1個の finite scheme を返す。有限 reachability、`forcedPure`、旧 coalescing を再利用しており、高速算法への置き換えは行っていない。正負の重みを持つ occurrence をそのまま伝播する例と、別 slot の pure sink への到達で拒否する例も kernel で検証した。

**まだ閉じない範囲**: protect/release/residual、operation-local 全称量化、Common type graph と head row の同時求解、request/handler の finite source generator、公開 `Core.infer`。head を格納できることを request の対応と数えない。

## 5. B4: finite role/method interface

### 5.1 既存の接点

`QualifiedInference.MethodDecl` の requirements と value は有限型構文である。ただし `MethodTable := Nat → MethodDecl` であり、実宣言一覧と未宣言名の失敗を検証する registry ではない。`Core.Qualified.Typing.method` は実際の role requirements を要求する独立判断だが、旧 required-field model に属する。

実 resolver は `Roles.Term` / `List Roles.Impl` 上にあり、`Roles.resolve`、`RoleConstraints.resolve_exact`、`RoleDictionaries.elaborate_success_iff`、`RoleVisibility` に停止・曖昧性・辞書・呼び出し側の可視性の証明がある。`RoleConstraints.resolvingTheory` は任意の `m.Ty → Roles.Term` を外から受け取るため、Common regular types の exact adapter を既に得たことにはならない。

`CommonFinite.Demand.role` は head を区別する観測であり、実 `impl` の選択や辞書の存在ではない。この観測を `Add` / `Display` 等の解決に読み替えない。

### 5.2 `common_role_registry_exact`〔未実装〕

**対象と量化**: 任意の有限 declaration/visible registry `D/V` と独立した well-formedness、実宣言に従って型・行が確定した任意の有限 goal description `g`。型引数の有限構文には nominal identity と regular graph の共有を保持し、実 source が生成する全確定 goal を覆う。

**結論**:

```text
resolveCommon D V g = resolved
  ↔ ActualRoleEvidence D V (interpretGoal D g)
```

ここで `ActualRoleEvidence` は、独立した実宣言の導出があり、spec の曖昧性条件に当たらないことを意味する。単なる辞書の存在は、複数候補のときまで受理してしまう。既存 `RoleConstraints.Resolves` の「導出と overlap 不在」の区別を保つ。

成功時は actual dictionary を生成し、noImpl と ambiguity も独立した仕様との iff にする。head matching と nested where のすべてに根の呼び出し側と同じ `V` を使う。Common の値を任意 decode で既存 `Roles.Term` に押し込む前提は採用しない。

`Common.Ty` の行葉は任意の `Occurrence → Prop` である。この semantic 値を受け取る Bool checker が自動的に実行可能になるとはしない。実行入力は有限の型・行構文と共有 slot、意味の theorem で量化するのは任意の Common assignment である。未確定 slot を持つ goal は次節の qualified constraints として扱い、上の確定 goal の theorem に無根拠に帰着しない。確定 goal の有限表現への到達と、意味を保った正規化も source solver 側に必要である。

既存 `Roles.WellFormed` の size/count による停止証明は有限な first-order term を対象にする。regular goal の展開に同じ measure をそのまま適用できるとは限らない。実際の有限 graph 表現について、宣言の減少条件が resolver の再帰を停止させることも不足補題に含める。有限個の declaration があることだけを、その証明としない。

associated type を持つ任意の解決済み goal、関連型名、共有 slot、既存 constraint store、任意の代入 `σ` に対して、解決が足す等式は普通の等式として、

```text
Models (store + [slot = selectedAssociatedType]) σ
  ↔ Models store σ ∧ σ(slot) ≈ selectedAssociatedType.eval σ
```

を満たす必要がある。先にあった bounds を捨てて associated slot を上書きしない。既存 `RoleConstraints.add_associated_exact` が ground term 層の接点になる。

### 5.3 `generate_common_qualified_finite_exact`〔未実装〕

**対象と量化**: 任意の検証済み有限 method/role declaration `D`、呼び出し側 registry `V`、任意の ambient assignment `ρ`、任意の symbolic/semantic environment `sΓ/Γ`、任意の対象式 `e`、任意の symbolic result `out`。

**前提と結論**: `EnvRel ρ sΓ Γ` の下で、

```text
Holds D V ρ (generateQualified D V sΓ e out)
  ↔ CommonQualifiedTyping D V Γ e (out.eval ρ)
```

を示す。`generateQualified` は有限構文を計算し、右辺の判断はその生成器と solver から独立に定義する。ambient assignment は任意であり、実宣言の qualifier 以外の意味条件を追加しない。

formula と scheme は method declaration ID、role goals、associated equations、ambient/generalized/weak slot の区別を保持する。`QualifiedGeneralization.lean` の `QualifiedInference.partition_exact`、`QualifiedInference.Interface.scheme_exact`、`QualifiedInference.qualified_let_exact` は既存の接点だが、与えられた interface の検査を、未解決 structural constraints からの principal interface 選択と同一視しない。

method selection は spec 6.4 の順序を保つ。既知 receiver は field 等を先にし、未知のまま SCC が確定した場合は role 候補を先にする。一度 freeze した method/field reference を呼び出し側の具体化で再解釈しない。`MethodResolution` は与えられた receiver snapshot の選択を証明しており、Common solver から SCC の安定状態を導出する theorem は別途必要。

その `common_method_freeze_exact` の対象は、任意の検証済み宣言と caller scope、任意の対象 SCC、任意の method site である。実推論終了時に計算する snapshot に対して、選ぶ reference が独立した仕様上の優先順位・曖昧性判断と iff で一致し、返した各 scheme の任意 parameter 代入でも同じ frozen reference を使用することを示す。任意の外部 snapshot が正しいという前提で source theorem を代用しない。

### 5.4 `solve_common_qualified_all_parameters`〔未実装〕

任意の検証済み実宣言環境 `D` と caller registry `V`、任意の対象閉式 `e`、任意の結果 `c` について、第1節の finite principal family と全 parameter soundness が必要である。さらに、その手前の実生成 qualified problem ごとに、任意の独立 rows/node values の Models を全回収し、返却した任意の scheme の任意の row/value parameters が Models を与えるという第3.4節の形が必要である。辞書の存在条件を row/value parameters の制限にしない。

現行の `QualifiedInference.Interface.scheme_exact` は、具体化について `∃ ι, Satisfies theory (requirements ι) ∧ ...` を保持する。この `Satisfies` を残したまま「任意 parameter が元の closed Typing を与える」とは言えない。有限 registry であることだけでも、許される全具体化が既存の無条件 structural scheme の有限和で表せるとはまだ従わない。その表現可能性と実辞書の合成を示す補題が不足している。

**採用方針**: source の `where` は finite qualified interface と実辞書の情報として保持する。定義を abstract dictionaries の下で検査する theorem と、呼び出し側で actual dictionary を生成して使う theorem を別々に立て、両者を公開判断へ接続する。`Satisfies` を parameter の隠れた証明欄へ移して solved と呼ぶ案は採用しない。辞書を仮定した判断を、元の辞書なしの closed Typing の代用にもしない。

weak slot は module 内の同じ ID として保持する。任意の module とその EOF の可視 registry に対し、型が確定した role goal の唯一性/曖昧性/不在を正確に検査し、未確定の weak slot を唯一の visible impl に default しない。`QualifiedGeneralization` の captured obligation と `RoleVisibility` / `RoleDictionaries` の caller scope を同じ推論結果へ接続する必要がある。

## 6. B5: invariant nominal と純粋な cast/construction

### 6.1 `common_nominal_invariant_exact`〔未実装〕

現在の `CommonFinite.Ty` / `CommonSyntax.Layer` に nominal constructor はない。

**採用方針**: nominal identity と共有 parameter references を持つ専用の finite layer を加える。structural variant への encoding は採用しない。constructor/tag identity は実宣言側に保持し、型引数を payload から無根拠に推測しない。parameter の種別（値型/行）も宣言側で保持する。

**対象と量化**: 任意の nominal ID `N/M`、任意の同じ宣言 kind に従う parameter tuples `a/b`。値型引数について必要な局所契約は、

```text
nominal N a ≤ nominal M b
  ↔ N = M ∧ 同じ arity ∧ ∀ i, a[i] ≈ b[i]
```

である。行引数も不変であり、その等価性は Common row の反対称性から literal equality に戻す。invariant slot の `(lower, upper)` bounds は最後に一つの actual argument を指す必要がある。片向き child edge だけを加えて covariance にする案は採用しない。

任意の旧 Common 型 `a/b` に対して、拡張 embedding は `a ≤ b ↔ embed a ≤ embed b` を満たし、旧 presence typing と solver の範囲も保存する。有限/regular observation、constructor inspector、shared graph saturation、全 parameter readback の各段階で nominal を扱う証明が必要になる。

### 6.2 `common_ground_cast_compatibility_exact`〔未実装〕

`Casts.Ty` は nominal を持つ別の ground syntax。`Casts.Compatibility` は ordinary compatibility とその checker を外から受け取り、nominal 引数の不変性を条件にする。`equalityCompatibility` は一つの例であり、Common subtype checker ではない。また、ground nominal args の比較は構文等号で、同値な表記の正規化は upstream obligation と明記されている。

有限/ground な対象文法を宣言し、その全ての `A/B` に対して、実際に構成する一つの `fitsCommonGround` と embedding の間に、

```text
fitsCommonGround.Rel A B
  ↔ CommonNominal.Subtype (embed A) (embed B)
```

を示す。任意の外部 `Casts.Compatibility` を Common subtype と同一視する主張ではない。対象 ground grammar を明示し、optional/default、regular graph、effectful arrow を未対応の ground grammar へ無条件に押し込まない。source 型の同値性を raw syntax equality と読み替えない。

既存 `Compatibility.nominalInvariant` は nominal 引数の raw syntax equality を要求する。このため、意味は等しいが構文の異なる引数を含む任意の `Casts.Ty` に、そのまま Common subtype を入れることはできない。既存 interface を使う ground adapter には、正規化した入力の像と、その正規化の exactness を明示する。全 regular Common 型までの拡張では、意味上の引数等価性を使う別の compatibility layer を用意し、旧 ground model をその特別な場合として保存する方針を採る。旧 theorem の nominalInvariant を弱める案や、未完成の全 interface 正規化を既にあるものとして使う案は採用しない。

### 6.3 `common_cast_plan_exact_and_pure`〔未実装〕

**対象と量化**: 任意の検証済み有限 cast registry `D`、境界で既知となる source/target types の任意の有限 description `A/B`。その意味を保つ型/行解釈を固定した上で、任意の環境 `Γ`、任意の source expression `e`、任意の original row `r`。単に §6.2 の ground adapter を作る段階と、全実生成 boundary description を扱う段階を区別する。

必要な契約は以下である。

1. `(∃ plan, synthesize D A B = some plan) ↔ Boundary D A B`。`Boundary` は探索から独立した判断であり、通常の compatibility が通る場合は keep とし、通らない場合だけ cast を探す。任意の `plan` について、返却したという事実から typed/pure の性質を導く。
2. `Γ ⊢ e : A ! r` と受理される boundary から、実際に elaboration した式の `Γ ⊢ elaborate(e) : B ! r` を導く。plan の型安全性や purity を入力仮定に残さず、検証済み cast declaration body から導く。
3. 任意の runtime environment と source computation について、境界挿入は request tree を保つ。arrow wrapper では、変換した引数で元の関数を呼ぶ計算との一致を示す。変換前の引数での呼び出しと同じ値になるとは主張しない。

`Casts.accepts_exact`、`ParametricCasts.search_exact`、`PureCasts.Plan.run_eq_pure`、`PureCasts.insert_eq_map` が既存の接点である。`PureCasts` は typed executable plan の実行を証明するが、ground boundary の成功からその plan を合成することまでは証明していない。

nominal 引数の内部へ cast を持ち上げない。必要な境界は、spec 6.5 のとおり元の nominal 構築位置に保持する。

### 6.4 `common_construction_sites_exact`〔未実装〕

**対象と量化**: 任意の検証済み finite resolved nominal declaration `D`、任意の対象 Core construction expression `e`、任意の symbolic/semantic environment `sΓ/Γ`、任意の assignment `ρ`、任意の symbolic result `out`。

**前提と結論**: `EnvRel ρ sΓ Γ` の下で、

```text
Holds D ρ (generateConstruction D sΓ e out)
  ↔ CommonConstructionTyping D Γ e (out.eval ρ)
```

を示す。右辺は source site expressions を再帰的に型付けする独立判断で、site の型付け自体を追加の入力仮定にしない。左辺の有限 constraints は全 invariant parameter occurrence、共有 weak slot、fixed field checks、pure cast boundaries を含む。その Models と全任意 original site assignments の関係を compiled graph 上で示す。

同じ parameter の複数 site は同じ slot を使う。planner の metadata に列挙された site だけが正しいと仮定するのでなく、実宣言と source 式から全 occurrence を収集し、その完全性を証明する。全 site の評価は書いた順で一度ずつ行い、隠れる field や結果で使われない site も落とさない。

既存 `NominalConstructions.finish_exact` は、与えられた original ground types と期待 parameter の下で planner を検査する。`Core.Construction.model` の結果は `Plan` であり、site source を `.free site` として保存するもので、Common 計算型の推論ではない。`NominalDataAssembly` は actual values に接続するが、typed source sites と `CastContract` を外から受け取る。それらを source typing から供給する橋が必要である。

任意の実生成 construction problem と任意の独立 rows/values について、第3.4節と同じ形式の全 instances exactness・全 parameter soundness を閉じる。さらに module 内の後続利用から weak parameter を解き、EOF で未確定なら元の要素型の合流を使う。`unionOf []` という planner descriptor があるだけで、空 list の型引数の解決と公開可能性を証明したことにはならない。

## 7. B1/B2 との依存と、先に進められる順番

| 作業 | B1/B2 から独立に進められる部分 | 統合時の依存 |
| --- | --- | --- |
| B3 row 基盤 | head solver は完了。scope embedding、signed row 演算、finite signature syntax | request の source rules と Common graph の同時求解 |
| B3 handler | finite quantifier scope と outer/local/inner の exactness | payload patterns/defaults/guards は B2、operation `where` は B4 |
| B4 role/method | finite declaration registry、Common goal representation、辞書と associated equations | union receiver cast は B5、effect-row method は B3、SCC の receiver snapshot は実 solver |
| B5 nominal/cast | invariant carrier、既存 ground cast との adapter、typed plan synthesis | construction source sites は B1 の統合判断、pattern elimination は B2 |
| B1 nil/cons/list data | nominal list declaration の有限表現は独立に設計可能 | invariant argument と deferred construction boundary が B5 に依存 |
| list spread | 既存 finite-list runtime view を保つ | 任意 `Fold` の辞書は B4、走査の effect は B3。停止する Fold だけに制限しない |

次の実装順を採る。

1. head row 基盤を既存 build/Audit に取り込み、公開 request 対応とは分けて記録する。
2. 有限 declaration syntax と解釈の exactness を用意し、signed row scope embedding と finite request generation を接続する。
3. 同時に、nominal carrier の保守拡張と Common role-goal representation を独立に進める。いずれも data/case の簡単な lowering で代用しない。
4. handler の全称局所型、partial pattern elaboration、実辞書、typed cast plan、construction sites を各独立判断に接続する。
5. 各段階で全 parameter soundness と principal/rejected iff を通してから、その constructor を公開 `Core.infer` の閉じた範囲に数える。

現在の structural `CommonData` bridge に `.nil` / `.cons` を加えるだけでは list は閉じない。list は nominal/invariant で、literal の要素に共有された weak parameter と構築位置の保留境界を持つためである。B2 の pattern を別の値述語上で検査できることも、任意 Common regular parameter への正確な elimination の代用にはならない。

spec 3 の E7（pipeline と catch）や spec 6 の K1（receiver のない role member の整合条件）は既存の未決として扱う。この記録の row/head、finite declaration、invariant carrier の作業ではそれらを決める必要はなく、新しい `notes/questions/` は追加しない。

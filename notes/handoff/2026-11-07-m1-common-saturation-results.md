# M1 共通モデル: 有限飽和、全解回収、公開入口

2026-11-07。`integration/m1-common` の継続作業。
設計契約は [前回復旧記録 §7](2026-11-07-m1-common-recovery-results.md#7-閉じていない補題) を変更しない。

## 1. 復旧時点と現在の範囲

依頼に記された `5c5969d68` より先の remote head `69535ea8ea6075f31bb2af7ef804b30d921c428c` を取得した。
まずその先頭そのものに対して `lake build --wfail` と `lake env lean --trust=0 Audit.lean` を実行し、
両方が終了コード 0 であることを確認した。baseline は 519 jobs、Audit は 45,801 declarations。
したがって、先頭を未完として巻き戻す必要はなかった。

残っていた detached 作業の証明を個別に読み、現在の branch へ取り込んだ。
`origin/yulang3` の `0530434f803be9ba4b9e47154a8d3a50372903db` を merge し、
ビルドと Audit を再確認した。`{..rest}` を record とする仕様もこの merge に含まれる。
その後の同じ branch への並行更新も、先頭を上書きせず取り込んだ。
変更の送信先は `integration/m1-common` だけで、`integration/types` と `yulang3` へは送信していない。

| 契約 | 現在の状態 |
| --- | --- |
| 7.1 symbolic rigid exactness | 既存の source/Core 版を維持。後続の実 worklist に接続 |
| 7.2 閉性・全 parameter soundness | 完了。有限 optional 境界を含む停止・全 rigid 分解・全 parameter の全 Models |
| 7.3 全 instance exactness | 完了。任意独立 rows と全 compiled values、行の等号・全 node の要求同値 |
| 7.4 公開入口 | 主型性、拒否 iff、unsupported 不出現、旧 instance の保存は完了。一般 source の旧 instance 反映が残る |
| 7.5 全 interface 標準形 | 未完。scalar 型族の任意 arity、正の constructor 型族、固定変数を保つ正負簡約、scalar 公開 interface 接続を追加 |

公開入口は `Core.infer` → `CommonSolvedSource` → `CommonBoundRefSolver.solveAll (compile atoms)`。
並行して作られた atom 入力版 `CommonBoundRefSolved` と `CommonPresenceSolvedSource` も保持した。
構文外を unsupported とする別入口は `Core.SyntaxGatedCommonInference.infer` として区別する。
両経路の theorem を削除・弱体化して一方に合わせたわけではない。

## 2. 記法と独立性

`Ty = Common.Ty`、`Row = Common.Row`、`S ≈ T = Common.Equivalent S T` とする。
型の比較は独立した要求意味の `Common.Subtype` であり、solver の成立や data 包含で定義し直していない。
`Comp.le` は型と行の両方の比較である。

実生成 clause `a` の入力 slot 数を `m = a.locals + 1`、元 compiled pool の node 数を `N` とする。
`rows : Fin m → Row` と `values : Fin N → Ty` は独立の任意割当てである。
`Models` は元 constructor 方程式、型比較辺、行制約の同時充足。

返却 scheme の行 parameters は通常の `Fin m → Row`。
型/再帰 parameters も通常の関数の組であり、実拡張 pool を `E` とすると
`(Fin m → Ty) × (Fin E.size → Ty)` である。
`Models`、`ResidualHolds`、support、solver 成功、閉性、fuel を parameter の型や条件に含めない。
source scheme はこれらと出力 ID を持つ有限構文からなる。

## 3. 7.1–7.2: 実 worklist の閉性と任意 parameter

### 3.1 維持した first pass の exactness

`CommonGeneratedRigidInspection.saturate_common_rigid_exact` と
`saturate_common_core_rigid_exact` は、任意の実生成 packed clause と独立 rows/values について、
元 constructor 方程式の下で rigid 比較が成立することと、計算済み有限 branch のどれかの
child/row/profile/presence 制約が成立することを同値にする。
具体化した型に inspector を呼んで scheme を後から選ぶ形ではない。

### 3.2 `CommonBoundRefAllParameters.saturation_closed`

任意の有限 pool、任意の初期 bound-reference 辺列、実 `run` が返した任意 state について、
全 rigid 比較の `Closed`、未処理比較がないこと、処理 trace 長が `(5N+3)²` 以下であることを示す。
`CommonBoundRefSolved.saturation_closed` は、任意 atom 列から初期辺を組み立てる入口でもこれを示し、
processed の重複がないことと trace/processed の同長も含む。

この有限 inventory は元 node と、代入前に列挙する required/rawOpt query および定数から作る。
optional node の追加、whole default の分解、lower/upper 伝播で発生する比較も同じ inventory に収まる。
未知 slot の profile を別々の自由値にせず、同じ共有 ID を optional pool の元 ID として保持する。

`CommonBoundRefWorklist.generated_run_models_exact` と `generated_core_run_models_exact` は、
任意 source/Core 式、任意実生成 clause、任意独立 rows/values に対し、**元 constructor Realizes の下で**、
元型比較列の成立 iff 実 run のいずれかの最終 branch の全辺・補助制約が成立、と示す。
この部品定理では元の明示行制約を別に扱う。最終 solver がそれも同時に解く。

`(5N+3)²` は各 branch の trace 長であり、返却 branch 数、scheme 数、総実行時間の多項式上限ではない。
`run` の再帰容量は inventory から決まり、未処理比較を残して容量が尽きないことを証明している。
caller が任意の fuel を渡す入口ではない。

### 3.3 `CommonBoundRefSolver.all_parameter_sound`

任意 atom 列 `atoms`、任意の `S ∈ solveAll (compile atoms)`、任意の行 parameters `rp`、
任意の型/再帰 parameters `vp : S.Parameters` について、

```text
(compile atoms).Models (S.instantiateRows rp) (S.instantiateValues rp vp)
```

を示す。この soundness 方向には生成文法の前提もない。
同じ契約を atom 入力版では `CommonBoundRefSolved.all_parameters_models` が与える。

最終 state の trace から有限分解の選択と child closure を回収し、有限観測 depth と source weight の
二重帰納で全比較を証明する。row/literal 条件は、実 run が row または true だけを残すことと、
元行・追加行の同時 row solver により内部で供給する。
`CommonBoundRefClosedSoundness.returned_solve_soundness` にある補助条件は最終 theorem には残らない。

## 4. 7.3: 全独立モデルと全自由 instance の一致

### `CommonBoundRefSolver.generated_models_exact` / `generated_core_models_exact`

任意 source/Core 式 `e`、その実 `normalise (principal [] e)` が返す任意 clause `a`、
任意の独立 `rows : Fin (a.locals+1) → Row`、任意の `values : Fin (compile a.pack).size → Ty` に対して、

```text
(compile a.pack).Models rows values
  ↔ ∃ S ∈ solveAll (compile a.pack), ∃ rp, ∃ vp : S.Parameters,
       S.instantiateRows rp = rows
       ∧ ∀ i, S.instantiateValues rp vp i ≈ values i
```

が成立する。量化する `i` は出力だけでなく、**元の全 compiled node**。
行は相互包含だけでなく関数として等しい。元の数値 node ID は pool 拡張の initial segment に保存する。
求解した全 parameter がモデルになる逆方向は §3.3 による。

atom 入力版の対応定理は `CommonBoundRefSolved.generated_solve_all_instances_exact` と
`generated_core_solve_all_instances_exact`。
generic な `compiled_models_exact` / `solve_all_instances_exact` は child/width/row の三つの構文前提を持つが、
上記 generated 版はそのすべてを clause membership から内部で供給する。
unknown slot に代入される型は regular/mask/default/負の arrow を含む任意の Common 型のままである。

`Compiled.origin` は元の有限構文だけを保持する。`Models` はこの metadata を読まない。
手書きの `Compiled` に無関係な origin を添えた入力の soundness には一般化しない。
今回の公開契約と source/Core の実経路は、必ず `compile atoms` を使う。

## 5. 7.4 の閉じた部分: 公開入口と保存

### 5.1 `Core.infer_principal` / `infer_instantiates`

任意の `e : Core.Required.Term`、任意の `c : Comp Common.model` に対して、

```text
Core.Typing (PresenceGeneration.CoreRules.model Common.model) [] e c
  ↔ ∃ S ∈ Core.infer e, ∃ p : S.Parameters,
       Comp.le Common.model (S.instantiate p) c
```

が成立する。support、成功、closed cache、fuel、残余条件を追加前提にしない。
さらに任意の `S ∈ Core.infer e` と**任意の** `p : S.Parameters` に対し、
同じ独立 Typing が結果 `S.instantiate p` について成立する。

source の任意閉式については `CommonSolvedSource.source_principal` / `source_instantiates`、
Core の有限 scheme 列については `core_principal` / `core_instantiates` が対応する。
入口は実 generate → normalise → pack → compile → solveAll の計算である。

### 5.2 `Core.infer_rejected_iff` / `infer_ne_unsupported`

任意の `e : Core.Required.Term` について、

```text
Core.infer e = .rejected
  ↔ ¬ ∃ c, Core.Typing (PresenceGeneration.CoreRules.model Common.model) [] e c
Core.infer e ≠ .unsupported
```

を示す。対象断片はもちろん、上記 presence 判断に規則がない構文も空 scheme 列から rejected になる。
他の effect/qualified/case モデルの型付け不能を意味するものではない。
別の syntax-gated 入口は構文外を unsupported とし、その定理は別 namespace に保持する。

### 5.3 `CommonSolvedLegacyPreservation.legacy_core_parameters`

任意の旧 supported source `e`、任意の旧結果 `c`、
`(SourcePrincipalInference.infer e).Instance Common.rowAlgebra c` を前提として、

```text
∃ S ∈ Core.infer (Core.Required.embed e), ∃ p : S.Parameters,
  (S.instantiate p).value ≈ Common.embedOld c.value
  ∧ (S.instantiate p).row = c.row
```

を示す。`legacy_instances_preserved` はこの回収を実公開入口の `Instance` に接続する。
旧 Core 入口を前提にする版は `legacy_core_entry_parameters` / `legacy_core_entry_preserved`。
これらは保存方向であり、逆向きの反映を仮定していない。

## 6. 7.4 の反映に追加した部品

### 6.1 任意旧境界・共有 flow

`CommonLegacyReflection.fixed_bounds_models_exact` / `fixed_bounds_output_exact` は、任意 slot 数 `n`、
任意境界 ID 型 `B`、任意 `evaluate : B → OldTy`、任意有限 lower/upper/check/flow 問題について、
任意 Common witness の存在と、一つの共有旧 witness の存在が同値であることを示す。
後者はさらに任意の出力 slot と任意の旧 regular target への上限比較を保持する。
境界型も Common witness も finite/scalar に制限しない。

`pair_upper_reflected` / `pair_lower_reflected`、`variant_upper_reflected` / `variant_lower_reflected`、
`arrow_upper_reflected` / `arrow_lower_reflected` は、任意 Common child と固定旧構成子境界の比較を反映する。
pair/tag の上側比較には旧 payload の有限 test 所属が必要。arrow の上側には旧 result の所属だけ、
下側には旧 input の所属だけが必要で、四つの行は任意のまま同じ値を保持する。

証明用の `envelope` は非計算的な意味的補間であり、実 infer や canonicalizer に組み込んでいない。
`envelope_does_not_preserve_pair_equation` は、tests が旧 top だけの場合、任意 Common pair の親と子へ
独立に envelope を適用すると pair 方程式を保たないことを示す。
決定46自体の反例ではなく、この証明方法の反例である。

### 6.2 空 record と実生成 clause の新旧対応

`CommonLegacyEmptyReflection.exact_empty_upper_old_iff` は、任意旧 regular target に対し、
exactEmpty がその embedding 以下 iff width がその embedding 以下、と示す。
任意旧結果と行について `empty_record_typing_exact` と `empty_record_legacy_instances_reflected` が反映を与える。
exactEmpty と width 自体を要求同値にしたわけではない。

`CommonLegacyGenerationTranslation.legacy_generated_clause_exact` は、任意旧 supported source e、
任意実生成 presence clause a について、`translateClause a` が実際の旧 generator の clause であり、
local 数・ID・row term・pack が保存されることを示す。
任意の**一つの共有旧割当て**で、新 atom 列の embedding 後の充足と旧 contextual atom 列の充足が同値。
変換成功は生成から証明し、公開前提にしない。

`CommonLegacyEmbeddedWitnesses.embedded_witnesses_iff_typing` は、任意 required-only source e と任意旧結果 c について、
実 presence clause と、出力が c に等しい共有旧 computation 割当てが存在すること iff 旧 contextual Typing、を示す。
`contextual_typing_preserved` は同じ required-only 前提で旧 contextual Typing を Common Typing へ保存する。
この二定理には旧 solver の supported 前提は不要。

## 7. 閉じていない補題

### 7.1–7.3

前回復旧記録の実生成 clause に関する契約は閉じた。
任意手書き atom 文法への completeness、分岐総数の多項式上限は、この契約に追加しない。

### 7.4 `legacy_instances_reflected` と共有旧 witness

必要な公開 statement は変えない。任意旧 supported source e・任意旧結果 c について、

```text
(Core.infer (Core.Required.embed e)).Instance (Common.embedComp c)
  → ∃ old,
      (SourcePrincipalInference.infer e).Instance Common.rowAlgebra old
      ∧ Common.embedOld c.value ≈ Common.embedOld old.value
      ∧ c.row = old.row
```

が未証明である。target を任意の新 exact/default 型へ拡大しない。

実生成 clause 列を `C(e)` と書くと、必要な意味的 witness 回収を次の形に絞れる。
任意旧 supported e、任意旧 computation c に対し、

```text
(∃ a ∈ C(e), ∃ v : Fin (a.locals+1) → Comp Common.model,
   v(last) = Common.embedComp c ∧ All Common.model v a.pack)
  →
(∃ b ∈ C(e), ∃ w : Fin (b.locals+1) → Comp legacyModel,
   w(last) = c ∧ All Common.model (CommonLegacyTyping.assignment w) b.pack)
```

左の Common witness は任意。右では同じ ID を一つの旧割当てが共有する。
元と同じ clause を選ぶことや、全内部 row を元 witness と等しくすることは要求しない。
それらを追加した graph interpolation は十分な強い補題だが、決定46の最小契約と取り違えない。
また、全 compiled rigid node を旧型へ写す要求も置かない。exactEmpty node は Common で再評価する。

この回収から先は、実 clause translation、旧 contextual typing exactness、
`contextual_typing_legacy_reflected` により、指定された結果行と要求同値な旧 instance へ接続できる。
不足は共有・負位置・構成子方程式を同時に保つ witness の存在証明である。
仕様の未決定、旧 solver の成功を前提に置く代案、独立 envelope の方程式保存で代用しない。

### 7.5 `public_interface_canonical_exact`

任意の有限 public interface I/J について、既存の公開 instance 意味における仕様上の等価性 iff
同じ計算可能な canonical encoding、という契約が未完である。
同数 parameter の全単射による α 同値で等価性を定義し直さない。

既存 Form の範囲だけでも、任意固定 slot 数 k、任意一般化 slot 数 n/m、任意の Form I/J について、
正負に共有された一般化変数を制限せず、全 rows・全固定割当て・全 target の subtype-instance 集合一致を
有限 code 一致へ完全に落とす定理が残る。`Positive I` / `Positive J` や再parameter化候補の存在を
前提に追加して、この残契約の代用にはしない。

全 public interface には、さらに一般 record/default/mask、有限の行式、regular graph、nominal identity、
role 義務と evidence、weak/captured の表示情報を同時に扱う有限構文と意味の接続が必要。
実 `Core.infer` の family から export・canonical encoding・display へ至る全経路も未完。
具体 `Common.Row = Occurrence → Prop` 全体を有限文字列に符号化する課題へすり替えず、有限 symbolic interface を対象とする。
全体の決定不能を証明したとは主張しない。

## 8. 7.5 で閉じた完全な部分言語

`CommonCanonicalIntervals.canonicalEncoding_exact` は、任意固定 slot 数 k、独立に異なる一般化 slot 数 n/m、
任意 scalar union/intersection 式 I/J について、全固定 Common 割当て・全 Common target に対する
要求同値な instance の存在の一致 iff 同じ二端点 code、と示す。
`instances_interval` は exact instances が全一般化 slot への同時 bottom/top 代入の閉区間と一致することを示す。
subtype で広げる instance 判断については `subtypeCanonicalEncoding_exact` が下端だけの完全 code を与える。

`CommonCanonicalPositive.canonicalEncoding_exact` は、任意 k/n/m、任意二つの Form I/J で
全一般化出現が正であるという構文条件の下、全 rows・全固定 Common 割当て・全 target の subtype-instance 一致 iff
同じ lower Form の完全 code、と示す。pair/required/variant/arrow result の共有を許し、
arrow domain は固定 slot だけを使う。固定 slot は正負に共有してよい。行 ID を変えない。

`CommonCanonicalPolarity.simplify_instances_exact` / `normalize_instances_exact` は、任意 Form・任意 frozen 指定・
任意固定割当て・任意 rows・任意 target で、非 frozen の正だけの変数を bottom、負だけの変数を top にし、
正負共有と frozen の ID を保持する一回の簡約が、subtype-instance 集合を保存・反映することを示す。
全 interface の canonical form、一般の再parameter化の完全性、固定点・冪等性の主張ではない。
`CommonCanonicalPolarityBoundary.normalize_not_idempotent` は、`a → (a & bottom)` が一回で
`a → bottom`、二回で `top → bottom` となる具体的な非冪等性も証明する。

`CommonCanonicalScalarExports.interface_canonicalEncoding_exact` は、任意 weak slot 数 k、任意 n/m、
任意 scalar 式二つについて、任意 role theory・任意 ambient computation 割当て・任意 target の
実 `QualifiedInference.Interface.scheme.Holds` の同値 iff 有限 code 一致、と示す。
対象は qualifier が空の scalar interface。role 義務付きの変数消去まで正当化しない。

`CommonCanonicalObstructions` は、同 arity・全 slot 使用の union と intersection が同じ exact family でも非 α であること、
共有 pair の exact image が単純な区間ではないこと、arrow の正負共有を分割できないこと、
負位置へ bottom 消去を適用できないこと、固定 slot を一般化し直せないことを kernel で示す。
一方、固定変数を正負に共有した constructor tree で正の一般化変数だけを 2 個から 0 個へ消す正例も証明する。

## 9. 検証

必須 gate は統合 tree で繰り返し実行した。コマンドは冒頭 README と同じ二つである。
Lean 4.35.0、Lean/Std の既存依存を用いた。
`sorry`、追加公理、`native_decide` は追加していない。有限具体例は kernel の `decide +kernel` で検証した。
監査は新規の主要 theorem を `Audit.lean` に登録し、全 Yulang declaration の allowlist 検査も実行する。

最終統合 gate は両方とも終了コード 0。build は 554 jobs、allowlist は 47,115 declarations。

```text
$ cd lean
$ lake build --wfail
✔ [552/554] Built Yulang.CommonCanonicalPolarityBoundary (859ms)
✔ [553/554] Built Yulang (571ms)
Build completed successfully (554 jobs).

$ lake env lean --trust=0 Audit.lean
Axiom allowlist passed for 47115 declarations from Yulang modules
...
'Yulang.CommonCanonicalPolarityBoundary.first_pass_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonCanonicalPolarityBoundary.second_pass_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonCanonicalPolarityBoundary.successive_passes_different' depends on axioms: [propext]
'Yulang.CommonCanonicalPolarityBoundary.normalize_not_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

上の省略記号より後は Audit の実際の末尾である。allowlist の位置だけを併記した。
最終確認時の `origin/yulang3` は上記 `0530434f8` のままで、統合済みである。

## 10. 新しい仕様の問い

`notes/questions/` への追加は **0 件**。
残っているのは内部の witness 補間と interface の証明・実装接続であり、
ユーザーに見える Yulang コードで新たな選択を求める未決定事項は見つからなかった。

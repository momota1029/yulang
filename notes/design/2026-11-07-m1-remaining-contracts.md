# 共通 presence carrier と全 source の M1 残契約

Status: Draft — implementation contracts, no new language decisions.

Date: 2026-11-07

Scope: `integration/m1-solver` で未実装の共通モデル・求解・source 接続。

このメモは設計時点の残契約を保持する。`integration/m1-common` で証明済みとなった部分と、現在も
開いている補題は [初回の実装結果](../handoff/2026-11-07-m1-common-results.md) と
[復旧後の実装結果](../handoff/2026-11-07-m1-common-recovery-results.md) を参照する。
下記契約の量化・前提を、実装済みの限定断片に合わせて縮小しない。

このメモの code block は **未実装契約の Lean 風型**であり、Lean に追加した declaration ではない。`Common`、`PresenceCompiler`、`PresenceSolved` は将来の実装を区別する仮名である。要求された定理を structure の law field や Instance の定義へ埋め込むことを完成とは数えない。

`Core.PresenceGeneration.Model` は演算の interface だけである。`PresenceOpenTailSignature.model finite` はその任意の既存解釈 finite を regular 化する表現変換であり、finite の意図した意味や具体的存在を証明していない。`Core.RequiredInference.infer` と `Core.PresenceInference.infer` は別入口のまま。統合 `Core.infer` はこの snapshot では存在しない。

`ContextualBranchInstances` と `ContextualRegularInference` により、既存 rigid grammar の全入力分岐・全独立解の具体 regular block 回収が閉じた。`ContextualTypeConstraintInference`、`ContextualJointConstraintInference`、`CoreContextualSourceInference` は、実 fixed-row/joint/source 入口の新 Models/Instance exactness と拒否完全性を接続する。旧 supported source の新独立 Typing への完全性と、RecordFree の support 前提を要しない主型性も完了した。

残るのは exact/default/open-tail を含む共通 presence carrier と全 source への接続である。上の rigid grammar に exactEmpty/default/mask-tail constructor が存在するわけではない。

## 1. 共通 carrier と負位置を含む要求意味

必要な実装物は、関数、両行、record の width/exact/presence/default、同深さ tail、free type parameter を同じ carrier に含む具体的な有限/regular 構文と、その独立した要求解釈である。`Common.model` の subTy はその要求による順序で定義する。

```lean
-- Common.Ty / Common.Demand / Common.Environment / Common.AcceptAt は
-- solver・Typing・「この定理が成り立つ」という law field に依存しない
-- 独立した構文・再帰的解釈として先に実装する。

theorem common_subtype_exact (S T : Common.Ty) :
  Common.model.subTy S T ↔
    ∀ depth rank env demand,
      Common.AcceptAt depth rank env T demand →
      Common.AcceptAt depth rank env S demand

theorem contextual_embedding_exact
    (S T : RegularInferenceModel.Ty Common.Row) :
  Common.model.subTy (Common.embedOld S) (Common.embedOld T) ↔
    ProducerContextualRegular.ProducerLe
      (RegularInferenceModel.graph Common.Row) Common.rowLe S T
```

上の第1式が subTy の定義展開になるだけでは十分ではない。AcceptAt が demand variable の任意型割当を保ち、arrow の負位置にも同じ環境を渡す具体意味であること、第2式の両方向、各constructorの分解/合同性を証明する必要がある。要求変数を有限 rigid test 列に戻してはいけない。

arrow の残る共通-carrier契約は、既に証明した旧 regular carrier 上の arrow iff の移送である。

```lean
theorem common_arrow_iff (A A' B B' : Common.Ty)
    (inRow inRow' outRow outRow' : Common.Row) :
  Common.model.subTy (Common.arrow A inRow B outRow)
                    (Common.arrow A' inRow' B' outRow') ↔
    Common.model.subTy A' A ∧ Common.rowLe inRow' inRow ∧
    Common.model.subTy B B' ∧ Common.rowLe outRow outRow'
```

row preorder laws は Common の具体 row 定義から別途証明する。引数/結果が var、mask、regular graph から得られた型でも除外しない。

## 2. exactEmpty / required / whole recordDefault

既存 `PresenceLayerExpressiveness.no_exactEmpty_layer` は、任意 payload 割当・任意 mask・任意有限 Layer でも exact empty を表現できないことを証明している。旧 Layer の組合せを増やすだけではこの契約を閉じられない。

```lean
theorem exactEmpty_below_width :
  Common.model.subTy Common.exactEmpty Common.emptyRecord

theorem required_as_width_tail (label : Nat) (payload : Common.Ty) :
  Common.record label payload Common.emptyRecord = Common.required label payload

-- equality を採用しない表現なら、要求同値版を証明し、
-- LegacyPreservation の呼出側を必要な congruence に沿って拡張する。
```

`exactEmpty ≠ emptyRecord` の構文等号だけでは、意味的に異なることを証明したことにはならない。独立した record readout か exact/closed demand による識別も必要となる。

whole-default は1個の field の union に縮めない。次は **独立した runtime readout** に課す正確な契約であり、producer subtype を set inclusion と定義する契約ではない。

```lean
theorem exactEmpty_data_exact (v : SourceDataRuntime.Value) :
  Common.DataReadout Common.exactEmpty v ↔ v = .record []

theorem width_data_exact (v : SourceDataRuntime.Value) :
  Common.DataReadout Common.emptyRecord v ↔
    ∃ fields, v = .record fields

theorem default_data_image (label : Nat) (source fallback : Common.Ty)
    (result : SourceDataRuntime.Value) :
  Common.DataReadout (Common.recordDefault label source fallback) result ↔
    ∃ fields value,
      Common.DataReadout source (.record fields) ∧
      Common.DataReadout fallback value ∧
      result = .record (SourceDataRuntime.Fields.insertDefault label value fields)
```

最後の runtime 操作は既存の `SourceDataRuntime.Fields.insertDefault` であり、`PresenceDataTypes.recordDefault` と同じ画像を要求する。fallback の存在を present-source 枝でも残す。strict 評価の fallback を無視する image law は既存 `PresenceConstructorDefaultBoundary` の反例と矛盾する。

重要な境界: DataReadout が要求同値に沿って等しくなるとは仮定しない。`PresenceProducerDataBoundary.no_exact_data_factorization` は、要求同値をcarrierの等号へ潰しながら strict data 意味も正確に因数分解する設計を否定する。arrow の producer 意味を空の DataReadout で代用しない。上の data law と独立に、関数/行を観測する AcceptAt の具体定義と分解法則が必要。

solver が必要とする whole-default 契約はさらに、全 source/fallback 型について、新しい要求意味から有限 branch obligations への完全分解である。元要求を結論側に残す tautological obligation にしてはいけない。

```lean
theorem default_inspect_exact (label : Nat) (source fallback target : Common.Ty) :
  Common.model.subTy (Common.recordDefault label source fallback) target ↔
    ∃ branch ∈ PresenceCompiler.inspectDefault label source fallback target,
      PresenceCompiler.IndependentObligationsHold branch
```

`inspectDefault` と IndependentObligationsHold は独立した実算法/意味として定義し、obligations の文法は求解可能な子比較・row比較・presence/exact情報を明示する。元の未分解 default 比較を再包装しただけの branch はこの契約の完成ではない。

## 3. 自由 mask family / 同深さ tail の共通モデル接続

`PresenceTailElimination.solve_mask` と `PresenceTailRegular.solved_instances_exact` は正の data-demand 方程式について成立する。共通producer順序への移送は未証明。

```lean
theorem common_mask_composition (T : Common.Ty) (H K : List Nat) :
  Common.Equivalent (Common.mask K (Common.mask H T))
                    (Common.mask (H ++ K) T)

theorem common_mask_parameter (parameter : Common.Ty) (H : List Nat)
    (depth rank : Nat) (env : Common.Environment) (demand : Common.Demand) :
  Common.AcceptAt depth rank env (Common.mask H parameter) demand ↔
    Common.MaskedAcceptAt depth rank env H parameter demand
```

MaskedAcceptAt は全 root/payload で許可された demand-mask 文法の独立意味であり、左辺の別名として作らない。外側 field 要求だけを除くこと、payload の mask を外側へ勝手に移さないことを保持する。

必要な全入力 compiler bridge は、任意 finite graph g、任意独立共通型/行割当 ρ について、元 graph の constructor equations/constraints と、実際に計算した branch/tail graph のモデルを保存反映すること。mask と同じ未知数の共有IDを両方向で保つ。

```lean
theorem presence_compile_exact (g : PresenceInput n)
    (ρ : Fin n → Core.PresenceGeneration.Comp Common.model) :
  PresenceInput.Models Common.model g ρ ↔
    ∃ branch ∈ PresenceCompiler.compile g,
      ∃ σ, branch.IndependentModels σ ∧
        ∀ i, Common.CompEquivalent (branch.readback σ i) (ρ i)
```

ここで compile の成功は前提にしない。受理 branch の自由 parameter に残余 Models を課さず、任意 parameter でモデルを得ることと任意独立解の回収を別々に証明する。

## 4. 行 solver との simultaneous 接続

既存 `RowFlowSchemes.Algebra` は empty/join と preorder、empty_le、join_le_iff を持つ。solver は右辺 var/empty を扱い、右辺 join を unsupported としている。新 contextual constructor inspector が row requirements を生成した後にも、この support 境界を source 全体から閉じる必要がある。

```lean
theorem presence_joint_instances_exact
    (problem : PresenceProblem n)
    (ρ : Fin n → Core.PresenceGeneration.Comp Common.model) :
  problem.Models Common.model ρ ↔
    ∃ scheme ∈ PresenceSolved.solve problem,
      ∃ rowParameters : Fin scheme.rowParameters → Common.Row,
      ∃ valueParameters : Fin scheme.valueParameters → Common.Ty,
        ∀ i, Common.CompEquivalent
          (scheme.instantiate rowParameters valueParameters i) (ρ i)
```

この定理に solver成功、解、Closed、supported checker、fuel を前提として足さない。宣言した全入力文法で support が必要なら、その文法の構文的述語だけを公開し、対象 source のすべての生成入力がその述語を満たす補題を別途証明する。

```lean
theorem generated_rows_supported (e : Inference.Expr)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise
      (Core.PresenceGeneration.principal ([] : SchemeEnv Empty) e)) :
  PresenceSolved.inputSupported clause.pack = true
```

record/default を含む全sourceでの上の補題が必要。単に旧 `recordFree_supported` を引用しない。自由rowを空にdefaultしない。row identityを等号で回収する旧joint証明を再利用する場合、具体rowのantisymmetryか、全value型内のrow equivalent置換の合同性も証明する。

## 5. 生成 formula、束縛、source lowering

すでに閉じた定理:

```lean
Core.PresenceGeneration.generate_models_iff_typing
  (m : Model) (e : Inference.Expr)
  (sΓ : SchemeEnv α) (Γ : List (Binding m)) (ρ : α → Comp m)
  (out : CompTerm α) (henv : EnvRel m ρ sΓ Γ) :
    (generate sΓ e out).Holds m ρ ↔ Typing m Γ e (out.eval m ρ)
```

このmodel-parametric定理は新carrierを選んでも使える。ただし残るのは、existential formula を消去した solved family と実 infer の接続。

```lean
theorem presence_normalise_exact (α : Type) (formula : Formula α)
    (ρ : α → Comp Common.model) :
  formula.Holds Common.model ρ ↔
    ∃ clause ∈ PresenceNormalForm.normalise formula,
      ∃ locals : Fin clause.locals → Comp Common.model,
        clause.Holds Common.model ρ locals
```

これは実際の `Core.PresenceGeneration.Formula`（旧 `Inference.Formula`とは別型）上で示す。`.existsSlot` の局所値/行をともに保持し、捕捉されたslotをgeneralizeしない。value-letのpoly/mono両枝とstrict defaultのfallbackを落とさない。

```lean
theorem presence_generated_solved_exact (e : Inference.Expr)
    (c : Comp Common.model) :
  (Core.PresenceGeneration.principal ([] : SchemeEnv Empty) e).Holds
      Common.model (Inference.extend Empty.elim c) ↔
    ∃ scheme ∈ PresenceSolved.inferSource e,
      ∃ rows : Fin scheme.rowParameters → Common.Row,
      ∃ values : Fin scheme.valueParameters → Common.Ty,
        Comp.le Common.model (scheme.instantiateOutput rows values) c
```

左辺が `Instance` の定義になっているだけでは不足。右辺の scheme は有限の構文データで、instantiate は計算可能な代入/graph closure。`Typing` や未解消 `Formula.Holds` をparameterに隠さない。

## 6. 最終公開 theorem と旧入口の保存/反映

```lean
theorem core_infer_principal (e : Core.Required.Term)
    (fragment : Core.InferenceSyntax.supported e = true)
    (c : Comp Common.model) :
  Core.Typing (Core.PresenceGeneration.CoreRules.model Common.model) [] e c ↔
    ∃ scheme ∈ (Core.infer e).schemes,
      ∃ rows : Fin scheme.rowParameters → Common.Row,
      ∃ values : Fin scheme.valueParameters → Common.Ty,
        Comp.le Common.model (scheme.instantiateOutput rows values) c

theorem core_infer_rejected_iff (e : Core.Required.Term)
    (fragment : Core.InferenceSyntax.supported e = true) :
  (Core.infer e).status = .rejected ↔
    ¬ ∃ c, Core.Typing (Core.PresenceGeneration.CoreRules.model Common.model) [] e c

theorem core_infer_not_unsupported (e : Core.Required.Term)
    (fragment : Core.InferenceSyntax.supported e = true) :
  (Core.infer e).status ≠ .unsupported
```

このsupportは元ASTに対する純粋な構文検査で、lambda/app/branch/unannotated let/pair/variant/record/default/fieldを含む。推論結果の成功をfragmentの定義に入れない。

旧入口との決定46の最終契約:

```lean
theorem legacy_instances_preserved (e : Inference.Expr)
    (supported : SourcePrincipalInference.supported e = true)
    (old : Inference.Comp (SourcePrincipalInference.model Common.rowAlgebra)) :
  (SourcePrincipalInference.infer e).Instance Common.rowAlgebra old →
    (Core.infer (Core.Required.embed e)).Instance (Common.embedComp old)

theorem legacy_instances_reflected (e : Inference.Expr)
    (supported : SourcePrincipalInference.supported e = true)
    (target : Inference.Comp (SourcePrincipalInference.model Common.rowAlgebra)) :
  (Core.infer (Core.Required.embed e)).Instance (Common.embedComp target) →
    ∃ old : Inference.Comp (SourcePrincipalInference.model Common.rowAlgebra),
      (SourcePrincipalInference.infer e).Instance Common.rowAlgebra old ∧
      Common.Equivalent (Common.embedOld target.1) (Common.embedOld old.1) ∧
      target.2 = old.2
```

対象は元の依頼と model-contracts.md の「任意の旧結果型への embedding」の範囲である。任意の新しい結果型に強めない。たとえば新 exactEmpty を結果として許す旧空record式についてまで旧width型instanceへの同値反映を要求すると、新たなabsence/exact観測との別の整合性問題を作る。この監査ではその追加義務を導入しない。

最後の row 等号は row carrier を共用する設計に対応する。異なる carrierなら明示したrow embeddingを挟む。今回の `Core.ProducerContextualInstances` は旧schemeの再解釈で同値を除く反映を示しているが、新presence入口から得た独立typing/instanceの反映と同一ではない。

新しいユーザー問いは追加しない。上記は実装/証明義務の分解であり、仕様の変更案ではない。

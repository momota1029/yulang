# Cycle130: 全89定理の量化と主張

一般B4Bridges V3: 未充填12/12。unrestricted evidenceNodeの阻害と、モデルごとの正しい条件付き辞書意味を分ける。各型は最終Metadata強化後のLean --trust=0出力。新公理なし。

## Yulang.GeneralDictionaryRecursiveEvidence.evidence_iff_payload

側: **補助**。任意の registry・context・モデル・root・payload について、具体的な source Evidence と、同じモデルの Instance を各節点に持つ PayloadEvidence が同値である。

```lean
@Yulang.GeneralDictionaryRecursiveEvidence.evidence_iff_payload : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (model : Yulang.GeneralNominalCommonBridge.Assignment) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (payload : Yulang.GeneralDictionaryReadback.Payload),
  Iff (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence roles registry context model root payload)
    (@Yulang.GeneralDictionaryReadback.PayloadEvidence roles
      (@Yulang.GeneralDictionaryRecursiveEvidence.Instance roles registry context model) root payload)
```

## Yulang.GeneralDictionaryRecursiveEvidence.instance_models

側: **健全性**。任意の registry・context・モデル・root・key・子列について、そのモデルで Instance が成り立つなら、同じモデルは元の context.state の Models を満たす。

```lean
@Yulang.GeneralDictionaryRecursiveEvidence.instance_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (model : Yulang.GeneralNominalCommonBridge.Assignment) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (key : Nat) (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  @Yulang.GeneralDictionaryRecursiveEvidence.Instance roles registry context model root key children →
    Yulang.GeneralNominalState.Models context.state model
```

## Yulang.GeneralDictionaryRecursiveEvidence.survivor_instance_exists

側: **健全性**。任意の registry・context・root・key・子列について、再帰的 Survivor なら、その一節点の Instance を満たすモデルが少なくとも一つ存在する。全元モデルでの成立や、辞書全体で共有できるモデルの存在は結論に含まない。

```lean
@Yulang.GeneralDictionaryRecursiveEvidence.survivor_instance_exists : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
  (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  @Yulang.GeneralNominalRecursiveCandidates.Survivor roles registry context root key children →
    @Exists.{1} Yulang.GeneralNominalCommonBridge.Assignment fun model =>
      @Yulang.GeneralDictionaryRecursiveEvidence.Instance roles registry context model root key children
```

## Yulang.GeneralDictionaryRecursiveEvidence.survivor_instance_of_branch

側: **健全性**。任意の検査済み registry・context・指定モデル・Survivor について、同じ key の可視かつ検査済み宣言、実際に取得された bounds、その指定モデルでの BranchModels があれば、同じ root・key・子列の Instance が成立する。

```lean
@Yulang.GeneralDictionaryRecursiveEvidence.survivor_instance_of_branch : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry),
  Yulang.GeneralDeclarations.Checked registry →
    ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
      (model : Yulang.GeneralNominalCommonBridge.Assignment) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
      (key : Nat) (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      @Yulang.GeneralNominalRecursiveCandidates.Survivor roles registry context root key children →
        ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
          @Membership.mem.{0, 0} Yulang.GeneralDeclarations.Declaration
              (List.{0} Yulang.GeneralDeclarations.Declaration)
              (@List.instMembership.{0} Yulang.GeneralDeclarations.Declaration) registry.declarations declaration →
            ∀ (valid : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration),
              @Eq.{1} Nat declaration.id key →
                ∀ (bounds : List.{0} (Yulang.GeneralNominalInspection.Bounds context.state)),
                  @Eq.{1} (Option.{0} (List.{0} (Yulang.GeneralNominalInspection.Bounds context.state)))
                      (@Yulang.GeneralNominalRecursiveCandidates.arguments roles context root)
                      (@some.{0} (List.{0} (Yulang.GeneralNominalInspection.Bounds context.state)) bounds) →
                    @Yulang.GeneralNominalRecursiveCandidates.BranchModels roles registry context root declaration valid
                        bounds model →
                      @Yulang.GeneralDictionaryRecursiveEvidence.Instance roles registry context model root key children
```

## Yulang.GeneralDictionaryRecursiveEvidence.evidence_node

側: **健全性**。任意の registry・context・指定モデル・root・key・子列・子辞書列について、親の Instance と、同じモデルで全子を対応順に証明する All₂ Evidence があれば、親の node 辞書に Evidence が成立する。

```lean
@Yulang.GeneralDictionaryRecursiveEvidence.evidence_node : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (model : Yulang.GeneralNominalCommonBridge.Assignment) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (key : Nat) (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles))
  (dictionaries : List.{0} Yulang.GeneralDictionaryReadback.Payload),
  @Yulang.GeneralDictionaryRecursiveEvidence.Instance roles registry context model root key children →
    @Yulang.CommonRoleOutermostResolver.All₂.{0, 0} (Yulang.GeneralSourceDictionaries.Occurrence roles)
        Yulang.GeneralDictionaryReadback.Payload
        (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence roles registry context model) children dictionaries →
      @Yulang.GeneralDictionaryRecursiveEvidence.Evidence roles registry context model root
        (Yulang.CommonRoleOutermostResolver.Dictionary.node key dictionaries)
```

## Yulang.GeneralDictionaryRecursiveEvidence.evidence_node_of_branch

側: **健全性**。任意の検査済み registry・context・指定モデル・Survivor について、対応する可視宣言の検査・key 一致・bounds 取得・そのモデルでの BranchModels と、全子の同一モデルでの Evidence を前提に、親辞書の Evidence を構成できる。

```lean
@Yulang.GeneralDictionaryRecursiveEvidence.evidence_node_of_branch : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry),
  Yulang.GeneralDeclarations.Checked registry →
    ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
      (model : Yulang.GeneralNominalCommonBridge.Assignment) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
      (key : Nat) (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles))
      (dictionaries : List.{0} Yulang.GeneralDictionaryReadback.Payload),
      @Yulang.GeneralNominalRecursiveCandidates.Survivor roles registry context root key children →
        ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
          @Membership.mem.{0, 0} Yulang.GeneralDeclarations.Declaration
              (List.{0} Yulang.GeneralDeclarations.Declaration)
              (@List.instMembership.{0} Yulang.GeneralDeclarations.Declaration) registry.declarations declaration →
            ∀ (valid : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration),
              @Eq.{1} Nat declaration.id key →
                ∀ (bounds : List.{0} (Yulang.GeneralNominalInspection.Bounds context.state)),
                  @Eq.{1} (Option.{0} (List.{0} (Yulang.GeneralNominalInspection.Bounds context.state)))
                      (@Yulang.GeneralNominalRecursiveCandidates.arguments roles context root)
                      (@some.{0} (List.{0} (Yulang.GeneralNominalInspection.Bounds context.state)) bounds) →
                    @Yulang.GeneralNominalRecursiveCandidates.BranchModels roles registry context root declaration valid
                        bounds model →
                      @Yulang.CommonRoleOutermostResolver.All₂.{0, 0}
                          (Yulang.GeneralSourceDictionaries.Occurrence roles) Yulang.GeneralDictionaryReadback.Payload
                          (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence roles registry context model) children
                          dictionaries →
                        @Yulang.GeneralDictionaryRecursiveEvidence.Evidence roles registry context model root
                          (Yulang.CommonRoleOutermostResolver.Dictionary.node key dictionaries)
```

## Yulang.GeneralDictionaryRecursiveEvidence.evidence_node_elim

側: **補助**。任意の registry・context・モデル・root・key・子辞書列について、node 辞書の Evidence から、親の Instance と各子辞書の同一モデルでの Evidence を持つ完全な source 子列が存在すると分かる。

```lean
@Yulang.GeneralDictionaryRecursiveEvidence.evidence_node_elim : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (model : Yulang.GeneralNominalCommonBridge.Assignment) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (key : Nat) (dictionaries : List.{0} Yulang.GeneralDictionaryReadback.Payload),
  @Yulang.GeneralDictionaryRecursiveEvidence.Evidence roles registry context model root
      (Yulang.CommonRoleOutermostResolver.Dictionary.node key dictionaries) →
    @Exists.{1} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)) fun children =>
      And (@Yulang.GeneralDictionaryRecursiveEvidence.Instance roles registry context model root key children)
        (@Yulang.CommonRoleOutermostResolver.All₂.{0, 0} (Yulang.GeneralSourceDictionaries.Occurrence roles)
          Yulang.GeneralDictionaryReadback.Payload
          (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence roles registry context model) children dictionaries)
```

## Yulang.GeneralDictionaryRecursiveEvidence.evidence_leaf_iff

側: **補助**。任意の registry・context・モデル・root・key について、子のない node 辞書の Evidence と、子列が空の同じ root・key の Instance が同値である。

```lean
@Yulang.GeneralDictionaryRecursiveEvidence.evidence_leaf_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (model : Yulang.GeneralNominalCommonBridge.Assignment) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (key : Nat),
  Iff
    (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence roles registry context model root
      (Yulang.CommonRoleOutermostResolver.Dictionary.node key
        (@List.nil.{0} Yulang.CommonRoleOutermostResolver.Dictionary)))
    (@Yulang.GeneralDictionaryRecursiveEvidence.Instance roles registry context model root key
      (@List.nil.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)))
```

## Yulang.GeneralDictionaryRecursiveEvidence.boundary_node_of_branch

側: **健全性**。任意の roles・Remaining・検査済み registry・context・指定モデルについて、具体 boundary の Unique、対応する可視宣言の検査・key 一致・bounds 取得・そのモデルでの BranchModels、および全子の同一モデルでの Evidence があれば、親辞書の boundary.Evidence が成立する。追加の BranchModels を必要とし、無条件の EvidenceNode ではない。

```lean
Yulang.GeneralDictionaryRecursiveEvidence.boundary_node_of_branch : ∀ (roles : Yulang.Roles.RoleDecls)
  (remaining : Yulang.GeneralNominalLocalBoundary.Remaining.{0} (Yulang.GeneralNominalCandidates.vocabulary roles))
  (registry : Yulang.GeneralDeclarations.Registry),
  @Yulang.B4Target.SourceBoundary.Checked.{0} (Yulang.GeneralNominalCandidates.vocabulary roles)
      (Yulang.GeneralDictionaryRecursiveEvidence.boundary roles remaining) registry →
    ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
      (model : Yulang.GeneralNominalCommonBridge.Assignment) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
      (key : Nat) (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles))
      (dictionaries : List.{0} Yulang.GeneralDictionaryReadback.Payload),
      @Yulang.B4Target.Unique.{0} (Yulang.GeneralNominalCandidates.vocabulary roles)
          (Yulang.GeneralDictionaryRecursiveEvidence.boundary roles remaining) registry context root key children →
        ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
          @Membership.mem.{0, 0} Yulang.GeneralDeclarations.Declaration
              (List.{0} Yulang.GeneralDeclarations.Declaration)
              (@List.instMembership.{0} Yulang.GeneralDeclarations.Declaration) registry.declarations declaration →
            ∀ (valid : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration),
              @Eq.{1} Nat declaration.id key →
                ∀ (bounds : List.{0} (Yulang.GeneralNominalInspection.Bounds context.state)),
                  @Eq.{1} (Option.{0} (List.{0} (Yulang.GeneralNominalInspection.Bounds context.state)))
                      (@Yulang.GeneralNominalRecursiveCandidates.arguments roles context root)
                      (@some.{0} (List.{0} (Yulang.GeneralNominalInspection.Bounds context.state)) bounds) →
                    @Yulang.GeneralNominalRecursiveCandidates.BranchModels roles registry context root declaration valid
                        bounds model →
                      @Yulang.CommonRoleOutermostResolver.All₂.{0, 0}
                          (Yulang.GeneralNominalCandidates.vocabulary roles).Demand
                          Yulang.CommonRoleOutermostResolver.Dictionary
                          (fun child dictionary =>
                            @Yulang.B4Target.SourceBoundary.Evidence.{0}
                              (Yulang.GeneralNominalCandidates.vocabulary roles)
                              (Yulang.GeneralDictionaryRecursiveEvidence.boundary roles remaining) registry context
                              model child dictionary)
                          children dictionaries →
                        @Yulang.B4Target.SourceBoundary.Evidence.{0} (Yulang.GeneralNominalCandidates.vocabulary roles)
                          (Yulang.GeneralDictionaryRecursiveEvidence.boundary roles remaining) registry context model
                          root (Yulang.CommonRoleOutermostResolver.Dictionary.node key dictionaries)
```

## Yulang.GeneralDictionaryRecursiveEvidence.boundary_evidenceNode_independent

側: **補助**。任意の roles と二つの Remaining について、同じ具体 Evidence を注入した boundary の EvidenceNode は同値である。Step・Stable・Generated の変更だけでは、この全状態向けの橋の成否は変わらない。

```lean
Yulang.GeneralDictionaryRecursiveEvidence.boundary_evidenceNode_independent : ∀ (roles : Yulang.Roles.RoleDecls)
  (first last : Yulang.GeneralNominalLocalBoundary.Remaining.{0} (Yulang.GeneralNominalCandidates.vocabulary roles)),
  Iff
    (@Yulang.B4TargetV3.EvidenceNode.{0} (Yulang.GeneralNominalCandidates.vocabulary roles)
      (Yulang.GeneralDictionaryRecursiveEvidence.boundary roles first))
    (@Yulang.B4TargetV3.EvidenceNode.{0} (Yulang.GeneralNominalCandidates.vocabulary roles)
      (Yulang.GeneralDictionaryRecursiveEvidence.boundary roles last))
```

## Yulang.GeneralDictionaryRecursiveEvidence.branch_models_iff

側: **補助**。任意の registry・context・root・検査済み宣言・bounds・モデルについて、BranchModels は、元状態の Models、同名捕捉区間の交差整合性、merge の全 ordinary atoms、全 selfChecks、ProjectionModels、生成された source equations の Models の連言と同値である。

```lean
@Yulang.GeneralDictionaryRecursiveEvidence.branch_models_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (bounds : List.{0} (Yulang.GeneralNominalInspection.Bounds context.state))
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Iff
    (@Yulang.GeneralNominalRecursiveCandidates.BranchModels roles registry context root declaration checked bounds
      model)
    (And (Yulang.GeneralNominalState.Models context.state model)
      (And
        (Yulang.GeneralNominalAllocation.Compatible
          (Yulang.GeneralNominalRecursiveInspection.bindings context.state
            (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds))
          model)
        (And
          (@Yulang.PresenceNormalForm.All.{0, 0} Nat Yulang.CommonNominalFullCarrier.model model
            (Yulang.GeneralNominalAllocation.merges context.state registry
              (@Yulang.GeneralSourceDictionaries.Occurrence.identity roles root) declaration
              (Yulang.GeneralNominalRecursiveInspection.bindings context.state
                (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds))))
          (And
            (@Yulang.PresenceNormalForm.All.{0, 0} Nat Yulang.CommonNominalFullCarrier.model model
              (Yulang.GeneralNominalRecursiveInspection.selfChecks context.state
                (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds)))
            (And
              (Yulang.GeneralNominalRecursiveInspection.ProjectionModels context.state
                (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds) model)
              (Yulang.GeneralNominalMaterialization.Models context.state declaration
                (Yulang.GeneralNominalAllocation.capture context.state registry
                  (@Yulang.GeneralSourceDictionaries.Occurrence.identity roles root) declaration.id
                  (Yulang.GeneralNominalRecursiveInspection.bindings context.state
                    (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds)))
                (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds)
                (@Yulang.GeneralNominalRecursiveCandidates.generated roles registry context root declaration checked
                  bounds)
                model))))))
```

## Yulang.GeneralDictionaryRecursiveEvidence.capture_occurs

側: **補助**。任意の context・宣言・bounds と report に含まれる捕捉について、その捕捉の source 両端は、計算された bindings の同名 binder 群に含まれる。

```lean
Yulang.GeneralDictionaryRecursiveEvidence.capture_occurs : ∀
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (declaration : Yulang.GeneralDeclarations.Declaration)
  (bounds : List.{0} (Yulang.GeneralNominalInspection.Bounds context.state))
  (captured : Yulang.GeneralNominalRecursiveInspection.Capture context.state),
  @Membership.mem.{0, 0} (Yulang.GeneralNominalRecursiveInspection.Capture context.state)
      (List.{0} (Yulang.GeneralNominalRecursiveInspection.Capture context.state))
      (@List.instMembership.{0} (Yulang.GeneralNominalRecursiveInspection.Capture context.state))
      (@Yulang.GeneralNominalRecursiveInspection.Report.captures context.state
        (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds))
      captured →
    @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (List.{0} Yulang.GeneralSourceState.Interval)
      (@List.instMembership.{0} Yulang.GeneralSourceState.Interval)
      (Yulang.GeneralNominalAllocation.occurrences
        (Yulang.GeneralNominalRecursiveInspection.bindings context.state
          (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds))
        (@Yulang.GeneralNominalRecursiveInspection.Capture.name context.state captured))
      (@Prod.mk.{0, 0} Nat Nat
        (context.state.base.source
          (@Prod.fst.{0, 0} (Fin context.state.base.slots) (Fin context.state.base.slots)
            (@Yulang.GeneralNominalRecursiveInspection.Capture.bounds context.state captured)))
        (context.state.base.source
          (@Prod.snd.{0, 0} (Fin context.state.base.slots) (Fin context.state.base.slots)
            (@Yulang.GeneralNominalRecursiveInspection.Capture.bounds context.state captured))))
```

## Yulang.GeneralDictionaryRecursiveEvidence.projected_value_fits_capture

側: **健全性**。任意の registry・context・root・検査済み宣言・bounds・BranchModels を満たすモデルについて、report 内の捕捉が宣言の入力名を持ち、指定 origin で actual が観察されるなら、actual はその binder の計算済み併合区間に収まる。反復捕捉や非単点区間も許す。

```lean
@Yulang.GeneralDictionaryRecursiveEvidence.projected_value_fits_capture : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (bounds : List.{0} (Yulang.GeneralNominalInspection.Bounds context.state))
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  @Yulang.GeneralNominalRecursiveCandidates.BranchModels roles registry context root declaration checked bounds model →
    ∀ (captured : Yulang.GeneralNominalRecursiveInspection.Capture context.state),
      @Membership.mem.{0, 0} (Yulang.GeneralNominalRecursiveInspection.Capture context.state)
          (List.{0} (Yulang.GeneralNominalRecursiveInspection.Capture context.state))
          (@List.instMembership.{0} (Yulang.GeneralNominalRecursiveInspection.Capture context.state))
          (@Yulang.GeneralNominalRecursiveInspection.Report.captures context.state
            (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds))
          captured →
        @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) declaration.inputNames
            (@Yulang.GeneralNominalRecursiveInspection.Capture.name context.state captured) →
          ∀ (origin : Yulang.GeneralNominalRecursiveInspection.Origin),
            @Eq.{1} (Option.{0} Yulang.GeneralNominalRecursiveInspection.Origin)
                (@Yulang.GeneralNominalRecursiveInspection.Capture.origin context.state captured)
                (@some.{0} Yulang.GeneralNominalRecursiveInspection.Origin origin) →
              ∀ (actual : Yulang.CommonNominalFullCarrier.Ty),
                Yulang.GeneralNominalRecursiveInspection.Observes model origin actual →
                  Yulang.GeneralNominalCaptureMerges.Fits model
                    ((Yulang.GeneralNominalAllocation.capture context.state registry
                          (@Yulang.GeneralSourceDictionaries.Occurrence.identity roles root) declaration.id
                          (Yulang.GeneralNominalRecursiveInspection.bindings context.state
                            (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds))).inputs
                      (@Yulang.GeneralNominalRecursiveInspection.Capture.name context.state captured))
                    actual
```

## Yulang.GeneralDictionaryRecursiveEvidence.projected_value_fits_child

側: **健全性**。任意の BranchModels を満たす指定モデルと、report 内の宣言済み入力捕捉・その origin の actual 観察について、署名が正しい任意の where clause の対象引数が同じ変数へ正規化されるなら、actual は実際に生成される子需要のその引数区間に収まる。

```lean
@Yulang.GeneralDictionaryRecursiveEvidence.projected_value_fits_child : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (bounds : List.{0} (Yulang.GeneralNominalInspection.Bounds context.state))
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  @Yulang.GeneralNominalRecursiveCandidates.BranchModels roles registry context root declaration checked bounds model →
    ∀ (captured : Yulang.GeneralNominalRecursiveInspection.Capture context.state),
      @Membership.mem.{0, 0} (Yulang.GeneralNominalRecursiveInspection.Capture context.state)
          (List.{0} (Yulang.GeneralNominalRecursiveInspection.Capture context.state))
          (@List.instMembership.{0} (Yulang.GeneralNominalRecursiveInspection.Capture context.state))
          (@Yulang.GeneralNominalRecursiveInspection.Report.captures context.state
            (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds))
          captured →
        @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) declaration.inputNames
            (@Yulang.GeneralNominalRecursiveInspection.Capture.name context.state captured) →
          ∀ (origin : Yulang.GeneralNominalRecursiveInspection.Origin),
            @Eq.{1} (Option.{0} Yulang.GeneralNominalRecursiveInspection.Origin)
                (@Yulang.GeneralNominalRecursiveInspection.Capture.origin context.state captured)
                (@some.{0} Yulang.GeneralNominalRecursiveInspection.Origin origin) →
              ∀ (actual : Yulang.CommonNominalFullCarrier.Ty),
                Yulang.GeneralNominalRecursiveInspection.Observes model origin actual →
                  ∀ (clause : Yulang.GeneralDeclarations.Clause)
                    (valid : Yulang.GeneralDeclarations.Clause.Signature roles clause)
                    (index : Fin (roles clause.role).arity),
                    @Eq.{1} Yulang.GeneralDeclarationPatterns.Pattern
                        (Yulang.GeneralDeclarationPatterns.normalize
                          (@getElem.{0, 0, 0} (List.{0} Yulang.GeneralDeclarationPatterns.Pattern) Nat
                            Yulang.GeneralDeclarationPatterns.Pattern
                            (fun as i =>
                              @LT.lt.{0} Nat instLTNat i
                                (@List.length.{0} Yulang.GeneralDeclarationPatterns.Pattern as))
                            (@List.instGetElemNatLtLength.{0} Yulang.GeneralDeclarationPatterns.Pattern)
                            clause.arguments (@Fin.val (roles clause.role).arity index) ⋯))
                        (Yulang.GeneralDeclarationPatterns.Pattern.var
                          (@Yulang.GeneralNominalRecursiveInspection.Capture.name context.state captured)) →
                      have captures :=
                        Yulang.GeneralNominalRecursiveInspection.bindings context.state
                          (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds);
                      let child :=
                        @Yulang.GeneralDeclarationDemands.childDemand roles declaration clause valid
                          (Yulang.GeneralNominalAllocation.capture context.state registry
                            (@Yulang.GeneralSourceDictionaries.Occurrence.identity roles root) declaration.id captures)
                          (@Yulang.GeneralNominalAllocation.allocation roles context.state registry
                            (@Yulang.GeneralSourceDictionaries.Occurrence.identity roles root) declaration.id clause);
                      Yulang.GeneralNominalCaptureMerges.Fits model
                        (@Yulang.GeneralSourceState.Demand.arguments roles child index) actual
```

## Yulang.GeneralDictionaryRecursiveEvidence.generated_scalar_equation

側: **健全性**。任意の registry・context・root・検査済み宣言・bounds・指定モデルについて、BranchModels が成立し、生成 schema に source target の scalar 検査が含まれるなら、そのモデルの target は指定 scalar 型と同値である。

```lean
@Yulang.GeneralDictionaryRecursiveEvidence.generated_scalar_equation : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (bounds : List.{0} (Yulang.GeneralNominalInspection.Bounds context.state))
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  @Yulang.GeneralNominalRecursiveCandidates.BranchModels roles registry context root declaration checked bounds model →
    ∀ (target : Nat) (scalar : Yulang.Inference.Base),
      @Membership.mem.{0, 0}
          (Prod.{0, 0} Yulang.GeneralNominalRecursiveInspection.Origin Yulang.GeneralNominalRecursiveInspection.Test)
          (List.{0}
            (Prod.{0, 0} Yulang.GeneralNominalRecursiveInspection.Origin Yulang.GeneralNominalRecursiveInspection.Test))
          (@List.instMembership.{0}
            (Prod.{0, 0} Yulang.GeneralNominalRecursiveInspection.Origin Yulang.GeneralNominalRecursiveInspection.Test))
          (@Yulang.GeneralNominalRecursiveCandidates.generated roles registry context root declaration checked
              bounds).tests
          (@Prod.mk.{0, 0} Yulang.GeneralNominalRecursiveInspection.Origin Yulang.GeneralNominalRecursiveInspection.Test
            (Yulang.GeneralNominalRecursiveInspection.Origin.source target)
            (Yulang.GeneralNominalRecursiveInspection.Test.scalar scalar)) →
        Yulang.CommonNominalFullCarrier.Equivalent
          (@Prod.fst.{0, 0} Yulang.CommonNominalFullCarrier.model.Ty Yulang.CommonNominalFullCarrier.model.Row
            (model target))
          (@Yulang.CommonNominalSyntax.Layer.base.{0, 0} Yulang.CommonNominalFullCarrier.Row
            (Yulang.CommonNominalSyntax.State.{0} Yulang.CommonNominalFullCarrier.Row) scalar)
```

## Yulang.GeneralDictionaryRecursiveEvidence.generated_output_binder_equation

側: **健全性**。任意の BranchModels を満たす指定モデルについて、宣言の output-only binder name を source target に結ぶ actual-mode の Use が生成 schema に含まれるなら、target の値と決定的に割り当てられた出力捕捉 source の値は同値である。

```lean
@Yulang.GeneralDictionaryRecursiveEvidence.generated_output_binder_equation : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (bounds : List.{0} (Yulang.GeneralNominalInspection.Bounds context.state))
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  @Yulang.GeneralNominalRecursiveCandidates.BranchModels roles registry context root declaration checked bounds model →
    ∀ (name target : Nat),
      @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) declaration.outputNames name →
        @Membership.mem.{0, 0} Yulang.GeneralNominalMaterialization.Use
            (List.{0} Yulang.GeneralNominalMaterialization.Use)
            (@List.instMembership.{0} Yulang.GeneralNominalMaterialization.Use)
            (@Yulang.GeneralNominalRecursiveCandidates.generated roles registry context root declaration checked
                bounds).variables
            { name := name, origin := Yulang.GeneralNominalRecursiveInspection.Origin.source target,
              mode := Yulang.GeneralNominalMaterialization.Mode.actual } →
          Yulang.CommonNominalFullCarrier.Equivalent
            (@Prod.fst.{0, 0} Yulang.CommonNominalFullCarrier.model.Ty Yulang.CommonNominalFullCarrier.model.Row
              (model target))
            (@Prod.fst.{0, 0} Yulang.CommonNominalFullCarrier.model.Ty Yulang.CommonNominalFullCarrier.model.Row
              (model
                ((Yulang.GeneralNominalAllocation.capture context.state registry
                      (@Yulang.GeneralSourceDictionaries.Occurrence.identity roles root) declaration.id
                      (Yulang.GeneralNominalRecursiveInspection.bindings context.state
                        (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds))).outputs
                  name)))
```

## Yulang.GeneralDictionaryRecursiveEvidence.instance_plan

側: **健全性**。任意の検査済み registry・context・モデル・root・key・子列について、モデル別 Instance があれば、その完全な子列は registry・context・root から計算した再帰的 frame の Plan を満たす。Survivor は前提にしない。

```lean
Yulang.GeneralDictionaryRecursiveEvidence.instance_plan : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)),
  @Yulang.GeneralDictionaryRecursiveEvidence.Instance registry.roles registry context model root key children →
    Yulang.GeneralDictionaryEmissionPlans.Plan registry checked
      (Yulang.GeneralDictionaryRecursiveReadback.frames registry context root) root key children
```

## Yulang.GeneralDictionaryRecursiveEvidence.instance_children_functional

側: **補助**。任意の検査済み registry・固定 context・root・key と任意の二モデルについて、それぞれのモデルで Instance がある二つの子列は等しい。一方のモデルでの意味を他方へ移す主張ではない。

```lean
@Yulang.GeneralDictionaryRecursiveEvidence.instance_children_functional : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry),
  Yulang.GeneralDeclarations.Checked registry →
    ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
      (firstModel lastModel : Yulang.GeneralNominalCommonBridge.Assignment)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (first last : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      @Yulang.GeneralDictionaryRecursiveEvidence.Instance roles registry context firstModel root key first →
        @Yulang.GeneralDictionaryRecursiveEvidence.Instance roles registry context lastModel root key last →
          @Eq.{1} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)) first last
```

## Yulang.GeneralDictionaryRecursiveEvidence.indexed_plan

側: **健全性**。任意の検査済み registry・context・モデル・source 辞書木について、全節点のモデル別 Instance による indexed Evidence があれば、同じ木は計算済み再帰的 frames による再構成 Rule の indexed Evidence を持つ。

```lean
Yulang.GeneralDictionaryRecursiveEvidence.indexed_plan : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (tree : Yulang.GeneralSourceDictionaries.Dictionary registry.roles),
  @Yulang.GeneralSourceDictionaries.Evidence registry.roles
      (@Yulang.GeneralDictionaryRecursiveEvidence.Instance registry.roles registry context model) tree →
    @Yulang.GeneralSourceDictionaries.Evidence registry.roles
      (Yulang.GeneralDictionaryPayloadReconstruction.Rule registry checked
        (Yulang.GeneralDictionaryRecursiveReadback.frames registry context))
      tree
```

## Yulang.GeneralDictionaryRecursiveEvidence.reconstruct_evidence

側: **完全性**。任意の検査済み registry・context・モデル・source 辞書木について、モデル別 Instance の indexed Evidence があるなら、その木の消去 payload と root から reconstruct は元の木を some として返す。既存の意味証拠に対する再構成の完全性に限る。

```lean
Yulang.GeneralDictionaryRecursiveEvidence.reconstruct_evidence : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (tree : Yulang.GeneralSourceDictionaries.Dictionary registry.roles),
  @Yulang.GeneralSourceDictionaries.Evidence registry.roles
      (@Yulang.GeneralDictionaryRecursiveEvidence.Instance registry.roles registry context model) tree →
    @Eq.{1} (Option.{0} (Yulang.GeneralSourceDictionaries.Dictionary registry.roles))
      (Yulang.GeneralDictionaryRecursiveReadback.reconstruct registry checked context
        (@Yulang.GeneralSourceDictionaries.erase registry.roles tree)
        (@Yulang.GeneralSourceDictionaries.Dictionary.root registry.roles tree))
      (@some.{0} (Yulang.GeneralSourceDictionaries.Dictionary registry.roles) tree)
```

## Yulang.GeneralDictionaryRecursiveEvidence.evidence_readback

側: **完全性**。任意の検査済み registry・context・モデル・root・payload について具体 Evidence があれば、reconstruct が返し、Readback を満たし、同じモデルの indexed Evidence を持つ source 辞書木が存在する。

```lean
Yulang.GeneralDictionaryRecursiveEvidence.evidence_readback : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (payload : Yulang.GeneralDictionaryReadback.Payload),
  @Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry.roles registry context model root payload →
    @Exists.{1} (Yulang.GeneralSourceDictionaries.Dictionary registry.roles) fun tree =>
      And
        (@Eq.{1} (Option.{0} (Yulang.GeneralSourceDictionaries.Dictionary registry.roles))
          (Yulang.GeneralDictionaryRecursiveReadback.reconstruct registry checked context payload root)
          (@some.{0} (Yulang.GeneralSourceDictionaries.Dictionary registry.roles) tree))
        (And (@Yulang.GeneralSourceDictionaries.Readback registry.roles root payload tree)
          (@Yulang.GeneralSourceDictionaries.Evidence registry.roles
            (@Yulang.GeneralDictionaryRecursiveEvidence.Instance registry.roles registry context model) tree))
```

## Yulang.GeneralDictionaryRecursiveEvidence.evidence_fixed_readback

側: **補助**。任意の検査済み registry・context・モデル・root・payload の Evidence から、一つの再構成済み source 木を得る。その同じ木は、同じ payload の Evidence が既に成立する任意の別モデルでも indexed Evidence を持つ。別モデルでの Evidence は前提であり、全元モデルでの成立は導かない。

```lean
Yulang.GeneralDictionaryRecursiveEvidence.evidence_fixed_readback : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (payload : Yulang.GeneralDictionaryReadback.Payload),
  @Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry.roles registry context model root payload →
    @Exists.{1} (Yulang.GeneralSourceDictionaries.Dictionary registry.roles) fun tree =>
      And
        (@Eq.{1} (Option.{0} (Yulang.GeneralSourceDictionaries.Dictionary registry.roles))
          (Yulang.GeneralDictionaryRecursiveReadback.reconstruct registry checked context payload root)
          (@some.{0} (Yulang.GeneralSourceDictionaries.Dictionary registry.roles) tree))
        (And (@Yulang.GeneralSourceDictionaries.Readback registry.roles root payload tree)
          (And
            (@Yulang.GeneralSourceDictionaries.Evidence registry.roles
              (@Yulang.GeneralDictionaryRecursiveEvidence.Instance registry.roles registry context model) tree)
            (∀ (otherModel : Yulang.GeneralNominalCommonBridge.Assignment),
              @Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry.roles registry context otherModel root
                  payload →
                @Yulang.GeneralSourceDictionaries.Evidence registry.roles
                  (@Yulang.GeneralDictionaryRecursiveEvidence.Instance registry.roles registry context otherModel)
                  tree)))
```

## Yulang.GeneralDictionaryRecursiveObstruction.declaration_checked

側: **補助**。head が List a、関連出力1が int、where 子が空の固定宣言について、既存 constructors・roles に対する DeclarationChecked が成立する。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.declaration_checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralDictionaryRecursiveObstruction.declaration
```

## Yulang.GeneralDictionaryRecursiveObstruction.registry_checked

側: **補助**。この固定宣言だけを可視にする registry は Checked を満たす。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.registry_checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralDictionaryRecursiveObstruction.registry
```

## Yulang.GeneralDictionaryRecursiveObstruction.query_exact

側: **補助**。固定 context と宣言から生成される head query は、nominal List の引数を binder 0 として捕捉する一つの query に厳密に等しい。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.query_exact : @Eq.{1} (List.{0} Yulang.GeneralNominalInspection.Query)
  (Yulang.GeneralNominalInspection.queries Yulang.GeneralDictionaryRecursiveObstruction.context.state
    Yulang.GeneralDictionaryRecursiveObstruction.context.interpretation
    Yulang.GeneralDictionaryRecursiveObstruction.declaration)
  (@List.cons.{0} Yulang.GeneralNominalInspection.Query
    (Yulang.GeneralNominalInspection.Query.nominal (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@List.cons.{0} Yulang.GeneralNominalInspection.Query
        (Yulang.GeneralNominalInspection.Query.variables
          (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil.{0} Nat)))
        (@List.nil.{0} Yulang.GeneralNominalInspection.Query)))
    (@List.nil.{0} Yulang.GeneralNominalInspection.Query))
```

## Yulang.GeneralDictionaryRecursiveObstruction.report_calculated

側: **補助**。固定例の bounds [(0,0)] の再帰的 report は、source 0 の nominal 引数を binder 0・区間 (1,1) として記録する既存 captured report に厳密に等しい。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.report_calculated : @Eq.{1}
  (Yulang.GeneralNominalRecursiveInspection.Report Yulang.GeneralDictionaryRecursiveObstruction.context.state)
  (Yulang.GeneralNominalRecursiveCandidates.report Yulang.GeneralDictionaryRecursiveObstruction.context
    Yulang.GeneralDictionaryRecursiveObstruction.declaration
    (@List.cons.{0} (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryRecursiveObstruction.context.state)
      (@Prod.mk.{0, 0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots)
        (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots)
        (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots) (nat_lit 0)
          (@Fin.instOfNat Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots ⋯ (nat_lit 0)))
        (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots) (nat_lit 0)
          (@Fin.instOfNat Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots ⋯ (nat_lit 0))))
      (@List.nil.{0}
        (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryRecursiveObstruction.context.state))))
  (Yulang.GeneralNominalUnaryCaptureFacts.captured Yulang.GeneralDictionaryRecursiveObstruction.context.state
    (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots) (nat_lit 0)
      (@Fin.instOfNat Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots ⋯ (nat_lit 0)))
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (@Prod.mk.{0, 0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots)
      (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots)
      (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots) (nat_lit 1)
        (@Fin.instOfNat Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots ⋯ (nat_lit 1)))
      (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots) (nat_lit 1)
        (@Fin.instOfNat Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots ⋯ (nat_lit 1)))))
```

## Yulang.GeneralDictionaryRecursiveObstruction.schema_calculated

側: **補助**。固定例の宣言・root・bounds から生成される schema は、source 1 が int であることを要求する scalar 検査一つだけに厳密に等しい。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.schema_calculated : @Eq.{1} Yulang.GeneralNominalMaterialization.Schema
  (@Yulang.GeneralNominalRecursiveCandidates.generated Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context
    Yulang.GeneralDictionaryRecursiveObstruction.root Yulang.GeneralDictionaryRecursiveObstruction.declaration
    Yulang.GeneralDictionaryRecursiveObstruction.declaration_checked
    (@List.cons.{0} (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryRecursiveObstruction.context.state)
      (@Prod.mk.{0, 0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots)
        (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots)
        (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots) (nat_lit 0)
          (@Fin.instOfNat Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots ⋯ (nat_lit 0)))
        (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots) (nat_lit 0)
          (@Fin.instOfNat Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots ⋯ (nat_lit 0))))
      (@List.nil.{0}
        (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryRecursiveObstruction.context.state))))
  {
    tests :=
      @List.cons.{0}
        (Prod.{0, 0} Yulang.GeneralNominalRecursiveInspection.Origin Yulang.GeneralNominalRecursiveInspection.Test)
        (@Prod.mk.{0, 0} Yulang.GeneralNominalRecursiveInspection.Origin Yulang.GeneralNominalRecursiveInspection.Test
          (Yulang.GeneralNominalRecursiveInspection.Origin.source
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (Yulang.GeneralNominalRecursiveInspection.Test.scalar Yulang.Inference.Base.int))
        (@List.nil.{0}
          (Prod.{0, 0} Yulang.GeneralNominalRecursiveInspection.Origin Yulang.GeneralNominalRecursiveInspection.Test)) }
```

## Yulang.GeneralDictionaryRecursiveObstruction.good_branch

側: **健全性**。固定例の int 値を持つ具体モデルは、元状態・private 区間・projection・生成された関連出力等式を含む BranchModels を満たす。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.good_branch : @Yulang.GeneralNominalRecursiveCandidates.BranchModels
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryRecursiveObstruction.registry
  Yulang.GeneralDictionaryRecursiveObstruction.context Yulang.GeneralDictionaryRecursiveObstruction.root
  Yulang.GeneralDictionaryRecursiveObstruction.declaration
  Yulang.GeneralDictionaryRecursiveObstruction.declaration_checked
  (@List.cons.{0} (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryRecursiveObstruction.context.state)
    (@Prod.mk.{0, 0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots)
      (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots)
      (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots) (nat_lit 0)
        (@Fin.instOfNat Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots ⋯ (nat_lit 0)))
      (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots) (nat_lit 0)
        (@Fin.instOfNat Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots ⋯ (nat_lit 0))))
    (@List.nil.{0} (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryRecursiveObstruction.context.state)))
  Yulang.GeneralNominalExamples.model
```

## Yulang.GeneralDictionaryRecursiveObstruction.metadata

側: **補助**。固定 registry と context は、constructors と primitive interpretation の整合性を表す Metadata を満たす。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.metadata : Yulang.GeneralNominalRecursiveCandidates.Metadata
  Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context
```

## Yulang.GeneralDictionaryRecursiveObstruction.linked

側: **補助**。固定 root の全入力端点と関連出力 target は、元 nominal 状態の source 一覧に存在し、Linked が成立する。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.linked : @Yulang.GeneralNominalState.Linked
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryRecursiveObstruction.context.state
  (@Yulang.GeneralSourceDictionaries.Occurrence.demand Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryRecursiveObstruction.root)
```

## Yulang.GeneralDictionaryRecursiveObstruction.not_pending

側: **補助**。固定 root の入力下界は既存 nominal descriptor から既知であり、RootPending は成立しない。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.not_pending : Not
  (@Yulang.GeneralNominalState.RootPending Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryRecursiveObstruction.context.state
    (@Yulang.GeneralSourceDictionaries.Occurrence.demand Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryRecursiveObstruction.root))
```

## Yulang.GeneralDictionaryRecursiveObstruction.prepared

側: **補助**。固定宣言は、Metadata・Linked・freshness・bounds 取得・検査完了・要求の準備完了と具体 branch モデルの存在を満たし、Prepared である。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.prepared : @Yulang.GeneralNominalRecursiveCandidates.Prepared
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryRecursiveObstruction.registry
  Yulang.GeneralDictionaryRecursiveObstruction.context Yulang.GeneralDictionaryRecursiveObstruction.root
  Yulang.GeneralDictionaryRecursiveObstruction.declaration
  Yulang.GeneralDictionaryRecursiveObstruction.declaration_checked
```

## Yulang.GeneralDictionaryRecursiveObstruction.survivor

側: **補助**。変更していない再帰的候補判断において、固定 root に key 40・子列 [] の Survivor が実際に存在する。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.survivor : @Yulang.GeneralNominalRecursiveCandidates.Survivor
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryRecursiveObstruction.registry
  Yulang.GeneralDictionaryRecursiveObstruction.context Yulang.GeneralDictionaryRecursiveObstruction.root
  (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
  (@List.nil.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
```

## Yulang.GeneralDictionaryRecursiveObstruction.not_rootK2

側: **補助**。固定 root の nominal head について RootK2 は成立しない。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.not_rootK2 : Not
  (@Yulang.GeneralNominalMixedRecurrence.RootK2 Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryRecursiveObstruction.context.state
    (@Yulang.GeneralSourceDictionaries.Occurrence.demand Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryRecursiveObstruction.root))
```

## Yulang.GeneralDictionaryRecursiveObstruction.not_candidateK2

側: **補助**。固定 registry・context・root について、再帰的検査で訪問される head に K2 がなく、CandidateK2 は成立しない。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.not_candidateK2 : Not
  (@Yulang.GeneralNominalRecursiveCandidates.CandidateK2 Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context
    Yulang.GeneralDictionaryRecursiveObstruction.root)
```

## Yulang.GeneralDictionaryRecursiveObstruction.not_inspection_pending

側: **補助**。固定 registry・context・root について、可視宣言は Prepared であり、InspectionPending は成立しない。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.not_inspection_pending : Not
  (@Yulang.GeneralNominalRecursiveCandidates.InspectionPending Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context
    Yulang.GeneralDictionaryRecursiveObstruction.root)
```

## Yulang.GeneralDictionaryRecursiveObstruction.safe

側: **補助**。固定 registry・context・root は recursiveFields の SafeKnown を満たす。RootPending・RootK2・CandidateK2・InspectionPending はいずれも成立しない。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.safe : @Yulang.GeneralNominalLocalBoundary.SafeKnown.{0}
  (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles)
  (Yulang.GeneralNominalLocalBoundary.recursiveFields Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context
  Yulang.GeneralDictionaryRecursiveObstruction.root
```

## Yulang.GeneralDictionaryRecursiveObstruction.unique

側: **補助**。固定 registry・context・root では key 40・子列 [] の Survivor が存在し、任意の別 Survivor も同じ key と同じ子列を持つ。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.unique : @Yulang.GeneralNominalLocalBoundary.Unique.{0}
  (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles)
  (Yulang.GeneralNominalLocalBoundary.recursiveFields Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context
  Yulang.GeneralDictionaryRecursiveObstruction.root (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
  (@List.nil.{0} (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand)
```

## Yulang.GeneralDictionaryRecursiveObstruction.selected

側: **補助**。固定 registry・context・root の独立な Local 判断は selected 40 [] を導く。分岐等式を元状態へ反映する Step は前提にしていない。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.selected : @Yulang.GeneralNominalLocalBoundary.Local.{0}
  (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles)
  (Yulang.GeneralNominalLocalBoundary.recursiveFields Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context
  Yulang.GeneralDictionaryRecursiveObstruction.root
  (@Yulang.CommonRoleOutermostResolver.Frontier.selected.{0}
    (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand
    (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
    (@List.nil.{0} (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand))
```

## Yulang.GeneralDictionaryRecursiveObstruction.bad_original_model

側: **阻害**。固定反例モデルは source 0 を List string、関連出力 target 1 を string としながら、元 context.state の Models を満たす。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.bad_original_model : Yulang.GeneralNominalState.Models
  Yulang.GeneralDictionaryRecursiveObstruction.context.state Yulang.GeneralDictionaryRecursiveObstruction.badModel
```

## Yulang.GeneralDictionaryRecursiveObstruction.bad_private_projection

側: **阻害**。同じ反例モデルは、候補の private head 区間と ProjectionModels も満たす。違反の原因は生成された関連出力等式に残る。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.bad_private_projection : And
  (Yulang.GeneralNominalState.Models
    (@Yulang.GeneralNominalRecursiveCandidates.privateState Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context
      Yulang.GeneralDictionaryRecursiveObstruction.root Yulang.GeneralDictionaryRecursiveObstruction.declaration
      (@List.cons.{0}
        (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryRecursiveObstruction.context.state)
        (@Prod.mk.{0, 0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots)
          (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots)
          (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots) (nat_lit 0)
            (@Fin.instOfNat Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots ⋯ (nat_lit 0)))
          (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots) (nat_lit 0)
            (@Fin.instOfNat Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots ⋯ (nat_lit 0))))
        (@List.nil.{0}
          (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryRecursiveObstruction.context.state))))
    Yulang.GeneralDictionaryRecursiveObstruction.badModel)
  (Yulang.GeneralNominalRecursiveInspection.ProjectionModels Yulang.GeneralDictionaryRecursiveObstruction.context.state
    (Yulang.GeneralNominalRecursiveCandidates.report Yulang.GeneralDictionaryRecursiveObstruction.context
      Yulang.GeneralDictionaryRecursiveObstruction.declaration
      (@List.cons.{0}
        (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryRecursiveObstruction.context.state)
        (@Prod.mk.{0, 0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots)
          (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots)
          (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots) (nat_lit 0)
            (@Fin.instOfNat Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots ⋯ (nat_lit 0)))
          (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots) (nat_lit 0)
            (@Fin.instOfNat Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots ⋯ (nat_lit 0))))
        (@List.nil.{0}
          (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryRecursiveObstruction.context.state))))
    Yulang.GeneralDictionaryRecursiveObstruction.badModel)
```

## Yulang.GeneralDictionaryRecursiveObstruction.bad_output_equation

側: **阻害**。固定反例モデルにおける source 1 の string 型は、宣言された int 型と同値ではない。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.bad_output_equation : Not
  (Yulang.CommonNominalFullCarrier.Equivalent
    (@Prod.fst.{0, 0} Yulang.CommonNominalFullCarrier.model.Ty Yulang.CommonNominalFullCarrier.model.Row
      (Yulang.GeneralDictionaryRecursiveObstruction.badModel
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@Yulang.CommonNominalSyntax.Layer.base.{0, 0} Yulang.CommonNominalFullCarrier.Row
      (Yulang.CommonNominalSyntax.State.{0} Yulang.CommonNominalFullCarrier.Row) Yulang.Inference.Base.int))
```

## Yulang.GeneralDictionaryRecursiveObstruction.bad_not_branch

側: **阻害**。固定反例モデルは元状態モデルであっても、source 1=int の生成要求に反するため、この候補の BranchModels を満たさない。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.bad_not_branch : Not
  (@Yulang.GeneralNominalRecursiveCandidates.BranchModels Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context
    Yulang.GeneralDictionaryRecursiveObstruction.root Yulang.GeneralDictionaryRecursiveObstruction.declaration
    Yulang.GeneralDictionaryRecursiveObstruction.declaration_checked
    (@List.cons.{0} (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryRecursiveObstruction.context.state)
      (@Prod.mk.{0, 0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots)
        (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots)
        (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots) (nat_lit 0)
          (@Fin.instOfNat Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots ⋯ (nat_lit 0)))
        (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots) (nat_lit 0)
          (@Fin.instOfNat Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots ⋯ (nat_lit 0))))
      (@List.nil.{0}
        (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryRecursiveObstruction.context.state)))
    Yulang.GeneralDictionaryRecursiveObstruction.badModel)
```

## Yulang.GeneralDictionaryRecursiveObstruction.original_model_gap

側: **阻害**。固定例では Checked・SafeKnown・Unique が同時に成立し、元状態を満たす反例モデルが存在する一方、そのモデルの BranchModels は成立しない。Survivor の存在的整合性から全元モデルの branch 意味は得られない。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.original_model_gap : And
  (Yulang.GeneralDeclarations.Checked Yulang.GeneralDictionaryRecursiveObstruction.registry)
  (And
    (@Yulang.GeneralNominalLocalBoundary.SafeKnown.{0}
      (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles)
      (Yulang.GeneralNominalLocalBoundary.recursiveFields Yulang.GeneralDeclarationExamples.roles)
      Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context
      Yulang.GeneralDictionaryRecursiveObstruction.root)
    (And
      (@Yulang.GeneralNominalLocalBoundary.Unique.{0}
        (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles)
        (Yulang.GeneralNominalLocalBoundary.recursiveFields Yulang.GeneralDeclarationExamples.roles)
        Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context
        Yulang.GeneralDictionaryRecursiveObstruction.root
        (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
        (@List.nil.{0} (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand))
      (And
        (Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryRecursiveObstruction.context.state
          Yulang.GeneralDictionaryRecursiveObstruction.badModel)
        (Not
          (@Yulang.GeneralNominalRecursiveCandidates.BranchModels Yulang.GeneralDeclarationExamples.roles
            Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context
            Yulang.GeneralDictionaryRecursiveObstruction.root Yulang.GeneralDictionaryRecursiveObstruction.declaration
            Yulang.GeneralDictionaryRecursiveObstruction.declaration_checked
            (@List.cons.{0}
              (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryRecursiveObstruction.context.state)
              (@Prod.mk.{0, 0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots)
                (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots)
                (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots)
                  (nat_lit 0)
                  (@Fin.instOfNat Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots ⋯ (nat_lit 0)))
                (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots)
                  (nat_lit 0)
                  (@Fin.instOfNat Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots ⋯ (nat_lit 0))))
              (@List.nil.{0}
                (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryRecursiveObstruction.context.state)))
            Yulang.GeneralDictionaryRecursiveObstruction.badModel)))))
```

## Yulang.GeneralDictionaryRecursiveObstruction.output_provenance

側: **補助**。固定例の int 要求は宣言の実際の associated equation に由来し、出力名は1、RHS は primitive int、root のその出力 target は source 1 である。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.output_provenance : And
  (@Membership.mem.{0, 0} Yulang.GeneralDeclarations.Equation (List.{0} Yulang.GeneralDeclarations.Equation)
    (@List.instMembership.{0} Yulang.GeneralDeclarations.Equation)
    Yulang.GeneralDictionaryRecursiveObstruction.declaration.associated
    Yulang.GeneralDictionaryRecursiveObstruction.equation)
  (And
    (@Eq.{1} Nat Yulang.GeneralDictionaryRecursiveObstruction.equation.name
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (And
      (@Eq.{1} Yulang.GeneralDeclarationPatterns.Pattern
        (Yulang.GeneralDeclarationPatterns.normalize Yulang.GeneralDictionaryRecursiveObstruction.equation.rhs)
        (Yulang.GeneralDeclarationPatterns.Pattern.app (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@List.nil.{0} Yulang.GeneralDeclarationPatterns.Pattern)))
      (And
        (@Eq.{1} (Option.{0} Yulang.GeneralCandidateInspection.Primitive)
          (Yulang.GeneralDictionaryRecursiveObstruction.context.interpretation.primitives
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@some.{0} Yulang.GeneralCandidateInspection.Primitive
            (Yulang.GeneralCandidateInspection.Primitive.scalar Yulang.Inference.Base.int)))
        (@Eq.{1} (List.{0} Yulang.GeneralSourceState.Output)
          (@Yulang.GeneralSourceState.Demand.outputs Yulang.GeneralDeclarationExamples.roles
            (@Yulang.GeneralSourceDictionaries.Occurrence.demand Yulang.GeneralDeclarationExamples.roles
              Yulang.GeneralDictionaryRecursiveObstruction.root))
          (@List.cons.{0} Yulang.GeneralSourceState.Output
            { name := @OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)),
              target := @OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) }
            (@List.nil.{0} Yulang.GeneralSourceState.Output))))))
```

## Yulang.GeneralDictionaryRecursiveObstruction.classified_any

側: **補助**。任意の Remaining 補完に対し、固定例の元 context では独立 V3 Classify が node 40 [] を selected と分類する。Evidence や Step・Stable・Generated の実装は使わない。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.classified_any : ∀
  (remaining :
    Yulang.GeneralNominalLocalBoundary.Remaining.{0}
      (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles)),
  @Yulang.B4TargetV3.Classify.{0} (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles)
    (@Yulang.GeneralNominalLocalBoundary.complete.{0}
      (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles)
      (Yulang.GeneralNominalLocalBoundary.recursiveFields Yulang.GeneralDeclarationExamples.roles) remaining)
    Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context
    Yulang.GeneralDictionaryRecursiveObstruction.root
    (Yulang.CommonRoleOutermostResolver.Result.selected
      (Yulang.CommonRoleOutermostResolver.Dictionary.node
        (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
        (@List.nil.{0} Yulang.CommonRoleOutermostResolver.Dictionary)))
```

## Yulang.GeneralDictionaryRecursiveObstruction.no_evidenceNode_of_output_sound

側: **阻害**。任意の Remaining について、その Evidence が固定辞書 node 40 [] の宣言済み出力等式 source 1=int を全モデルで尊重するなら、recursiveFields を補完した全状態向け EvidenceNode は成立しない。Evidence の表現には依存せず、最終状態向け B4 全体の反証ではない。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.no_evidenceNode_of_output_sound : ∀
  (remaining :
    Yulang.GeneralNominalLocalBoundary.Remaining.{0}
      (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles)),
  (∀ (model : (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles).Model),
      @Yulang.GeneralNominalLocalBoundary.Remaining.Evidence.{0}
          (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles) remaining
          Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context
          model Yulang.GeneralDictionaryRecursiveObstruction.root
          (Yulang.CommonRoleOutermostResolver.Dictionary.node
            (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
            (@List.nil.{0} Yulang.CommonRoleOutermostResolver.Dictionary)) →
        Yulang.CommonNominalFullCarrier.Equivalent
          (@Prod.fst.{0, 0} Yulang.CommonNominalFullCarrier.model.Ty Yulang.CommonNominalFullCarrier.model.Row
            (model (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Yulang.CommonNominalSyntax.Layer.base.{0, 0} Yulang.CommonNominalFullCarrier.Row
            (Yulang.CommonNominalSyntax.State.{0} Yulang.CommonNominalFullCarrier.Row) Yulang.Inference.Base.int)) →
    Not
      (@Yulang.B4TargetV3.EvidenceNode.{0}
        (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles)
        (@Yulang.GeneralNominalLocalBoundary.complete.{0}
          (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles)
          (Yulang.GeneralNominalLocalBoundary.recursiveFields Yulang.GeneralDeclarationExamples.roles) remaining))
```

## Yulang.GeneralDictionaryRecursiveObstruction.no_dictionarySound_of_unchanged

側: **阻害**。任意の Remaining と executor について、Evidence が固定例の出力等式を尊重し、この入力に対する executor の最終状態が元 context と等しいなら、DictionarySound は成立しない。分岐等式を最終状態へ反映する executor はこの反証の対象ではない。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.no_dictionarySound_of_unchanged : ∀
  (remaining :
    Yulang.GeneralNominalLocalBoundary.Remaining.{0}
      (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles)),
  (∀ (model : (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles).Model),
      @Yulang.GeneralNominalLocalBoundary.Remaining.Evidence.{0}
          (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles) remaining
          Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context
          model Yulang.GeneralDictionaryRecursiveObstruction.root
          (Yulang.CommonRoleOutermostResolver.Dictionary.node
            (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
            (@List.nil.{0} Yulang.CommonRoleOutermostResolver.Dictionary)) →
        Yulang.CommonNominalFullCarrier.Equivalent
          (@Prod.fst.{0, 0} Yulang.CommonNominalFullCarrier.model.Ty Yulang.CommonNominalFullCarrier.model.Row
            (model (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Yulang.CommonNominalSyntax.Layer.base.{0, 0} Yulang.CommonNominalFullCarrier.Row
            (Yulang.CommonNominalSyntax.State.{0} Yulang.CommonNominalFullCarrier.Row) Yulang.Inference.Base.int)) →
    ∀
      (executor :
        Yulang.B4TargetV3.Executor.{0}
          (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles)),
      @Eq.{1} (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles).State
          (@Prod.fst.{0, 0} (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles).State
            Yulang.CommonRoleOutermostResolver.Tree
            (@Yulang.B4TargetV3.Executor.run.{0}
              (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles) executor
              Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context
              Yulang.GeneralDictionaryRecursiveObstruction.root))
          Yulang.GeneralDictionaryRecursiveObstruction.context →
        Not
          (@Yulang.B4TargetV3.DictionarySound.{0}
            (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles)
            (@Yulang.GeneralNominalLocalBoundary.complete.{0}
              (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles)
              (Yulang.GeneralNominalLocalBoundary.recursiveFields Yulang.GeneralDeclarationExamples.roles) remaining)
            executor)
```

## Yulang.GeneralDictionaryRecursiveObstruction.branch_iff_output

側: **補助**。固定例の任意のモデルについて、BranchModels は「元 context.state の Models と source 1=int の同値」の連言と同値である。head 捕捉と projection は元状態から既に従う。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.branch_iff_output : ∀
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Iff
    (@Yulang.GeneralNominalRecursiveCandidates.BranchModels Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context
      Yulang.GeneralDictionaryRecursiveObstruction.root Yulang.GeneralDictionaryRecursiveObstruction.declaration
      Yulang.GeneralDictionaryRecursiveObstruction.declaration_checked
      (@List.cons.{0}
        (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryRecursiveObstruction.context.state)
        (@Prod.mk.{0, 0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots)
          (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots)
          (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots) (nat_lit 0)
            (@Fin.instOfNat Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots ⋯ (nat_lit 0)))
          (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots) (nat_lit 0)
            (@Fin.instOfNat Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots ⋯ (nat_lit 0))))
        (@List.nil.{0}
          (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryRecursiveObstruction.context.state)))
      model)
    (And (Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryRecursiveObstruction.context.state model)
      (Yulang.CommonNominalFullCarrier.Equivalent
        (@Prod.fst.{0, 0} Yulang.CommonNominalFullCarrier.model.Ty Yulang.CommonNominalFullCarrier.model.Row
          (model (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Yulang.CommonNominalSyntax.Layer.base.{0, 0} Yulang.CommonNominalFullCarrier.Row
          (Yulang.CommonNominalSyntax.State.{0} Yulang.CommonNominalFullCarrier.Row) Yulang.Inference.Base.int)))
```

## Yulang.GeneralDictionaryRecursiveObstruction.instance_output_sound

側: **健全性**。固定 registry・context・root の任意のモデル・key・子列について、具体 Instance が成立するなら、そのモデルの source 1 は宣言の int と同値である。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.instance_output_sound : ∀
  (model : Yulang.GeneralNominalCommonBridge.Assignment) (key : Nat)
  (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)),
  @Yulang.GeneralDictionaryRecursiveEvidence.Instance Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context model
      Yulang.GeneralDictionaryRecursiveObstruction.root key children →
    Yulang.CommonNominalFullCarrier.Equivalent
      (@Prod.fst.{0, 0} Yulang.CommonNominalFullCarrier.model.Ty Yulang.CommonNominalFullCarrier.model.Row
        (model (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Yulang.CommonNominalSyntax.Layer.base.{0, 0} Yulang.CommonNominalFullCarrier.Row
        (Yulang.CommonNominalSyntax.State.{0} Yulang.CommonNominalFullCarrier.Row) Yulang.Inference.Base.int)
```

## Yulang.GeneralDictionaryRecursiveObstruction.bad_not_instance

側: **阻害**。固定反例モデルでは、任意の key と任意の子列について、固定 root の具体 Instance は成立しない。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.bad_not_instance : ∀ (key : Nat)
  (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)),
  Not
    (@Yulang.GeneralDictionaryRecursiveEvidence.Instance Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context
      Yulang.GeneralDictionaryRecursiveObstruction.badModel Yulang.GeneralDictionaryRecursiveObstruction.root key
      children)
```

## Yulang.GeneralDictionaryRecursiveObstruction.evidence_output_sound

側: **健全性**。固定例の任意のモデルについて、node 40 [] に具体 Evidence があれば、そのモデルの source 1 は int と同値である。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.evidence_output_sound : ∀
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  @Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context model
      Yulang.GeneralDictionaryRecursiveObstruction.root
      (Yulang.CommonRoleOutermostResolver.Dictionary.node
        (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
        (@List.nil.{0} Yulang.CommonRoleOutermostResolver.Dictionary)) →
    Yulang.CommonNominalFullCarrier.Equivalent
      (@Prod.fst.{0, 0} Yulang.CommonNominalFullCarrier.model.Ty Yulang.CommonNominalFullCarrier.model.Row
        (model (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Yulang.CommonNominalSyntax.Layer.base.{0, 0} Yulang.CommonNominalFullCarrier.Row
        (Yulang.CommonNominalSyntax.State.{0} Yulang.CommonNominalFullCarrier.Row) Yulang.Inference.Base.int)
```

## Yulang.GeneralDictionaryRecursiveObstruction.evidence_iff_output

側: **健全性**。固定例の任意のモデルについて、node 40 [] の具体 Evidence は「元 context.state の Models と source 1=int」の連言と同値である。欠けている source 制約をこの固定例で正確に特定する。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.evidence_iff_output : ∀
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Iff
    (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context model
      Yulang.GeneralDictionaryRecursiveObstruction.root
      (Yulang.CommonRoleOutermostResolver.Dictionary.node
        (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
        (@List.nil.{0} Yulang.CommonRoleOutermostResolver.Dictionary)))
    (And (Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryRecursiveObstruction.context.state model)
      (Yulang.CommonNominalFullCarrier.Equivalent
        (@Prod.fst.{0, 0} Yulang.CommonNominalFullCarrier.model.Ty Yulang.CommonNominalFullCarrier.model.Row
          (model (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Yulang.CommonNominalSyntax.Layer.base.{0, 0} Yulang.CommonNominalFullCarrier.Row
          (Yulang.CommonNominalSyntax.State.{0} Yulang.CommonNominalFullCarrier.Row) Yulang.Inference.Base.int)))
```

## Yulang.GeneralDictionaryRecursiveObstruction.bad_not_evidence

側: **阻害**。固定反例モデルでは、独立分類が選ぶ node 40 [] に具体 Evidence は成立しない。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.bad_not_evidence : Not
  (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context
    Yulang.GeneralDictionaryRecursiveObstruction.badModel Yulang.GeneralDictionaryRecursiveObstruction.root
    (Yulang.CommonRoleOutermostResolver.Dictionary.node (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
      (@List.nil.{0} Yulang.CommonRoleOutermostResolver.Dictionary)))
```

## Yulang.GeneralDictionaryRecursiveObstruction.good_evidence

側: **健全性**。固定例の int 値を持つ具体モデルでは、同じ node 40 [] に具体 Evidence が成立する。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.good_evidence : @Yulang.GeneralDictionaryRecursiveEvidence.Evidence
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryRecursiveObstruction.registry
  Yulang.GeneralDictionaryRecursiveObstruction.context Yulang.GeneralNominalExamples.model
  Yulang.GeneralDictionaryRecursiveObstruction.root
  (Yulang.CommonRoleOutermostResolver.Dictionary.node (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
    (@List.nil.{0} Yulang.CommonRoleOutermostResolver.Dictionary))
```

## Yulang.GeneralDictionaryRecursiveObstruction.classified

側: **補助**。任意の Remaining に具体 Evidence を注入した boundary でも、固定例の元 context における V3 Classify は node 40 [] を selected と分類する。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.classified : ∀
  (remaining :
    Yulang.GeneralNominalLocalBoundary.Remaining.{0}
      (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles)),
  @Yulang.B4TargetV3.Classify.{0} (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles)
    (Yulang.GeneralDictionaryRecursiveEvidence.boundary Yulang.GeneralDeclarationExamples.roles remaining)
    Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context
    Yulang.GeneralDictionaryRecursiveObstruction.root
    (Yulang.CommonRoleOutermostResolver.Result.selected
      (Yulang.CommonRoleOutermostResolver.Dictionary.node
        (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
        (@List.nil.{0} Yulang.CommonRoleOutermostResolver.Dictionary)))
```

## Yulang.GeneralDictionaryRecursiveObstruction.no_evidenceNode

側: **阻害**。任意の Remaining について、具体 Evidence と変更していない recursiveFields を組み合わせた boundary の全状態向け EvidenceNode は成立しない。Step・Stable・Generated の選び方に依存せず、最終状態への制約反映後の B4 を否定しない。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.no_evidenceNode : ∀
  (remaining :
    Yulang.GeneralNominalLocalBoundary.Remaining.{0}
      (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles)),
  Not
    (@Yulang.B4TargetV3.EvidenceNode.{0}
      (Yulang.GeneralNominalCandidates.vocabulary Yulang.GeneralDeclarationExamples.roles)
      (Yulang.GeneralDictionaryRecursiveEvidence.boundary Yulang.GeneralDeclarationExamples.roles remaining))
```

## Yulang.GeneralDictionaryRecursiveObstruction.concrete_evidence_gap

側: **阻害**。同一の固定辞書 node 40 [] に対し、int モデルでは具体 Evidence があり、別の string 反例モデルは元 Models を満たすが Evidence を持たない。正の証拠と負の証拠がともに実在する。

```lean
Yulang.GeneralDictionaryRecursiveObstruction.concrete_evidence_gap : And
  (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context
    Yulang.GeneralNominalExamples.model Yulang.GeneralDictionaryRecursiveObstruction.root
    (Yulang.CommonRoleOutermostResolver.Dictionary.node (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
      (@List.nil.{0} Yulang.CommonRoleOutermostResolver.Dictionary)))
  (And
    (Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryRecursiveObstruction.context.state
      Yulang.GeneralDictionaryRecursiveObstruction.badModel)
    (Not
      (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context
        Yulang.GeneralDictionaryRecursiveObstruction.badModel Yulang.GeneralDictionaryRecursiveObstruction.root
        (Yulang.CommonRoleOutermostResolver.Dictionary.node
          (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
          (@List.nil.{0} Yulang.CommonRoleOutermostResolver.Dictionary)))))
```

## Yulang.GeneralDictionaryRecursiveOrder.report_reorders

側: **補助**。任意の固定 context・bounds と DeclarationReorders を満たす二宣言について、再帰的 report は厳密に等しい。head が保たれるため where の列挙順に依存しない。

```lean
Yulang.GeneralDictionaryRecursiveOrder.report_reorders : ∀ (context : Yulang.GeneralNominalCandidates.Context)
  (first last : Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralRegistryReordering.DeclarationReorders first last →
    ∀ (bounds : List.{0} (Yulang.GeneralNominalInspection.Bounds context.state)),
      @Eq.{1} (Yulang.GeneralNominalRecursiveInspection.Report context.state)
        (Yulang.GeneralNominalRecursiveCandidates.report context first bounds)
        (Yulang.GeneralNominalRecursiveCandidates.report context last bounds)
```

## Yulang.GeneralDictionaryRecursiveOrder.bindings_reorders

側: **補助**。同じ constructors・roles の任意の二宣言列について、変更後 registry が Checked で両 registry が Reorders を満たすなら、任意の固定 context・root・key の計算済み bindings は等しい。Survivor や lookup 成功は前提にしない。

```lean
Yulang.GeneralDictionaryRecursiveOrder.bindings_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last } →
    Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
        { constructors := constructors, roles := roles, declarations := last } →
      ∀ (context : Yulang.GeneralNominalCandidates.Context) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
        (key : Nat),
        @Eq.{1} Yulang.GeneralNominalAllocation.Bindings
          (Yulang.GeneralDictionaryRecursiveReadback.bindings
            { constructors := constructors, roles := roles, declarations := first } context root key)
          (Yulang.GeneralDictionaryRecursiveReadback.bindings
            { constructors := constructors, roles := roles, declarations := last } context root key)
```

## Yulang.GeneralDictionaryRecursiveOrder.frame_reorders

側: **補助**。同じ constructors・roles の任意の二宣言列について、変更後 registry の Checked と Reorders を前提に、任意の固定 context・root の計算済み frame は等しい。reserved・ownership 列や successor 状態の等しさは主張しない。

```lean
Yulang.GeneralDictionaryRecursiveOrder.frame_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last } →
    Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
        { constructors := constructors, roles := roles, declarations := last } →
      ∀ (context : Yulang.GeneralNominalCandidates.Context) (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
        @Eq.{1}
          (Yulang.GeneralDictionaryEmissionPlans.Frame
            { constructors := constructors, roles := roles, declarations := first }.roles)
          (Yulang.GeneralDictionaryRecursiveReadback.frame
            { constructors := constructors, roles := roles, declarations := first } context root)
          (Yulang.GeneralDictionaryRecursiveReadback.frame
            { constructors := constructors, roles := roles, declarations := last } context root)
```

## Yulang.GeneralDictionaryRecursiveOrder.frames_reorders

側: **補助**。同じ constructors・roles の任意の二宣言列について、変更後 registry の Checked と Reorders を前提に、固定 context 上の全 occurrence に対応する frames 関数は等しい。

```lean
Yulang.GeneralDictionaryRecursiveOrder.frames_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last } →
    Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
        { constructors := constructors, roles := roles, declarations := last } →
      ∀ (context : Yulang.GeneralNominalCandidates.Context),
        @Eq.{1}
          (Yulang.GeneralDictionaryTransactions.Frames
            { constructors := constructors, roles := roles, declarations := first }.roles)
          (Yulang.GeneralDictionaryRecursiveReadback.frames
            { constructors := constructors, roles := roles, declarations := first } context)
          (Yulang.GeneralDictionaryRecursiveReadback.frames
            { constructors := constructors, roles := roles, declarations := last } context)
```

## Yulang.GeneralDictionaryRecursiveOrder.reconstruct_reorders

側: **補助**。同じ constructors・roles の任意の二つの Checked registry が Reorders を満たすなら、任意の固定 context・root・payload に対する再構成の Option 返値は厳密に等しい。最終状態や異なる payload の子順は比較しない。

```lean
Yulang.GeneralDictionaryRecursiveOrder.reconstruct_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (context : Yulang.GeneralNominalCandidates.Context) (payload : Yulang.GeneralDictionaryReadback.Payload)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      @Eq.{1}
        (Option.{0}
          (Yulang.GeneralSourceDictionaries.Dictionary
            { constructors := constructors, roles := roles, declarations := first }.roles))
        (Yulang.GeneralDictionaryRecursiveReadback.reconstruct
          { constructors := constructors, roles := roles, declarations := first } one context payload root)
        (Yulang.GeneralDictionaryRecursiveReadback.reconstruct
          { constructors := constructors, roles := roles, declarations := last } two context payload root)
```

## Yulang.GeneralDictionaryRecursiveOrder.prepare_reorders

側: **補助**。同じ constructors・roles の任意の二つの Checked registry が Reorders を満たすなら、任意の固定 context・root・payload に対する部分 prepare の Option 返値は成功・失敗とも厳密に等しい。一般 materialization の完全性は示していない。

```lean
Yulang.GeneralDictionaryRecursiveOrder.prepare_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (context : Yulang.GeneralNominalCandidates.Context) (payload : Yulang.GeneralDictionaryReadback.Payload)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      @Eq.{1}
        (Option.{0}
          (Yulang.GeneralDictionaryTransactions.Prepared
            { constructors := constructors, roles := roles, declarations := first }.roles context.state.base))
        (Yulang.GeneralDictionaryRecursivePreparation.prepare
          { constructors := constructors, roles := roles, declarations := first } one context payload root)
        (Yulang.GeneralDictionaryRecursivePreparation.prepare
          { constructors := constructors, roles := roles, declarations := last } two context payload root)
```

## Yulang.GeneralDictionaryRecursivePreparation.prepare_candidate_evidence

側: **健全性**。任意の検査済み registry・context・root・payload・prepared tree について、再帰的 Survivor の PayloadEvidence があり、部分 prepare がその tree を返すなら、返された同じ dictionary は全節点の Survivor による indexed Evidence を持つ。

```lean
Yulang.GeneralDictionaryRecursivePreparation.prepare_candidate_evidence : ∀
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (payload : Yulang.GeneralDictionaryReadback.Payload)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles context.state.base),
  @Yulang.GeneralDictionaryReadback.PayloadEvidence registry.roles
      (@Yulang.GeneralNominalRecursiveCandidates.Survivor registry.roles registry context) root payload →
    @Eq.{1} (Option.{0} (Yulang.GeneralDictionaryTransactions.Prepared registry.roles context.state.base))
        (Yulang.GeneralDictionaryRecursivePreparation.prepare registry checked context payload root)
        (@some.{0} (Yulang.GeneralDictionaryTransactions.Prepared registry.roles context.state.base) tree) →
      @Yulang.GeneralSourceDictionaries.Evidence registry.roles
        (@Yulang.GeneralNominalRecursiveCandidates.Survivor registry.roles registry context)
        (@Yulang.GeneralDictionaryTransactions.Prepared.dictionary registry.roles context.state.base tree)
```

## Yulang.GeneralDictionaryRecursivePreparation.prepare_source_evidence

側: **健全性**。任意の検査済み registry・context・root・payload・prepared tree について prepare が成功するなら、transaction を記録した nominal 状態を満たす任意のモデルで、返された同じ dictionary は既存の対応変数限定の宣言 Instance による source Evidence を持つ。元の未記録状態の全モデルは対象にしない。

```lean
Yulang.GeneralDictionaryRecursivePreparation.prepare_source_evidence : ∀
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (payload : Yulang.GeneralDictionaryReadback.Payload)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles context.state.base),
  @Eq.{1} (Option.{0} (Yulang.GeneralDictionaryTransactions.Prepared registry.roles context.state.base))
      (Yulang.GeneralDictionaryRecursivePreparation.prepare registry checked context payload root)
      (@some.{0} (Yulang.GeneralDictionaryTransactions.Prepared registry.roles context.state.base) tree) →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalState.Models
          (@Yulang.GeneralDictionaryNominalRecording.record registry.roles context.state
            (@Yulang.GeneralDictionaryTransactions.Prepared.items registry.roles context.state.base tree))
          model →
        @Yulang.GeneralSourceDictionaries.Evidence registry.roles
          (Yulang.GeneralDictionaryNominalSourceEvidence.Instance registry checked
            (Yulang.GeneralDictionaryRecursiveReadback.frames registry context) model)
          (@Yulang.GeneralDictionaryTransactions.Prepared.dictionary registry.roles context.state.base tree)
```

## Yulang.GeneralDictionaryRecursivePreparation.prepare_uniform_joint

側: **健全性**。任意の検査済み registry・context・root・payload・prepared tree について、候補 PayloadEvidence と prepare 成功があれば、一つの Readback witness が候補 indexed Evidence を持ち、記録済み状態を満たす任意のモデルで元 Models と対応変数限定の宣言 source Evidence も満たす。記録済みモデルの存在や部分 prepare の全域性は結論に含まない。

```lean
Yulang.GeneralDictionaryRecursivePreparation.prepare_uniform_joint : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (payload : Yulang.GeneralDictionaryReadback.Payload)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles context.state.base),
  @Yulang.GeneralDictionaryReadback.PayloadEvidence registry.roles
      (@Yulang.GeneralNominalRecursiveCandidates.Survivor registry.roles registry context) root payload →
    @Eq.{1} (Option.{0} (Yulang.GeneralDictionaryTransactions.Prepared registry.roles context.state.base))
        (Yulang.GeneralDictionaryRecursivePreparation.prepare registry checked context payload root)
        (@some.{0} (Yulang.GeneralDictionaryTransactions.Prepared registry.roles context.state.base) tree) →
      @Exists.{1} (Yulang.GeneralSourceDictionaries.Dictionary registry.roles) fun witness =>
        And (@Yulang.GeneralSourceDictionaries.Readback registry.roles root payload witness)
          (And
            (@Yulang.GeneralSourceDictionaries.Evidence registry.roles
              (@Yulang.GeneralNominalRecursiveCandidates.Survivor registry.roles registry context) witness)
            (∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalState.Models
                  (@Yulang.GeneralDictionaryNominalRecording.record registry.roles context.state
                    (@Yulang.GeneralDictionaryTransactions.Prepared.items registry.roles context.state.base tree))
                  model →
                And (Yulang.GeneralNominalState.Models context.state model)
                  (@Yulang.GeneralSourceDictionaries.Evidence registry.roles
                    (Yulang.GeneralDictionaryNominalSourceEvidence.Instance registry checked
                      (Yulang.GeneralDictionaryRecursiveReadback.frames registry context) model)
                    witness)))
```

## Yulang.GeneralDictionaryRecursiveReadback.bindings_found

側: **補助**。任意の検査済み registry・context・root・key について、対応 key・role の可視宣言と実際の bounds 取得が与えられれば、計算された bindings はその宣言の再帰的 report の bindings と厳密に等しい。

```lean
Yulang.GeneralDictionaryRecursiveReadback.bindings_found : ∀ (registry : Yulang.GeneralDeclarations.Registry),
  Yulang.GeneralDeclarations.Checked registry →
    ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
      (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
      (selected : Yulang.GeneralDeclarations.Declaration),
      @Membership.mem.{0, 0} Yulang.GeneralDeclarations.Declaration (List.{0} Yulang.GeneralDeclarations.Declaration)
          (@List.instMembership.{0} Yulang.GeneralDeclarations.Declaration) registry.declarations selected →
        @Eq.{1} Nat selected.id key →
          @Eq.{1} Nat selected.role
              (@Yulang.GeneralSourceState.Demand.role registry.roles
                (@Yulang.GeneralSourceDictionaries.Occurrence.demand registry.roles root)) →
            ∀ (bounds : List.{0} (Yulang.GeneralNominalInspection.Bounds context.state)),
              @Eq.{1} (Option.{0} (List.{0} (Yulang.GeneralNominalInspection.Bounds context.state)))
                  (@Yulang.GeneralNominalRecursiveCandidates.arguments registry.roles context root)
                  (@some.{0} (List.{0} (Yulang.GeneralNominalInspection.Bounds context.state)) bounds) →
                @Eq.{1} Yulang.GeneralNominalAllocation.Bindings
                  (Yulang.GeneralDictionaryRecursiveReadback.bindings registry context root key)
                  (Yulang.GeneralNominalRecursiveInspection.bindings context.state
                    (Yulang.GeneralNominalRecursiveCandidates.report context selected bounds))
```

## Yulang.GeneralDictionaryRecursiveReadback.survivor_plan

側: **健全性**。任意の検査済み registry・context・root・key・子列について、再帰的 Survivor があれば、完全な子列は caller が frames を渡さずに計算した再帰的 frame の Plan を満たす。

```lean
Yulang.GeneralDictionaryRecursiveReadback.survivor_plan : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)),
  @Yulang.GeneralNominalRecursiveCandidates.Survivor registry.roles registry context root key children →
    Yulang.GeneralDictionaryEmissionPlans.Plan registry checked
      (Yulang.GeneralDictionaryRecursiveReadback.frames registry context root) root key children
```

## Yulang.GeneralDictionaryRecursiveReadback.evidence_plan

側: **健全性**。任意の検査済み registry・context・source 辞書木について、全節点の再帰的 Survivor による indexed Evidence があれば、同じ木は計算済み frames による再構成 Rule の indexed Evidence を持つ。

```lean
Yulang.GeneralDictionaryRecursiveReadback.evidence_plan : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (tree : Yulang.GeneralSourceDictionaries.Dictionary registry.roles),
  @Yulang.GeneralSourceDictionaries.Evidence registry.roles
      (@Yulang.GeneralNominalRecursiveCandidates.Survivor registry.roles registry context) tree →
    @Yulang.GeneralSourceDictionaries.Evidence registry.roles
      (Yulang.GeneralDictionaryPayloadReconstruction.Rule registry checked
        (Yulang.GeneralDictionaryRecursiveReadback.frames registry context))
      tree
```

## Yulang.GeneralDictionaryRecursiveReadback.reconstruct_candidate

側: **完全性**。任意の検査済み registry・context・source 辞書木について、全節点の再帰的 Survivor の indexed Evidence があれば、その木の消去 payload と root から reconstruct は元の木を some として返す。候補証拠木の発見自体は前提に残る。

```lean
Yulang.GeneralDictionaryRecursiveReadback.reconstruct_candidate : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (tree : Yulang.GeneralSourceDictionaries.Dictionary registry.roles),
  @Yulang.GeneralSourceDictionaries.Evidence registry.roles
      (@Yulang.GeneralNominalRecursiveCandidates.Survivor registry.roles registry context) tree →
    @Eq.{1} (Option.{0} (Yulang.GeneralSourceDictionaries.Dictionary registry.roles))
      (Yulang.GeneralDictionaryRecursiveReadback.reconstruct registry checked context
        (@Yulang.GeneralSourceDictionaries.erase registry.roles tree)
        (@Yulang.GeneralSourceDictionaries.Dictionary.root registry.roles tree))
      (@some.{0} (Yulang.GeneralSourceDictionaries.Dictionary registry.roles) tree)
```

## Yulang.GeneralDictionaryRecursiveReadback.payload_candidate_readback

側: **完全性**。任意の検査済み registry・context・root・payload について、再帰的 Survivor の PayloadEvidence があれば、reconstruct が返し、Readback と同じ候補の indexed Evidence を満たす source 木が存在する。

```lean
Yulang.GeneralDictionaryRecursiveReadback.payload_candidate_readback : ∀
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (payload : Yulang.GeneralDictionaryReadback.Payload),
  @Yulang.GeneralDictionaryReadback.PayloadEvidence registry.roles
      (@Yulang.GeneralNominalRecursiveCandidates.Survivor registry.roles registry context) root payload →
    @Exists.{1} (Yulang.GeneralSourceDictionaries.Dictionary registry.roles) fun tree =>
      And
        (@Eq.{1} (Option.{0} (Yulang.GeneralSourceDictionaries.Dictionary registry.roles))
          (Yulang.GeneralDictionaryRecursiveReadback.reconstruct registry checked context payload root)
          (@some.{0} (Yulang.GeneralSourceDictionaries.Dictionary registry.roles) tree))
        (And (@Yulang.GeneralSourceDictionaries.Readback registry.roles root payload tree)
          (@Yulang.GeneralSourceDictionaries.Evidence registry.roles
            (@Yulang.GeneralNominalRecursiveCandidates.Survivor registry.roles registry context) tree))
```

## Yulang.GeneralDictionaryRecursiveReadback.payload_candidate_unique

側: **補助**。任意の検査済み registry・context・root・payload に再帰的 Survivor の PayloadEvidence があれば、再構成された source 木が存在し、同じ root・payload の Readback と候補 indexed Evidence を持つ任意の別木はその木に等しい。

```lean
Yulang.GeneralDictionaryRecursiveReadback.payload_candidate_unique : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (payload : Yulang.GeneralDictionaryReadback.Payload),
  @Yulang.GeneralDictionaryReadback.PayloadEvidence registry.roles
      (@Yulang.GeneralNominalRecursiveCandidates.Survivor registry.roles registry context) root payload →
    @Exists.{1} (Yulang.GeneralSourceDictionaries.Dictionary registry.roles) fun tree =>
      And
        (@Eq.{1} (Option.{0} (Yulang.GeneralSourceDictionaries.Dictionary registry.roles))
          (Yulang.GeneralDictionaryRecursiveReadback.reconstruct registry checked context payload root)
          (@some.{0} (Yulang.GeneralSourceDictionaries.Dictionary registry.roles) tree))
        (And (@Yulang.GeneralSourceDictionaries.Readback registry.roles root payload tree)
          (And
            (@Yulang.GeneralSourceDictionaries.Evidence registry.roles
              (@Yulang.GeneralNominalRecursiveCandidates.Survivor registry.roles registry context) tree)
            (∀ (other : Yulang.GeneralSourceDictionaries.Dictionary registry.roles),
              @Yulang.GeneralSourceDictionaries.Readback registry.roles root payload other →
                @Yulang.GeneralSourceDictionaries.Evidence registry.roles
                    (@Yulang.GeneralNominalRecursiveCandidates.Survivor registry.roles registry context) other →
                  @Eq.{1} (Yulang.GeneralSourceDictionaries.Dictionary registry.roles) other tree)))
```

## Yulang.GeneralDictionaryRecursiveRecordingExamples.output_atoms_exact

側: **補助**。固定例の任意のモデルについて、source 1≤int と int≤source 1 の二つの ordinary atoms を満たすことと、source 1 が int と同値であることは同値である。

```lean
Yulang.GeneralDictionaryRecursiveRecordingExamples.output_atoms_exact : ∀
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Iff
    (@Yulang.PresenceNormalForm.All.{0, 0} Nat Yulang.CommonNominalFullCarrier.model model
      Yulang.GeneralDictionaryRecursiveRecordingExamples.outputAtoms)
    (Yulang.CommonNominalFullCarrier.Equivalent
      (@Prod.fst.{0, 0} Yulang.CommonNominalFullCarrier.model.Ty Yulang.CommonNominalFullCarrier.model.Row
        (model (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Yulang.CommonNominalSyntax.Layer.base.{0, 0} Yulang.CommonNominalFullCarrier.Row
        (Yulang.CommonNominalSyntax.State.{0} Yulang.CommonNominalFullCarrier.Row) Yulang.Inference.Base.int))
```

## Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded_models_exact

側: **健全性**。固定例の任意のモデルについて、二つの出力 atoms を追加した recorded 状態の Models は「元状態の Models と source 1=int」の連言と同値である。全モデルを対象とする厳密な制約追加である。

```lean
Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded_models_exact : ∀
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Iff (Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded model)
    (And (Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryRecursiveObstruction.context.state model)
      (Yulang.CommonNominalFullCarrier.Equivalent
        (@Prod.fst.{0, 0} Yulang.CommonNominalFullCarrier.model.Ty Yulang.CommonNominalFullCarrier.model.Row
          (model (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Yulang.CommonNominalSyntax.Layer.base.{0, 0} Yulang.CommonNominalFullCarrier.Row
          (Yulang.CommonNominalSyntax.State.{0} Yulang.CommonNominalFullCarrier.Row) Yulang.Inference.Base.int)))
```

## Yulang.GeneralDictionaryRecursiveRecordingExamples.good_recorded_model

側: **補助**。固定例の int 値を持つ具体モデルは、出力等式を記録した recorded 状態の Models を満たす。

```lean
Yulang.GeneralDictionaryRecursiveRecordingExamples.good_recorded_model : Yulang.GeneralNominalState.Models
  Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded Yulang.GeneralNominalExamples.model
```

## Yulang.GeneralDictionaryRecursiveRecordingExamples.bad_not_recorded

側: **阻害**。元状態を満たしていた固定 string 反例モデルは、出力等式を記録した recorded 状態の Models を満たさない。

```lean
Yulang.GeneralDictionaryRecursiveRecordingExamples.bad_not_recorded : Not
  (Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded
    Yulang.GeneralDictionaryRecursiveObstruction.badModel)
```

## Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded_strict_nonempty

側: **健全性**。固定 recorded 状態にはモデルが存在し、その任意のモデルは元状態のモデルでもある一方、元状態には recorded を満たさないモデルも存在する。したがって記録は非空かつ真に狭いモデル集合を与える。

```lean
Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded_strict_nonempty : And
  (@Exists.{1} Yulang.GeneralNominalCommonBridge.Assignment fun model =>
    Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded model)
  (And
    (∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded model →
        Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryRecursiveObstruction.context.state model)
    (@Exists.{1} Yulang.GeneralNominalCommonBridge.Assignment fun model =>
      And (Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryRecursiveObstruction.context.state model)
        (Not (Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded model))))
```

## Yulang.GeneralDictionaryRecursiveRecordingExamples.candidate_tree

側: **補助**。固定 sourceTree=node root 40 [] は、変更していない再帰的 Survivor を各節点の判断とする indexed Evidence を持つ。

```lean
Yulang.GeneralDictionaryRecursiveRecordingExamples.candidate_tree : @Yulang.GeneralSourceDictionaries.Evidence
  Yulang.GeneralDeclarationExamples.roles
  (@Yulang.GeneralNominalRecursiveCandidates.Survivor Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context)
  Yulang.GeneralDictionaryRecursiveRecordingExamples.sourceTree
```

## Yulang.GeneralDictionaryRecursiveRecordingExamples.reconstruct_exact

側: **完全性**。固定 nominal head 例の payload node 40 [] と root から、計算済み再帰的 frames の reconstruct は固定 sourceTree を厳密に返す。旧変数限定 materializer の成功は前提にしない。

```lean
Yulang.GeneralDictionaryRecursiveRecordingExamples.reconstruct_exact : @Eq.{1}
  (Option.{0} (Yulang.GeneralSourceDictionaries.Dictionary Yulang.GeneralDictionaryRecursiveObstruction.registry.roles))
  (Yulang.GeneralDictionaryRecursiveReadback.reconstruct Yulang.GeneralDictionaryRecursiveObstruction.registry
    Yulang.GeneralDictionaryRecursiveObstruction.registry_checked Yulang.GeneralDictionaryRecursiveObstruction.context
    (Yulang.CommonRoleOutermostResolver.Dictionary.node (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
      (@List.nil.{0} Yulang.CommonRoleOutermostResolver.Dictionary))
    Yulang.GeneralDictionaryRecursiveObstruction.root)
  (@some.{0} (Yulang.GeneralSourceDictionaries.Dictionary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryRecursiveRecordingExamples.sourceTree)
```

## Yulang.GeneralDictionaryRecursiveRecordingExamples.compound_head_deferred

側: **阻害**。固定例の List a という nominal head について、任意の capture を渡しても、旧変数限定 compileAt は位置0で none を返す。再構成の成功は旧 materialization の全域性を意味しない。

```lean
Yulang.GeneralDictionaryRecursiveRecordingExamples.compound_head_deferred : ∀
  (capture : Yulang.GeneralDeclarationDemands.Capture),
  @Eq.{1}
    (Option.{0}
      (Yulang.Core.PresenceGeneration.TyTerm
        (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots)))
    (Yulang.GeneralDictionaryVariableHeads.compileAt Yulang.GeneralDictionaryRecursiveObstruction.context.state.base
      Yulang.GeneralDictionaryRecursiveObstruction.declaration capture
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@none.{0}
      (Yulang.Core.PresenceGeneration.TyTerm
        (Fin Yulang.GeneralDictionaryRecursiveObstruction.context.state.base.slots)))
```

## Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded_models_iff_evidence

側: **健全性**。固定例の任意のモデルについて、出力等式を追加した recorded 状態の Models と、元 context の固定辞書 node 40 [] の具体 Evidence は同値である。この例では記録した等式が必要十分である。

```lean
Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded_models_iff_evidence : ∀
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Iff (Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded model)
    (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context model
      Yulang.GeneralDictionaryRecursiveObstruction.root
      (Yulang.CommonRoleOutermostResolver.Dictionary.node
        (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
        (@List.nil.{0} Yulang.CommonRoleOutermostResolver.Dictionary)))
```

## Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded_uniform_evidence

側: **健全性**。固定 recorded 状態を満たす任意のモデルで、元 context の同一辞書 node 40 [] に具体 Evidence が成立する。具体的な等式記録の回帰結果であり、一般 Step や飽和 driver の実装ではない。

```lean
Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded_uniform_evidence : ∀
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded model →
    @Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryRecursiveObstruction.registry Yulang.GeneralDictionaryRecursiveObstruction.context model
      Yulang.GeneralDictionaryRecursiveObstruction.root
      (Yulang.CommonRoleOutermostResolver.Dictionary.node
        (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
        (@List.nil.{0} Yulang.CommonRoleOutermostResolver.Dictionary))
```

## Yulang.GeneralDictionaryRecursiveSemanticOrder.generated_reorders

側: **補助**。同じ constructors・roles の任意の二宣言列、固定 context・root・bounds、および DeclarationReorders を満たす検査済み二宣言について、生成 materialization schema は厳密に等しい。宣言列全体の Reorders は前提に不要である。

```lean
Yulang.GeneralDictionaryRecursiveSemanticOrder.generated_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration)
  (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (a b : Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralRegistryReordering.DeclarationReorders a b →
    ∀ (ac : Yulang.GeneralDeclarations.DeclarationChecked constructors roles a)
      (bc : Yulang.GeneralDeclarations.DeclarationChecked constructors roles b)
      (bounds : List.{0} (Yulang.GeneralNominalInspection.Bounds context.state)),
      @Eq.{1} Yulang.GeneralNominalMaterialization.Schema
        (@Yulang.GeneralNominalRecursiveCandidates.generated roles
          { constructors := constructors, roles := roles, declarations := first } context root a ac bounds)
        (@Yulang.GeneralNominalRecursiveCandidates.generated roles
          { constructors := constructors, roles := roles, declarations := last } context root b bc bounds)
```

## Yulang.GeneralDictionaryRecursiveSemanticOrder.branch_reorders

側: **健全性**。同じ constructors・roles の任意の二宣言列、固定 context・root・bounds・指定モデル、および DeclarationReorders を満たす検査済み二宣言について、同じモデルの BranchModels は同値である。存在的な別モデルへ置き換えない。

```lean
Yulang.GeneralDictionaryRecursiveSemanticOrder.branch_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration)
  (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (a b : Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralRegistryReordering.DeclarationReorders a b →
    ∀ (ac : Yulang.GeneralDeclarations.DeclarationChecked constructors roles a)
      (bc : Yulang.GeneralDeclarations.DeclarationChecked constructors roles b)
      (bounds : List.{0} (Yulang.GeneralNominalInspection.Bounds context.state))
      (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Iff
        (@Yulang.GeneralNominalRecursiveCandidates.BranchModels roles
          { constructors := constructors, roles := roles, declarations := first } context root a ac bounds model)
        (@Yulang.GeneralNominalRecursiveCandidates.BranchModels roles
          { constructors := constructors, roles := roles, declarations := last } context root b bc bounds model)
```

## Yulang.GeneralDictionaryRecursiveSemanticOrder.instance_reorders_forward

側: **健全性**。同じ constructors・roles の二つの Checked registry が Reorders を満たすとき、任意の固定 context・モデル・root・key・完全な子列について、変更前の具体 Instance から変更後の同一データの Instance が従う。

```lean
Yulang.GeneralDictionaryRecursiveSemanticOrder.instance_reorders_forward : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first } →
    Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last } →
      Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
          { constructors := constructors, roles := roles, declarations := last } →
        ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
          (model : Yulang.GeneralNominalCommonBridge.Assignment)
          (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
          (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
          @Yulang.GeneralDictionaryRecursiveEvidence.Instance roles
              { constructors := constructors, roles := roles, declarations := first } context model root key children →
            @Yulang.GeneralDictionaryRecursiveEvidence.Instance roles
              { constructors := constructors, roles := roles, declarations := last } context model root key children
```

## Yulang.GeneralDictionaryRecursiveSemanticOrder.instance_reorders

側: **健全性**。同じ constructors・roles の二つの Checked registry が Reorders を満たすとき、任意の固定 context・モデル・root・key・完全な子列の具体 Instance は変更前後で同値である。

```lean
Yulang.GeneralDictionaryRecursiveSemanticOrder.instance_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first } →
    Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last } →
      Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
          { constructors := constructors, roles := roles, declarations := last } →
        ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
          (model : Yulang.GeneralNominalCommonBridge.Assignment)
          (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
          (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
          Iff
            (@Yulang.GeneralDictionaryRecursiveEvidence.Instance roles
              { constructors := constructors, roles := roles, declarations := first } context model root key children)
            (@Yulang.GeneralDictionaryRecursiveEvidence.Instance roles
              { constructors := constructors, roles := roles, declarations := last } context model root key children)
```

## Yulang.GeneralDictionaryRecursiveSemanticOrder.indexed_reorders

側: **健全性**。同じ constructors・roles の二つの Checked registry が Reorders を満たすとき、任意の固定 context・モデル・source 辞書木について、具体 Instance による indexed Evidence は同値であり、木もモデルも変えない。

```lean
Yulang.GeneralDictionaryRecursiveSemanticOrder.indexed_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first } →
    Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last } →
      Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
          { constructors := constructors, roles := roles, declarations := last } →
        ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
          (model : Yulang.GeneralNominalCommonBridge.Assignment)
          (tree : Yulang.GeneralSourceDictionaries.Dictionary roles),
          Iff
            (@Yulang.GeneralSourceDictionaries.Evidence roles
              (@Yulang.GeneralDictionaryRecursiveEvidence.Instance roles
                { constructors := constructors, roles := roles, declarations := first } context model)
              tree)
            (@Yulang.GeneralSourceDictionaries.Evidence roles
              (@Yulang.GeneralDictionaryRecursiveEvidence.Instance roles
                { constructors := constructors, roles := roles, declarations := last } context model)
              tree)
```

## Yulang.GeneralDictionaryRecursiveSemanticOrder.evidence_reorders

側: **健全性**。同じ constructors・roles の二つの Checked registry が Reorders を満たすとき、任意の固定 context・モデル・root・payload の具体 Evidence は変更前後で同値であり、同じ source witness を使える。異なる飽和順の最終状態を比較する B4 の証明ではない。

```lean
Yulang.GeneralDictionaryRecursiveSemanticOrder.evidence_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first } →
    Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last } →
      Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
          { constructors := constructors, roles := roles, declarations := last } →
        ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
          (model : Yulang.GeneralNominalCommonBridge.Assignment)
          (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
          (payload : Yulang.GeneralDictionaryReadback.Payload),
          Iff
            (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence roles
              { constructors := constructors, roles := roles, declarations := first } context model root payload)
            (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence roles
              { constructors := constructors, roles := roles, declarations := last } context model root payload)
```


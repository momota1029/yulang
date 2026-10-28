import YulangClosure.OriginalSourceOwnerReificationTrace

/-! Concrete finite owner-table reification for the executed fixed fixture.
Trace SHA-256: b9a15df005c730db27fc385c58ca07b433f1095f017e0969155106da7478fb0a.
Coordinates are row indices, distinct from Rust provenance ordinals. The
Context, incoming route, ambient scope and runtime frames remain caller inputs.
No universal frontend refinement or whole-language theorem is asserted. -/
namespace YulangClosure.OriginalSourceOwnerReificationInstance

open OriginalSource OriginalSourceEvents OriginalIdentityRealization
open OriginalSourceOwnerReification OriginalSourceOwnerReificationTrace

/-- Indices of every typed key in the frozen emitted table. -/
def coordinates : OriginalCoordinates := {
  physical := fun
    | .definition => 0 | .outerLambda => 1 | .outerBody => 2
    | .application => 3 | .rawCallee => 4 | .argument => 5
    | .innerLambda => 6 | .innerBody => 7 | .sibling => 8
  formal := fun | .outer => 9 | .inner => 10
  wild := fun | .outer => 11 | .inner => 12
  statement := fun | .application => 13
  binding := fun | .value => 14
  name := fun | .declaration => 0 | .outer => 1 | .inner => 2
  declaration := fun | .value => 0 }

theorem coordinates_constructed :
    constructCoordinates originTable = some coordinates := rfl

theorem site_rows (key : SiteKey) :
    originTable.siteKeys[coordinates.site key]? = some key := by
  cases key with
  | physical key => cases key <;> rfl
  | formal key => cases key <;> rfl
  | wild key => cases key <;> rfl
  | statement key => cases key <;> rfl
  | binding key => cases key <;> rfl

theorem name_rows (key : NameKey) :
    (originTable.names.map NameRow.key)[coordinates.name key]? = some key := by
  cases key <;> rfl

theorem declaration_rows (key : DeclarationKey) :
    (originTable.declarations.map DeclarationRow.key)[coordinates.declaration key]? = some key := by
  cases key <;> rfl

theorem coordinate_laws : CoordinateLaws originTable coordinates :=
  coordinate_laws_of_rows originTable coordinates site_rows name_rows declaration_rows

theorem inner_name_source :
    TableToSource originTable coordinates (.name .innerBody .inner)
      ((LocatedExpression.name .innerBody .inner).erase coordinates) := by
  exact TableToSource.name .innerBody .inner
    (originTable.resolutions[1]'(by decide))
    (originTable.physical[7]'(by decide))
    (originTable.formals[1]'(by decide))
    (originTable.names[2]'(by decide))
    (by decide) rfl (by decide) rfl rfl (by decide) rfl (by decide) rfl rfl

theorem argument_source :
    TableToSource originTable coordinates (.name .argument .outer)
      ((LocatedExpression.name .argument .outer).erase coordinates) := by
  exact TableToSource.name .argument .outer
    (originTable.resolutions[0]'(by decide))
    (originTable.physical[5]'(by decide))
    (originTable.formals[0]'(by decide))
    (originTable.names[1]'(by decide))
    (by decide) rfl (by decide) rfl rfl (by decide) rfl (by decide) rfl rfl

theorem sibling_source :
    TableToSource originTable coordinates (.name .sibling .outer)
      ((LocatedExpression.name .sibling .outer).erase coordinates) := by
  exact TableToSource.name .sibling .outer
    (originTable.resolutions[2]'(by decide))
    (originTable.physical[8]'(by decide))
    (originTable.formals[0]'(by decide))
    (originTable.names[1]'(by decide))
    (by decide) rfl (by decide) rfl rfl (by decide) rfl (by decide) rfl rfl

theorem inner_source :
    TableToSource originTable coordinates innerTerm (innerTerm.erase coordinates) := by
  exact TableToSource.lambda .innerLambda .inner .inner .inner _ _
    (originTable.formals[1]'(by decide)) (originTable.wilds[1]'(by decide))
    (originTable.names[2]'(by decide)) (originTable.physical[6]'(by decide))
    (by decide) rfl (by decide) rfl rfl (by decide) rfl rfl
    (by decide) rfl rfl inner_name_source

theorem grouped_inner_source :
    TableToSource originTable coordinates (.group .rawCallee .innerLambda innerTerm)
      (innerTerm.erase coordinates) := by
  exact TableToSource.group .rawCallee .innerLambda innerTerm _
    (originTable.groups[0]'(by decide)) (originTable.physical[4]'(by decide))
    (by decide) rfl (by decide) rfl rfl rfl inner_source

theorem application_table_source :
    TableToSource originTable coordinates applicationTerm
      (applicationTerm.erase coordinates) := by
  exact TableToSource.app .application _ _ _ _
    (originTable.physical[3]'(by decide)) (by decide) rfl
    grouped_inner_source argument_source

theorem body_source :
    TableToSource originTable coordinates bodyTerm (bodyTerm.erase coordinates) := by
  exact TableToSource.block .outerBody .application _ _ _ _
    (originTable.physical[2]'(by decide)) (originTable.statements[0]'(by decide))
    (by decide) rfl (by decide) rfl rfl rfl rfl rfl
    application_table_source sibling_source

theorem fixture_source :
    TableToSource originTable coordinates fixtureTerm (fixtureTerm.erase coordinates) := by
  exact TableToSource.lambda .outerLambda .outer .outer .outer _ _
    (originTable.formals[0]'(by decide)) (originTable.wilds[0]'(by decide))
    (originTable.names[1]'(by decide)) (originTable.physical[1]'(by decide))
    (by decide) rfl (by decide) rfl rfl (by decide) rfl rfl
    (by decide) rfl rfl body_source

theorem declaration_source :
    TableToDeclaration originTable coordinates .value fixtureTerm
      (bindingSource coordinates) := by
  exact TableToDeclaration.binding .value .declaration fixtureTerm _
    (originTable.declarations[0]'(by decide)) (originTable.physical[0]'(by decide))
    (originTable.names[0]'(by decide))
    (by decide) rfl (by decide) rfl (by decide) rfl rfl fixture_source

/-- The emitted table explicitly leaves caller preparation unobserved. -/
theorem caller_context_unobserved : originTable.callerContext = none := rfl

theorem realized_inner_owner_available (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry) :
    (innerOwnerQuery coordinates rootContext rootRoute rootAmbient).isSome = true :=
  OriginalSourceOwnerReification.inner_owner_available coordinates rootContext rootRoute rootAmbient

theorem realized_local_ambient_kinds (rootContext : Context)
    (rootRoute : Route) :
    (localAmbient coordinates rootContext rootRoute).map (fun entry => entry.binder.kind) =
      [.description, .viewLogic, .invocation, .receipt, .returnRebind, .shared,
       .eventProof, .viewLogic] :=
  OriginalSourceOwnerReification.local_ambient_kinds coordinates rootContext rootRoute

theorem realized_target_invocation_binder (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry) :
    (innerOwner coordinates rootContext rootRoute rootAmbient).binder =
      ⟨coordinates.physical .innerLambda, .invocation, 0⟩ :=
  OriginalSourceOwnerReification.target_invocation_binder coordinates rootContext rootRoute rootAmbient

theorem realized_identity_source (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry) :
    (innerIdentity coordinates rootContext rootRoute rootAmbient).parameter.source =
      innerTerm.erase coordinates :=
  OriginalSourceOwnerReification.identity_source coordinates rootContext rootRoute rootAmbient

theorem realized_identity_registration (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry) :
    (sourceEntries (innerContext coordinates rootContext)
      (innerTerm.erase coordinates)).head? =
      some (innerIdentity coordinates rootContext rootRoute rootAmbient).parameter.registration :=
  OriginalSourceOwnerReification.identity_registration coordinates rootContext rootRoute rootAmbient

theorem realized_identity_body_binding (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry) :
    lookupBinding (OriginalFormalShared.bodyContext
      (innerIdentity coordinates rootContext rootRoute rootAmbient).parameter)
      (coordinates.name .inner) =
      some ({name := coordinates.name .inner, owner := coordinates.formal .inner, kind := .formal, entry := some .value, singleUse := true} : Binding) :=
  OriginalSourceOwnerReification.identity_body_binding coordinates rootContext rootRoute rootAmbient

theorem realized_application_source (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry) :
    applicationTerm.erase coordinates =
      .app ⟨coordinates.physical .application, none⟩
        (innerIdentity coordinates rootContext rootRoute rootAmbient).parameter.source
        (argumentTerm.erase coordinates) :=
  OriginalSourceOwnerReification.application_source coordinates rootContext rootRoute rootAmbient

theorem realized_application_owners (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry) :
    OriginalSourceEnvironment.sourceCallOwners (innerContext coordinates rootContext)
      (applicationTerm.erase coordinates) =
      .application (coordinates.physical .application) (innerContext coordinates rootContext)
        (coordinates.physical .innerLambda) (coordinates.physical .argument) ::
      (OriginalSourceEnvironment.sourceCallOwners (innerContext coordinates rootContext)
        (innerIdentity coordinates rootContext rootRoute rootAmbient).parameter.source ++
       OriginalSourceEnvironment.sourceCallOwners (innerContext coordinates rootContext)
        (argumentTerm.erase coordinates)) :=
  OriginalSourceOwnerReification.application_owners coordinates rootContext rootRoute rootAmbient

theorem realized_identity_invocation_owner (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry) :
    (sourceOwners (innerContext coordinates rootContext) (innerTerm.erase coordinates)).head? =
      some (lambdaInvocationOwner (coordinates.physical .innerLambda)
        (innerIdentity coordinates rootContext rootRoute rootAmbient).parameter.formal) :=
  OriginalSourceOwnerReification.identity_invocation_owner coordinates rootContext rootRoute rootAmbient

theorem realized_target_scope_from_root (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry) :
    (innerOwner coordinates rootContext rootRoute rootAmbient).telescope =
      (innerIdentity coordinates rootContext rootRoute rootAmbient).ambient ++
        (innerOwner coordinates rootContext rootRoute rootAmbient).telescope.drop
          ((innerOwner coordinates rootContext rootRoute rootAmbient).telescope.length - 2) :=
  OriginalSourceOwnerReification.target_scope_from_root coordinates rootContext rootRoute rootAmbient

theorem realized_introduction_scope_binders {s : OriginalSourceInterpretation.Sorts} {View : Type}
    (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry)
    (frames : ∀ entry, entry ∈
      (innerIdentity coordinates rootContext rootRoute rootAmbient).ambient →
        OwnedFrame s View entry) :
    (introduction coordinates rootContext rootRoute rootAmbient frames).telescope.frames.map Frame.binder =
      (innerIdentity coordinates rootContext rootRoute rootAmbient).ambient.map ScopeEntry.binder :=
  OriginalSourceOwnerReification.introduction_scope_binders coordinates rootContext rootRoute rootAmbient frames

/-- The concrete inner tree is the same source consumed by Identity. -/
theorem table_to_identity_source (rootContext : Context) (rootRoute : Route)
    (rootAmbient : List ScopeEntry) :
    TableToSource originTable coordinates innerTerm
      (innerIdentity coordinates rootContext rootRoute rootAmbient).parameter.source := by
  rw [realized_identity_source]
  exact inner_source

/-- The concrete application relation and the accepted Identity equation share
one constructed coordinate map and the original full argument. -/
theorem table_to_application_source (rootContext : Context) (rootRoute : Route)
    (rootAmbient : List ScopeEntry) :
    TableToSource originTable coordinates applicationTerm
      (.app ⟨coordinates.physical .application, none⟩
        (innerIdentity coordinates rootContext rootRoute rootAmbient).parameter.source
        (argumentTerm.erase coordinates)) := by
  rw [← realized_application_source]
  exact application_table_source

end YulangClosure.OriginalSourceOwnerReificationInstance

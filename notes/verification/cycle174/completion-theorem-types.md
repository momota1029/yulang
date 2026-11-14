# Cycle174 final declaration types

153 named declarations (including definitions), 125 named theorems; these are not 125 general B4 theorems.

```text
Yulang.GeneralDictionaryAgreedBounded174.runFuel.{u_1} {Request : Type u_1}
  (protocol : Yulang.CommonRoleOutermostResolver.Protocol.{u_1} Request) :
  Nat → Request → Yulang.CommonRoleOutermostResolver.Tree
Yulang.GeneralDictionaryAgreedBounded174.runFuel_resolves.{u_1} {Request : Type u_1}
  (protocol : Yulang.CommonRoleOutermostResolver.Protocol.{u_1} Request)
  (exact : Yulang.CommonRoleOutermostResolver.FrontierExact.{u_1} protocol) (rank : Request → Nat)
  (decreases :
    ∀ {child parent : Request},
      Yulang.CommonRoleOutermostResolver.Child.{u_1} (Yulang.CommonRoleOutermostResolver.Protocol.Local.{u_1} protocol)
          child parent →
        LT.lt.{0} (rank child) (rank parent))
  (fuel : Nat) (request : Request) (enough : LT.lt.{0} (rank request) fuel) :
  Yulang.CommonRoleOutermostResolver.Resolves.{u_1} (Yulang.CommonRoleOutermostResolver.Protocol.Local.{u_1} protocol)
    request (Yulang.GeneralDictionaryAgreedBounded174.runFuel.{u_1} protocol fuel request)
Yulang.GeneralDictionaryAgreedBounded174.certified_resolves {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (passed : Eq.{1} (Yulang.GeneralDictionaryAgreedUniform174.certify registry) true)
  (exact :
    Yulang.CommonRoleOutermostResolver.FrontierExact.{0}
      (Yulang.GeneralNominalActualAgreedBoundary.frontiers defer gap registry state)) :
  Yulang.CommonRoleOutermostResolver.Resolves.{0}
    (Yulang.CommonRoleOutermostResolver.Protocol.Local.{0}
      (Yulang.GeneralNominalActualAgreedBoundary.frontiers defer gap registry state))
    root
    (Yulang.GeneralDictionaryAgreedBounded174.runFuel.{0}
      (Yulang.GeneralNominalActualAgreedBoundary.frontiers defer gap registry state)
      (HAdd.hAdd.{0, 0, 0} (List.length.{0} (Yulang.GeneralDictionaryAgreedUniform174.roleNodes registry)) 1) root)
Yulang.GeneralDictionaryAgreedBounded174.certified_final_eq {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (checked :
    Yulang.B4Target.SourceBoundary.Checked.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
      registry)
  (passed : Eq.{1} (Yulang.GeneralDictionaryAgreedUniform174.certify registry) true)
  (reachable :
    Yulang.B4TargetV5.Reachable.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state) :
  Eq.{1}
    (Yulang.GeneralDictionaryAgreedBounded174.runFuel.{0}
      (Yulang.GeneralNominalActualAgreedBoundary.frontiers defer gap registry
        (Prod.fst.{0, 0}
          (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry
            state root)))
      (HAdd.hAdd.{0, 0, 0} (List.length.{0} (Yulang.GeneralDictionaryAgreedUniform174.roleNodes registry)) 1) root)
    (Prod.snd.{0, 0}
      (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry state
        root))
Yulang.GeneralDictionaryAgreedChecked174.run_resolves_iff {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {fuel : Nat}
  (checked :
    Yulang.B4Target.SourceBoundary.Checked.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
      registry)
  (passed : Eq.{1} (Yulang.GeneralDictionaryAgreedComputed174.check registry fuel) true)
  (reachable :
    Yulang.B4TargetV5.Reachable.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state)
  (tree : Yulang.CommonRoleOutermostResolver.Tree) :
  Eq.{1}
      (Prod.snd.{0, 0}
        (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry state
          root))
      tree ↔
    Yulang.CommonRoleOutermostResolver.Resolves.{0}
      (Yulang.B4TargetV3.Local.{0}
        (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
          (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
        registry
        (Prod.fst.{0, 0}
          (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry
            state root)))
      root tree
Yulang.GeneralDictionaryAgreedChecked174.completed_iff {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {fuel : Nat}
  (checked :
    Yulang.B4Target.SourceBoundary.Checked.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
      registry)
  (passed : Eq.{1} (Yulang.GeneralDictionaryAgreedComputed174.check registry fuel) true)
  (reachable :
    Yulang.B4TargetV5.Reachable.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state)
  (out : Yulang.CommonRoleOutermostResolver.Result) :
  Yulang.B4TargetV3.Completed
      (Prod.snd.{0, 0}
        (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry state
          root))
      out ↔
    Yulang.B4TargetV3.Classify.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
      registry
      (Prod.fst.{0, 0}
        (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry state
          root))
      root out
Yulang.GeneralDictionaryAgreedChecked174.initial_run_resolves_iff {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {fuel : Nat}
  (checked :
    Yulang.B4Target.SourceBoundary.Checked.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
      registry)
  (passed : Eq.{1} (Yulang.GeneralDictionaryAgreedComputed174.check registry fuel) true)
  (initial :
    Yulang.B4TargetV5.SourceBoundary.Initial.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry
      root state)
  (tree : Yulang.CommonRoleOutermostResolver.Tree) :
  Eq.{1}
      (Prod.snd.{0, 0}
        (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry state
          root))
      tree ↔
    Yulang.CommonRoleOutermostResolver.Resolves.{0}
      (Yulang.B4TargetV3.Local.{0}
        (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
          (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
        registry
        (Prod.fst.{0, 0}
          (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry
            state root)))
      root tree
Yulang.GeneralDictionaryAgreedChecked174.accepted_fuels_same_spec {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {fuel : Nat}
  (checked :
    Yulang.B4Target.SourceBoundary.Checked.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
      registry)
  (passed : Eq.{1} (Yulang.GeneralDictionaryAgreedComputed174.check registry fuel) true)
  (reachable :
    Yulang.B4TargetV5.Reachable.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state)
  (tree : Yulang.CommonRoleOutermostResolver.Tree) :
  (Exists.{1} fun otherFuel =>
      Eq.{1} (Yulang.GeneralDictionaryAgreedComputed174.check registry otherFuel) true ∧
        Eq.{1}
          (Prod.snd.{0, 0}
            (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry
              state root))
          tree) ↔
    Yulang.CommonRoleOutermostResolver.Resolves.{0}
      (Yulang.B4TargetV3.Local.{0}
        (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
          (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
        registry
        (Prod.fst.{0, 0}
          (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry
            state root)))
      root tree
Yulang.GeneralDictionaryAgreedComposition174.Remaining {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles) : Prop
Yulang.GeneralDictionaryAgreedComposition174.policy_at {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles}
  (rest : Yulang.GeneralDictionaryAgreedComposition174.Remaining defer gap)
  (registry : Yulang.GeneralDeclarations.Registry)
  (checked :
    Yulang.B4Target.SourceBoundary.Checked.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
      registry)
  (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (reachable :
    Yulang.B4TargetV5.Reachable.{0} (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap) registry root state)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles) : Eq.{1} defer true ∨ ¬gap registry state focus
Yulang.GeneralDictionaryAgreedComposition174.evidenceNode {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles}
  (rest : Yulang.GeneralDictionaryAgreedComposition174.Remaining defer gap) :
  Yulang.B4SkeletonV5.EvidenceNode.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap)
Yulang.GeneralDictionaryAgreedComposition174.generatedChildren {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles}
  (rest : Yulang.GeneralDictionaryAgreedComposition174.Remaining defer gap) :
  Yulang.B4SkeletonV5.GeneratedChildren.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap)
Yulang.GeneralDictionaryAgreedComposition174.generatedChildren_pending {roles : Yulang.Roles.RoleDecls}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} :
  Yulang.B4SkeletonV5.GeneratedChildren.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary true gap)
Yulang.GeneralDictionaryAgreedComposition174.bridges {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles)
  (rest : Yulang.GeneralDictionaryAgreedComposition174.Remaining defer gap) :
  Yulang.B4SkeletonV5.B4Bridges.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap)
    (Yulang.GeneralDictionaryAgreedGround174.executor defer gap)
    (Yulang.GeneralNominalActualAgreedBoundary.frontiers defer gap)
Yulang.GeneralDictionaryAgreedComposition174.statement {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles)
  (rest : Yulang.GeneralDictionaryAgreedComposition174.Remaining defer gap) :
  Yulang.B4TargetV5.Statement.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap)
    (Yulang.GeneralDictionaryAgreedGround174.executor defer gap)
Yulang.GeneralDictionaryAgreedComputed174.childRoles (registry : Yulang.GeneralDeclarations.Registry) (role : Nat) :
  List.{0} Nat
Yulang.GeneralDictionaryAgreedComputed174.computedHeight (registry : Yulang.GeneralDeclarations.Registry) :
  Nat → Nat → Nat
Yulang.GeneralDictionaryAgreedComputed174.check (registry : Yulang.GeneralDeclarations.Registry) (fuel : Nat) : Bool
Yulang.GeneralDictionaryAgreedComputed174.check_iff (registry : Yulang.GeneralDeclarations.Registry) (fuel : Nat) :
  Eq.{1} (Yulang.GeneralDictionaryAgreedComputed174.check registry fuel) true ↔
    Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry
      (Yulang.GeneralDictionaryAgreedComputed174.computedHeight registry fuel)
Yulang.GeneralDictionaryAgreedComputed174.check_sound {registry : Yulang.GeneralDeclarations.Registry} {fuel : Nat}
  (passed : Eq.{1} (Yulang.GeneralDictionaryAgreedComputed174.check registry fuel) true) :
  Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry
    (Yulang.GeneralDictionaryAgreedComputed174.computedHeight registry fuel)
Yulang.GeneralDictionaryAgreedComputed174.checked_whereAccessible {registry : Yulang.GeneralDeclarations.Registry}
  {fuel : Nat} {roles : Yulang.Roles.RoleDecls}
  (passed : Eq.{1} (Yulang.GeneralDictionaryAgreedComputed174.check registry fuel) true) (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) :
  Acc.{1}
    (Yulang.CommonRoleOutermostResolver.Child.{0}
      (Yulang.B4TargetV3.Local.{0}
        (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
          (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
        registry state))
    root
Yulang.GeneralDictionaryAgreedComputed174.mem_childRoles {registry : Yulang.GeneralDeclarations.Registry}
  {role child : Nat} :
  Membership.mem.{0, 0} (Yulang.GeneralDictionaryAgreedComputed174.childRoles registry role) child ↔
    Exists.{1} fun declaration =>
      Membership.mem.{0, 0} registry.declarations declaration ∧
        Eq.{1} declaration.role role ∧
          Exists.{1} fun clause => Membership.mem.{0, 0} declaration.requirements clause ∧ Eq.{1} clause.role child
Yulang.GeneralDictionaryAgreedComputed174.child_rank_lt {registry : Yulang.GeneralDeclarations.Registry}
  {rank : Nat → Nat} {role child : Nat}
  (stratified : Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank)
  (present : Membership.mem.{0, 0} (Yulang.GeneralDictionaryAgreedComputed174.childRoles registry role) child) :
  LT.lt.{0} (rank child) (rank role)
Yulang.GeneralDictionaryAgreedComputed174.height_stabilizes {registry : Yulang.GeneralDeclarations.Registry}
  {rank : Nat → Nat} (stratified : Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank)
  (role a b : Nat) :
  LE.le.{0} (rank role) a →
    LE.le.{0} (rank role) b →
      Eq.{1} (Yulang.GeneralDictionaryAgreedComputed174.computedHeight registry a role)
        (Yulang.GeneralDictionaryAgreedComputed174.computedHeight registry b role)
Yulang.GeneralDictionaryAgreedComputed174.check_complete {registry : Yulang.GeneralDeclarations.Registry}
  {rank : Nat → Nat} {fuel : Nat} (stratified : Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank)
  (large :
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      Membership.mem.{0, 0} registry.declarations declaration → LE.le.{0} (rank declaration.role) fuel) :
  Eq.{1} (Yulang.GeneralDictionaryAgreedComputed174.check registry fuel) true
Yulang.GeneralDictionaryAgreedComputed174.rankBudget (registry : Yulang.GeneralDeclarations.Registry)
  (rank : Nat → Nat) : Nat
Yulang.GeneralDictionaryAgreedComputed174.check_complete_budget {registry : Yulang.GeneralDeclarations.Registry}
  {rank : Nat → Nat} (stratified : Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank) :
  Eq.{1}
    (Yulang.GeneralDictionaryAgreedComputed174.check registry
      (Yulang.GeneralDictionaryAgreedComputed174.rankBudget registry rank))
    true
Yulang.GeneralDictionaryAgreedComputed174.exists_check_iff {registry : Yulang.GeneralDeclarations.Registry} :
  (Exists.{1} fun fuel => Eq.{1} (Yulang.GeneralDictionaryAgreedComputed174.check registry fuel) true) ↔
    Exists.{1} fun rank => Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank
Yulang.GeneralDictionaryAgreedComputed174.check_of_leaves {registry : Yulang.GeneralDeclarations.Registry}
  (leaves :
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      Membership.mem.{0, 0} registry.declarations declaration → Eq.{1} declaration.requirements List.nil.{0})
  (fuel : Nat) : Eq.{1} (Yulang.GeneralDictionaryAgreedComputed174.check registry fuel) true
Yulang.GeneralDictionaryAgreedComputed174.wrap_zero_false :
  Eq.{1} (Yulang.GeneralDictionaryAgreedComputed174.check Yulang.GeneralDictionaryAgreedRoleExamples174.wrapOnly 0)
    false
Yulang.GeneralDictionaryAgreedComputed174.wrap_computed :
  Eq.{1} (Yulang.GeneralDictionaryAgreedComputed174.check Yulang.GeneralDictionaryAgreedRoleExamples174.wrapOnly 1) true
Yulang.GeneralDictionaryAgreedComputed174.display_fails (fuel : Nat) :
  Eq.{1} (Yulang.GeneralDictionaryAgreedComputed174.check Yulang.GeneralDeclarationExamples.registry fuel) false
Yulang.GeneralDictionaryAgreedEdge174.RoleStratified (registry : Yulang.GeneralDeclarations.Registry)
  (rank : Nat → Nat) : Prop
Yulang.GeneralDictionaryAgreedEdge174.selected_child_role {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles}
  {parent : Yulang.B4Target.Vocabulary.Demand.{0} (Yulang.GeneralNominalActualAgreedLocal.vocabulary roles)} {key : Nat}
  {children :
    List.{0} (Yulang.B4Target.Vocabulary.Demand.{0} (Yulang.GeneralNominalActualAgreedLocal.vocabulary roles))}
  {child : Yulang.B4Target.Vocabulary.Demand.{0} (Yulang.GeneralNominalActualAgreedLocal.vocabulary roles)}
  (selected :
    Yulang.GeneralNominalActualAgreedLocal.Local defer gap registry state parent
      (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} key children))
  (member : Membership.mem.{0, 0} children child) :
  Exists.{1} fun declaration =>
    Membership.mem.{0, 0} registry.declarations declaration ∧
      Exists.{1} fun clause =>
        Membership.mem.{0, 0} declaration.requirements clause ∧
          Eq.{1} declaration.role parent.demand.role ∧ Eq.{1} clause.role child.demand.role
Yulang.GeneralDictionaryAgreedEdge174.child_role_decreases {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {rank : Nat → Nat}
  {child parent : Yulang.B4Target.Vocabulary.Demand.{0} (Yulang.GeneralNominalActualAgreedLocal.vocabulary roles)}
  (stratified : Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank)
  (edge :
    Yulang.CommonRoleOutermostResolver.Child.{0} (Yulang.GeneralNominalActualAgreedLocal.Local defer gap registry state)
      child parent) :
  LT.lt.{0} (rank child.demand.role) (rank parent.demand.role)
Yulang.GeneralDictionaryAgreedEdge174.whereAccessible {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {rank : Nat → Nat}
  (stratified : Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) :
  Acc.{1}
    (Yulang.CommonRoleOutermostResolver.Child.{0}
      (Yulang.GeneralNominalActualAgreedLocal.Local defer gap registry state))
    root
Yulang.GeneralDictionaryAgreedEdge174.boundary_whereAccessible {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {rank : Nat → Nat}
  (stratified : Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) :
  Acc.{1}
    (Yulang.CommonRoleOutermostResolver.Child.{0}
      (Yulang.B4TargetV3.Local.{0}
        (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
          (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
        registry state))
    root
Yulang.GeneralDictionaryAgreedEdge174.leaves_stratified {registry : Yulang.GeneralDeclarations.Registry}
  (leaves :
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      Membership.mem.{0, 0} registry.declarations declaration → Eq.{1} declaration.requirements List.nil.{0}) :
  Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry fun x => 0
Yulang.GeneralDictionaryAgreedEdge174.leaf_whereAccessible {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles}
  (leaves :
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      Membership.mem.{0, 0} registry.declarations declaration → Eq.{1} declaration.requirements List.nil.{0})
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) :
  Acc.{1}
    (Yulang.CommonRoleOutermostResolver.Child.{0}
      (Yulang.B4TargetV3.Local.{0}
        (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
          (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
        registry state))
    root
Yulang.GeneralDictionaryAgreedEdge174.stratified_reorders {registry other : Yulang.GeneralDeclarations.Registry}
  {rank : Nat → Nat} (order : Yulang.GeneralRegistryReordering.Reorders registry other)
  (stratified : Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank) :
  Yulang.GeneralDictionaryAgreedEdge174.RoleStratified other rank
Yulang.GeneralDictionaryAgreedEdge174.Descent {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles) (registry : Yulang.GeneralDeclarations.Registry)
  (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles) :
  Nat → Yulang.GeneralSourceDictionaries.Occurrence roles → Prop
Yulang.GeneralDictionaryAgreedEdge174.descent_bounded {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {rank : Nat → Nat}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles} {depth : Nat}
  {child : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (stratified : Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank)
  (path : Yulang.GeneralDictionaryAgreedEdge174.Descent defer gap registry state root depth child) :
  LE.le.{0} (HAdd.hAdd.{0, 0, 0} depth (rank child.demand.role)) (rank root.demand.role)
Yulang.GeneralDictionaryAgreedEvidence174.RecordedExtensions {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSupport.Tracked roles) : Prop
Yulang.GeneralDictionaryAgreedEvidence174.selected_instance {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {key : Nat}
  {children :
    List.{0} (Yulang.B4Target.Vocabulary.Demand.{0} (Yulang.GeneralNominalActualAgreedLocal.vocabulary roles))}
  (formed : Yulang.GeneralNominalActualInspectionSteps.SourceFormed registry root state)
  (growth : Yulang.GeneralDictionaryAgreedEvidence174.RecordedExtensions state)
  (policy : Eq.{1} defer true ∨ ¬gap registry state focus)
  (stable :
    Yulang.B4Target.SourceBoundary.Stable.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
      registry state focus)
  (selected :
    Yulang.GeneralNominalActualAgreedLocal.Local defer gap registry state focus
      (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} key children))
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid : Yulang.GeneralNominalSaturationState.Models state.current model) :
  Yulang.GeneralDictionaryRecursiveEvidence.Instance registry state.current.context model focus key children
Yulang.GeneralDictionaryAgreedEvidence174.selected_evidence {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {key : Nat}
  {children :
    List.{0} (Yulang.B4Target.Vocabulary.Demand.{0} (Yulang.GeneralNominalActualAgreedLocal.vocabulary roles))}
  (formed : Yulang.GeneralNominalActualInspectionSteps.SourceFormed registry root state)
  (growth : Yulang.GeneralDictionaryAgreedEvidence174.RecordedExtensions state)
  (policy : Eq.{1} defer true ∨ ¬gap registry state focus)
  (stable :
    Yulang.B4Target.SourceBoundary.Stable.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
      registry state focus)
  (selected :
    Yulang.GeneralNominalActualAgreedLocal.Local defer gap registry state focus
      (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} key children))
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid : Yulang.GeneralNominalSaturationState.Models state.current model)
  (dictionaries : List.{0} Yulang.GeneralDictionaryReadback.Payload)
  (given :
    Yulang.CommonRoleOutermostResolver.All₂.{0, 0}
      (Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model) children dictionaries) :
  Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model focus
    (Yulang.CommonRoleOutermostResolver.Dictionary.node key dictionaries)
Yulang.GeneralDictionaryAgreedEvidence174.ReachableRecordedExtensions {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles) : Prop
Yulang.GeneralDictionaryAgreedEvidence174.evidenceNode_of_policy {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles}
  (growth : Yulang.GeneralDictionaryAgreedEvidence174.ReachableRecordedExtensions defer gap)
  (policy :
    ∀ (registry : Yulang.B4Target.Vocabulary.Registry.{0} (Yulang.GeneralNominalActualAgreedBoundary.vocabulary roles)),
      Yulang.B4Target.SourceBoundary.Checked.{0}
          (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
            (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
          registry →
        ∀ (state : Yulang.B4Target.Vocabulary.State.{0} (Yulang.GeneralNominalActualAgreedBoundary.vocabulary roles))
          (root : Yulang.B4Target.Vocabulary.Demand.{0} (Yulang.GeneralNominalActualAgreedBoundary.vocabulary roles)),
          Yulang.B4TargetV5.Reachable.{0} (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap) registry root
              state →
            ∀ (demand : Yulang.GeneralSourceDictionaries.Occurrence roles),
              Eq.{1} defer true ∨ ¬gap registry state demand) :
  Yulang.B4SkeletonV5.EvidenceNode.{0} (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap)
Yulang.GeneralDictionaryAgreedEvidence174.evidenceNode_pending {roles : Yulang.Roles.RoleDecls}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles}
  (growth : Yulang.GeneralDictionaryAgreedEvidence174.ReachableRecordedExtensions true gap) :
  Yulang.B4SkeletonV5.EvidenceNode.{0} (Yulang.GeneralNominalActualAgreedBoundary.boundary true gap)
Yulang.GeneralDictionaryAgreedEvidence174.evidenceNode_complete {roles : Yulang.Roles.RoleDecls}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles}
  (growth : Yulang.GeneralDictionaryAgreedEvidence174.ReachableRecordedExtensions false gap)
  (complete : Yulang.GeneralNominalActualAgreedBoundary.GapFree gap) :
  Yulang.B4SkeletonV5.EvidenceNode.{0} (Yulang.GeneralNominalActualAgreedBoundary.boundary false gap)
Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryAt {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (before : Yulang.GeneralNominalSupport.Tracked roles) :
  Yulang.GeneralSourceDictionaries.Occurrence roles → Yulang.GeneralNominalSupport.Tracked roles → Prop
Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryStep {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSupport.Tracked roles) : Prop
Yulang.GeneralDictionaryAgreedEvidence174.ordinary_at_actual {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSupport.Tracked roles}
  (action : Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryAt registry before focus after) :
  Yulang.GeneralNominalActualInspectionSteps.At registry before focus after
Yulang.GeneralDictionaryAgreedEvidence174.ordinary_step_actual {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSupport.Tracked roles}
  (step : Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryStep registry root before after) :
  Yulang.GeneralNominalActualInspectionSteps.Step registry root before after
Yulang.GeneralDictionaryAgreedEvidence174.ordinary_at_extension {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSupport.Tracked roles}
  (action : Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryAt registry before focus after) :
  Yulang.GeneralDictionaryOrdinaryTrace.Extension before.current.context after.current.context
Yulang.GeneralDictionaryAgreedEvidence174.ordinary_steps_actual {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSupport.Tracked roles}
  (path :
    Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryStep registry root) before after) :
  Yulang.B4Target.Steps.{1} (Yulang.GeneralNominalActualInspectionSteps.Step registry root) before after
Yulang.GeneralDictionaryAgreedEvidence174.ordinary_packets_extension {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSupport.Tracked roles}
  (old : Yulang.GeneralDictionaryAgreedEvidence174.RecordedExtensions before)
  (path :
    Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryStep registry root) before after) :
  Yulang.GeneralDictionaryAgreedEvidence174.RecordedExtensions after
Yulang.GeneralDictionaryAgreedEvidence174.ordinary_initial_extensions {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles} (context : Yulang.GeneralNominalCandidates.Context)
  (path :
    Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryStep registry root)
      (Yulang.GeneralNominalSupport.initial context root) state) :
  Yulang.GeneralDictionaryAgreedEvidence174.RecordedExtensions state
Yulang.GeneralDictionaryAgreedEvidence174.ordinary_initial_formed {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles} (context : Yulang.GeneralNominalCandidates.Context)
  (source : Yulang.GeneralNominalSourceFormation.InitialSource registry context root)
  (path :
    Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryStep registry root)
      (Yulang.GeneralNominalSupport.initial context root) state) :
  Yulang.GeneralNominalActualInspectionSteps.SourceFormed registry root state
Yulang.GeneralDictionaryAgreedEvidence174.ordinary_initial_selected_evidence {roles : Yulang.Roles.RoleDecls}
  {defer : Bool} {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles}
  {root focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {children :
    List.{0} (Yulang.B4Target.Vocabulary.Demand.{0} (Yulang.GeneralNominalActualAgreedLocal.vocabulary roles))}
  (context : Yulang.GeneralNominalCandidates.Context)
  (source : Yulang.GeneralNominalSourceFormation.InitialSource registry context root)
  (path :
    Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryStep registry root)
      (Yulang.GeneralNominalSupport.initial context root) state)
  (policy : Eq.{1} defer true ∨ ¬gap registry state focus)
  (stable :
    Yulang.B4Target.SourceBoundary.Stable.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
      registry state focus)
  (selected :
    Yulang.GeneralNominalActualAgreedLocal.Local defer gap registry state focus
      (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} key children))
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid : Yulang.GeneralNominalSaturationState.Models state.current model)
  (dictionaries : List.{0} Yulang.GeneralDictionaryReadback.Payload)
  (given :
    Yulang.CommonRoleOutermostResolver.All₂.{0, 0}
      (Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model) children dictionaries) :
  Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model focus
    (Yulang.CommonRoleOutermostResolver.Dictionary.node key dictionaries)
Yulang.GeneralDictionaryAgreedEvidence174.selected_child_generated {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {key : Nat}
  {children :
    List.{0} (Yulang.B4Target.Vocabulary.Demand.{0} (Yulang.GeneralNominalActualAgreedBoundary.vocabulary roles))}
  {child : Yulang.B4Target.Vocabulary.Demand.{0} (Yulang.GeneralNominalActualAgreedBoundary.vocabulary roles)}
  (policy : Eq.{1} defer true ∨ ¬gap registry state focus)
  (stable :
    Yulang.B4Target.SourceBoundary.Stable.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
      registry state focus)
  (selected :
    Yulang.B4TargetV3.Local.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
      registry state focus (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} key children))
  (reached : Eq.{1} focus root ∨ Yulang.GeneralNominalSaturationState.Generated state.current root focus)
  (member : Membership.mem.{0, 0} children child) :
  Yulang.GeneralNominalSaturationState.Generated state.current root child
Yulang.GeneralDictionaryAgreedEvidence174.dictionary_evidence_snapshot {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (formed : Yulang.GeneralNominalActualInspectionSteps.SourceFormed registry root state)
  (growth : Yulang.GeneralDictionaryAgreedEvidence174.RecordedExtensions state)
  (policy :
    ∀ (demand : Yulang.GeneralSourceDictionaries.Occurrence roles), Eq.{1} defer true ∨ ¬gap registry state demand)
  (rootStable :
    Yulang.B4Target.SourceBoundary.Stable.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
      registry state root)
  (generatedStable :
    ∀ (demand : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.GeneralNominalSaturationState.Generated state.current root demand →
        Yulang.B4Target.SourceBoundary.Stable.{0}
          (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
            (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
          registry state demand)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid : Yulang.GeneralNominalSaturationState.Models state.current model)
  (dictionary : Yulang.GeneralDictionaryReadback.Payload) (focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (reached : Eq.{1} focus root ∨ Yulang.GeneralNominalSaturationState.Generated state.current root focus)
  (derived :
    Yulang.B4TargetV3.Classify.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
      registry state focus (Yulang.CommonRoleOutermostResolver.Result.selected dictionary)) :
  Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model focus dictionary
Yulang.GeneralDictionaryAgreedEvidence174.dictionaries_evidence_snapshot {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (formed : Yulang.GeneralNominalActualInspectionSteps.SourceFormed registry root state)
  (growth : Yulang.GeneralDictionaryAgreedEvidence174.RecordedExtensions state)
  (policy :
    ∀ (demand : Yulang.GeneralSourceDictionaries.Occurrence roles), Eq.{1} defer true ∨ ¬gap registry state demand)
  (rootStable :
    Yulang.B4Target.SourceBoundary.Stable.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
      registry state root)
  (generatedStable :
    ∀ (demand : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.GeneralNominalSaturationState.Generated state.current root demand →
        Yulang.B4Target.SourceBoundary.Stable.{0}
          (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
            (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
          registry state demand)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid : Yulang.GeneralNominalSaturationState.Models state.current model)
  (dictionaries : List.{0} Yulang.GeneralDictionaryReadback.Payload)
  (demands : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles))
  (reached :
    ∀ (child : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Membership.mem.{0, 0} demands child →
        Eq.{1} child root ∨ Yulang.GeneralNominalSaturationState.Generated state.current root child)
  (derived :
    Yulang.CommonRoleOutermostResolver.All₂.{0, 0}
      (fun child dictionary =>
        Yulang.B4TargetV3.Classify.{0}
          (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
            (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
          registry state child (Yulang.CommonRoleOutermostResolver.Result.selected dictionary))
      demands dictionaries) :
  Yulang.CommonRoleOutermostResolver.All₂.{0, 0}
    (Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model) demands dictionaries
Yulang.GeneralDictionaryAgreedEvidence174.ordinary_initial_dictionary_evidence {roles : Yulang.Roles.RoleDecls}
  {defer : Bool} {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles} (context : Yulang.GeneralNominalCandidates.Context)
  (source : Yulang.GeneralNominalSourceFormation.InitialSource registry context root)
  (path :
    Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryStep registry root)
      (Yulang.GeneralNominalSupport.initial context root) state)
  (policy :
    ∀ (demand : Yulang.GeneralSourceDictionaries.Occurrence roles), Eq.{1} defer true ∨ ¬gap registry state demand)
  (rootStable :
    Yulang.B4Target.SourceBoundary.Stable.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
      registry state root)
  (generatedStable :
    ∀ (demand : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.GeneralNominalSaturationState.Generated state.current root demand →
        Yulang.B4Target.SourceBoundary.Stable.{0}
          (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
            (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
          registry state demand)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid : Yulang.GeneralNominalSaturationState.Models state.current model)
  (dictionary : Yulang.GeneralDictionaryReadback.Payload)
  (derived :
    Yulang.B4TargetV3.Classify.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
      registry state root (Yulang.CommonRoleOutermostResolver.Result.selected dictionary)) :
  Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model root dictionary
Yulang.GeneralDictionaryAgreedEvidence174.ordinary_halted_dictionary_evidence {roles : Yulang.Roles.RoleDecls}
  {defer : Bool} {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSupport.Tracked roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (checked :
    Yulang.B4Target.SourceBoundary.Checked.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
      registry)
  (context : Yulang.GeneralNominalCandidates.Context)
  (source : Yulang.GeneralNominalSourceFormation.InitialSource registry context root)
  (path :
    Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryStep registry root)
      (Yulang.GeneralNominalSupport.initial context root) state)
  (halted :
    ∀ (after : Yulang.GeneralNominalSupport.Tracked roles),
      ¬Yulang.GeneralNominalActualInspectionSteps.Step registry root state after)
  (policy :
    ∀ (demand : Yulang.GeneralSourceDictionaries.Occurrence roles), Eq.{1} defer true ∨ ¬gap registry state demand)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid : Yulang.GeneralNominalSaturationState.Models state.current model)
  (dictionary : Yulang.GeneralDictionaryReadback.Payload)
  (derived :
    Yulang.B4TargetV3.Classify.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
      registry state root (Yulang.CommonRoleOutermostResolver.Result.selected dictionary)) :
  Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model root dictionary
Yulang.GeneralDictionaryAgreedExact174.frontiers {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles) :
  Yulang.B4SkeletonV3.Frontiers.{0} (Yulang.GeneralNominalActualAgreedBoundary.vocabulary roles)
Yulang.GeneralDictionaryAgreedExact174.final_reachable {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (checked :
    Yulang.B4Target.SourceBoundary.Checked.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
      registry)
  (reachable :
    Yulang.B4TargetV5.Reachable.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state) :
  Yulang.B4TargetV5.Reachable.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root
    (Prod.fst.{0, 0}
      (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry state
        root))
Yulang.GeneralDictionaryAgreedExact174.final_exact {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (checked :
    Yulang.B4Target.SourceBoundary.Checked.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
      registry)
  (reachable :
    Yulang.B4TargetV5.Reachable.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state) :
  Yulang.CommonRoleOutermostResolver.FrontierExact.{0}
    (Yulang.GeneralDictionaryAgreedExact174.frontiers defer gap registry
      (Prod.fst.{0, 0}
        (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry state
          root)))
Yulang.GeneralDictionaryAgreedExact174.run_resolves_iff {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {rank : Nat → Nat}
  (checked :
    Yulang.B4Target.SourceBoundary.Checked.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
      registry)
  (stratified : Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank)
  (reachable :
    Yulang.B4TargetV5.Reachable.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state)
  (tree : Yulang.CommonRoleOutermostResolver.Tree) :
  Eq.{1}
      (Prod.snd.{0, 0}
        (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry state
          root))
      tree ↔
    Yulang.CommonRoleOutermostResolver.Resolves.{0}
      (Yulang.B4TargetV3.Local.{0}
        (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
          (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
        registry
        (Prod.fst.{0, 0}
          (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry
            state root)))
      root tree
Yulang.GeneralDictionaryAgreedExact174.completed_iff {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {rank : Nat → Nat}
  (checked :
    Yulang.B4Target.SourceBoundary.Checked.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
      registry)
  (stratified : Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank)
  (reachable :
    Yulang.B4TargetV5.Reachable.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state)
  (out : Yulang.CommonRoleOutermostResolver.Result) :
  Yulang.B4TargetV3.Completed
      (Prod.snd.{0, 0}
        (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry state
          root))
      out ↔
    Yulang.B4TargetV3.Classify.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
      registry
      (Prod.fst.{0, 0}
        (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry state
          root))
      root out
Yulang.GeneralDictionaryAgreedExact174.initial_run_resolves_iff {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {rank : Nat → Nat}
  (checked :
    Yulang.B4Target.SourceBoundary.Checked.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
      registry)
  (stratified : Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank)
  (initial :
    Yulang.B4TargetV5.SourceBoundary.Initial.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry
      root state)
  (tree : Yulang.CommonRoleOutermostResolver.Tree) :
  Eq.{1}
      (Prod.snd.{0, 0}
        (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry state
          root))
      tree ↔
    Yulang.CommonRoleOutermostResolver.Resolves.{0}
      (Yulang.B4TargetV3.Local.{0}
        (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
          (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
        registry
        (Prod.fst.{0, 0}
          (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry
            state root)))
      root tree
Yulang.GeneralDictionaryAgreedGround174.boundary {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles) :
  Yulang.B4TargetV5.SourceBoundary.{0} (Yulang.GeneralNominalActualBoundary.vocabulary roles)
Yulang.GeneralDictionaryAgreedGround174.reachable_old {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.B4Target.Vocabulary.Registry.{0} (Yulang.GeneralNominalActualBoundary.vocabulary roles)}
  {root : Yulang.B4Target.Vocabulary.Demand.{0} (Yulang.GeneralNominalActualBoundary.vocabulary roles)}
  {state : Yulang.B4Target.Vocabulary.State.{0} (Yulang.GeneralNominalActualBoundary.vocabulary roles)} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles}
  (h :
    Yulang.B4TargetV5.Reachable.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state) :
  Yulang.B4TargetV5.Reachable.{0} (Yulang.GeneralNominalActualBoundary.groundBoundary roles) registry root state
Yulang.GeneralDictionaryAgreedGround174.reachable_agreed {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.B4Target.Vocabulary.Registry.{0} (Yulang.GeneralNominalActualBoundary.vocabulary roles)}
  {root : Yulang.B4Target.Vocabulary.Demand.{0} (Yulang.GeneralNominalActualBoundary.vocabulary roles)}
  {state : Yulang.B4Target.Vocabulary.State.{0} (Yulang.GeneralNominalActualBoundary.vocabulary roles)} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles}
  (h :
    Yulang.B4TargetV5.Reachable.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state) :
  Yulang.B4TargetV5.Reachable.{0} (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap) registry root state
Yulang.GeneralDictionaryAgreedGround174.progress {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles) (registry : Yulang.GeneralDeclarations.Registry)
  (checked :
    Yulang.B4Target.SourceBoundary.Checked.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
      registry)
  (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (reachable :
    Yulang.B4TargetV5.Reachable.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state) :
  Acc.{1}
    (fun next current =>
      Yulang.B4Target.SourceBoundary.Step.{0}
        (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
          (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
        registry root current next)
    state
Yulang.GeneralDictionaryAgreedGround174.diagnostic {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles) (registry : Yulang.GeneralDeclarations.Registry)
  (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles) :
  Yulang.CommonRoleOutermostResolver.Tree
Yulang.GeneralDictionaryAgreedGround174.diagnostic_eq_resolve {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles) (registry : Yulang.GeneralDeclarations.Registry)
  (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (exact :
    Yulang.CommonRoleOutermostResolver.FrontierExact.{0}
      (Yulang.GeneralNominalActualAgreedBoundary.frontiers defer gap registry state))
  (accessible :
    Acc.{1}
      (Yulang.CommonRoleOutermostResolver.Child.{0}
        (Yulang.CommonRoleOutermostResolver.Protocol.Local.{0}
          (Yulang.GeneralNominalActualAgreedBoundary.frontiers defer gap registry state)))
      root) :
  Eq.{1} (Yulang.GeneralDictionaryAgreedGround174.diagnostic defer gap registry state root)
    (Yulang.CommonRoleOutermostResolver.resolve.{0}
      (Yulang.GeneralNominalActualAgreedBoundary.frontiers defer gap registry state) exact root accessible)
Yulang.GeneralDictionaryAgreedGround174.executor {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles) :
  Yulang.B4TargetV3.Executor.{0} (Yulang.GeneralNominalActualBoundary.vocabulary roles)
Yulang.GeneralDictionaryAgreedGround174.execution {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles) (registry : Yulang.GeneralDeclarations.Registry)
  (checked :
    Yulang.B4Target.SourceBoundary.Checked.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
      registry)
  (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (reachable :
    Yulang.B4TargetV5.Reachable.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state) :
  Yulang.B4Target.Steps.{1}
    (Yulang.B4Target.SourceBoundary.Step.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
      registry root)
    state
    (Prod.fst.{0, 0}
      (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry state
        root))
Yulang.GeneralDictionaryAgreedGround174.halted {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles) (registry : Yulang.GeneralDeclarations.Registry)
  (checked :
    Yulang.B4Target.SourceBoundary.Checked.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
      registry)
  (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (reachable :
    Yulang.B4TargetV5.Reachable.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state)
  (next : Yulang.B4Target.Vocabulary.State.{0} (Yulang.GeneralNominalActualBoundary.vocabulary roles)) :
  ¬Yulang.B4Target.SourceBoundary.Step.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
      registry root
      (Prod.fst.{0, 0}
        (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry state
          root))
      next
Yulang.GeneralDictionaryAgreedGround174.treeExecution {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles) (registry : Yulang.GeneralDeclarations.Registry)
  (_checked :
    Yulang.B4Target.SourceBoundary.Checked.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
      registry)
  (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (_reachable :
    Yulang.B4TargetV5.Reachable.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state)
  (exact :
    Yulang.CommonRoleOutermostResolver.FrontierExact.{0}
      (Yulang.GeneralNominalActualAgreedBoundary.frontiers defer gap registry
        (Prod.fst.{0, 0}
          (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry
            state root))))
  (accessible :
    Acc.{1}
      (Yulang.CommonRoleOutermostResolver.Child.{0}
        (Yulang.CommonRoleOutermostResolver.Protocol.Local.{0}
          (Yulang.GeneralNominalActualAgreedBoundary.frontiers defer gap registry
            (Prod.fst.{0, 0}
              (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry
                state root)))))
      root) :
  Eq.{1}
    (Prod.snd.{0, 0}
      (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry state
        root))
    (Yulang.CommonRoleOutermostResolver.resolve.{0}
      (Yulang.GeneralNominalActualAgreedBoundary.frontiers defer gap registry
        (Prod.fst.{0, 0}
          (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry
            state root)))
      exact root accessible)
Yulang.GeneralDictionaryAgreedGround174.saturationTotal {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles) :
  Yulang.B4TargetV5.SaturationTotal.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap)
    (Yulang.GeneralDictionaryAgreedGround174.executor defer gap)
Yulang.GeneralDictionaryAgreedGround174.initialReorders {roles : Yulang.Roles.RoleDecls} (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles)
  (registry other : Yulang.GeneralDeclarations.Registry)
  (order :
    Yulang.B4Target.SourceBoundary.Reorders.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
      registry other)
  (state : Yulang.GeneralNominalSupport.Tracked roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (given :
    Yulang.B4TargetV5.SourceBoundary.Initial.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry
      root state) :
  Yulang.B4TargetV5.SourceBoundary.Initial.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) other root
    state
Yulang.GeneralDictionaryAgreedHistoryObstruction174.extension_known
  {before after : Yulang.GeneralNominalCandidates.Context}
  (growth : Yulang.GeneralDictionaryOrdinaryTrace.Extension before after) (source : Nat) :
  Yulang.GeneralNominalState.Known after.state source ↔ Yulang.GeneralNominalState.Known before.state source
Yulang.GeneralDictionaryAgreedHistoryObstruction174.refresh_not_extension {source : Nat}
  {before after : Yulang.GeneralNominalCandidates.Context}
  (unknown : ¬Yulang.GeneralNominalState.Known before.state source)
  (known : Yulang.GeneralNominalState.Known after.state source) :
  ¬Yulang.GeneralDictionaryOrdinaryTrace.Extension before after
Yulang.GeneralDictionaryAgreedHistoryObstruction174.historical_refresh_not_extension
  {history before : Yulang.GeneralNominalCandidates.Context} {source : Nat}
  {after : Yulang.GeneralNominalCandidates.Context}
  (old : Yulang.GeneralDictionaryOrdinaryTrace.Extension history before)
  (unknown : ¬Yulang.GeneralNominalState.Known before.state source)
  (known : Yulang.GeneralNominalState.Known after.state source) :
  ¬Yulang.GeneralDictionaryOrdinaryTrace.Extension history after
Yulang.GeneralDictionaryAgreedHistoryObstruction174.PointIndex (context : Yulang.GeneralNominalCandidates.Context)
  (index : Nat) : Prop
Yulang.GeneralDictionaryAgreedHistoryObstruction174.extension_point
  {before after : Yulang.GeneralNominalCandidates.Context}
  (growth : Yulang.GeneralDictionaryOrdinaryTrace.Extension before after) (index : Nat) :
  Yulang.GeneralDictionaryAgreedHistoryObstruction174.PointIndex after index ↔
    Yulang.GeneralDictionaryAgreedHistoryObstruction174.PointIndex before index
Yulang.GeneralDictionaryAgreedHistoryObstruction174.revision_not_extension {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles}
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state)
  (improved : Yulang.GeneralNominalReobservationSteps.Improves revision) :
  ¬Yulang.GeneralDictionaryOrdinaryTrace.Extension state.context revision.result.context
Yulang.GeneralDictionaryAgreedHistoryObstruction174.historical_revision_not_extension
  {history : Yulang.GeneralNominalCandidates.Context} {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles}
  (old : Yulang.GeneralDictionaryOrdinaryTrace.Extension history state.context)
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state)
  (improved : Yulang.GeneralNominalReobservationSteps.Improves revision) :
  ¬Yulang.GeneralDictionaryOrdinaryTrace.Extension history revision.result.context
Yulang.GeneralDictionaryAgreedHistoryObstruction174.recorded_refresh_failure {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSupport.Tracked roles)
  (old : Yulang.GeneralDictionaryAgreedEvidence174.RecordedExtensions state)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (member : Membership.mem.{0, 0} state.current.packets packet) (context : Yulang.GeneralNominalCandidates.Context)
  (source : Nat) (unknown : ¬Yulang.GeneralNominalState.Known state.current.context.state source)
  (known : Yulang.GeneralNominalState.Known context.state source) :
  ¬Yulang.GeneralDictionaryAgreedEvidence174.RecordedExtensions
      { source := state.source, current := Yulang.GeneralNominalSaturationState.regenerate state.current context,
        facts := state.facts }
Yulang.GeneralDictionaryAgreedHistoryObstruction174.recorded_revision_failure {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSupport.Tracked roles)
  (old : Yulang.GeneralDictionaryAgreedEvidence174.RecordedExtensions state)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (member : Membership.mem.{0, 0} state.current.packets packet)
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state.current)
  (improved : Yulang.GeneralNominalReobservationSteps.Improves revision) :
  ¬Yulang.GeneralDictionaryAgreedEvidence174.RecordedExtensions
      { source := state.source, current := revision.result, facts := state.facts }
Yulang.GeneralDictionaryAgreedRefiningTrace174.At {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (before : Yulang.GeneralNominalSupport.Tracked roles) :
  Yulang.GeneralSourceDictionaries.Occurrence roles → Yulang.GeneralNominalSupport.Tracked roles → Prop
Yulang.GeneralDictionaryAgreedRefiningTrace174.Step {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSupport.Tracked roles) : Prop
Yulang.GeneralDictionaryAgreedRefiningTrace174.at_actual {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSupport.Tracked roles}
  (action : Yulang.GeneralDictionaryAgreedRefiningTrace174.At registry before focus after) :
  Yulang.GeneralNominalActualInspectionSteps.At registry before focus after
Yulang.GeneralDictionaryAgreedRefiningTrace174.step_actual {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSupport.Tracked roles}
  (step : Yulang.GeneralDictionaryAgreedRefiningTrace174.Step registry root before after) :
  Yulang.GeneralNominalActualInspectionSteps.Step registry root before after
Yulang.GeneralDictionaryAgreedRefiningTrace174.steps_actual {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSupport.Tracked roles}
  (path : Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionaryAgreedRefiningTrace174.Step registry root) before after) :
  Yulang.B4Target.Steps.{1} (Yulang.GeneralNominalActualInspectionSteps.Step registry root) before after
Yulang.GeneralDictionaryAgreedRefiningTrace174.step_models {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSupport.Tracked roles}
  (step : Yulang.GeneralDictionaryAgreedRefiningTrace174.Step registry root before after)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid : Yulang.GeneralNominalSaturationState.Models after.current model) :
  Yulang.GeneralNominalSaturationState.Models before.current model
Yulang.GeneralDictionaryAgreedRefiningTrace174.step_formed {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSupport.Tracked roles}
  (formed : Yulang.GeneralNominalActualInspectionSteps.SourceFormed registry root before)
  (step : Yulang.GeneralDictionaryAgreedRefiningTrace174.Step registry root before after) :
  Yulang.GeneralNominalActualInspectionSteps.SourceFormed registry root after
Yulang.GeneralDictionaryAgreedRefiningTrace174.at_instance {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSupport.Tracked roles}
  (action : Yulang.GeneralDictionaryAgreedRefiningTrace174.At registry before focus after)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid : Yulang.GeneralNominalSaturationState.Models after.current model)
  (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
  (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles))
  (old :
    Yulang.GeneralDictionaryRecursiveEvidence.Instance registry before.current.context model occurrence key children) :
  Yulang.GeneralDictionaryRecursiveEvidence.Instance registry after.current.context model occurrence key children
Yulang.GeneralDictionaryAgreedRefiningTrace174.RecordedCurrent {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles) : Prop
Yulang.GeneralDictionaryAgreedRefiningTrace174.step_recorded {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSupport.Tracked roles}
  (formed : Yulang.GeneralNominalActualInspectionSteps.SourceFormed registry root before)
  (old : Yulang.GeneralDictionaryAgreedRefiningTrace174.RecordedCurrent registry before)
  (step : Yulang.GeneralDictionaryAgreedRefiningTrace174.Step registry root before after) :
  Yulang.GeneralDictionaryAgreedRefiningTrace174.RecordedCurrent registry after
Yulang.GeneralDictionaryAgreedRefiningTrace174.initial_recorded {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (context : Yulang.GeneralNominalCandidates.Context) :
  Yulang.GeneralDictionaryAgreedRefiningTrace174.RecordedCurrent registry
    (Yulang.GeneralNominalSupport.initial context root)
Yulang.GeneralDictionaryAgreedRefiningTrace174.trace_formed_recorded {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSupport.Tracked roles}
  (formed : Yulang.GeneralNominalActualInspectionSteps.SourceFormed registry root before)
  (old : Yulang.GeneralDictionaryAgreedRefiningTrace174.RecordedCurrent registry before)
  (path : Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionaryAgreedRefiningTrace174.Step registry root) before after) :
  Yulang.GeneralNominalActualInspectionSteps.SourceFormed registry root after ∧
    Yulang.GeneralDictionaryAgreedRefiningTrace174.RecordedCurrent registry after
Yulang.GeneralDictionaryAgreedRefiningTrace174.initial_trace_recorded {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {after : Yulang.GeneralNominalSupport.Tracked roles} (context : Yulang.GeneralNominalCandidates.Context)
  (source : Yulang.GeneralNominalSourceFormation.InitialSource registry context root)
  (path :
    Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionaryAgreedRefiningTrace174.Step registry root)
      (Yulang.GeneralNominalSupport.initial context root) after) :
  Yulang.GeneralDictionaryAgreedRefiningTrace174.RecordedCurrent registry after
Yulang.GeneralDictionaryAgreedRefiningTrace174.initial_trace_instance {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {after : Yulang.GeneralNominalSupport.Tracked roles} (context : Yulang.GeneralNominalCandidates.Context)
  (source : Yulang.GeneralNominalSourceFormation.InitialSource registry context root)
  (path :
    Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionaryAgreedRefiningTrace174.Step registry root)
      (Yulang.GeneralNominalSupport.initial context root) after)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (member : Membership.mem.{0, 0} after.current.packets packet) (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid : Yulang.GeneralNominalSaturationState.Models after.current model) :
  Yulang.GeneralDictionaryRecursiveEvidence.Instance registry after.current.context model packet.site.occurrence
    packet.declaration.id packet.children
Yulang.GeneralDictionaryAgreedRefiningTrace174.initial_trace_evidence {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {after : Yulang.GeneralNominalSupport.Tracked roles} (context : Yulang.GeneralNominalCandidates.Context)
  (source : Yulang.GeneralNominalSourceFormation.InitialSource registry context root)
  (path :
    Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionaryAgreedRefiningTrace174.Step registry root)
      (Yulang.GeneralNominalSupport.initial context root) after)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (member : Membership.mem.{0, 0} after.current.packets packet) (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid : Yulang.GeneralNominalSaturationState.Models after.current model)
  (dictionaries : List.{0} Yulang.GeneralDictionaryReadback.Payload)
  (given :
    Yulang.CommonRoleOutermostResolver.All₂.{0, 0}
      (Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry after.current.context model) packet.children
      dictionaries) :
  Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry after.current.context model packet.site.occurrence
    (Yulang.CommonRoleOutermostResolver.Dictionary.node packet.declaration.id dictionaries)
Yulang.GeneralDictionaryAgreedRefiningTrace174.initial_trace_selected_instance {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {after : Yulang.GeneralNominalSupport.Tracked roles} {key : Nat}
  {children :
    List.{0} (Yulang.B4Target.Vocabulary.Demand.{0} (Yulang.GeneralNominalActualAgreedLocal.vocabulary roles))}
  (context : Yulang.GeneralNominalCandidates.Context)
  (source : Yulang.GeneralNominalSourceFormation.InitialSource registry context root)
  (path :
    Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionaryAgreedRefiningTrace174.Step registry root)
      (Yulang.GeneralNominalSupport.initial context root) after)
  {defer : Bool} {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles}
  (policy : Eq.{1} defer true ∨ ¬gap registry after focus)
  (stable :
    Yulang.B4Target.SourceBoundary.Stable.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
      registry after focus)
  (selected :
    Yulang.GeneralNominalActualAgreedLocal.Local defer gap registry after focus
      (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} key children))
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid : Yulang.GeneralNominalSaturationState.Models after.current model) :
  Yulang.GeneralDictionaryRecursiveEvidence.Instance registry after.current.context model focus key children
Yulang.GeneralDictionaryAgreedRefiningTrace174.initial_trace_selected_evidence {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {after : Yulang.GeneralNominalSupport.Tracked roles} {key : Nat}
  {children :
    List.{0} (Yulang.B4Target.Vocabulary.Demand.{0} (Yulang.GeneralNominalActualAgreedLocal.vocabulary roles))}
  (context : Yulang.GeneralNominalCandidates.Context)
  (source : Yulang.GeneralNominalSourceFormation.InitialSource registry context root)
  (path :
    Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionaryAgreedRefiningTrace174.Step registry root)
      (Yulang.GeneralNominalSupport.initial context root) after)
  {defer : Bool} {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles}
  (policy : Eq.{1} defer true ∨ ¬gap registry after focus)
  (stable :
    Yulang.B4Target.SourceBoundary.Stable.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
      registry after focus)
  (selected :
    Yulang.GeneralNominalActualAgreedLocal.Local defer gap registry after focus
      (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} key children))
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid : Yulang.GeneralNominalSaturationState.Models after.current model)
  (dictionaries : List.{0} Yulang.GeneralDictionaryReadback.Payload)
  (given :
    Yulang.CommonRoleOutermostResolver.All₂.{0, 0}
      (Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry after.current.context model) children dictionaries) :
  Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry after.current.context model focus
    (Yulang.CommonRoleOutermostResolver.Dictionary.node key dictionaries)
Yulang.GeneralDictionaryAgreedRefresh174.refreshed {roles : Yulang.Roles.RoleDecls}
  (before : Yulang.GeneralNominalSupport.Tracked roles)
  (next : Yulang.GeneralDictionaryInspectionTransport.Observation before.current.context.state) :
  Yulang.GeneralNominalSupport.Tracked roles
Yulang.GeneralDictionaryAgreedRefresh174.recorded_instance {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (before : Yulang.GeneralNominalSupport.Tracked roles)
  (formed : Yulang.GeneralNominalActualInspectionSteps.SourceFormed registry root before)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (member : Membership.mem.{0, 0} before.current.packets packet)
  (growth : Yulang.GeneralDictionaryOrdinaryTrace.Extension packet.context before.current.context)
  (next : Yulang.GeneralDictionaryInspectionTransport.Observation before.current.context.state)
  (view : Eq.{1} next.view before.current.context.state.view)
  (certificate :
    Yulang.GeneralNominalCycleSteps.Refresh before.current
      (Yulang.GeneralDictionaryInspectionTransport.reobserve before.current.context next))
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid :
    Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralDictionaryAgreedRefresh174.refreshed before next).current
      model) :
  Yulang.GeneralDictionaryRecursiveEvidence.Instance registry
    (Yulang.GeneralDictionaryAgreedRefresh174.refreshed before next).current.context model packet.site.occurrence
    packet.declaration.id packet.children
Yulang.GeneralDictionaryAgreedRefresh174.recorded_evidence {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (before : Yulang.GeneralNominalSupport.Tracked roles)
  (formed : Yulang.GeneralNominalActualInspectionSteps.SourceFormed registry root before)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (member : Membership.mem.{0, 0} before.current.packets packet)
  (growth : Yulang.GeneralDictionaryOrdinaryTrace.Extension packet.context before.current.context)
  (next : Yulang.GeneralDictionaryInspectionTransport.Observation before.current.context.state)
  (view : Eq.{1} next.view before.current.context.state.view)
  (certificate :
    Yulang.GeneralNominalCycleSteps.Refresh before.current
      (Yulang.GeneralDictionaryInspectionTransport.reobserve before.current.context next))
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid :
    Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralDictionaryAgreedRefresh174.refreshed before next).current
      model)
  (dictionaries : List.{0} Yulang.GeneralDictionaryReadback.Payload)
  (given :
    Yulang.CommonRoleOutermostResolver.All₂.{0, 0}
      (Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry
        (Yulang.GeneralDictionaryAgreedRefresh174.refreshed before next).current.context model)
      packet.children dictionaries) :
  Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry
    (Yulang.GeneralDictionaryAgreedRefresh174.refreshed before next).current.context model packet.site.occurrence
    (Yulang.CommonRoleOutermostResolver.Dictionary.node packet.declaration.id dictionaries)
Yulang.GeneralDictionaryAgreedRefresh174.actual_step {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (before : Yulang.GeneralNominalSupport.Tracked roles) (focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (generated : Yulang.GeneralNominalSaturationState.Generated before.current root focus)
  (next : Yulang.GeneralDictionaryInspectionTransport.Observation before.current.context.state)
  (certificate :
    Yulang.GeneralNominalCycleSteps.Refresh before.current
      (Yulang.GeneralDictionaryInspectionTransport.reobserve before.current.context next))
  (identity : Nat)
  (member : Membership.mem.{0, 0} (Yulang.GeneralNominalState.sources before.current.context.state) identity)
  (unknown : ¬Yulang.GeneralNominalState.Known before.current.context.state identity)
  (known :
    Yulang.GeneralNominalState.Known
      (Yulang.GeneralDictionaryInspectionTransport.reobserve before.current.context next).state identity) :
  Yulang.GeneralNominalActualInspectionSteps.Step registry root before
    (Yulang.GeneralDictionaryAgreedRefresh174.refreshed before next)
Yulang.GeneralDictionaryAgreedRefresh174.ordinary_then_refresh_actual {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (context : Yulang.GeneralNominalCandidates.Context) (before : Yulang.GeneralNominalSupport.Tracked roles)
  (path :
    Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryStep registry root)
      (Yulang.GeneralNominalSupport.initial context root) before)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (generated : Yulang.GeneralNominalSaturationState.Generated before.current root focus)
  (next : Yulang.GeneralDictionaryInspectionTransport.Observation before.current.context.state)
  (certificate :
    Yulang.GeneralNominalCycleSteps.Refresh before.current
      (Yulang.GeneralDictionaryInspectionTransport.reobserve before.current.context next))
  (identity : Nat)
  (member : Membership.mem.{0, 0} (Yulang.GeneralNominalState.sources before.current.context.state) identity)
  (unknown : ¬Yulang.GeneralNominalState.Known before.current.context.state identity)
  (known :
    Yulang.GeneralNominalState.Known
      (Yulang.GeneralDictionaryInspectionTransport.reobserve before.current.context next).state identity) :
  Yulang.B4Target.Steps.{1} (Yulang.GeneralNominalActualInspectionSteps.Step registry root)
    (Yulang.GeneralNominalSupport.initial context root) (Yulang.GeneralDictionaryAgreedRefresh174.refreshed before next)
Yulang.GeneralDictionaryAgreedRefresh174.ordinary_then_refresh_instance {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (context : Yulang.GeneralNominalCandidates.Context)
  (source : Yulang.GeneralNominalSourceFormation.InitialSource registry context root)
  (before : Yulang.GeneralNominalSupport.Tracked roles)
  (path :
    Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryStep registry root)
      (Yulang.GeneralNominalSupport.initial context root) before)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (member : Membership.mem.{0, 0} before.current.packets packet)
  (next : Yulang.GeneralDictionaryInspectionTransport.Observation before.current.context.state)
  (view : Eq.{1} next.view before.current.context.state.view)
  (certificate :
    Yulang.GeneralNominalCycleSteps.Refresh before.current
      (Yulang.GeneralDictionaryInspectionTransport.reobserve before.current.context next))
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid :
    Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralDictionaryAgreedRefresh174.refreshed before next).current
      model) :
  Yulang.GeneralDictionaryRecursiveEvidence.Instance registry
    (Yulang.GeneralDictionaryAgreedRefresh174.refreshed before next).current.context model packet.site.occurrence
    packet.declaration.id packet.children
Yulang.GeneralDictionaryAgreedRefresh174.ordinary_then_refresh_evidence {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (context : Yulang.GeneralNominalCandidates.Context)
  (source : Yulang.GeneralNominalSourceFormation.InitialSource registry context root)
  (before : Yulang.GeneralNominalSupport.Tracked roles)
  (path :
    Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryStep registry root)
      (Yulang.GeneralNominalSupport.initial context root) before)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (member : Membership.mem.{0, 0} before.current.packets packet)
  (next : Yulang.GeneralDictionaryInspectionTransport.Observation before.current.context.state)
  (view : Eq.{1} next.view before.current.context.state.view)
  (certificate :
    Yulang.GeneralNominalCycleSteps.Refresh before.current
      (Yulang.GeneralDictionaryInspectionTransport.reobserve before.current.context next))
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid :
    Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralDictionaryAgreedRefresh174.refreshed before next).current
      model)
  (dictionaries : List.{0} Yulang.GeneralDictionaryReadback.Payload)
  (given :
    Yulang.CommonRoleOutermostResolver.All₂.{0, 0}
      (Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry
        (Yulang.GeneralDictionaryAgreedRefresh174.refreshed before next).current.context model)
      packet.children dictionaries) :
  Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry
    (Yulang.GeneralDictionaryAgreedRefresh174.refreshed before next).current.context model packet.site.occurrence
    (Yulang.CommonRoleOutermostResolver.Dictionary.node packet.declaration.id dictionaries)
Yulang.GeneralDictionaryAgreedRefresh174.ordinary_then_refresh_result {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (context : Yulang.GeneralNominalCandidates.Context)
  (source : Yulang.GeneralNominalSourceFormation.InitialSource registry context root)
  (before : Yulang.GeneralNominalSupport.Tracked roles)
  (path :
    Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionaryAgreedEvidence174.OrdinaryStep registry root)
      (Yulang.GeneralNominalSupport.initial context root) before)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (recorded : Membership.mem.{0, 0} before.current.packets packet)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (generated : Yulang.GeneralNominalSaturationState.Generated before.current root focus)
  (next : Yulang.GeneralDictionaryInspectionTransport.Observation before.current.context.state)
  (view : Eq.{1} next.view before.current.context.state.view)
  (certificate :
    Yulang.GeneralNominalCycleSteps.Refresh before.current
      (Yulang.GeneralDictionaryInspectionTransport.reobserve before.current.context next))
  (identity : Nat)
  (member : Membership.mem.{0, 0} (Yulang.GeneralNominalState.sources before.current.context.state) identity)
  (unknown : ¬Yulang.GeneralNominalState.Known before.current.context.state identity)
  (known :
    Yulang.GeneralNominalState.Known
      (Yulang.GeneralDictionaryInspectionTransport.reobserve before.current.context next).state identity)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid :
    Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralDictionaryAgreedRefresh174.refreshed before next).current
      model)
  (dictionaries : List.{0} Yulang.GeneralDictionaryReadback.Payload)
  (given :
    Yulang.CommonRoleOutermostResolver.All₂.{0, 0}
      (Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry
        (Yulang.GeneralDictionaryAgreedRefresh174.refreshed before next).current.context model)
      packet.children dictionaries) :
  Yulang.B4Target.Steps.{1} (Yulang.GeneralNominalActualInspectionSteps.Step registry root)
      (Yulang.GeneralNominalSupport.initial context root)
      (Yulang.GeneralDictionaryAgreedRefresh174.refreshed before next) ∧
    Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry
      (Yulang.GeneralDictionaryAgreedRefresh174.refreshed before next).current.context model packet.site.occurrence
      (Yulang.CommonRoleOutermostResolver.Dictionary.node packet.declaration.id dictionaries)
Yulang.GeneralDictionaryAgreedRoleExamples174.wrapOnly : Yulang.GeneralDeclarations.Registry
Yulang.GeneralDictionaryAgreedRoleExamples174.roleRank (role : Nat) : Nat
Yulang.GeneralDictionaryAgreedRoleExamples174.wrapOnly_checked :
  Yulang.GeneralDeclarations.Checked Yulang.GeneralDictionaryAgreedRoleExamples174.wrapOnly
Yulang.GeneralDictionaryAgreedRoleExamples174.wrapOnly_nonleaf :
  Ne.{1} Yulang.GeneralDeclarationExamples.wrap.requirements List.nil.{0}
Yulang.GeneralDictionaryAgreedRoleExamples174.wrapOnly_stratified :
  Yulang.GeneralDictionaryAgreedEdge174.RoleStratified Yulang.GeneralDictionaryAgreedRoleExamples174.wrapOnly
    Yulang.GeneralDictionaryAgreedRoleExamples174.roleRank
Yulang.GeneralDictionaryAgreedRoleExamples174.wrapOnly_accessible (defer : Bool)
  (gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate Yulang.GeneralDeclarationExamples.roles)
  (state : Yulang.GeneralNominalSupport.Tracked Yulang.GeneralDeclarationExamples.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles) :
  Acc.{1}
    (Yulang.CommonRoleOutermostResolver.Child.{0}
      (Yulang.B4TargetV3.Local.{0}
        (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
          (Yulang.GeneralNominalActualAgreedBoundary.boundary defer gap))
        Yulang.GeneralDictionaryAgreedRoleExamples174.wrapOnly state))
    root
Yulang.GeneralDictionaryAgreedRoleExamples174.display_not_stratified (rank : Nat → Nat) :
  ¬Yulang.GeneralDictionaryAgreedEdge174.RoleStratified Yulang.GeneralDeclarationExamples.registry rank
Yulang.GeneralDictionaryAgreedSearchOrder174.childRoles_mem_iff {first last : Yulang.GeneralDeclarations.Registry}
  {role child : Nat} (order : Yulang.GeneralRegistryReordering.Reorders first last) :
  Membership.mem.{0, 0} (Yulang.GeneralDictionaryAgreedComputed174.childRoles first role) child ↔
    Membership.mem.{0, 0} (Yulang.GeneralDictionaryAgreedComputed174.childRoles last role) child
Yulang.GeneralDictionaryAgreedSearchOrder174.fold_max_le_iff (xs : List.{0} Nat) (f : Nat → Nat) (initial bound : Nat) :
  LE.le.{0} (List.foldl.{0, 0} (fun h x => max.{0} h (f x)) initial xs) bound ↔
    LE.le.{0} initial bound ∧ ∀ (x : Nat), Membership.mem.{0, 0} xs x → LE.le.{0} (f x) bound
Yulang.GeneralDictionaryAgreedSearchOrder174.fold_max_eq (xs ys : List.{0} Nat) (f g : Nat → Nat)
  (members : ∀ (x : Nat), Membership.mem.{0, 0} xs x ↔ Membership.mem.{0, 0} ys x)
  (values : ∀ (x : Nat), Membership.mem.{0, 0} xs x → Eq.{1} (f x) (g x)) (initial : Nat) :
  Eq.{1} (List.foldl.{0, 0} (fun h x => max.{0} h (f x)) initial xs)
    (List.foldl.{0, 0} (fun h x => max.{0} h (g x)) initial ys)
Yulang.GeneralDictionaryAgreedSearchOrder174.computedHeight_reorders {first last : Yulang.GeneralDeclarations.Registry}
  (order : Yulang.GeneralRegistryReordering.Reorders first last) (fuel role : Nat) :
  Eq.{1} (Yulang.GeneralDictionaryAgreedComputed174.computedHeight first fuel role)
    (Yulang.GeneralDictionaryAgreedComputed174.computedHeight last fuel role)
Yulang.GeneralDictionaryAgreedSearchOrder174.stratified_reorders_iff {first last : Yulang.GeneralDeclarations.Registry}
  (order : Yulang.GeneralRegistryReordering.Reorders first last) (rank : Nat → Nat) :
  Yulang.GeneralDictionaryAgreedEdge174.RoleStratified first rank ↔
    Yulang.GeneralDictionaryAgreedEdge174.RoleStratified last rank
Yulang.GeneralDictionaryAgreedSearchOrder174.check_reorders {first last : Yulang.GeneralDeclarations.Registry}
  (order : Yulang.GeneralRegistryReordering.Reorders first last) (fuel : Nat) :
  Eq.{1} (Yulang.GeneralDictionaryAgreedComputed174.check first fuel)
    (Yulang.GeneralDictionaryAgreedComputed174.check last fuel)
Yulang.GeneralDictionaryAgreedSearchOrder174.rankBudget_reorders {first last : Yulang.GeneralDeclarations.Registry}
  (order : Yulang.GeneralRegistryReordering.Reorders first last) (rank : Nat → Nat) :
  Eq.{1} (Yulang.GeneralDictionaryAgreedComputed174.rankBudget first rank)
    (Yulang.GeneralDictionaryAgreedComputed174.rankBudget last rank)
Yulang.GeneralDictionaryAgreedSearchOrder174.reversedExample : Yulang.GeneralDeclarations.Registry
Yulang.GeneralDictionaryAgreedSearchOrder174.example_reorders :
  Yulang.GeneralRegistryReordering.Reorders Yulang.GeneralDeclarationExamples.registry
    Yulang.GeneralDictionaryAgreedSearchOrder174.reversedExample
Yulang.GeneralDictionaryAgreedSearchOrder174.reversedExample_checked :
  Yulang.GeneralDeclarations.Checked Yulang.GeneralDictionaryAgreedSearchOrder174.reversedExample
Yulang.GeneralDictionaryAgreedSearchOrder174.recursive_example_height :
  Eq.{1} (Yulang.GeneralDictionaryAgreedComputed174.computedHeight Yulang.GeneralDeclarationExamples.registry 3 0) 3 ∧
    Eq.{1}
      (Yulang.GeneralDictionaryAgreedComputed174.computedHeight
        Yulang.GeneralDictionaryAgreedSearchOrder174.reversedExample 3 0)
      3
Yulang.GeneralDictionaryAgreedSearchOrder174.recursive_example_check (fuel : Nat) :
  Eq.{1}
    (Yulang.GeneralDictionaryAgreedComputed174.check Yulang.GeneralDictionaryAgreedSearchOrder174.reversedExample fuel)
    false
Yulang.GeneralDictionaryAgreedUniform174.roleNodes (registry : Yulang.GeneralDeclarations.Registry) : List.{0} Nat
Yulang.GeneralDictionaryAgreedUniform174.belowCount (rank : Nat → Nat) (bound : Nat) : List.{0} Nat → Nat
Yulang.GeneralDictionaryAgreedUniform174.belowCount_le_length (rank : Nat → Nat) (bound : Nat) (nodes : List.{0} Nat) :
  LE.le.{0} (Yulang.GeneralDictionaryAgreedUniform174.belowCount rank bound nodes) (List.length.{0} nodes)
Yulang.GeneralDictionaryAgreedUniform174.belowCount_mono {a b : Nat} (rank : Nat → Nat) (nodes : List.{0} Nat)
  (less : LE.le.{0} a b) :
  LE.le.{0} (Yulang.GeneralDictionaryAgreedUniform174.belowCount rank a nodes)
    (Yulang.GeneralDictionaryAgreedUniform174.belowCount rank b nodes)
Yulang.GeneralDictionaryAgreedUniform174.belowCount_strict {child bound : Nat} (rank : Nat → Nat) (nodes : List.{0} Nat)
  (present : Membership.mem.{0, 0} nodes child) (less : LT.lt.{0} (rank child) bound) :
  LT.lt.{0} (Yulang.GeneralDictionaryAgreedUniform174.belowCount rank (rank child) nodes)
    (Yulang.GeneralDictionaryAgreedUniform174.belowCount rank bound nodes)
Yulang.GeneralDictionaryAgreedUniform174.child_mem_nodes {declaration : Yulang.GeneralDeclarations.Declaration}
  {clause : Yulang.GeneralDeclarations.Clause} {registry : Yulang.GeneralDeclarations.Registry}
  (visible : Membership.mem.{0, 0} registry.declarations declaration)
  (member : Membership.mem.{0, 0} declaration.requirements clause) :
  Membership.mem.{0, 0} (Yulang.GeneralDictionaryAgreedUniform174.roleNodes registry) clause.role
Yulang.GeneralDictionaryAgreedUniform174.compressedRank (registry : Yulang.GeneralDeclarations.Registry)
  (rank : Nat → Nat) (role : Nat) : Nat
Yulang.GeneralDictionaryAgreedUniform174.compressed_stratified {registry : Yulang.GeneralDeclarations.Registry}
  {rank : Nat → Nat} (stratified : Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank) :
  Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry
    (Yulang.GeneralDictionaryAgreedUniform174.compressedRank registry rank)
Yulang.GeneralDictionaryAgreedUniform174.uniform_complete {registry : Yulang.GeneralDeclarations.Registry}
  {rank : Nat → Nat} (stratified : Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank) :
  Eq.{1}
    (Yulang.GeneralDictionaryAgreedComputed174.check registry
      (List.length.{0} (Yulang.GeneralDictionaryAgreedUniform174.roleNodes registry)))
    true
Yulang.GeneralDictionaryAgreedUniform174.certify (registry : Yulang.GeneralDeclarations.Registry) : Bool
Yulang.GeneralDictionaryAgreedUniform174.certify_iff {registry : Yulang.GeneralDeclarations.Registry} :
  Eq.{1} (Yulang.GeneralDictionaryAgreedUniform174.certify registry) true ↔
    Exists.{1} fun rank => Yulang.GeneralDictionaryAgreedEdge174.RoleStratified registry rank
Yulang.GeneralDictionaryAgreedUniform174.certify_reorders {first last : Yulang.GeneralDeclarations.Registry}
  (order : Yulang.GeneralRegistryReordering.Reorders first last) :
  Eq.{1} (Yulang.GeneralDictionaryAgreedUniform174.certify first)
    (Yulang.GeneralDictionaryAgreedUniform174.certify last)
Yulang.GeneralDictionaryAgreedUniform174.certified_run_resolves_iff {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (checked :
    Yulang.B4Target.SourceBoundary.Checked.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
      registry)
  (passed : Eq.{1} (Yulang.GeneralDictionaryAgreedUniform174.certify registry) true)
  (reachable :
    Yulang.B4TargetV5.Reachable.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state)
  (tree : Yulang.CommonRoleOutermostResolver.Tree) :
  Eq.{1}
      (Prod.snd.{0, 0}
        (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry state
          root))
      tree ↔
    Yulang.CommonRoleOutermostResolver.Resolves.{0}
      (Yulang.B4TargetV3.Local.{0}
        (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
          (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
        registry
        (Prod.fst.{0, 0}
          (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry
            state root)))
      root tree
Yulang.GeneralDictionaryAgreedUniform174.certified_completed_iff {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (checked :
    Yulang.B4Target.SourceBoundary.Checked.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
      registry)
  (passed : Eq.{1} (Yulang.GeneralDictionaryAgreedUniform174.certify registry) true)
  (reachable :
    Yulang.B4TargetV5.Reachable.{0} (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap) registry root state)
  (out : Yulang.CommonRoleOutermostResolver.Result) :
  Yulang.B4TargetV3.Completed
      (Prod.snd.{0, 0}
        (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry state
          root))
      out ↔
    Yulang.B4TargetV3.Classify.{0}
      (Yulang.B4TargetV5.SourceBoundary.toSourceBoundary.{0}
        (Yulang.GeneralDictionaryAgreedGround174.boundary defer gap))
      registry
      (Prod.fst.{0, 0}
        (Yulang.B4TargetV3.Executor.run.{0} (Yulang.GeneralDictionaryAgreedGround174.executor defer gap) registry state
          root))
      root out
Yulang.GeneralDictionaryAgreedUniform174.wrap_certified :
  Eq.{1} (Yulang.GeneralDictionaryAgreedUniform174.certify Yulang.GeneralDictionaryAgreedRoleExamples174.wrapOnly) true
Yulang.GeneralDictionaryAgreedUniform174.recursive_not_certified :
  Eq.{1} (Yulang.GeneralDictionaryAgreedUniform174.certify Yulang.GeneralDeclarationExamples.registry) false
Yulang.GeneralDictionaryAgreedUniform174.computedHeight_le_fuel (registry : Yulang.GeneralDeclarations.Registry)
  (fuel role : Nat) : LE.le.{0} (Yulang.GeneralDictionaryAgreedComputed174.computedHeight registry fuel role) fuel
Yulang.GeneralDictionaryAgreedUniform174.certified_descent_bound {roles : Yulang.Roles.RoleDecls} {defer : Bool}
  {gap : Yulang.GeneralNominalActualAgreedLocal.GapPredicate roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalSupport.Tracked roles} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {depth : Nat} {child : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (passed : Eq.{1} (Yulang.GeneralDictionaryAgreedUniform174.certify registry) true)
  (path : Yulang.GeneralDictionaryAgreedEdge174.Descent defer gap registry state root depth child) :
  LE.le.{0} depth (List.length.{0} (Yulang.GeneralDictionaryAgreedUniform174.roleNodes registry))
EXIT:0
```

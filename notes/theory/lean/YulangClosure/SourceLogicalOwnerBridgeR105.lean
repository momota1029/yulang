import YulangClosure.SourceLogicalOccurrencesR104
import YulangClosure.OriginalSourceEvents

/-!
R105 syntactic route correspondence, constructed without execution by this
leaf. The primary owns the single frozen flattened check. No semantic
admission, source judgment, decoded formal contract, or runtime event is
constructed here. Source Generalize selection §§2–3 selects construction
§§3–5, especially §3.3's original declaration and event telescopes.
-/
namespace YulangClosure.OriginalSource.LogicalOwnerBridgeR105

/-- Both address systems observe one unchanged original cursor. The logical
scope retains nonbinder anchors; the owner telescope retains binder routes. -/
structure Position where
  route : OriginalSourceEvents.Route
  telescope : List OriginalSourceEvents.ScopeEntry
  enclosing : List LogicalOccurrencesR104.ScopeFrame
  cursor : LogicalOccurrencesR104.Cursor

def erase (position : Position) : LogicalOccurrencesR104.Position :=
  ⟨position.enclosing, position.cursor⟩

def root (tree : RuleTree) : Position := ⟨[], [], [], .tree tree⟩

/-- This is stateful translation, not a map on Bool labels. In particular,
forest head elides its edge, forest tail uses 1, and choice right uses 3. -/
def advance (position : Position) (bit : Bool) : Option Position :=
  let ⟨route, telescope, scope, cursor⟩ := position
  match cursor, bit with
  | .tree (.rule _ _ _ _ children), false =>
      some ⟨route ++ [0], telescope, scope, .forest children⟩
  | .tree (.existsE binder body), false =>
      some ⟨route ++ [0], OriginalSourceEvents.extendScope telescope route binder,
        scope ++ [.existsE binder], .tree body⟩
  | .tree (.forallE binder body), false =>
      some ⟨route ++ [0], OriginalSourceEvents.extendScope telescope route binder,
        scope ++ [.forallE binder], .tree body⟩
  | .tree (.initializerE site body), false =>
      some ⟨route ++ [0], telescope, scope ++ [.initializerE site], .tree body⟩
  | .tree (.executionE binder body), false =>
      some ⟨route ++ [0], OriginalSourceEvents.extendScope telescope route binder,
        scope ++ [.executionE binder], .tree body⟩
  | .tree (.sharedE binder body), false =>
      some ⟨route ++ [0], OriginalSourceEvents.extendScope telescope route binder,
        scope ++ [.sharedE binder], .tree body⟩
  | .tree (.publishGroup bindings body), false =>
      some ⟨route ++ [0], telescope, scope ++ [.publishGroup bindings], .tree body⟩
  | .tree (.atPublication binding body), false =>
      some ⟨route ++ [0], telescope, scope ++ [.atPublication binding], .tree body⟩
  | .tree (.aliasPublication original aliasName body), false =>
      some ⟨route ++ [0], telescope,
        scope ++ [.aliasPublication original aliasName], .tree body⟩
  | .tree (.choice _ left _), false =>
      some ⟨route ++ [0], telescope, scope, .tree left⟩
  | .tree (.choice _ _ right), true =>
      some ⟨route ++ [3], telescope, scope, .tree right⟩
  | .forest (.cons head _), false =>
      some ⟨route, telescope, scope, .tree head⟩
  | .forest (.cons _ tail), true =>
      some ⟨route ++ [1], telescope, scope, .forest tail⟩
  | _, _ => none

def follow (position : Position) : LogicalOccurrencesR104.Route → Option Position
  | [] => some position
  | bit :: route => (advance position bit).bind fun next => follow next route

theorem forest_head_route (route : OriginalSourceEvents.Route)
    (telescope : List OriginalSourceEvents.ScopeEntry)
    (scope : List LogicalOccurrencesR104.ScopeFrame) (head : RuleTree) (tail : RuleForest) :
    (advance ⟨route, telescope, scope, .forest (.cons head tail)⟩ false).map Position.route =
      some route := rfl

theorem forest_sibling_route (route : OriginalSourceEvents.Route)
    (telescope : List OriginalSourceEvents.ScopeEntry)
    (scope : List LogicalOccurrencesR104.ScopeFrame) (head : RuleTree) (tail : RuleForest) :
    (advance ⟨route, telescope, scope, .forest (.cons head tail)⟩ true).map Position.route =
      some (route ++ [1]) := rfl

theorem choice_right_route (route : OriginalSourceEvents.Route)
    (telescope : List OriginalSourceEvents.ScopeEntry)
    (scope : List LogicalOccurrencesR104.ScopeFrame) (site : Site) (left right : RuleTree) :
    (advance ⟨route, telescope, scope, .tree (.choice site left right)⟩ true).map Position.route =
      some (route ++ [3]) := rfl

theorem advance_erases (position : Position) (bit : Bool) :
    (advance position bit).map erase =
      LogicalOccurrencesR104.advance position.enclosing position.cursor bit := by
  rcases position with ⟨route, telescope, scope, cursor⟩
  cases cursor with
  | tree tree => cases tree <;> cases bit <;> rfl
  | forest forest => cases forest <;> cases bit <;> rfl

theorem follow_erases (position : Position) (route : LogicalOccurrencesR104.Route) :
    (follow position route).map erase =
      LogicalOccurrencesR104.follow position.enclosing position.cursor route := by
  induction route generalizing position with
  | nil => rfl
  | cons bit route ih =>
      have step := advance_erases position bit
      cases reached : advance position bit with
      | none =>
          simp only [reached, Option.map_none] at step
          simp only [follow, reached, Option.bind_none, Option.map_none, LogicalOccurrencesR104.follow, ← step]
      | some next =>
          simp only [reached, Option.map_some] at step
          simpa only [follow, reached, Option.bind_some, LogicalOccurrencesR104.follow, ← step] using ih next

/-- Only the original executable/proof owner catalogue is used here. -/
def ownersAt (position : Position) : List OriginalSourceEvents.Owner :=
  match position.cursor with
  | .tree tree => OriginalSourceEvents.owners position.route position.telescope tree
  | .forest forest => OriginalSourceEvents.forestOwners position.route position.telescope forest

theorem advance_owner (position : Position) (bit : Bool) (next : Position)
    (introduction : OriginalSourceEvents.Owner) (step : advance position bit = some next)
    (present : introduction ∈ ownersAt next) : introduction ∈ ownersAt position := by
  rcases position with ⟨route, telescope, scope, cursor⟩
  cases cursor with
  | tree tree =>
      cases tree with
      | rule rule site context premises children =>
          cases bit with
          | false => cases step; exact present
          | true => cases step
      | existsE binder body =>
          cases bit with
          | false => cases step; exact List.mem_append_right _ present
          | true => cases step
      | forallE binder body =>
          cases bit with
          | false => cases step; exact List.mem_append_right _ present
          | true => cases step
      | initializerE site body =>
          cases bit with
          | false => cases step; exact present
          | true => cases step
      | executionE binder body =>
          cases bit with
          | false => cases step; exact List.mem_append_right _ present
          | true => cases step
      | sharedE binder body =>
          cases bit with
          | false => cases step; exact List.mem_append_right _ present
          | true => cases step
      | publishGroup bindings body =>
          cases bit with
          | false => cases step; exact present
          | true => cases step
      | atPublication binding body =>
          cases bit with
          | false => cases step; exact present
          | true => cases step
      | aliasPublication original aliasName body =>
          cases bit with
          | false => cases step; exact present
          | true => cases step
      | choice site left right =>
          cases bit with
          | false => cases step; exact List.mem_append_left _ present
          | true => cases step; exact List.mem_append_right _ present
  | forest forest =>
      cases forest with
      | nil => cases bit <;> cases step
      | cons head tail =>
          cases bit with
          | false => cases step; exact List.mem_append_left _ present
          | true => cases step; exact List.mem_append_right _ present

theorem follow_owner (position : Position) (route : LogicalOccurrencesR104.Route) (last : Position)
    (introduction : OriginalSourceEvents.Owner) (reached : follow position route = some last)
    (present : introduction ∈ ownersAt last) : introduction ∈ ownersAt position := by
  induction route generalizing position with
  | nil =>
      have same : position = last := Option.some.inj reached
      cases same
      exact present
  | cons bit route ih =>
      cases step : advance position bit with
      | none => simp only [follow, step, Option.bind_none] at reached; cases reached
      | some next =>
          have rest : follow next route = some last := by
            simpa only [follow, step, Option.bind_some] using reached
          exact advance_owner position bit next introduction step (ih next rest)

def annotationRoute (mark : Mark) : OriginalSourceEvents.Route :=
  match mark.annotation with | none => [] | some _ => [0]

/-- A logical address carries no Lifetime and makes no runtime-owner claim. -/
structure LogicalAddress where
  route : OriginalSourceEvents.Route
  binder : Binder
  telescope : List OriginalSourceEvents.ScopeEntry
  enclosing : List LogicalOccurrencesR104.ScopeFrame
  subtree : RuleTree

def LogicalAddress.position (address : LogicalAddress) : Position :=
  ⟨address.route, address.telescope, address.enclosing,
    .tree (.existsE address.binder address.subtree)⟩

def appAddress (context : Context) (mark : Mark)
    (callee argument : Source .expression) : LogicalAddress :=
  ⟨annotationRoute mark, ⟨mark.site, .viewLogic, 0⟩, [], [],
    LogicalOccurrencesR104.appRule context mark callee argument⟩

theorem app_route_exact (context : Context) (mark : Mark)
    (callee argument : Source .expression) :
    follow (root (sourceRules context (.app mark callee argument)))
      (LogicalOccurrencesR104.annotationRoute mark) = some (appAddress context mark callee argument).position := by
  rcases mark with ⟨site, annotation⟩
  cases annotation <;> simp only [sourceRules] <;> rfl

theorem app_viewlogic_separate (context : Context) (mark : Mark)
    (callee argument : Source .expression) :
    OriginalSourceEvents.binderOwner (appAddress context mark callee argument).route
      (appAddress context mark callee argument).telescope
      (appAddress context mark callee argument).binder = [] := rfl

theorem app_bridge (context : Context) (mark : Mark)
    (callee argument : Source .expression) :
    (LogicalOccurrencesR104.annotationRoute mark,
      (⟨⟨mark.site, .viewLogic, 0⟩, [],
        LogicalOccurrencesR104.appRule context mark callee argument⟩ : LogicalOccurrencesR104.Occurrence)) ∈
      LogicalOccurrencesR104.sourceInventory context (.app mark callee argument) [] ∧
    follow (root (sourceRules context (.app mark callee argument)))
      (LogicalOccurrencesR104.annotationRoute mark) = some (appAddress context mark callee argument).position ∧
    OriginalSourceEvents.binderOwner (appAddress context mark callee argument).route
      (appAddress context mark callee argument).telescope
      (appAddress context mark callee argument).binder = [] :=
  ⟨LogicalOccurrencesR104.app_inventory context mark callee argument [],
    app_route_exact context mark callee argument,
    app_viewlogic_separate context mark callee argument⟩

def bodyRoute (mark : Mark) (formal : Formal) : OriginalSourceEvents.Route :=
  annotationRoute mark ++ [0, 0, 0, 0, 0, 0, 0, 0] ++
    (match formal.entry with | .value => [0] | .computation => []) ++ [1]

def bodyTelescope (mark : Mark) (formal : Formal) : List OriginalSourceEvents.ScopeEntry :=
  let prefix := annotationRoute mark
  [⟨prefix, ⟨formal.site, .description, 0⟩⟩,
   ⟨prefix ++ [0], ⟨mark.site, .viewLogic, 0⟩⟩,
   ⟨prefix ++ [0, 0, 0], ⟨mark.site, .invocation, 0⟩⟩,
   ⟨prefix ++ [0, 0, 0, 0], ⟨formal.site, .receipt, 0⟩⟩] ++
    (match formal.entry with
      | .value => [⟨prefix ++ [0, 0, 0, 0, 0, 0], ⟨formal.site, .returnRebind, 0⟩⟩]
      | .computation => []) ++
    [⟨prefix ++ [0, 0, 0, 0, 0, 0] ++
        (match formal.entry with | .value => [0] | .computation => []),
      ⟨formal.site, .shared, 0⟩⟩]

def bodyAddress (context : Context) (mark : Mark) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) : LogicalAddress :=
  ⟨bodyRoute mark formal, ⟨body.site, .eventProof, 0⟩,
    bodyTelescope mark formal, LogicalOccurrencesR104.bodyScope [] mark formal,
    LogicalOccurrencesR104.bodyRule context mark formal pattern body⟩

/-- Nonbinder anchors stay in the R104 scope; only binder frames contribute
to the original owner telescope. No route is reconstructed from a Site. -/
def scopeBinders : List LogicalOccurrencesR104.ScopeFrame → List Binder
  | [] => []
  | .existsE binder :: tail | .forallE binder :: tail |
      .executionE binder :: tail | .sharedE binder :: tail => binder :: scopeBinders tail
  | _ :: tail => scopeBinders tail

theorem body_telescope_binders (mark : Mark) (formal : Formal) :
    (bodyTelescope mark formal).map OriginalSourceEvents.ScopeEntry.binder =
      scopeBinders (LogicalOccurrencesR104.bodyScope [] mark formal) := by
  rcases mark with ⟨site, annotation⟩
  rcases formal with ⟨formalSite, formalName, formalAnnotation, outerComputation⟩
  cases annotation <;> cases outerComputation <;> rfl

theorem lambda_body_route_exact (context : Context) (mark : Mark) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) :
    follow (root (sourceRules context (.lambda mark formal pattern body)))
      (LogicalOccurrencesR104.bodyRoute mark formal) =
      some (bodyAddress context mark formal pattern body).position := by
  rcases mark with ⟨site, annotation⟩
  rcases formal with ⟨formalSite, formalName, formalAnnotation, outerComputation⟩
  cases annotation <;> cases outerComputation <;> simp only [sourceRules] <;> rfl

/-- This Owner is descriptionProof, never actualEvent. -/
def bodyOwner (mark : Mark) (formal : Formal) (body : Source .expression) : OriginalSourceEvents.Owner :=
  OriginalSourceEvents.owner (bodyRoute mark formal) (bodyTelescope mark formal)
    ⟨body.site, .eventProof, 0⟩ .descriptionProof

theorem lambda_body_owner (context : Context) (mark : Mark) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) :
    bodyOwner mark formal body ∈ OriginalSourceEvents.sourceOwners context (.lambda mark formal pattern body) := by
  apply follow_owner (root (sourceRules context (.lambda mark formal pattern body)))
    (LogicalOccurrencesR104.bodyRoute mark formal) (bodyAddress context mark formal pattern body).position
    (bodyOwner mark formal body) (lambda_body_route_exact context mark formal pattern body)
  change bodyOwner mark formal body ∈
    OriginalSourceEvents.binderOwner (bodyRoute mark formal) (bodyTelescope mark formal) ⟨body.site, .eventProof, 0⟩ ++ _
  apply List.mem_append_left
  change bodyOwner mark formal body ∈ [bodyOwner mark formal body]
  exact List.mem_cons_self

/-- The key constructor retains these coordinates as data. This theorem
does not assert that a descriptionProof is an admitted actual runtime event. -/
theorem body_key_coordinates {s : OriginalSourceInterpretation.Sorts} {View : Type}
    (mark : Mark) (formal : Formal) (body : Source .expression) (origin : Declaration)
    (parents : List (EventStep (OriginalSourceEnvironment.Runtime s View)))
    (occurrence : Nat) (raw : OriginalSourceEnvironment.Runtime s View) :
    (OriginalSourceEvents.actualKey (bodyOwner mark formal body) origin parents occurrence raw).route = bodyRoute mark formal ∧
    (OriginalSourceEvents.actualKey (bodyOwner mark formal body) origin parents occurrence raw).binder =
      ⟨body.site, .eventProof, 0⟩ ∧
    (OriginalSourceEvents.actualKey (bodyOwner mark formal body) origin parents occurrence raw).parents = parents ∧
    (OriginalSourceEvents.actualKey (bodyOwner mark formal body) origin parents occurrence raw).occurrence = occurrence ∧
    (OriginalSourceEvents.actualKey (bodyOwner mark formal body) origin parents occurrence raw).raw = raw :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Both inventories concern the same generated existential, without adding
a LocalAdmissions.logical premise or selecting a semantic witness. -/
theorem lambda_body_bridge (context : Context) (mark : Mark) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) :
    (LogicalOccurrencesR104.bodyRoute mark formal,
      (⟨⟨body.site, .eventProof, 0⟩, LogicalOccurrencesR104.bodyScope [] mark formal,
        LogicalOccurrencesR104.bodyRule context mark formal pattern body⟩ : LogicalOccurrencesR104.Occurrence)) ∈
      LogicalOccurrencesR104.sourceInventory context (.lambda mark formal pattern body) [] ∧
    bodyOwner mark formal body ∈ OriginalSourceEvents.sourceOwners context (.lambda mark formal pattern body) ∧
    follow (root (sourceRules context (.lambda mark formal pattern body)))
      (LogicalOccurrencesR104.bodyRoute mark formal) =
      some (bodyAddress context mark formal pattern body).position :=
  ⟨LogicalOccurrencesR104.lambda_body_inventory context mark formal pattern body [],
    lambda_body_owner context mark formal pattern body,
    lambda_body_route_exact context mark formal pattern body⟩

end YulangClosure.OriginalSource.LogicalOwnerBridgeR105

#check @YulangClosure.OriginalSource.LogicalOwnerBridgeR105.forest_head_route
#print axioms YulangClosure.OriginalSource.LogicalOwnerBridgeR105.forest_head_route
#check @YulangClosure.OriginalSource.LogicalOwnerBridgeR105.forest_sibling_route
#print axioms YulangClosure.OriginalSource.LogicalOwnerBridgeR105.forest_sibling_route
#check @YulangClosure.OriginalSource.LogicalOwnerBridgeR105.choice_right_route
#print axioms YulangClosure.OriginalSource.LogicalOwnerBridgeR105.choice_right_route
#check @YulangClosure.OriginalSource.LogicalOwnerBridgeR105.advance_erases
#print axioms YulangClosure.OriginalSource.LogicalOwnerBridgeR105.advance_erases
#check @YulangClosure.OriginalSource.LogicalOwnerBridgeR105.follow_erases
#print axioms YulangClosure.OriginalSource.LogicalOwnerBridgeR105.follow_erases
#check @YulangClosure.OriginalSource.LogicalOwnerBridgeR105.advance_owner
#print axioms YulangClosure.OriginalSource.LogicalOwnerBridgeR105.advance_owner
#check @YulangClosure.OriginalSource.LogicalOwnerBridgeR105.follow_owner
#print axioms YulangClosure.OriginalSource.LogicalOwnerBridgeR105.follow_owner
#check @YulangClosure.OriginalSource.LogicalOwnerBridgeR105.app_route_exact
#print axioms YulangClosure.OriginalSource.LogicalOwnerBridgeR105.app_route_exact
#check @YulangClosure.OriginalSource.LogicalOwnerBridgeR105.app_viewlogic_separate
#print axioms YulangClosure.OriginalSource.LogicalOwnerBridgeR105.app_viewlogic_separate
#check @YulangClosure.OriginalSource.LogicalOwnerBridgeR105.app_bridge
#print axioms YulangClosure.OriginalSource.LogicalOwnerBridgeR105.app_bridge
#check @YulangClosure.OriginalSource.LogicalOwnerBridgeR105.lambda_body_route_exact
#print axioms YulangClosure.OriginalSource.LogicalOwnerBridgeR105.lambda_body_route_exact
#check @YulangClosure.OriginalSource.LogicalOwnerBridgeR105.body_telescope_binders
#print axioms YulangClosure.OriginalSource.LogicalOwnerBridgeR105.body_telescope_binders
#check @YulangClosure.OriginalSource.LogicalOwnerBridgeR105.lambda_body_owner
#print axioms YulangClosure.OriginalSource.LogicalOwnerBridgeR105.lambda_body_owner
#check @YulangClosure.OriginalSource.LogicalOwnerBridgeR105.body_key_coordinates
#print axioms YulangClosure.OriginalSource.LogicalOwnerBridgeR105.body_key_coordinates
#check @YulangClosure.OriginalSource.LogicalOwnerBridgeR105.lambda_body_bridge
#print axioms YulangClosure.OriginalSource.LogicalOwnerBridgeR105.lambda_body_bridge

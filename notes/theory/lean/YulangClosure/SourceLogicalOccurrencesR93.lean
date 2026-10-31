import YulangClosure.OriginalSourceGeneration

/-!
R93: syntactic occurrence provenance, with no semantic admission premise.
The two directions of a route are positions in the generated tree/forest,
not site IDs. A rule enters its forest on `false`; a forest cons enters its
head on `false` and its tail on `true`. Every unary wrapper enters on `false`.
Choice uses `false`/`true`. Thus repeated sites do not identify occurrences.

CONSTRUCTED, NOT CHECKED: execution belongs to the primary's fixed R93 gate.
No root import or source constructor is changed by this module.
-/
namespace YulangClosure.OriginalSource.LogicalOccurrencesR93

abbrev Route := List Bool

/-- Ordered syntactic scope, including anchors which are not quantifiers.
This is not an assignment of semantic values to the telescope. -/
inductive ScopeFrame where
  | existsE (binder : Binder)
  | forallE (binder : Binder)
  | initializerE (site : Site)
  | executionE (binder : Binder)
  | sharedE (binder : Binder)
  | publishGroup (bindings : List (Name × Site))
  | atPublication (binding : Name)
  | aliasPublication (original aliasName : Name)

structure Occurrence where
  binder : Binder
  enclosing : List ScopeFrame
  subtree : RuleTree

def logicalKind : BinderKind → Bool
  | .viewLogic | .eventProof | .publishedInstance => true
  | _ => false

inductive Cursor where
  | tree (tree : RuleTree)
  | forest (forest : RuleForest)

structure Position where
  enclosing : List ScopeFrame
  cursor : Cursor

/-- Observe only actual logical existential introductions. -/
def payload (scope : List ScopeFrame) : Cursor → Option Occurrence
  | .tree (.existsE binder body) =>
      if logicalKind binder.kind then some ⟨binder, scope, body⟩ else none
  | _ => none

/-- One structural step in the ORIGINAL RuleTree/RuleForest. -/
def advance (scope : List ScopeFrame) : Cursor → Bool → Option Position
  | .tree (.rule _ _ _ _ children), false => some ⟨scope, .forest children⟩
  | .tree (.existsE binder body), false =>
      some ⟨scope ++ [.existsE binder], .tree body⟩
  | .tree (.forallE binder body), false =>
      some ⟨scope ++ [.forallE binder], .tree body⟩
  | .tree (.initializerE site body), false =>
      some ⟨scope ++ [.initializerE site], .tree body⟩
  | .tree (.executionE binder body), false =>
      some ⟨scope ++ [.executionE binder], .tree body⟩
  | .tree (.sharedE binder body), false =>
      some ⟨scope ++ [.sharedE binder], .tree body⟩
  | .tree (.publishGroup bindings body), false =>
      some ⟨scope ++ [.publishGroup bindings], .tree body⟩
  | .tree (.atPublication binding body), false =>
      some ⟨scope ++ [.atPublication binding], .tree body⟩
  | .tree (.aliasPublication original aliasName body), false =>
      some ⟨scope ++ [.aliasPublication original aliasName], .tree body⟩
  | .tree (.choice _ left _), false => some ⟨scope, .tree left⟩
  | .tree (.choice _ _ right), true => some ⟨scope, .tree right⟩
  | .forest (.cons head _), false => some ⟨scope, .tree head⟩
  | .forest (.cons _ tail), true => some ⟨scope, .forest tail⟩
  | _, _ => none

def follow (scope : List ScopeFrame) (cursor : Cursor) : Route → Option Position
  | [] => some ⟨scope, cursor⟩
  | bit :: route => (advance scope cursor bit).bind fun position =>
      follow position.enclosing position.cursor route

def observe (scope : List ScopeFrame) (cursor : Cursor) : Route → Option Occurrence
  | [] => payload scope cursor
  | bit :: route => (advance scope cursor bit).bind fun position =>
      observe position.enclosing position.cursor route

/-- A finite positional index, separate from the original syntax walker. -/
inductive Index where
  | empty
  | node (entry : Option Occurrence) (left right : Index)

mutual
def encodeTree (scope : List ScopeFrame) : RuleTree → Index
  | tree@(.rule _ _ _ _ children) =>
      .node (payload scope (.tree tree)) (encodeForest scope children) .empty
  | tree@(.existsE binder body) =>
      .node (payload scope (.tree tree))
        (encodeTree (scope ++ [.existsE binder]) body) .empty
  | tree@(.forallE binder body) =>
      .node (payload scope (.tree tree))
        (encodeTree (scope ++ [.forallE binder]) body) .empty
  | tree@(.initializerE site body) =>
      .node (payload scope (.tree tree))
        (encodeTree (scope ++ [.initializerE site]) body) .empty
  | tree@(.executionE binder body) =>
      .node (payload scope (.tree tree))
        (encodeTree (scope ++ [.executionE binder]) body) .empty
  | tree@(.sharedE binder body) =>
      .node (payload scope (.tree tree))
        (encodeTree (scope ++ [.sharedE binder]) body) .empty
  | tree@(.publishGroup bindings body) =>
      .node (payload scope (.tree tree))
        (encodeTree (scope ++ [.publishGroup bindings]) body) .empty
  | tree@(.atPublication binding body) =>
      .node (payload scope (.tree tree))
        (encodeTree (scope ++ [.atPublication binding]) body) .empty
  | tree@(.aliasPublication original aliasName body) =>
      .node (payload scope (.tree tree))
        (encodeTree (scope ++ [.aliasPublication original aliasName]) body) .empty
  | tree@(.choice _ left right) =>
      .node (payload scope (.tree tree)) (encodeTree scope left) (encodeTree scope right)

def encodeForest (scope : List ScopeFrame) : RuleForest → Index
  | .nil => .empty
  | .cons head tail => .node none (encodeTree scope head) (encodeForest scope tail)
end

def encode (scope : List ScopeFrame) : Cursor → Index
  | .tree tree => encodeTree scope tree
  | .forest forest => encodeForest scope forest

def lookup : Index → Route → Option Occurrence
  | .empty, _ => none
  | .node entry _ _, [] => entry
  | .node _ left _, false :: route => lookup left route
  | .node _ _ right, true :: route => lookup right route

def inventory : Index → List (Route × Occurrence)
  | .empty => []
  | .node entry left right =>
      (entry.toList.map fun occurrence => ([], occurrence)) ++
      (inventory left |>.map fun entry => (false :: entry.1, entry.2)) ++
      (inventory right |>.map fun entry => (true :: entry.1, entry.2))

theorem inventory_iff_lookup (index : Index) (route : Route) (occurrence : Occurrence) :
    (route, occurrence) ∈ inventory index ↔ lookup index route = some occurrence := by
  induction index generalizing route with
  | empty => simp [inventory, lookup]
  | node entry left right leftIH rightIH =>
      cases route with
      | nil => cases entry <;> simp [inventory, lookup, List.mem_map, Prod.exists, eq_comm]
      | cons bit route =>
          cases bit <;>
            simp [inventory, lookup, List.mem_map, Prod.exists, leftIH, rightIH, eq_comm]

/-- The index agrees with traversal of the unchanged original syntax. -/
theorem encode_lookup (scope : List ScopeFrame) (cursor : Cursor) (route : Route) :
    lookup (encode scope cursor) route = observe scope cursor route := by
  induction route generalizing scope cursor with
  | nil =>
      cases cursor with
      | tree tree => cases tree <;> rfl
      | forest forest => cases forest <;> rfl
  | cons bit route ih =>
      cases cursor with
      | tree tree =>
          cases tree <;> cases bit <;>
            simp only [encode, encodeTree, lookup, observe, advance, Option.bind_some,
              Option.bind_none] <;> first | rfl | apply ih
      | forest forest =>
          cases forest <;> cases bit <;>
            simp only [encode, encodeForest, lookup, observe, advance, Option.bind_some,
              Option.bind_none] <;> first | rfl | apply ih

theorem observe_eq_follow (scope : List ScopeFrame) (cursor : Cursor) (route : Route) :
    observe scope cursor route =
      (follow scope cursor route).bind (fun position =>
        payload position.enclosing position.cursor) := by
  induction route generalizing scope cursor with
  | nil => rfl
  | cons bit route ih =>
      simp only [observe, follow]
      cases advance scope cursor bit with
      | none => rfl
      | some position => simpa using ih position.enclosing position.cursor

def sourceIndex (context : Context) {category : Category} (source : Source category)
    (scope : List ScopeFrame := []) : Index :=
  encodeTree scope (sourceRules context source)

def sourceInventory (context : Context) {category : Category} (source : Source category)
    (scope : List ScopeFrame := []) : List (Route × Occurrence) :=
  inventory (sourceIndex context source scope)

theorem source_membership_iff (context : Context) {category : Category}
    (source : Source category) (scope : List ScopeFrame) (route : Route)
    (occurrence : Occurrence) :
    (route, occurrence) ∈ sourceInventory context source scope ↔
      observe scope (.tree (sourceRules context source)) route = some occurrence := by
  unfold sourceInventory
  rw [inventory_iff_lookup]
  change lookup (encode scope (.tree (sourceRules context source))) route = some occurrence ↔ _
  rw [encode_lookup]

theorem full_route_unique (context : Context) {category : Category}
    (source : Source category) (scope : List ScopeFrame) (route : Route)
    (first second : Occurrence)
    (hfirst : (route, first) ∈ sourceInventory context source scope)
    (hsecond : (route, second) ∈ sourceInventory context source scope) :
    first = second := by
  have h₁ := (source_membership_iff context source scope route first).mp hfirst
  have h₂ := (source_membership_iff context source scope route second).mp hsecond
  exact Option.some.inj (h₁.symm.trans h₂)

/-- Membership preserves the entire binder, enclosing telescope and original
generated body, rather than only its site or binder kind. -/
theorem source_provenance (context : Context) {category : Category}
    (source : Source category) (scope : List ScopeFrame) (route : Route)
    (occurrence : Occurrence)
    (member : (route, occurrence) ∈ sourceInventory context source scope) :
    ∃ binder body,
      follow scope (.tree (sourceRules context source)) route =
        some ⟨occurrence.enclosing, .tree (.existsE binder body)⟩ ∧
      logicalKind binder.kind = true ∧
      occurrence.binder = binder ∧ occurrence.subtree = body := by
  have found := (source_membership_iff context source scope route occurrence).mp member
  rw [observe_eq_follow] at found
  cases hfollow : follow scope (.tree (sourceRules context source)) route with
  | none => simp [hfollow] at found
  | some position =>
      simp only [hfollow, Option.bind_some] at found
      rcases position with ⟨enclosing, cursor⟩
      cases cursor with
      | forest forest => simp [payload] at found
      | tree tree =>
          cases tree with
          | existsE binder body =>
            simp only [payload] at found
            split at found
            next logical =>
              have eq : (⟨binder, enclosing, body⟩ : Occurrence) = occurrence :=
                Option.some.inj found
              cases eq
              exact ⟨binder, body, hfollow, logical, rfl, rfl⟩
            next => simp at found
          | rule _ _ _ _ _ => simp [payload] at found
          | forallE _ _ => simp [payload] at found
          | initializerE _ _ => simp [payload] at found
          | executionE _ _ => simp [payload] at found
          | sharedE _ _ => simp [payload] at found
          | publishGroup _ _ => simp [payload] at found
          | atPublication _ _ => simp [payload] at found
          | aliasPublication _ _ _ => simp [payload] at found
          | choice _ _ _ => simp [payload] at found

/-- Optional annotations contribute two structural steps, without a binder. -/
def annotationRoute (mark : Mark) : Route :=
  match mark.annotation with | none => [] | some _ => [false, false]

def appRule (context : Context) (mark : Mark)
    (callee argument : Source .expression) : RuleTree :=
  .rule .app mark.site context
    ((([.descriptorFormation, .wholeArgumentCompatibility,
        .completeCallCertificate, .sourceCallIncidence, .callableImage] ++
        if singletonFormalCall context callee argument then [.roleAndInitialCallOrigin] else []).map
      (fun kind => Premise.atom (atom kind mark.site context [callee.site, argument.site]))) ++
      [.checking ⟨.value, mark.site, context, ⟨callee.site, .returnedValue⟩,
        ⟨mark.site, .descriptor⟩⟩,
       .checking ⟨.computation, mark.site, context, ⟨mark.site, .callableImage⟩,
        ⟨mark.site, .synthesis⟩⟩])
    (.two (sourceRules context callee) (sourceRules context argument))

theorem app_exact (context : Context) (mark : Mark)
    (callee argument : Source .expression) (scope : List ScopeFrame) :
    observe scope (.tree (sourceRules context (.app mark callee argument)))
      (annotationRoute mark) =
      some ⟨⟨mark.site, .viewLogic, 0⟩, scope, appRule context mark callee argument⟩ := by
  rcases mark with ⟨site, annotation⟩
  cases annotation <;> simp only [sourceRules] <;> rfl

def formalContext (context : Context) (formal : Formal) (body : Source .expression) : Context :=
  {name := formal.name, owner := formal.site, kind := BindingKind.formal,
    annotation := formal.annotation, entry := some formal.entry,
    singleUse := body.nameCount formal.name == 1} :: context

def bodyContext (context : Context) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) : Context :=
  pattern.bindingRecords.filter (fun binding =>
    !((formalContext context formal body).any (fun prior => prior.name == binding.name))) ++
      formalContext context formal body

def bodyRule (context : Context) (mark : Mark) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) : RuleTree :=
  let inner := bodyContext context formal pattern body
  .rule .sequence body.site inner
    (([.completeBodyConsumer, .actualReturnOrPendingSuffix].map
      (fun kind => Premise.atom (atom kind body.site inner [mark.site, formal.site]))) ++
      [.checking ⟨.computation, body.site, inner, ⟨body.site, .finalRoot⟩,
        ⟨mark.site, .bodyConsumer⟩⟩])
    (.one (sourceRules inner body))

def bodyRoute (mark : Mark) (formal : Formal) : Route :=
  annotationRoute mark ++ [false, false, false, false, false, false, false, false] ++
    (match formal.entry with | .value => [false] | .computation => []) ++
    [false, false, true, false]

def bodyScope (scope : List ScopeFrame) (mark : Mark) (formal : Formal) : List ScopeFrame :=
  scope ++ [.existsE ⟨formal.site, .description, 0⟩,
    .existsE ⟨mark.site, .viewLogic, 0⟩,
    .forallE ⟨mark.site, .invocation, 0⟩,
    .existsE ⟨formal.site, .receipt, 0⟩] ++
    (match formal.entry with
      | .value => [.executionE ⟨formal.site, .returnRebind, 0⟩]
      | .computation => []) ++
    [.sharedE ⟨formal.site, .shared, 0⟩]

theorem lambda_body_exact (context : Context) (mark : Mark) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) (scope : List ScopeFrame) :
    observe scope (.tree (sourceRules context (.lambda mark formal pattern body)))
      (bodyRoute mark formal) =
      some ⟨⟨body.site, .eventProof, 0⟩, bodyScope scope mark formal,
        bodyRule context mark formal pattern body⟩ := by
  rcases mark with ⟨site, annotation⟩
  rcases formal with ⟨formalSite, formalName, formalAnnotation, outerComputation⟩
  cases annotation <;> cases outerComputation <;>
    simp only [sourceRules] <;>
    dsimp [bodyRoute, annotationRoute, Formal.entry, observe, advance, payload,
      logicalKind, bodyScope, bodyRule, bodyContext, formalContext,
      RuleForest.one, RuleForest.two] <;>
    simp only [List.append_assoc]

theorem app_inventory (context : Context) (mark : Mark)
    (callee argument : Source .expression) (scope : List ScopeFrame) :
    (annotationRoute mark,
      (⟨⟨mark.site, .viewLogic, 0⟩, scope, appRule context mark callee argument⟩ : Occurrence)) ∈
      sourceInventory context (.app mark callee argument) scope :=
  (source_membership_iff _ _ _ _ _).mpr (app_exact context mark callee argument scope)

theorem lambda_body_inventory (context : Context) (mark : Mark) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) (scope : List ScopeFrame) :
    (bodyRoute mark formal,
      (⟨⟨body.site, .eventProof, 0⟩, bodyScope scope mark formal,
        bodyRule context mark formal pattern body⟩ : Occurrence)) ∈
      sourceInventory context (.lambda mark formal pattern body) scope :=
  (source_membership_iff _ _ _ _ _).mpr
    (lambda_body_exact context mark formal pattern body scope)

end YulangClosure.OriginalSource.LogicalOccurrencesR93

-- These commands are deliberately in the leased module: the primary's direct
-- file check can print every delivered type and transitive axiom list without
-- creating an unleased audit file. No printed result is claimed before that check.
#check @YulangClosure.OriginalSource.LogicalOccurrencesR93.inventory_iff_lookup
#print axioms YulangClosure.OriginalSource.LogicalOccurrencesR93.inventory_iff_lookup
#check @YulangClosure.OriginalSource.LogicalOccurrencesR93.encode_lookup
#print axioms YulangClosure.OriginalSource.LogicalOccurrencesR93.encode_lookup
#check @YulangClosure.OriginalSource.LogicalOccurrencesR93.observe_eq_follow
#print axioms YulangClosure.OriginalSource.LogicalOccurrencesR93.observe_eq_follow
#check @YulangClosure.OriginalSource.LogicalOccurrencesR93.source_membership_iff
#print axioms YulangClosure.OriginalSource.LogicalOccurrencesR93.source_membership_iff
#check @YulangClosure.OriginalSource.LogicalOccurrencesR93.full_route_unique
#print axioms YulangClosure.OriginalSource.LogicalOccurrencesR93.full_route_unique
#check @YulangClosure.OriginalSource.LogicalOccurrencesR93.source_provenance
#print axioms YulangClosure.OriginalSource.LogicalOccurrencesR93.source_provenance
#check @YulangClosure.OriginalSource.LogicalOccurrencesR93.app_exact
#print axioms YulangClosure.OriginalSource.LogicalOccurrencesR93.app_exact
#check @YulangClosure.OriginalSource.LogicalOccurrencesR93.lambda_body_exact
#print axioms YulangClosure.OriginalSource.LogicalOccurrencesR93.lambda_body_exact
#check @YulangClosure.OriginalSource.LogicalOccurrencesR93.app_inventory
#print axioms YulangClosure.OriginalSource.LogicalOccurrencesR93.app_inventory
#check @YulangClosure.OriginalSource.LogicalOccurrencesR93.lambda_body_inventory
#print axioms YulangClosure.OriginalSource.LogicalOccurrencesR93.lambda_body_inventory

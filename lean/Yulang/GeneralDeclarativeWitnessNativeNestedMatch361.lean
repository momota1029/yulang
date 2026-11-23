import Yulang.GeneralDeclarativeWitnessNativeKinds361

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessNativeNestedMatch361
open GeneralDeclarativeWitnessNativeKinds361 (Ctor readCtor)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessNativeValue360 (Code Value FromCenters)
open GeneralDeclarativeWitnessNominalSource359 (SlotRead Route)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (Pattern)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty)

abbrev Captures := List (Nat × Capture)

/-- Exact, constructive unary-source reading. At a payload variable, copy
the independently captured interval of the writer's source variable, not
the numerical address of the installed native outer constructor. -/
inductive Matches (e : Environment) (locals : SlotRead) : Route → Code → Pattern → Captures → Type where
  | leaf {writer receiver} {span : Capture} (origin : locals writer = some span) :
    Matches e locals (.bind writer) (.leaf span.center) (.var receiver) [(receiver,span)]
  | empty (u : Ctor e key 0) :
    Matches e locals (.nullary key) (.nullary key) (.app key []) []
  | unary (u : Ctor e key 1) (payload : Matches e locals source code pat spans) :
    Matches e locals (.unary key source) (.unary key code) (.app key [pat]) spans

abbrev Found (e : Environment) (locals : SlotRead) (source : Route) (code : Code) (pat : Pattern) :=
  Σ captures, Matches e locals source code pat captures

def read (e : Environment) (locals : SlotRead) :
    (source : Route) → (code : Code) → (pat : Pattern) → Option (Found e locals source code pat)
  | .bind writer, .leaf actual, .var receiver =>
    match found : locals writer with
    | none => none
    | some span =>
      if same : span.center = actual then
        some ⟨[(receiver,span)],same ▸ Matches.leaf found⟩
      else none
  | .nullary routeKey, .nullary nativeKey, .app patternKey [] =>
    if a : routeKey = nativeKey then
      if b : nativeKey = patternKey then
        (readCtor e routeKey 0).map fun u => ⟨[],by rw [← b,← a]; exact Matches.empty u⟩
      else none
    else none
  | .unary routeKey source, .unary nativeKey actual, .app patternKey [pat] =>
    if a : routeKey = nativeKey then
      if b : nativeKey = patternKey then do
        let u ← readCtor e routeKey 1
        let m ← read e locals source actual pat
        some ⟨m.1,by rw [← b,← a]; exact Matches.unary u m.2⟩
      else none
    else none
  | _,_,_ => none

theorem source_centers {e locals source code pat caps} (m : Matches e locals source code pat caps) :
    FromCenters locals source code := by
  induction m with
  | leaf found => exact .leaf found
  | empty _ => exact .nil
  | unary _ _ premise => exact .cons premise

theorem every_captured_span_has_literal_origin {e locals source code pat caps} (m : Matches e locals source code pat caps) :
    ∀ member ∈ caps, ∃ writer, locals writer = some member.2 := by
  induction m with
  | leaf found =>
    intro binding present
    cases List.mem_singleton.mp present
    exact ⟨_,found⟩
  | empty _ => simp
  | unary _ _ ih => exact ih

inductive Meaning (e : Environment) : Value → Pattern → List (Nat × Ty) → Prop where
  | leaf : Meaning e (.leaf x) (.var receiver) [(receiver,x)]
  | empty (u : Ctor e key 0) : Meaning e (.nullary key) (.app key []) []
  | unary (u : Ctor e key 1) :
    Meaning e native pat bindings → Meaning e (.unary key native) (.app key [pat]) bindings

def values (m : Assignment) (caps : Captures) : List (Nat × Ty) :=
  caps.map fun pair => (pair.1,(m pair.2.center).1)

theorem independent_match_sound {e locals route code pat caps}
    (matched : Matches e locals route code pat caps) (m : Assignment) :
    Meaning e (code.eval m) pat (values m caps) := by
  induction matched with
  | leaf _ => exact .leaf
  | empty u => exact .empty u
  | unary u _ next => exact .unary u next

end Yulang.GeneralDeclarativeWitnessNativeNestedMatch361

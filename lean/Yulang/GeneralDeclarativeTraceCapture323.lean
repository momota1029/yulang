import Yulang.GeneralDeclarativeSemanticSharing323
import Yulang.GeneralDeclarativeTraceExpand323
import Yulang.GeneralDeclarativeAliasMeaning321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTraceCapture323
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeTermCapture322 (first repr_found)
open GeneralDeclarativeTraceExpand323 (convert)
open GeneralDeclarativeSemanticSharing323 (FirstNames SameBinder SharedAt sufficient)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeAliasMeaning321 (alias_sound)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)

def sourceName (o : Occurrence) : Option Nat :=
  match o.term with
  | .variable name => some name
  | _ => none

def reuse (raw : List GeneralDeclarativeTrace321.Occurrence) (range : Nat → Capture) (binder : Nat) :
    Capture :=
  let span := range binder
  let seen := raw.map convert
  ⟨span.lower,((first seen binder).bind sourceName).getD span.center,span.upper⟩

/-- Named actual traces already carry enough logical names. The
representative is the first actual source name, not a newly allocated
or model-dependent name. This says nothing about endpoint merging. -/
theorem anchored (s : State) (raw : List GeneralDeclarativeTrace321.Occurrence)
    (range : Nat → Capture) : FirstNames s (raw.map convert) (reuse raw range) := by
  intro n o found
  have belongs := (repr_found found).1
  obtain ⟨source,_,rfl⟩ := List.mem_map.mp belongs
  intro model valid
  simp only [reuse,found,Option.bind_some,sourceName,convert,Option.getD_some]
  exact eqv_refl (model source.argument).1

def OrdinarySharing (s : State) (raw : List GeneralDeclarativeTrace321.Occurrence) : Prop :=
  ∀ x ∈ raw, ∀ y ∈ raw, x.binder = y.binder → Alias s x.argument y.argument

theorem aliases_suffice {s : State} {raw : List GeneralDeclarativeTrace321.Occurrence}
    (sharing : OrdinarySharing s raw) :
    SameBinder s (raw.map convert) := by
  intro x hx y hy same m valid
  obtain ⟨o,old,rfl⟩ := List.mem_map.mp hx
  obtain ⟨p,other,rfl⟩ := List.mem_map.mp hy
  exact alias_sound (sharing o old p other same) m valid

theorem trace_shared {s : State} {raw : List GeneralDeclarativeTrace321.Occurrence}
    (mode : ∀ o ∈ raw, o.mode = .actual) (sharing : OrdinarySharing s raw)
    (range : Nat → Capture) :
    SharedAt s (raw.map convert) (reuse raw range) := by
  apply sufficient _ (aliases_suffice sharing) (anchored s raw range)
  intro o member
  obtain ⟨old,found,rfl⟩ := List.mem_map.mp member
  exact mode old found

end Yulang.GeneralDeclarativeTraceCapture323

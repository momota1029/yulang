import Yulang.GeneralDeclarativeBatch320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 13000
set_option maxHeartbeats 3400000
namespace Yulang.GeneralDeclarativeArgumentFacts320
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeAssembly320 (Head)
open GeneralDeclarativeNormalized320 (NormalArg ordered_map)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralDeclarativeBatch320 (zipFacts zip_sound)
open CommonRoleOutermostResolver (All₂)

def headFact (c : Constructors) (interp : Interpretation) (capture : Nat → Capture)
    (arg : Capture) (p : Pattern) : Option (List Equation) :=
  (translate c interp p).map fun e => [⟨arg.center,logical capture .actual e⟩]

def whereFacts (c : Constructors) (interp : Interpretation) (capture : Nat → Capture)
    (arg : Capture) (p : Pattern) : Option (List Equation) :=
  (translate c interp (normalize p)).map fun e =>
    [⟨arg.lower,logical capture .lower e⟩,⟨arg.center,logical capture .actual e⟩,
      ⟨arg.upper,logical capture .upper e⟩]

theorem head_fact {s c interp capture arg p facts}
    (generated : headFact c interp capture arg p = some facts)
    (settled : facts ⊆ s.equations) (bound : Bounds s arg) :
    Head s c interp capture arg p := by
  cases hx : translate c interp p with
  | none => simp [headFact,hx] at generated
  | some e =>
    have eq : [⟨arg.center,logical capture .actual e⟩] = facts := by
      simpa [headFact,hx] using generated
    subst facts
    exact ⟨bound,e,hx,.direct (.whole (settled List.mem_cons_self))⟩

theorem where_fact {s c interp capture arg p facts}
    (generated : whereFacts c interp capture arg p = some facts)
    (settled : facts ⊆ s.equations) :
    NormalArg s c interp capture arg p := by
  cases hx : translate c interp (normalize p) with
  | none => simp [whereFacts,hx] at generated
  | some e =>
    have eq : [⟨arg.lower,logical capture .lower e⟩,⟨arg.center,logical capture .actual e⟩,
      ⟨arg.upper,logical capture .upper e⟩] = facts := by simpa [whereFacts,hx] using generated
    subst facts
    exact ⟨e,hx,.whole (settled List.mem_cons_self),
      .whole (settled (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))),
      .direct (.whole (settled (List.mem_cons_of_mem _ List.mem_cons_self)))⟩

theorem compiled_head {s c interp capture args ps facts}
    (generated : zipFacts (headFact c interp capture) args ps = some facts)
    (settled : facts ⊆ s.equations) (bounds : ∀ arg ∈ args, Bounds s arg) :
    All₂ (Head s c interp capture) args ps := by
  apply ordered_map (zip_sound generated)
  rintro arg there p _ ⟨batch,compiled,included⟩
  exact head_fact compiled (fun _ h => settled (included h)) (bounds arg there)

theorem compiled_where {s c interp capture args ps facts}
    (generated : zipFacts (whereFacts c interp capture) args ps = some facts)
    (settled : facts ⊆ s.equations) :
    All₂ (NormalArg s c interp capture) args ps := by
  apply ordered_map (zip_sound generated)
  rintro arg _ p _ ⟨batch,compiled,included⟩
  exact where_fact compiled (fun _ h => settled (included h))

end Yulang.GeneralDeclarativeArgumentFacts320

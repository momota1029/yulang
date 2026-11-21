import Yulang.GeneralDeclarativeEqualities322
import Yulang.GeneralDeclarativeNormalSupport321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeProjectedLower322
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeEqualities322 (Derives entails)
open GeneralDeclarativeNormalSupport321 (NormalSupport observed restricted_valid)
open GeneralDeclarativeLowerKnown321 (Tag Knows constructorTag)
open GeneralDeclarativeDemand320 (Demand)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeEntailment320 (Entails)

/-- Ordinary normalization may expose the head of a logical name without
a literal constructor row at that name (for example a pair projection).
Only the source/finished observation state may justify this fact. -/
def Exposed (s : State) (name : Nat) (tag : Tag) : Prop :=
  ∃ head, constructorTag head = some tag ∧ Derives s (.variable name) head

def Ready (p : NormalSupport s completed) (d : Demand) : Prop :=
  ∀ arg ∈ d.arguments, ∃ tag, Exposed (observed p) arg.lower tag

theorem from_linked_equation {s : State} (known : Knows s name tag) :
    Exposed s name tag := by
  obtain ⟨row,listed,alias,shape⟩ := known
  exact ⟨row.right,shape,.trans (.congruent (.variable alias)) (.row listed)⟩

theorem justified_projection {s : State} (p : NormalSupport s completed)
    (derived : Derives (observed p) (.variable name) head) :
    Entails s ⟨name,head⟩ :=
  fun m valid => entails derived m (restricted_valid p m valid)

/-- In a supported pair equation, only the relevant projected value needs
the constructor known. The other coordinate can remain opaque. -/
theorem pair_first_head {s : State}
    (one : Derives s (.variable pairName) (.primitive .pair [a,b]))
    (two : Derives s (.variable pairName) (.primitive .pair [x,y]))
    (asName : Derives s (.variable lower) a)
    (reveals : Derives s x head) (tag : constructorTag head = some k) :
    Exposed s lower k :=
  ⟨head,tag,.trans asName (.trans (.pairFirst (.trans (.symm one) two)) reveals)⟩

end Yulang.GeneralDeclarativeProjectedLower322

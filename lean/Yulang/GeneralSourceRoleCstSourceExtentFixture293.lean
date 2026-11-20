import Yulang.GeneralSourceRoleCstSourceExtent293
import Yulang.GeneralSourceRoleCstConsumerFixture293

/-! Concrete control: the attached output points to the defaulted direct
member, not to the earlier top-level declaration with the same name. -/
namespace Yulang.GeneralSourceRoleCstSourceExtentFixture293
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstSpan293 (Extent)
open GeneralSourceRoleCstSourceExtent293 (lookupExtent)
open GeneralSourceRoleCstConsumerFixture293 (stored)
open GeneralSourceRoleCstFixture293 (namedBody sigil required)
open GeneralSourceRoleCstTree293 (Tree)

def selected : Address Nat := ⟨10,[2,6,1,0]⟩
def topLevel : Address Nat := ⟨10,[0]⟩
def anotherParse : Address Nat := ⟨11,[2,6,1,0]⟩

theorem direct_default_span :
    lookupExtent stored selected = some (namedBody (sigil "'key"),⟨47,64⟩) := rfl

theorem earlier_top_level_not_same :
    lookupExtent stored topLevel = some (required,⟨0,10⟩) ∧
    selected.path ≠ topLevel.path := ⟨rfl,by decide⟩

theorem foreign_extent_rejected : lookupExtent stored anotherParse = none := rfl

#guard (lookupExtent stored anotherParse).isNone

end Yulang.GeneralSourceRoleCstSourceExtentFixture293

import Yulang.GeneralRebasePairKeys261
namespace Yulang.GeneralRebaseStableBody261
open GeneralNominalCenters
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseStep258 (Fact)

/-- One fixed plan supplies each named body's meaning, independently of which
subset of requests is observed now. Changing the plan still requires a bridge. -/
def Holds (plan : Plan roles) (owner : Nat) (assignment : Assignment) (fact : Fact) : Prop :=
 ∀ output, fact ∈ GeneralRebaseBodyTable261.keys plan owner output →
 GeneralRebaseBodyTable261.localHolds plan owner output assignment fact

theorem collision (plan : Plan roles) (owner : Nat) (first last : Output) (fact : Fact)
 (one : fact ∈ GeneralRebaseBodyTable261.keys plan owner first)
 (two : fact ∈ GeneralRebaseBodyTable261.keys plan owner last) : first = last := by
 classical
 by_cases same : first = last
 · exact same
 · exact False.elim (GeneralRebaseBodyTable261.different_requests plan owner first last same fact ⟨one,two⟩)

theorem all_exact (plan : Plan roles) (owner : Nat) (outputs : List Output) (assignment : Assignment) :
 (∀ fact ∈ GeneralRebaseBodyTable261.facts plan owner outputs, Holds plan owner assignment fact) ↔
 ∀ output ∈ outputs, ∀ body,
 GeneralDictionaryAssociatedProvenance.lookup roles plan.packet.declaration output.name = some body →
 GeneralNominalVersionedEffects231.BodyHolds plan output.target assignment body := by
 constructor
 · intro valid output included
   apply (GeneralRebaseBodyTable261.local_exact ..).mp
   intro fact within
   exact valid fact ((GeneralRebaseBodyTable261.member ..).mpr ⟨output,included,within⟩) output within
 · intro valid fact included other within
   obtain ⟨output,present,belongs⟩ := (GeneralRebaseBodyTable261.member ..).mp included
   have same := collision plan owner output other fact belongs within
   subst other
   exact (GeneralRebaseBodyTable261.local_exact ..).mpr (valid output present) fact belongs

theorem pair_outside (plan : Plan roles) (owner : Nat) (first last output : Output) :
 GeneralRebasePairKeys261.key owner first last ∉ GeneralRebaseBodyTable261.keys plan owner output := by
 intro member
 obtain ⟨index,same⟩ := (GeneralRebaseOwnedOutputKeys260.member ..).mp member
 exact GeneralRebasePairKeys261.body_separate owner first last (GeneralRebaseNamedRequest260.code output) index.val same

theorem at_pair (plan : Plan roles) (owner : Nat) (first last : Output) (assignment : Assignment) :
 Holds plan owner assignment (GeneralRebasePairKeys261.key owner first last) := by
 intro output member
 exact False.elim (pair_outside plan owner first last output member)

theorem pair_at_body (plan : Plan roles) (owner : Nat) (output : Output) (assignment : Assignment) (fact : Fact)
 (member : fact ∈ GeneralRebaseBodyTable261.keys plan owner output) :
 GeneralRebasePairKeys261.Holds owner assignment fact := by
 intro first last same
 subst fact
 exact False.elim (pair_outside plan owner first last output member)

theorem monotone (plan : Plan roles) (owner : Nat) (small large : List Output)
 (included : ∀ output ∈ small, output ∈ large) :
 ∀ fact ∈ GeneralRebaseBodyTable261.facts plan owner small,
 fact ∈ GeneralRebaseBodyTable261.facts plan owner large := by
 intro fact present
 obtain ⟨output,one,two⟩ := (GeneralRebaseBodyTable261.member ..).mp present
 exact (GeneralRebaseBodyTable261.member ..).mpr ⟨output,included _ one,two⟩
end Yulang.GeneralRebaseStableBody261

import Yulang.GeneralRebaseExecutableRequests262
import Yulang.GeneralRebaseClassCheck261

namespace Yulang.GeneralRebaseMultiSelection263
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceDictionaries (Occurrence)

structure Selection (roles : Roles.RoleDecls) where
 owner : Nat
 root : Occurrence roles
 plan : Plan roles

/-- Owner identities distinguish both demand identity and declaration identity. -/
def ofPlan (plan : Plan roles) : Selection roles :=
 ⟨GeneralNominalIdentities.pair plan.packet.site.occurrence.identity plan.packet.declaration.id,
   plan.packet.site.occurrence,plan⟩

def registered (source : GeneralNominalCenteredSteps.State roles) : List (Selection roles) :=
 source.plans.map ofPlan

def requests (source : GeneralNominalCenteredSteps.State roles) (selected : Selection roles) :=
 GeneralRebaseExecutableRequests262.requests source selected.root

def proposal (source : GeneralNominalCenteredSteps.State roles) (selected : Selection roles) : Proposal :=
 GeneralRebaseStableClass261.facts selected.plan selected.owner (requests source selected)

theorem registered_exact (source : GeneralNominalCenteredSteps.State roles) (selected : Selection roles) :
 selected ∈ registered source ↔ ∃ plan ∈ source.plans, ofPlan plan = selected := List.mem_map

structure Diagnostic (roles : Roles.RoleDecls) where
 selected : Selection roles
 reason : GeneralRebaseClassCheck261.Failure

def check (source : GeneralNominalCenteredSteps.State roles) : List (Selection roles) → Except (Diagnostic roles) Unit
 | [] => .ok ()
 | selected :: rest =>
   match GeneralRebaseClassCheck261.check selected.plan (requests source selected) with
   | .error reason => .error ⟨selected,reason⟩
   | .ok () => check source rest

def Ready (source : GeneralNominalCenteredSteps.State roles) (selected : List (Selection roles)) : Prop :=
 ∀ entry ∈ selected, GeneralRebaseClassCheck261.Ready entry.plan (requests source entry)

theorem check_exact (source : GeneralNominalCenteredSteps.State roles) (selected : List (Selection roles)) :
 check source selected = .ok () ↔ Ready source selected := by
 induction selected with
 | nil => simp [check,Ready]
 | cons entry rest ih =>
   simp only [check]
   cases result : GeneralRebaseClassCheck261.check entry.plan (requests source entry) with
   | error reason =>
     constructor
     · intro equal; cases equal
     · intro ready
       have checked := (GeneralRebaseClassCheck261.check_exact ..).mpr (ready entry List.mem_cons_self)
       rw [result] at checked
       cases checked
   | ok checkedUnit =>
     cases checkedUnit
     rw [ih]
     constructor
     · intro tail found member
       rcases List.mem_cons.mp member with rfl | member
       · exact (GeneralRebaseClassCheck261.check_exact ..).mp result
       · exact tail found member
     · intro ready found member
       exact ready found (List.mem_cons_of_mem _ member)

theorem error_selected (source : GeneralNominalCenteredSteps.State roles) (selected : List (Selection roles))
 (reason : Diagnostic roles) (failed : check source selected = .error reason) :
 reason.selected ∈ selected ∧
 GeneralRebaseClassCheck261.check reason.selected.plan (requests source reason.selected) = .error reason.reason := by
 induction selected with
 | nil => cases failed
 | cons entry rest ih =>
   unfold check at failed
   split at failed
   · rename_i error checked
     cases Except.error.inj failed
     exact ⟨List.mem_cons_self,checked⟩
   · obtain ⟨member,diagnostic⟩ := ih failed
     exact ⟨List.mem_cons_of_mem _ member,diagnostic⟩
end Yulang.GeneralRebaseMultiSelection263

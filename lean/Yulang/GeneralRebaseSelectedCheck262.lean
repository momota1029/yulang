import Yulang.GeneralRebaseObservedPlan262

namespace Yulang.GeneralRebaseSelectedCheck262
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralSourceDictionaries (Occurrence)

/-- An internal translation diagnostic for one actually selected root.
This does not classify a source program as rejected. -/
structure Failure (roles : Roles.RoleDecls) where
 root : Occurrence roles
 reason : GeneralRebaseClassCheck261.Failure

def checkRoots (source : GeneralNominalCenteredSteps.State roles)
 (plans : Occurrence roles → Plan roles) : List (Occurrence roles) → Except (Failure roles) Unit
 | [] => .ok ()
 | root :: rest =>
   match GeneralRebaseClassCheck261.check (plans root) (GeneralRebaseExecutableRequests262.requests source root) with
   | .error reason => .error ⟨root,reason⟩
   | .ok () => checkRoots source plans rest

def ReadyRoots (source : GeneralNominalCenteredSteps.State roles)
 (plans : Occurrence roles → Plan roles) (roots : List (Occurrence roles)) : Prop :=
 ∀ root ∈ roots, GeneralRebaseClassCheck261.Ready (plans root) (GeneralRebaseExecutableRequests262.requests source root)

theorem check_exact (source : GeneralNominalCenteredSteps.State roles)
 (plans : Occurrence roles → Plan roles) (roots : List (Occurrence roles)) :
 checkRoots source plans roots = .ok () ↔ ReadyRoots source plans roots := by
 induction roots with
 | nil => simp [checkRoots,ReadyRoots]
 | cons root rest ih =>
   unfold checkRoots
   cases result : GeneralRebaseClassCheck261.check (plans root) (GeneralRebaseExecutableRequests262.requests source root) with
   | error reason =>
     constructor
     · intro impossible; cases impossible
     · intro ready
       have accepted := (GeneralRebaseClassCheck261.check_exact ..).mpr (ready root List.mem_cons_self)
       rw [result] at accepted
       cases accepted
   | ok resultUnit =>
     cases resultUnit
     rw [ih]
     constructor
     · intro ready item member
       rcases List.mem_cons.mp member with rfl | tail
       · exact (GeneralRebaseClassCheck261.check_exact ..).mp result
       · exact ready item tail
     · intro ready item member
       exact ready item (List.mem_cons_of_mem _ member)

theorem error_selected (source : GeneralNominalCenteredSteps.State roles)
 (plans : Occurrence roles → Plan roles) (roots : List (Occurrence roles)) (failure : Failure roles)
 (failed : checkRoots source plans roots = .error failure) :
 failure.root ∈ roots ∧ GeneralRebaseClassCheck261.check (plans failure.root)
   (GeneralRebaseExecutableRequests262.requests source failure.root) = .error failure.reason := by
 induction roots with
 | nil => cases failed
 | cons root rest ih =>
   unfold checkRoots at failed
   split at failed
   · rename_i reason result
     cases Except.error.inj failed
     exact ⟨List.mem_cons_self,result⟩
   · obtain ⟨member,result⟩ := ih failed
     exact ⟨List.mem_cons_of_mem _ member,result⟩

/-- Readiness is exactly the existing actual-snapshot body readiness predicate,
not a demand for every possible candidate-pool pair to translate. -/
theorem actual_ready (source : GeneralNominalCenteredSteps.State roles)
 (plans : Occurrence roles → Plan roles) (roots : List (Occurrence roles)) :
 ReadyRoots source plans roots ↔ ∀ root ∈ roots,
 GeneralNominalCenteredHeadMatEffects.Ready source root (plans root) := by
 unfold ReadyRoots
 simp only [GeneralRebaseExecutableRequests262.requests_eq,
   ← GeneralRebaseClassCheck261.check_exact,GeneralRebaseClassCheck261.actual_ready]
end Yulang.GeneralRebaseSelectedCheck262

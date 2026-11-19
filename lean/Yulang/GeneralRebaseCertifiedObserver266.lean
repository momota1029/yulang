import Yulang.GeneralRebaseProjectionSettle266

namespace Yulang.GeneralRebaseCertifiedObserver266
open GeneralRebaseStep258
open GeneralRebaseCompression266 (Basis)
open GeneralRebaseLiveProjection264 (SourceState project)
open GeneralSourceState (Output)

/-- A supplied source edge plus its kernel certificate. The observation
function is executable on the supplied list; discovery of the list is outside
this definition. -/
structure Edge (registry : GeneralDeclarations.Registry)
 (root : GeneralSourceDictionaries.Occurrence roles) where
 before : SourceState roles
 after : SourceState roles
 actual : GeneralNominalVersionedMixedKernel234.Step registry root before after

variable {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}

def chosen (owners : List Nat) (pool : List Output) (state : State (Basis owners pool))
 (edge : Edge registry root) : Bool :=
 decide ((project owners pool edge.before).remaining = state.remaining) &&
   !(decide ((project owners pool edge.after).remaining = state.remaining))

theorem chosen_exact (owners : List Nat) (pool : List Output) (state : State (Basis owners pool))
 (edge : Edge registry root) : chosen owners pool state edge = true ↔
 project owners pool edge.before = state ∧ project owners pool edge.after ≠ state := by
 simp only [chosen,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',decide_eq_false_iff_not]
 constructor
 · rintro ⟨first,last⟩
   exact ⟨state_ext _ _ first,fun equal => last (congrArg State.remaining equal)⟩
 · rintro ⟨first,last⟩
   exact ⟨congrArg State.remaining first,fun equal => last (state_ext _ _ equal)⟩

def observe (owners : List Nat) (pool : List Output) (edges : List (Edge registry root)) :
 Observer (Basis owners pool) :=
 fun state => (edges.filter (chosen owners pool state)).map fun edge =>
   present (project owners pool edge.after)

theorem membership (owners : List Nat) (pool : List Output) (edges : List (Edge registry root))
 (first : State (Basis owners pool)) (proposal : Proposal) :
 proposal ∈ observe owners pool edges first ↔
 ∃ edge ∈ edges, project owners pool edge.before = first ∧
   project owners pool edge.after ≠ first ∧ present (project owners pool edge.after) = proposal := by
 simp only [observe,List.mem_map,List.mem_filter,chosen_exact]
 constructor
 · rintro ⟨edge,⟨member,first,last⟩,eq⟩
   exact ⟨edge,member,first,last,eq⟩
 · rintro ⟨edge,member,first,last,eq⟩
   exact ⟨edge,⟨member,first,last⟩,eq⟩

theorem step_exact (owners : List Nat) (pool : List Output) (edges : List (Edge registry root))
 (first last : State (Basis owners pool)) :
 Step (observe owners pool edges) first last ↔
 ∃ edge ∈ edges, project owners pool edge.before = first ∧
   project owners pool edge.after = last ∧ last ≠ first := by
 constructor
 · rintro ⟨proposal,listed,change,_⟩
   obtain ⟨edge,member,starts,different,rfl⟩ := (membership owners pool edges first proposal).mp listed
   have exactWrite := GeneralRebaseProjectionObserver266.witness_write owners pool
     (⟨edge.before,edge.after,edge.actual,starts,rfl⟩ :
        GeneralRebaseProjectionObserver266.Witness owners pool registry root first (project owners pool edge.after))
   rw [exactWrite] at change
   exact ⟨edge,member,starts,change.symm, fun same => different (change.symm.trans same)⟩
 · rintro ⟨edge,member,starts,ends,different⟩
   have exactWrite := GeneralRebaseProjectionObserver266.witness_write owners pool
     (⟨edge.before,edge.after,edge.actual,starts,ends⟩ :
        GeneralRebaseProjectionObserver266.Witness owners pool registry root first last)
   refine ⟨present last,(membership owners pool edges first _).mpr
     ⟨edge,member,starts,fun same => different (ends.symm.trans same),congrArg present ends⟩,
     exactWrite.symm,?_⟩
   exact fun same => different (state_ext _ _ same)

theorem closed (owners : List Nat) (pool : List Output) (edges : List (Edge registry root)) :
 GeneralRebaseClosedObserver259.Closed (observe owners pool edges) := by
 intro state selected listed fact member
 obtain ⟨edge,_,_,_,rfl⟩ := (membership owners pool edges state selected).mp listed
 exact ((GeneralRebaseFactSemantics259.present_iff _ fact).mp member).1

theorem observer_bound (owners : List Nat) (pool : List Output)
 (edges : List (Edge registry root)) (state : State (Basis owners pool)) :
 (observe owners pool edges state).length ≤ edges.length := by
 unfold observe
 rw [List.length_map]
 exact List.length_filter_le _ _

end Yulang.GeneralRebaseCertifiedObserver266

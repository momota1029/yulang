import Yulang.GeneralNominalRegistryInvariant250
/-! Requests can alternate registered owners without losing raw coverage.
Unknown owners fail internal preparation. New packet/delta generation and
source acceptance remain outside this finite command compiler. -/
namespace Yulang.GeneralNominalMultiOwnerCommands250
open GeneralNominalMaterializedOwnerFrame249 (Frame)
open GeneralNominalOwnerOpening250 (Handle)
open GeneralNominalOwnerRegistry250 (lookup Registered)
open GeneralNominalJournalAppend250 (Delta)
open GeneralNominalFiniteInstallTrace250 (Command)
open GeneralNominalInstallCoverage250 (Covered)
open GeneralPresenceOwnerRewrite244 (Coherent)
open GeneralPresenceOrderedDependence247 (TargetsWithin)
open GeneralPresenceOrderedBlock247

structure Request where
 root : Nat
 declaration : Nat
 bindings : GeneralNominalAllocation.Bindings
 delta : Delta

def compile (handles : List Handle) (request : Request) : Option Command :=
 (lookup handles request.root request.declaration).map fun handle =>
 ⟨GeneralNominalRebaseDefinitions241.entries handle.seed handle.root handle.declaration request.bindings handle.names,request.delta⟩

def compileMany (handles : List Handle) : List Request → Option (List Command)
 | [] => some []
 | request :: rest => (compile handles request).bind fun command =>
   (compileMany handles rest).map (command :: ·)

theorem compile_sound (frame : Frame) (handles : List Handle) (registered : Registered frame handles)
 (request : Request) (command : Command) (success : compile handles request = some command) :
 TargetsWithin command.raw frame.definitions ∧ Coherent command.raw := by
 unfold compile at success
 cases found : lookup handles request.root request.declaration with
 | none => simp [found] at success
 | some handle =>
   simp only [found,Option.map_some,Option.some.injEq] at success
   subst command
   exact ⟨GeneralNominalOwnerRegistry250.handle_coverage frame handles registered handle
     (GeneralNominalRegistryInvariant250.lookup_fields handles _ _ handle found).2.2 request.bindings,
     GeneralNominalRebaseDefinitions241.coherent handle.seed handle.root handle.declaration request.bindings handle.names⟩

theorem compileMany_members (frame : Frame) (handles : List Handle) (registered : Registered frame handles)
 (requests : List Request) (commands : List Command) (success : compileMany handles requests = some commands) :
 ∀ command ∈ commands, TargetsWithin command.raw frame.definitions ∧ Coherent command.raw := by
 induction requests generalizing commands with
 | nil => simp [compileMany] at success; subst commands; simp
 | cons request rest ih =>
   cases found : compile handles request with
   | none => simp [compileMany,found] at success
   | some command =>
     cases tail : compileMany handles rest with
     | none => simp [compileMany,found,tail] at success
     | some commandsTail =>
       simp only [compileMany,found,Option.bind_some,tail,Option.map_some,Option.some.injEq] at success
       subst commands
       intro chosen member
       rcases List.mem_cons.mp member with rfl | member
       · exact compile_sound frame handles registered request chosen found
       · exact ih commandsTail tail chosen member

theorem compileMany_covered (frame : Frame) (handles : List Handle) (registered : Registered frame handles)
 (requests : List Request) (commands : List Command) (success : compileMany handles requests = some commands) :
 Covered frame commands :=
 GeneralNominalInstallCoverage250.covered_from_initial frame commands
   (fun command member => (compileMany_members frame handles registered requests commands success command member).1)
   (fun command member => (compileMany_members frame handles registered requests commands success command member).2)

theorem checked_success (frame : Frame) (safe : SafeOrder frame.definitions)
 (handles : List Handle) (registered : Registered frame handles)
 (requests : List Request) (commands : List Command) (success : compileMany handles requests = some commands) :
 GeneralNominalCheckedInstall250.run frame commands = some (GeneralNominalFiniteInstallTrace250.run frame commands) :=
 GeneralNominalCheckedInstall250.run_success frame safe commands (compileMany_covered frame handles registered requests commands success)
end Yulang.GeneralNominalMultiOwnerCommands250

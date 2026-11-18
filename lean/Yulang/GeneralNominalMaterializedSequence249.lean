import Yulang.GeneralNominalMaterializedOwnerFrame249
import Yulang.GeneralNominalJournalSubstClosed249
/-! Literal fixed-metadata normalization along an explicitly supplied finite
refresh list. New metadata and growing definition bodies are not bounded. -/
namespace Yulang.GeneralNominalMaterializedSequence249
open GeneralNominalMaterializedOwnerFrame249
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedDependence247 GeneralPresenceOrderedSubstitution247

abbrev Block := List (Entry Nat)

def canonical (frame : Frame) (current : Block) : Frame :=
 ⟨GeneralNominalJournalSubst249.subst (mapping frame.definitions) frame.metadata,
  rewrite frame.definitions frame.consumers,current⟩

def run (frame : Frame) : List Block → Frame
 | [] => frame
 | next :: rest => run (rebase frame next) rest

def finalBlock (current : Block) : List Block → Block
 | [] => current
 | next :: rest => finalBlock next rest

theorem rebase_twice (frame : Frame) (first last : Block)
 (safe : SafeOrder frame.definitions) (within : TargetsWithin first frame.definitions) :
 rebase (rebase frame first) last = canonical frame last := by
 simp only [rebase,canonical,
   GeneralNominalJournalSubstClosed249.journal_absorbs frame.definitions first safe within,
   GeneralPresenceOrderedSyntax247.rewrite_absorbs frame.definitions first safe within]

theorem rebase_canonical (frame : Frame) (current next : Block)
 (safe : SafeOrder frame.definitions) (within : TargetsWithin current frame.definitions) :
 rebase (canonical frame current) next = canonical frame next :=
 rebase_twice frame current next safe within

theorem run_canonical (frame : Frame) (current : Block) (blocks : List Block)
 (safe : SafeOrder frame.definitions) (withinCurrent : TargetsWithin current frame.definitions)
 (withinBlocks : ∀ block ∈ blocks, TargetsWithin block frame.definitions) :
 run (canonical frame current) blocks = canonical frame (finalBlock current blocks) := by
 induction blocks generalizing current with
 | nil => rfl
 | cons next rest ih =>
   rw [run,rebase_canonical frame current next safe withinCurrent]
   exact ih next (withinBlocks next (by simp)) (fun block member => withinBlocks block (by simp [member]))

theorem run_nonempty (frame : Frame) (first : Block) (rest : List Block)
 (safe : SafeOrder frame.definitions) (within : ∀ block ∈ first :: rest, TargetsWithin block frame.definitions) :
 run frame (first :: rest) = canonical frame (finalBlock first rest) :=
 run_canonical frame first rest safe (within first (by simp)) (fun block member => within block (by simp [member]))

theorem metadata_fixed (frame : Frame) (first : Block) (rest : List Block)
 (safe : SafeOrder frame.definitions) (within : ∀ block ∈ first :: rest, TargetsWithin block frame.definitions) :
 (run frame (first :: rest)).metadata = (rebase frame first).metadata := by
 rw [run_nonempty frame first rest safe within]
 rfl

theorem consumers_fixed (frame : Frame) (first : Block) (rest : List Block)
 (safe : SafeOrder frame.definitions) (within : ∀ block ∈ first :: rest, TargetsWithin block frame.definitions) :
 (run frame (first :: rest)).consumers = (rebase frame first).consumers := by
 rw [run_nonempty frame first rest safe within]
 rfl

theorem run_formed (frame : Frame) (formed : Formed frame) (blocks : List Block)
 (safe : ∀ block ∈ blocks, SafeOrder block) : Formed (run frame blocks) := by
 induction blocks generalizing frame with
 | nil => exact formed
 | cons next rest ih =>
   exact ih (rebase frame next) (rebase_formed frame formed next (safe next (by simp)))
     (fun block member => safe block (by simp [member]))
end Yulang.GeneralNominalMaterializedSequence249

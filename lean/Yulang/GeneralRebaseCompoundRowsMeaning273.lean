import Yulang.GeneralRebaseCompoundRows273

namespace Yulang.GeneralRebaseCompoundRowsMeaning273
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseCompoundRows273 (Agrees)
open GeneralRebaseCompoundFiniteMeaning273 (Meaning support)
open GeneralRebaseCompoundSourceTypes273 (before_exact source_depends_on_types restricted_exact)
open GeneralRebaseSourceStrictFixture265 (owners pool)
open GeneralRebaseLiveProjection264 (project)
open GeneralNominalVersionedJournal232 (Models)
open GeneralDictionaryCompoundFrame238 (before installed)
open GeneralDictionaryCompoundPoint238 (point)
open GeneralRebaseSourceStepDriver270 (next)

def Public (s : GeneralNominalVersionedJournal232.State GeneralDictionaryJournalRefinement228Source.roles)
 (boundary : Assignment) : Prop := ∃ m, Agrees m boundary ∧ Models s m

theorem before_public (boundary : Assignment) :
 Public before boundary ↔ Meaning (project owners pool before) boundary := by
 rw [GeneralRebaseSourceStepDriver270.Compound.computed_initial,Meaning,GeneralRebaseFactSemantics259.initial_exact]
 constructor
 · rintro ⟨model,same,good⟩
   exact (source_depends_on_types model boundary (fun id small => congrArg Prod.fst (same.1 id small))).mp
    ((before_exact model).mp good)
 · intro good
   exact ⟨boundary,⟨fun _ _ => rfl,fun _ => rfl⟩,(before_exact _).mpr good⟩

theorem installed_public (boundary : Assignment) :
 Public installed boundary ↔ Meaning (project owners pool installed) boundary :=
 (GeneralRebaseCompoundRows273.public_exact boundary).trans
   ((GeneralRebaseCompoundPublic273.public_exact boundary).symm.trans
     (GeneralRebaseCompoundFiniteMeaning273.original_installed_public boundary))

theorem point_public (boundary : Assignment) :
 Public point boundary ↔ Meaning (project owners pool installed) boundary :=
 (exists_congr (fun m => and_congr Iff.rfl (GeneralDictionaryCompoundPoint238.models_iff m))).trans
   (installed_public boundary)

/-- Pointwise in every joint public assignment, the executable strict step
agrees with the genuine original after-journal. The row component of every
identity, including private type slots, is literally unchanged on completion. -/
theorem computed_public_step :
 ∃ finish, next support (project owners pool before) = some finish ∧
   ∀ boundary : Assignment, Meaning finish boundary ↔ Public installed boundary :=
 ⟨project owners pool installed,GeneralRebaseSourceStepDriver270.Compound.matches_concrete,
   fun boundary => (installed_public boundary).symm⟩

theorem full_completion_of_computed (finish : GeneralRebaseStep258.State support)
 (computed : next support (project owners pool before) = some finish)
 (boundary : Assignment) (accepted : Meaning finish boundary) :
 Agrees (GeneralRebaseCompoundRows273.completeRows boundary) boundary ∧
 Models installed (GeneralRebaseCompoundRows273.completeRows boundary) := by
 have identified : finish = project owners pool installed :=
   Option.some.inj (computed.symm.trans GeneralRebaseSourceStepDriver270.Compound.matches_concrete)
 subst finish
 have fixed := (GeneralRebaseCompoundRows273.public_exact boundary).mp ((installed_public boundary).mpr accepted)
 exact ⟨GeneralRebaseCompoundRows273.complete_rows boundary,GeneralRebaseCompoundRows273.complete_valid boundary fixed⟩

end Yulang.GeneralRebaseCompoundRowsMeaning273

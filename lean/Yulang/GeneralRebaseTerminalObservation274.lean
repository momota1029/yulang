import Yulang.GeneralRebaseTerminalActivation274

set_option maxRecDepth 22000
set_option maxHeartbeats 7300000
namespace Yulang.GeneralRebaseTerminalObservation274
open GeneralNominalCandidates (Context)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalAllocation (Bindings)
open GeneralDeclarations (Declaration)
open GeneralNominalRecursiveCandidates (arguments report)
open GeneralNominalRecursiveInspection (bindings Finished)
open GeneralDictionaryJournalRefinement228Source (root context)
open GeneralDictionaryOptionalInitial229 (declaration)
open GeneralDictionaryVersionedPointStage233 (point)
open GeneralRebaseTerminalMachine274 (Stage Event next owner firstBindings pointBindings)

def collect (c : Context) (focus : Occurrence roles) (candidate : Declaration) : Option Bindings := do
 let bounds ← arguments c focus
 let evidence := report c candidate bounds
 if evidence.blocked.isEmpty && evidence.conflicts.isEmpty && evidence.arity.isEmpty
 then some (bindings c.state evidence) else none

theorem exact (c : Context) (focus : Occurrence roles) (candidate : Declaration) (answer : Bindings) :
 collect c focus candidate = some answer ↔
 ∃ bounds, arguments c focus = some bounds ∧ Finished (report c candidate bounds) ∧
   bindings c.state (report c candidate bounds) = answer := by
 unfold collect
 cases available : arguments c focus with
 | none => simp [Option.bind]
 | some bounds =>
   simp only [Bind.bind,Option.bind]
   constructor
   · intro hit
     split at hit
     · rename_i checks
       have triple := Bool.and_eq_true_iff.mp checks
       have pair := Bool.and_eq_true_iff.mp triple.1
       exact ⟨bounds,rfl,⟨List.isEmpty_iff.mp pair.1,List.isEmpty_iff.mp pair.2,List.isEmpty_iff.mp triple.2⟩,
         Option.some.inj hit⟩
     · contradiction
   · rintro ⟨observed,selected,finite,answer⟩
     cases Option.some.inj selected
     unfold Finished at finite
     simp [finite.1,finite.2.1,finite.2.2,answer]

theorem first : collect context root declaration = some firstBindings := by
 apply (exact ..).mpr
 refine ⟨[(0,0)],by decide +kernel,?_,?_⟩
 · rw [GeneralDictionaryOptionalInstall229.report_exact]
   exact ⟨rfl,rfl,rfl⟩
 · rw [GeneralDictionaryOptionalInstall229.report_exact]
   rfl

theorem revision : collect point.core.erased.current.context root declaration = some pointBindings := by
 rw [GeneralDictionaryVersionedPointStage233.context_exact]
 apply (exact ..).mpr
 refine ⟨[(0,0)],by decide +kernel,?_,?_⟩
 · rw [GeneralDictionaryOptionalCurrent229.report_exact]
   exact ⟨rfl,rfl,rfl⟩
 · rw [GeneralDictionaryOptionalCurrent229.report_exact]
   rfl

def installFrom (c : Context) : Option Stage :=
 (collect c root declaration).bind (fun result => next .source (.install owner result 2))

def observeFrom (c : Context) : Option Stage :=
 (collect c root declaration).bind (fun result => next .installed (.observe owner result 2))

theorem install_computed : installFrom context = some .installed := by rw [installFrom,first]; rfl

theorem observed_computed : observeFrom point.core.erased.current.context = some .observed := by
 rw [observeFrom,revision]; rfl

theorem rejects_unrevised : observeFrom context = none := by rw [observeFrom,first]; rfl

theorem bounded_not_generic (c : Context) :
 observeFrom c = some .observed →
 ∃ bounds, arguments c root = some bounds ∧ Finished (report c declaration bounds) ∧
    bindings c.state (report c declaration bounds) = pointBindings := by
 intro hit
 unfold observeFrom at hit
 cases found : collect c root declaration with
 | none => simp [found,Option.bind] at hit
 | some bs =>
   have accepted : next .installed (.observe owner bs 2) = some .observed := by simpa [found,Option.bind] using hit
   let block := GeneralRebaseCompoundOwnerBlock273.point
   change (if owner = owner ∧ GeneralRebaseCompoundOwnerBlock273.compile bs 2 = some block then some .observed else none) =
     some Stage.observed at accepted
   by_cases matchesBlock : GeneralRebaseCompoundOwnerBlock273.compile bs 2 = some block
   · have decoded := GeneralRebaseCompoundOwnerBlock273.compiler_exact bs 2 block matchesBlock
     have exactBindings : bs = pointBindings := decoded.1
     rw [exactBindings] at found
     exact (exact ..).mp found
   · simp [matchesBlock] at accepted

end Yulang.GeneralRebaseTerminalObservation274

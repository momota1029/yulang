import Yulang.GeneralDeclarativeWitnessClassify334
import Yulang.GeneralDeclarativeNestedSiblingsModels332

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 18000000
namespace Yulang.GeneralDeclarativeWitnessFixture334
open GeneralDeclarativeNestedSiblingsFrame332
open GeneralDeclarativeNestedSiblingsDecl332 (registry impl checked)
open GeneralDeclarativeNestedSiblingsResult332 (to_final current root_ready one_ready two_ready root_matches one_matches
  two_matches no_cycles dictionary root_only child_only)
open GeneralDeclarativeNestedSiblingsModels332 (inhabited)
open GeneralDeclarativeNestedDecl332 (root normal normalizedExpr)
open GeneralDeclarativeNestedExample332 (interpretation uses)
open GeneralDeclarativeNestedFrame332 (spans fallback)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativePriority321 (Recurs)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeWitnessHead334 (Slice Actuals)
open GeneralDeclarativeWitnessNode334 (Witness)
open GeneralDeclarativeWitnessClassify334 (Rule dictionary_sound)
open GeneralDeclarativeCurrentReceipt330 (literal)
open GeneralDeclarativeObserverGrowth330 (preserve sources_grow)
open GeneralDeclarativeGrowth327 (Extends trans fits)
open GeneralDeclarativeStableTrace329 (Actual)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)
open GeneralDeclarativeNestedDecode332 (normalized_sound)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)
open GeneralDeclarationExamples (constructors)
open CommonRoleOutermostResolver (Classify)

def waiting (_ : Demand) (_ : Declaration) : Prop := False

theorem safe (done : Nat → Prop) (d : Demand) :
    ¬Recurs final registry interpretation (candidates (current done) registry interpretation waiting) d := by
  rintro (⟨arg,_,cycle⟩|⟨_,_,_,_,_,_,_,_,_,site,_,cycle⟩)
  · exact no_cycles arg.lower cycle
  · exact no_cycles site cycle

theorem root_choice (done : Nat → Prop) :
    Elected final registry interpretation (current done)
      (candidates (current done) registry interpretation waiting) root impl :=
  ⟨root_ready done,safe done _,fun ⟨_,_,no⟩ => no,
    ⟨⟨List.mem_cons_self,rfl⟩,.inr (root_matches done)⟩,
    fun _actual survives => congrArg Declaration.id (root_only _ survives.1.1 survives.1.2)⟩

private abbrev priorParent (done : Nat → Prop) : Extends source parent :=
  trans (actual_head done).1.grows grow_parent

def rootSlice (done : Nat → Prop) : Slice (current done) :=
  ⟨source,origins done,to_final done,sources_grow (origins done) (to_final done)⟩

theorem root_reads (done : Nat → Prop) :
    Read (restriction (origins done)) .actual (.variable 0) normalizedExpr
      (uses .actual) := by
  obtain ⟨c,printed,w⟩ := normalized_sound (actual done)
  cases Option.some.inj (printed.symm.trans normal)
  exact w

noncomputable def rootWitness (done : Nat → Prop) :
    Witness (current done) registry interpretation waiting root impl childList :=
  { chosen := root_choice done
    slice := rootSlice done
    protect := keep
    fallback := fallback
    targets := targets
    named := stage
    spans := spans
    source := .cons (.inline (view := fun _ => none) (point_bounded _ _) normal (root_reads done) rfl) .nil
    ordinary := parent
    compiled := exact_order_writes.1
    receipt := literal (trans grow_one grow_two) }

def oneSlice (done : Nat → Prop) : Slice (current done) :=
  ⟨parent,preserve (origins done) (priorParent done),trans grow_one grow_two,
    sources_grow _ (trans grow_one grow_two)⟩

def twoSlice (done : Nat → Prop) : Slice (current done) :=
  ⟨firstDone,preserve (origins done) (trans (priorParent done) grow_one),grow_two,
    sources_grow _ grow_two⟩

theorem one_choice (done : Nat → Prop) :
    Elected final registry interpretation (current done)
      (candidates (current done) registry interpretation waiting) first leaf :=
  ⟨one_ready done,safe done _,fun ⟨_,_,no⟩ => no,
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,.inr (one_matches done)⟩,
    fun _actual survives => congrArg Declaration.id (child_only _ survives.1.1 survives.1.2)⟩

theorem two_choice (done : Nat → Prop) :
    Elected final registry interpretation (current done)
      (candidates (current done) registry interpretation waiting) second leaf :=
  ⟨two_ready done,safe done _,fun ⟨_,_,no⟩ => no,
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,.inr (two_matches done)⟩,
    fun _actual survives => congrArg Declaration.id (child_only _ survives.1.1 survives.1.2)⟩

def firstWitness (done : Nat → Prop) :
    Witness (current done) registry interpretation waiting first leaf [] :=
  { chosen := one_choice done
    slice := oneSlice done
    protect := keep
    fallback := fallback
    targets := targets
    named := parent
    spans := spansOne
    source := .cons (.named ⟨bound_one,.variable 0,[⟨0,.actual,3⟩],rfl,.capture,
      .cons ⟨rfl,rfl,bound_one⟩ .nil⟩) .nil
    ordinary := firstDone
    compiled := exact_order_writes.2.1
    receipt := literal grow_two }

def secondWitness (done : Nat → Prop) :
    Witness (current done) registry interpretation waiting second leaf [] :=
  { chosen := two_choice done
    slice := twoSlice done
    protect := keep
    fallback := fallback
    targets := targets
    named := firstDone
    spans := spansTwo
    source := .cons (.named ⟨fits grow_one bound_two,.variable 0,[⟨0,.actual,11⟩],rfl,.capture,
      .cons ⟨rfl,rfl,fits grow_one bound_two⟩ .nil⟩) .nil
    ordinary := final
    compiled := exact_order_writes.2.2
    receipt := literal (GeneralDeclarativeClauseBatch327.reflexive _) }

theorem actual_tree (done : Nat → Prop) :
    Classify (Rule (current done) registry interpretation waiting) root (.selected dictionary) :=
  ⟨.selected impl.id [.selected leaf.id [],.selected leaf.id []],
    .selected (.selected (rootWitness done))
      (.cons (.selected (.selected (firstWitness done)) .nil)
        (.cons (.selected (.selected (secondWitness done)) .nil) .nil)),
    .selected (.cons (.selected .nil (.selected rfl)) (.cons (.selected .nil (.selected rfl)) .nil))
      (.selected rfl)⟩

theorem nonvacuous :
    ∃ m, Models final m ∧ Evidence registry interpretation m root dictionary := by
  obtain ⟨m,fit⟩ := inhabited
  exact ⟨m,fit,dictionary_sound checked covered wanted_root (actual_tree (fun _ => False)) m fit⟩

end Yulang.GeneralDeclarativeWitnessFixture334

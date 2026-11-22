import Yulang.GeneralDeclarativeVersionedRootCompiler342
import Yulang.GeneralNominalGroundAccessibility

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralDeclarativeInitialRoot343
open GeneralDictionaryJournalRefinement228Source
  (labels context root fooTerm closed ground base snapshot interpretation)
open GeneralNominalGroundAccessibility (ClosedTerm GroundRoots)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeOrigins321 (Supported Backed)
open GeneralDeclarativeVersionedRootGuard342 (observedRoot actualDemand)
open GeneralDeclarativeVersionedRootRead342 (publicRow)
open GeneralDeclarativeVersionedRootShape342 (spans)
open GeneralWhereOriginSingleSource318 (sourceRegistry declaration)
open GeneralDeclarativeVersionedChildWitness342 (waiting)

abbrev sourceArg : GeneralDeclarationPatterns.Pattern := .app 2 []
abbrev authoredLabel : GeneralDeclarationPatterns.Pattern := .app 0 [sourceArg,sourceArg]
abbrev sourceTerm : Core.PresenceGeneration.TyTerm (Fin 5) := .emptyRecord

/-- This relation is about the authored input to this concrete run, not about
any sound but unbacked equality in a final solver snapshot. Its source anchors
are the existing ground input label and the existing width atom. -/
structure InputOrigin (row : Equation) : Prop where
  authored : labels[0]? = some authoredLabel
  checked : ClosedTerm context authoredLabel fooTerm
  translated : GeneralNominalCenteredHeadMatExpressions.translate sourceRegistry.constructors interpretation
    (GeneralDeclarationPatterns.normalize authoredLabel) =
      some (.nominal 0 [.primitive .emptyRecord [],.primitive .emptyRecord []])
  input : (root.demand.arguments 0).1 = 0
  width_name : base.source (2 : Fin 5) = 2
  width_atoms : GeneralSourceState.equationAtoms (2 : Fin 5) sourceTerm ⊆ base.ordinary
  printed : row = ⟨(root.demand.arguments 0).1,
    .nominal 0 (List.replicate 2 (.variable (base.source (2 : Fin 5))))⟩

theorem anchored : InputOrigin publicRow := by
  refine ⟨rfl,closed,rfl,rfl,rfl,?_,rfl⟩
  intro fact listed
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ listed))

theorem origin_unique {row : Equation} (w : InputOrigin row) : row = publicRow := w.printed

def support (done : Nat → Prop) : Supported observedRoot done :=
  ⟨fun row origin => InputOrigin row ∧ origin = .source,
    fun input => origin_unique input.1 ▸ List.mem_singleton_self _⟩

theorem source_backed (done : Nat → Prop) : Backed (support done) publicRow :=
  ⟨.source,⟨anchored,rfl⟩,.source⟩

/-- Source derivation for the exact root guard; there is no dependence on
installed output evidence, stale history, or semantic equation truth alone. -/
theorem root_election (done : Nat → Prop) :
    GeneralDeclarativeTaggedElection340.Election (support done) sourceRegistry interpretation waiting actualDemand declaration :=
  GeneralDeclarativeVersionedRootShape342.root_election (support done) (source_backed done)

theorem exact_inputs (done : Nat → Prop) (keep : List Nat) :
    GeneralDeclarativeTaggedInputs340.Inputs (support done) sourceRegistry.constructors interpretation keep
      observedRoot actualDemand.arguments declaration.head observedRoot spans [] :=
  GeneralDeclarativeVersionedRootShape342.exact_inputs (support done) (source_backed done) keep

end Yulang.GeneralDeclarativeInitialRoot343

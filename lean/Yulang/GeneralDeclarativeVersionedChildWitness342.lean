import Yulang.GeneralDeclarativeVersionedChildBody342
import Yulang.GeneralDeclarativeStoppedPaired341

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16500
set_option maxHeartbeats 10000000
namespace Yulang.GeneralDeclarativeVersionedChildWitness342
open GeneralWherePhysicalCommit319 (final newChild produced)
open GeneralWhereOriginSingleSource318 (sourceRegistry registry checked)
open GeneralDictionaryJournalRefinement228Source (roles root interpretation)
open GeneralLiveCompoundRegistry316 (leaf)
open GeneralDeclarativeVersionedChildView342 (basis arg d lower actual upper range support done supported actual_arguments)
open GeneralDeclarativeVersionedChildBody342 (expanded spans keep fallback targets compiled grown level ranked current_models seed)
open GeneralDeclarativeOrigins321 (restriction Supported)
open GeneralDeclarativeObserverGrowth330 (preserve sources_grow)
open GeneralDeclarativeLowerKnown321 (knows_row alias_refl)
open GeneralDeclarativeStableTrace329 (Actual)
open GeneralDeclarativeTaggedInputs340 (Inputs)
open GeneralDeclarativeTaggedElection340 (Election)
open GeneralDeclarativeTaggedSelected340 (Selected)
open GeneralDeclarativeTaggedDictionary340 (Rule dictionary_sound)
open GeneralDeclarativeWitnessHead334 (Argument Slice)
open GeneralDeclarativeCurrentReceipt330 (literal)
open GeneralDeclarativeClauseBatch327 (reflexive)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralWhereOriginSupport318 (journalSources)
open CommonRoleOutermostResolver (All₂ Resolves Summarizes Classify)
open GeneralDeclarations (Declaration)

noncomputable def current : Supported expanded done := preserve support grown

def waiting (_ : Demand) (_ : Declaration) : Prop := False

theorem ordinary_read :
    Actual basis sourceRegistry.constructors interpretation support arg (.variant 0 (.var 0)) spans := by
  refine ⟨range,.variant 0 (.variable 0),[⟨0,.actual,2⟩],rfl,?_ ,?_⟩
  · exact .variant (alias_refl _) (supported actual (List.mem_cons_of_mem _ List.mem_cons_self)) .capture
  · exact .cons ⟨rfl,rfl,point_bounded _ _⟩ .nil

theorem heads :
    Inputs support sourceRegistry.constructors interpretation keep basis d.arguments leaf.head basis spans [] := by
  exact .cons (.prior (.old (.named ordinary_read))) .nil

theorem active_supported (row : GeneralDeclarativeHead320.Equation) (seen : row ∈ basis.equations) :
    row ∈ (restriction current).equations :=
  (sources_grow support grown).equations (supported row seen)

theorem choice : Election current sourceRegistry interpretation waiting d leaf := by
  refine ⟨?_,⟨level,ranked⟩,fun ⟨_,_,h⟩ => h,?_,?_⟩
  · intro a located
    cases List.mem_singleton.mp located
    exact .inl ⟨_,knows_row (active_supported lower List.mem_cons_self) rfl⟩
  · refine ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,.cons (.named ?_) .nil⟩
    have br : GeneralDeclarativeDemand320.Bounds (restriction support) arg := range
    refine ⟨GeneralDeclarativeGrowth327.fits (sources_grow support grown) br,.variant 0 (.variable 0),
      [⟨0,.lower,2⟩],[⟨0,.upper,2⟩],rfl,?_ ,?_⟩
    · exact .variant (alias_refl _) (active_supported lower List.mem_cons_self) .capture
    · exact .variant (alias_refl _) (active_supported upper (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) .capture
  · intro other possible
    rcases List.mem_cons.mp possible.1.1 with old|here
    · rw [old] at possible
      cases possible.1.2
    · cases List.mem_singleton.mp here
      rfl

noncomputable def witness : Selected current [] sourceRegistry interpretation waiting d leaf [] :=
  ⟨⟨basis,support,grown,sources_grow support grown⟩,keep,basis,spans,[],heads,
    fallback,targets,expanded,compiled,literal (reflexive _),fun _ h => h,choice⟩

theorem selected : Classify (Rule current [] sourceRegistry interpretation waiting) d (.selected (.node leaf.id [])) :=
  ⟨.selected leaf.id [],.selected (.whole witness) .nil,.selected .nil (.selected rfl)⟩

theorem declared : Declared sourceRegistry d := fun _ h => False.elim (List.not_mem_nil h)

theorem coverage : Coverage sourceRegistry interpretation := by
  refine ⟨?_,GeneralLiveCompoundRegistry316.coverage.2⟩
  intro impl visible
  rcases List.mem_cons.mp visible with same | tail
  · subst impl
    simp [GeneralNominalCenteredHeadWFSource.DeclarationCovered,
      GeneralNominalCenteredHeadWFSource.PatternsCovered,GeneralNominalCenteredHeadWFSource.PatternCovered,
      GeneralNominalCenteredHeadWFSource.ConstructorUse,interpretation,
      GeneralDictionaryJournalRefinement228Source.constructors,GeneralDictionaryOptionalExpression229.pattern]
    exact ⟨rfl,rfl,rfl⟩
  · cases List.mem_singleton.mp tail
    exact GeneralLiveCompoundRegistry316.coverage.1 leaf (List.mem_cons_of_mem _ List.mem_cons_self)

/-- The genuine generated child uses current versioned support and
the latest witness judgement on one conservative assignment. This
does not claim the ordinary unversioned root packet can be used. -/
theorem actual (m : Assignment) (fit : GeneralWhereVersionInstall317.Models final m) :
    GeneralNominalSaturationState.Generated final.mixed.core.erased.current root newChild.occurrence ∧
    GeneralStoppedOrdinarySite335.demand newChild = d ∧
    Classify (Rule current [] sourceRegistry interpretation waiting) d (.selected (.node leaf.id [])) ∧
    ∃ n, GeneralWhereVersionInstall317.Models final n ∧ (∀ k ∈ journalSources final, n k = m k) ∧
      GeneralNominalVersionedEvidence231.Evidence registry final.mixed.core n newChild.occurrence (.node leaf.id []) ∧
      GeneralDeclarativeExactDictionary337.Evidence sourceRegistry interpretation n d (.node leaf.id []) := by
  refine ⟨produced,actual_arguments,selected,?_⟩
  obtain ⟨n,present,raw,keeps⟩ := current_models m fit
  exact ⟨n,raw,keeps,GeneralWherePhysicalChildCert319.leaf_evidence n raw,
    dictionary_sound checked coverage declared selected ⟨present,fun _ missing => False.elim (List.not_mem_nil missing)⟩⟩

end Yulang.GeneralDeclarativeVersionedChildWitness342

import Yulang.GeneralDeclarativeReobserve324
import Yulang.GeneralDeclarativeNamedTree320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOutputIdentity324
open GeneralDeclarations (Declaration Checked)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeSourceEmission322 (Names demand useOutput)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeEmissionOutputs322 (Agree)
open GeneralDeclarativeSharedNF324 (shared_heads)
open GeneralDeclarativeNFHead324 (Scan)
open GeneralDeclarativeRepeatedActual323 (BindsAt)
open GeneralDeclarativeReobserve324 (Reobserves ordinary_reobserved)
open GeneralDeclarativeModelStable324 (StableUnder stable_exact)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeNamedTree320 (position)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralDeclarationDemands (outputTarget)
open GeneralDeclarationPatterns (normalize)
open CommonRoleOutermostResolver (All₂)
open CommonNominalFullCarrier (Equivalent)

theorem direct_target (names : Names) (defined : eqn.rhs = .var n) (visible : n ∈ decl.outputNames) :
    (useOutput decl names allocate eqn).target = names.output n := by
  simp [useOutput,outputTarget,defined,normalize,visible,Names.old]

/-- Read the designated output binder from its actual producing where
clause and equation, not from an unrelated child or a shared numeric key. -/
theorem output_identity (produced : decl.Produced)
    (same : All₂ (fun a b : GeneralDeclarativeDemand320.Demand => a.outputs = b.outputs)
      (children decl old oldPlace) (children decl new newPlace))
    (n : Nat) (bound : n ∈ decl.outputNames) : old.output n = new.output n := by
  obtain ⟨binder,declared,rfl⟩ := List.mem_map.mp bound
  obtain ⟨clause,declaredClause,_,eqn,declaredEq,_,body⟩ := produced binder declared
  obtain ⟨i,guard,atClause⟩ := List.getElem_of_mem declaredClause
  have point : decl.requirements[i]? = some clause := List.getElem?_eq_some_iff.mpr ⟨guard,atClause⟩
  have oldAt : (children decl old oldPlace)[i]? =
      some (demand decl clause old (oldPlace.compound clause) (oldPlace.targets clause)) := by
    simp [children,List.getElem?_map,point]
  have newAt : (children decl new newPlace)[i]? =
      some (demand decl clause new (newPlace.compound clause) (newPlace.targets clause)) := by
    simp [children,List.getElem?_map,point]
  have lists := position same oldAt newAt
  obtain ⟨j,inside,atEq⟩ := List.getElem_of_mem declaredEq
  have printed : clause.outputs[j]? = some eqn := List.getElem?_eq_some_iff.mpr ⟨inside,atEq⟩
  have named := congrArg (fun e => e[j]?) lists
  have eqOut :
      useOutput decl old (oldPlace.targets clause) eqn = useOutput decl new (newPlace.targets clause) eqn :=
    Option.some.inj (by simpa [demand,List.getElem?_map,printed] using named)
  have first := direct_target (allocate := oldPlace.targets clause) old body bound
  have second := direct_target (allocate := newPlace.targets clause) new body bound
  exact first.symm.trans ((congrArg GeneralSourceState.Output.target eqOut).trans second)

theorem roots_agree {s : State}
    (vis : ∀ m, Models s m → All₂ (fun arg pat => ∃ uses, Scan s c interp arg pat uses ∧
      BindsAt m old.input uses ∧ BindsAt m new.input uses) args decl.head)
    (produced : decl.Produced) (oldValid : Agree decl old) (newValid : Agree decl new)
    (same : All₂ (fun a b : GeneralDeclarativeDemand320.Demand => a.outputs = b.outputs)
      (children decl old oldPlace) (children decl new newPlace)) :
    Reobserves s decl old.input new.input := by
  intro m valid
  refine ⟨shared_heads (vis m valid),?_⟩
  intro n bound
  rw [oldValid n bound,newValid n bound,output_identity produced same n bound]
  exact eqv_refl _

theorem keep_old_rules {s t : State}
    (stronger : ∀ m, Models t m → Models s m)
    (stable : StableUnder s applies) : StableUnder t applies := by
  apply stable_exact.mpr
  intro row enabled m valid
  exact stable_exact.mp stable row enabled m (stronger m valid)

/-- Carry an actual ordinary associated rule to a reobservation with
the same demand (in particular the original fixed target). Head sharing
comes from the real normalized observations. Output-only binders are
checked through their actual ordered generating clauses. -/
theorem stable_reobserved {s t : State} (checked : Checked r) (visible : impl ∈ r.declarations)
    (stronger : ∀ m, Models t m → Models s m)
    (retained : StableUnder s (SourceEquation r interp d impl old.input))
    (vis : ∀ m, Models t m → All₂ (fun arg pat => ∃ uses, Scan t r.constructors interp arg pat uses ∧
      BindsAt m old.input uses ∧ BindsAt m new.input uses) d.arguments impl.head)
    (oldValid : Agree impl old) (newValid : Agree impl new)
    (same : All₂ (fun a b : GeneralDeclarativeDemand320.Demand => a.outputs = b.outputs)
      (children impl old oldPlace) (children impl new newPlace)) :
    StableUnder t (SourceEquation r interp d impl new.input) :=
  ordinary_reobserved checked visible (roots_agree vis (checked.2 impl visible).produced oldValid newValid same)
    (keep_old_rules stronger retained)

end Yulang.GeneralDeclarativeOutputIdentity324

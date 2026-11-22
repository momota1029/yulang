import Yulang.GeneralStoppedLowerOrigin335
import Yulang.GeneralDeclarativeWitnessHead334
import Yulang.GeneralNominalVersionedJournal232

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralStoppedSourceRefinement335
open Core.PresenceGeneration (CompTerm TyTerm RowTerm)
open GeneralNominalRefinements (Refines)
open GeneralStoppedLower335 (lower normal original exact_models)
open GeneralStoppedLowerOrigin335 (exact_rows ScalarRow NominalRow literal_nominal_preserved)
open GeneralNominalRebaseRawView243 (atom slot)
open GeneralDeclarativeGrowth327 (Extends)
open GeneralDeclarativeWitnessHead334 (Slice)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeHead320 (Models)

theorem row_reindexed (f : α → β) (g : β → CompTerm γ) (e : RowTerm α) :
    (e.rename f).subst g = e.subst (g ∘ f) := by
  induction e with
  | var => rfl
  | empty => rfl
  | join _ _ a b => rw [RowTerm.rename,RowTerm.subst,a,b]; rfl

theorem type_reindexed (f : α → β) (g : β → CompTerm γ) (e : TyTerm α) :
    (e.rename f).subst g = e.subst (g ∘ f) := by
  induction e <;> simp only [TyTerm.rename,TyTerm.subst,row_reindexed, Function.comp_apply, *]

theorem atom_reindexed (f : α → β) (g : β → CompTerm Nat) (a : PresenceNormalForm.Atom α) :
    atom g (a.rename f) = atom (g ∘ f) a := by
  cases a <;> simp only [PresenceNormalForm.Atom.rename,atom,row_reindexed,type_reindexed]

theorem physical_source (g : Refines before after) :
    slot after.base CompTerm.var ∘ g.base.embed = slot before.base CompTerm.var := by
  funext k
  simp only [Function.comp_def,slot,CompTerm.var,g.base.source,g.base.rowSource]

theorem normal_preserved (g : Refines before after) :
    (normal before).ordinary ⊆ (normal after).ordinary ∧
      (normal before).intervals ⊆ (normal after).intervals := by
  constructor
  · intro a there
    rcases List.mem_append.mp there with physical|logical
    · obtain ⟨row,member,rfl⟩ := List.mem_map.mp physical
      apply List.mem_append_left _
      refine List.mem_map.mpr ⟨row.rename g.base.embed,g.base.ordinary _ member,?_⟩
      rw [atom_reindexed,physical_source g]
    · exact List.mem_append_right _ (g.ordinary _ logical)
  · intro pair member
    obtain ⟨p,placed,rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨(g.base.embed p.1,g.base.embed p.2),g.base.intervals p placed,
      by rw [g.base.source,g.base.source]⟩

/-- A checked refinement promises model-entailing rewriting of old
scalar observations, not that the old scalar is still directly
present in the observation table. This positive record condition is
separate from ordinary truth. -/
def ScalarStorage (before after : GeneralNominalState.State) (g : Refines before after) : Prop :=
  ∀ k b, (before.base.heads k).equation = some (.base b) →
      (after.base.heads (g.base.embed k)).equation = some (.base b)

theorem scalar_preserved (g : Refines before after) (stored : ScalarStorage before after g)
    (actual : ScalarRow before row) : ScalarRow after row := by
  obtain ⟨k,term,value,read,encoded,same⟩ := actual
  cases term <;> simp [GeneralStoppedShape335.headExpr] at encoded
  refine ⟨g.base.embed k,_,value,stored _ _ read,?_,?_⟩
  · cases encoded; rfl
  · exact same.trans (congrArg (fun n => (⟨n,value⟩ : GeneralDeclarativeHead320.Equation)) (g.base.source k).symm)

theorem projected_normal (made : lower raw = some s) : s.normal = normal raw := by
  unfold lower at made
  obtain ⟨_,_,rfl⟩ := Option.map_eq_some_iff.mp made
  rfl

/-- In the supported scalar/point-nominal fragment, actual source
refinement plus exact scalar readback preserves every authored row.
No inference about an output-origin row follows. -/
theorem preserves (g : Refines before after) (stored : ScalarStorage before after g)
    (origin : lower before = some s) (stopped : lower after = some t) : Extends s t := by
  have ⟨atoms,intervals⟩ := normal_preserved g
  refine ⟨(projected_normal origin).symm ▸ (projected_normal stopped).symm ▸ atoms,
    (projected_normal origin).symm ▸ (projected_normal stopped).symm ▸ intervals,?_⟩
  intro row visible
  apply (exact_rows stopped row).mpr
  rcases (exact_rows origin row).mp visible with scalar|nominal
  · exact .inl (scalar_preserved g stored scalar)
  · exact .inr (literal_nominal_preserved g nominal)

def source {s t : GeneralDeclarativeHead320.State} (seen : Extends s t) (done : Nat → Prop) :
    Supported t done :=
  GeneralDeclarativeObserverGrowth330.preserve (original s s (fun _ held => held) done) seen

def sourceSlice {s t : GeneralDeclarativeHead320.State} (seen : Extends s t) (done : Nat → Prop) :
    Slice (source seen done) :=
  ⟨s,original s s (fun _ held => held) done,seen,GeneralDeclarativeObserverGrowth330.sources_grow _ seen⟩

/-- Every actual raw journal model already satisfies the projected
ordinary context; the opposite implication must account for its
live effects and installation history separately. -/
theorem stopped_models (raw : GeneralNominalVersionedJournal232.State roles)
    (made : lower raw.core.erased.current.context.state = some s)
    (fit : GeneralNominalVersionedJournal232.Models raw m) :
    Models s m :=
  (exact_models _ m made).mpr fit.1.1

end Yulang.GeneralStoppedSourceRefinement335

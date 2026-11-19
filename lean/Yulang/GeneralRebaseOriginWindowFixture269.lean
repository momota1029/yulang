import Yulang.GeneralRebaseOriginEdgeScan269
import Yulang.GeneralNominalProgressObstruction
import Yulang.GeneralRebaseActualArguments269
import Yulang.GeneralNominalVersionedAcyclic232

namespace Yulang.GeneralRebaseOriginWindowFixture269
open GeneralNominalProgressObstruction (state descriptor context root model value equation state_models)
open GeneralNominalVersionedJournal232 (initial Models)
open GeneralNominalVersionedCycles232 (Equal Head Edge Cyclic)
open GeneralNominalRecursiveInspection (Origin Test Observes)
open GeneralNominalOriginTerms (project arity Same)
open GeneralRebaseOriginCycles268 (Window Sound)
open GeneralRebaseOriginQuotient269 (TestsCover)
open CommonNominalFullCarrier
open GeneralDictionaryInspectionHeads215 (tag_subtype tagged_nominal tagged_shape)

abbrev journal := initial context (root 0)
def keyOrigin : Origin := .source 0
def childOrigin : Origin := .nominal keyOrigin 0 0
abbrev only : Test := .nominal 0 1

theorem journal_models : Models journal model := by
 apply (GeneralNominalVersionedJournal232.initial_models ..).mpr
 exact ⟨state_models,fun _ => ⟨subtype_refl _,subtype_refl _⟩⟩

theorem observed_child : Equal journal childOrigin keyOrigin := by
 intro a valid
 obtain ⟨arg,seen,fits⟩ := GeneralNominalProjections.parameter_binding_valid
   state a valid.1.1 0 descriptor rfl 0 0 (.type (0,0)) rfl
 cases arg with
 | inr => cases fits
 | inl actual =>
   have specific : Observes a childOrigin actual :=
     GeneralNominalRecursiveInspection.embed_observation a _ actual seen
   refine ⟨⟨actual,specific⟩,⟨_,.source 0⟩,?_⟩
   intro x y ox oy
   cases oy
   have recov := GeneralNominalRecursiveInspection.recover_observation a
     (.argument (.source 0) 0 0) x ox
   have same := GeneralNominalProjections.observation_unique a _ _ _ recov seen
   exact ⟨subtype_trans same.1 fits.2,subtype_trans fits.1 same.2⟩

theorem root_self : Equal journal keyOrigin keyOrigin :=
 fun a _ => GeneralNominalOriginTerms.source_self a 0

theorem known_head : Head journal keyOrigin only := by
 intro a valid
 have raw : GeneralNominalState.Models state a := valid.1.1
 obtain ⟨args,fits,head⟩ := raw.2.1 (0 : Fin 1) descriptor rfl
 refine ⟨⟨_,.source 0⟩,?_⟩
 intro x seen
 cases seen
 exact ⟨args,(GeneralRebaseActualArguments269.fits_length fits).symm,head⟩

theorem head_exhaustive (test : Test) (head : Head journal keyOrigin test) (child : arity test ≠ 0) :
 test = only := by
 have held := (head model journal_models).2 _ (.source 0)
 change test.Holds value at held
 cases test with
 | scalar scalar => have impossible := child rfl; cases impossible
 | structural shape =>
   obtain ⟨values,size,same⟩ := held
   have incompatible := tag_subtype (tagged_nominal 0 [.inl value])
     (tagged_shape shape values size) (subtype_trans equation.2 same.1)
   cases shape <;> cases incompatible
 | nominal name count =>
   obtain ⟨values,size,same⟩ := held
   have matching := (nominal_regular_invariant_exact 0 name [.inl value] values).mp
     (subtype_trans equation.2 same.1)
   have nameZero : name = 0 := matching.1.symm
   have one : count = 1 := size.symm.trans matching.2.1.symm
   subst name
   subst count
   rw [one]

theorem actual_self : Edge journal keyOrigin keyOrigin :=
 ⟨keyOrigin,only,⟨0,by decide +kernel⟩,known_head,root_self,observed_child⟩

def window : Window 1 := ⟨fun _ => keyOrigin,fun _ _ => some true,some true⟩

theorem window_sound : Sound journal window :=
 ⟨fun _ _ => actual_self,⟨model,journal_models⟩⟩

theorem test_cover : TestsCover journal window.point (fun _ => [only]) := by
 constructor
 · intro _ t _ head ar
   exact List.mem_singleton.mpr (head_exhaustive t head ar)
 · intro _ t member idx _ _ _
   cases List.mem_singleton.mp member
   change Fin 1 at idx
   have index : idx = (0 : Fin 1) := Fin.fin_one_eq_zero idx
   subst idx
   exact ⟨0,observed_child⟩

theorem semantic_forward : GeneralRebaseOriginQuotient269.Forward journal window.point :=
 GeneralRebaseOriginQuotient269.forward_of_tests journal window.point (fun _ => [only]) test_cover

theorem actual_projected_edge : Edge journal keyOrigin childOrigin :=
 GeneralRebaseOriginCongruence269.edge_of_equiv root_self
  (GeneralRebaseOriginCongruence269.equal_symm observed_child) actual_self

/-- Literal closure requires the distinct projected syntax, but semantic
closure is checked on the singleton source representative. -/
theorem not_literal_forward : ¬ GeneralRebaseOriginCycles268.Forward journal window := by
 intro literal
 obtain ⟨_,equal⟩ := literal 0 childOrigin actual_projected_edge
 change keyOrigin = childOrigin at equal
 cases equal

def matchOrigin (o : Origin) (_ : Fin 1) : Option Bool :=
 if o = childOrigin then some true else if o = keyOrigin then some true else none

theorem query_result : GeneralRebaseOriginExecutable269.cyclic window matchOrigin
 (fun _ => true) (fun _ => false) childOrigin = some true := by decide +kernel

/-- Real cyclic calculation through a semantic representative even though
the query origin is absent syntactically from the finite window. This is
a constructed initial journal, not a surface-program reachability claim. -/
theorem query_sound : Cyclic journal childOrigin := by
 have cert : ∀ i, GeneralRebasePartialBool268.Reflect (Equal journal childOrigin (window.point i))
     (matchOrigin childOrigin i) := by
   intro i
   exact observed_child
 have found := GeneralRebaseOriginExecutable269.with_semantic_closure window window_sound matchOrigin cert semantic_forward
 rw [query_result] at found
 exact found

def equality (first last : Origin) : Option Bool :=
 if last = keyOrigin then matchOrigin first 0 else none

theorem equality_sound (first last : Origin) :
 GeneralRebasePartialBool268.Reflect (Equal journal first last) (equality first last) := by
 unfold equality
 split
 · rename_i h
   subst last
   unfold matchOrigin
   split
   · rename_i h
     subst first
     exact observed_child
   · split
     · rename_i h
       subst first
       exact root_self
     · trivial
 · trivial

def assembled : Window 1 := GeneralRebaseOriginEdgeScan269.assemble
  (fun _ => keyOrigin) (fun _ => [only]) (fun _ _ => some true) equality (some true)

theorem assembled_sound : Sound journal assembled := by
 apply GeneralRebaseOriginEdgeScan269.assemble_sound journal _ _ _ _ _ test_cover
 · intro _ t found
   cases List.mem_singleton.mp found
   exact known_head
 · exact equality_sound
 · exact ⟨model,journal_models⟩

theorem assembled_query : GeneralRebaseOriginExecutable269.cyclic assembled matchOrigin
 (fun _ => true) (fun _ => false) childOrigin = some true := by decide +kernel

theorem scanned_cycle : Cyclic journal childOrigin := by
 have cert : ∀ i, GeneralRebasePartialBool268.Reflect (Equal journal childOrigin (assembled.point i))
     (matchOrigin childOrigin i) := by
   intro i
   exact observed_child
 have found := GeneralRebaseOriginExecutable269.with_semantic_closure assembled assembled_sound matchOrigin cert semantic_forward
 rw [assembled_query] at found
 exact found

end Yulang.GeneralRebaseOriginWindowFixture269

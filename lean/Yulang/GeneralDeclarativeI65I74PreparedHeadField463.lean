import Yulang.GeneralDeclarativeI65I74PreparedHeadStart463
import Yulang.GeneralDeclarativeI65I74IndexedNativeEvidence463
import Yulang.GeneralDeclarativeI65I74ExistingInspectedOrigins463

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem)
open WrittenPattern460 PhysicalVisit463
open WrittenPattern460.PhysicalOrigin (Hit locateRoute)
open RecordTraversal455.MixedQA (MixedPath)
open InlineStructuralPolicy458 (policy)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open RecordTraversal455 (naked_raw_cycle_has_finite_wire455)
open RecordK2412 (checkCycleAt412 cycle_at_sound412)
open RoutedMixed456 (endsAtField)
open Yulang.GeneralDeclarationPatterns (normalize)

/-- No new public Result/Witness tag; a receipt for one checked head place
and actual existing compiled field traversal. Not candidate matching,
pre-ambiguity dispatch, or source position selection for diagnostics. -/
structure HeadFieldReceipt where
  authored : HeadAddress
  path : MixedPath
  terminal : Nat
  stamp : Bool
  rows : List Nat
  literal : List Hit

structure HeadFieldWire (p : Problem) where
  authored : HeadAddress
  spine : CompilerFieldWire p.state.core

def readHeadField {p : Problem} (checked : CheckedTable p.state.core.current)
    (w : HeadFieldWire p) : Option HeadFieldReceipt := do
  let a ← readPrecheckedHead (p := p) checked w.authored
  let h := a.orig
  let (path,last,_,used) ← readJoint p.state.core.current.ordinary (policy p.state.core)
    (fun _ => queryKeys p.state.core) inheritedCompilerPlacement h.capture.lower
    (normalized (readTerm h.original)) h.code w.spine.visit
  if endsAtField path last && checkCycleAt412 p.state.core.current.ordinary last w.spine.cycle then
    some ⟨h.location,path,last,used,indexedRows w.spine.visit,
      locateRoute (fun _ => queryKeys p.state.core) h.original h.capture.lower path⟩
  else none

def ExactHeadField {p : Problem} (checked : CheckedTable p.state.core.current)
    (r : HeadFieldReceipt) : Prop :=
  ∃ (a : PrecheckedHead (p := p) checked) (last : Term),
    a.orig.location = r.authored ∧
    IndexedJoint p.state.core.current.ordinary (policy p.state.core)
      (fun _ => queryKeys p.state.core) a.orig.capture.lower
      (normalized (readTerm a.orig.original)) a.orig.code r.path r.rows r.terminal last r.stamp ∧
    endsAtField r.path r.terminal = true ∧
    AliasCycle p.state.core.current.ordinary (observed p.state.core.current.ordinary) r.terminal ∧
    r.literal = locateRoute (fun _ => queryKeys p.state.core) a.orig.original a.orig.capture.lower r.path

theorem prechecked_head_field_iff_finite_exact_wire {p : Problem}
    (checked : CheckedTable p.state.core.current) (r : HeadFieldReceipt) :
    ExactHeadField (p := p) checked r ↔ ∃ w, readHeadField (p := p) checked w = some r := by
  constructor
  · rintro ⟨a,last,auth,joint,field,cycle,literal⟩
    obtain ⟨w,ordinals,trail⟩ := exact_indexed_structural_route_has_same_order_finite_wire joint
    obtain ⟨cyc,seen⟩ := (naked_raw_cycle_has_finite_wire455 _ r.terminal).mp cycle
    refine ⟨⟨a.orig.location,⟨w,cyc⟩⟩,?_⟩
    rcases r with ⟨addr,path,n,stamp,rows,lit⟩
    dsimp at auth literal trail seen field ⊢
    subst addr
    subst lit
    simp [readHeadField,each_prechecked_head_position_replays checked a,trail,field,
      seen,ordinals,Option.bind]
  · rintro ⟨w,run⟩
    cases source : readPrecheckedHead (p := p) checked w.authored with
    | none => simp [readHeadField,source,Option.bind] at run
    | some a =>
      cases trail : readJoint p.state.core.current.ordinary (policy p.state.core) (fun _ => queryKeys p.state.core)
          inheritedCompilerPlacement a.orig.capture.lower (normalized (readTerm a.orig.original))
          a.orig.code w.spine.visit with
      | none => simp [readHeadField,source,trail,Option.bind] at run
      | some result =>
        obtain ⟨path,terminal,last,stamp⟩ := result
        by_cases yes : endsAtField path terminal = true ∧
            checkCycleAt412 p.state.core.current.ordinary terminal w.spine.cycle = true
        · have eq : ⟨a.orig.location,path,terminal,stamp,indexedRows w.spine.visit,
              locateRoute (fun _ => queryKeys p.state.core) a.orig.original a.orig.capture.lower path⟩ = r :=
            Option.some.inj (by simpa [readHeadField,source,trail,yes,Option.bind] using run)
          subst r
          exact ⟨a,last,rfl,read_same_wire_preserves_every_selected_physical_index trail,
            yes.1,cycle_at_sound412 yes.2,rfl⟩
        · simp [readHeadField,source,trail,yes,Option.bind] at run

theorem exact_prechecked_head_field_keeps_original_and_evidence_in_each_fit
    (input : Input) {r : HeadFieldReceipt}
    (orig : ExactHeadField (p := input.problem.old) input.checked r)
    (m : I72.Model) (fit : I72.FitsFull input.problem.state m) :
    ∃ (h : PrecheckedHead (p := input.problem.old) input.checked) (last : Term),
      h.orig.location = r.authored ∧ r.literal ≠ [] ∧
      IndexedSourceFit input.problem.state.base.core m (fun _ => queryKeys input.problem.state.base.core)
        h.orig.capture.lower (normalized (readTerm h.orig.original)) h.orig.code r.path r.rows
        r.terminal last r.stamp ∧
      AliasCycle input.problem.state.base.core.current.ordinary
        (observed input.problem.state.base.core.current.ordinary) r.terminal := by
  obtain ⟨h,last,addr,actual,_,cycle,lit⟩ := orig
  have model := all_same_fits_preserve_native_proof_on_each_identical_physical_row actual m fit.1
  have joint := erase_indices_preserves_an_identical_authorized_trail actual
  have compiled := descend_actual_compiler_alignment
    (source_head_member_compiles_exactly_once_for_its_original_pattern h.orig) joint
  have org : readTerm (normalize h.orig.original) = normalized (readTerm h.orig.original) := by
    rw [← read_write_term (normalized _),normalized_reencodes_exactly,write_read_term]
  obtain ⟨poses,t,pos,selected⟩ :=
    PhysicalOrigin.existing_compiled_trail_has_finite_literal_origin compiled h.orig.original org
  have found := PhysicalOrigin.route_occurrences_exact.mpr pos
  refine ⟨h,last,addr,?_,model,cycle⟩
  intro missing
  rw [← lit,missing] at found
  exact List.not_mem_nil found

end Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463

import Yulang.GeneralDeclarativeI65I74OriginalPhysicalPositions463
import Yulang.GeneralDeclarativeI65I74PreviousOrdinaryMaterialBoundary465

set_option backward.isDefEq.respectTransparency false
namespace Yulang.C466WrittenBinderCoordinates
open GeneralDeclarationPatterns (Pattern variablesArgs)
open GeneralDeclarativeI65.I72.WrittenPattern460.PhysicalOrigin (Pose atSource sourceStep)
open GeneralDeclarativeTermWalk322 (Occurrence Walk)
open GeneralNominalCenteredHeadMatExpressions (translate)

abbrev BinderAt := List Pose × Nat
def under (which : Pose) (body : List BinderAt) : List BinderAt :=
  body.map fun a => (which::a.1,a.2)

mutual
def bindersAt : Pattern → List BinderAt
  | .var n => [([],n)]
  | .app _ args => argsAt 0 args
  | .record _ p t => under .payload (bindersAt p) ++ under .tail (bindersAt t)
  | .variant _ p => under .variant (bindersAt p)
  | .join p q => under .left (bindersAt p) ++ under .right (bindersAt q)
termination_by p => sizeOf p

def argsAt (i : Nat) : List Pattern → List BinderAt
  | [] => []
  | p::rest => under (.app i) (bindersAt p) ++ argsAt (i+1) rest
termination_by ps => sizeOf ps
end

private theorem under_maps_binders (pos : Pose) (xs : List BinderAt) :
    (under pos xs).map Prod.snd = xs.map Prod.snd := by simp [under,List.map_map,Function.comp_def]
mutual
theorem written_binder_indices_keep_the_old_order_and_multiplicity (p : Pattern) :
    (bindersAt p).map Prod.snd = p.variables := by
  cases p with
  | var => simp [bindersAt,Pattern.variables]
  | app key xs =>
    simp [bindersAt,Pattern.variables,args_indices_keep_the_old_order_and_multiplicity 0 xs]
  | record l p t =>
    simp [bindersAt,Pattern.variables,under_maps_binders,
      written_binder_indices_keep_the_old_order_and_multiplicity p,
      written_binder_indices_keep_the_old_order_and_multiplicity t]
  | variant l p =>
    simp [bindersAt,Pattern.variables,under_maps_binders,
      written_binder_indices_keep_the_old_order_and_multiplicity p]
  | join p q =>
    simp [bindersAt,Pattern.variables,under_maps_binders,
      written_binder_indices_keep_the_old_order_and_multiplicity p,
      written_binder_indices_keep_the_old_order_and_multiplicity q]
termination_by sizeOf p

theorem args_indices_keep_the_old_order_and_multiplicity (i : Nat) (ps : List Pattern) :
    (argsAt i ps).map Prod.snd = variablesArgs ps := by
  cases ps with
  | nil => simp [argsAt,variablesArgs]
  | cons p rest =>
    simp [argsAt,variablesArgs,under_maps_binders,
      written_binder_indices_keep_the_old_order_and_multiplicity p,
      args_indices_keep_the_old_order_and_multiplicity (i+1) rest]
termination_by sizeOf ps
end

private theorem actual_under {pose : Pose} {xs : List BinderAt} {a : BinderAt} (mem : a ∈ under pose xs) :
    ∃ trail, (trail,a.2) ∈ xs ∧ a.1 = pose::trail := by
  obtain ⟨⟨q,n⟩,uses,same⟩ := List.mem_map.mp mem
  cases same
  exact ⟨q,uses,rfl⟩

mutual
theorem each_binder_address_records_a_literal_occurrence (p : Pattern) (loc : BinderAt)
    (found : loc ∈ bindersAt p) : atSource p loc.1 = some (.var loc.2) := by
  cases p with
  | var n =>
    rw [bindersAt] at found
    obtain rfl := List.mem_singleton.mp found
    rfl
  | app key args =>
    rw [bindersAt] at found
    obtain ⟨i,u,rest,lookup,pos,deep⟩ := literal_binder_in_app_at_original_index 0 args loc found
    rw [pos]
    simp [atSource,sourceStep,lookup,Option.bind,deep]
  | record l p t =>
    rw [bindersAt,List.mem_append] at found
    rcases found with left|right
    · obtain ⟨q,uses,same⟩ := actual_under left
      rw [same]
      exact each_binder_address_records_a_literal_occurrence p (q,loc.2) uses
    · obtain ⟨q,uses,same⟩ := actual_under right
      rw [same]
      exact each_binder_address_records_a_literal_occurrence t (q,loc.2) uses
  | variant l p =>
    rw [bindersAt] at found
    obtain ⟨q,uses,same⟩ := actual_under found
    rw [same]
    exact each_binder_address_records_a_literal_occurrence p (q,loc.2) uses
  | join p t =>
    rw [bindersAt,List.mem_append] at found
    rcases found with left|right
    · obtain ⟨q,uses,same⟩ := actual_under left
      rw [same]
      exact each_binder_address_records_a_literal_occurrence p (q,loc.2) uses
    · obtain ⟨q,uses,same⟩ := actual_under right
      rw [same]
      exact each_binder_address_records_a_literal_occurrence t (q,loc.2) uses
termination_by sizeOf p

theorem literal_binder_in_app_at_original_index (off : Nat) (ps : List Pattern)
    (loc : BinderAt) (found : loc ∈ argsAt off ps) :
    ∃ i u rest, ps[i]? = some u ∧ loc.1 = .app (off+i)::rest ∧ atSource u rest = some (.var loc.2) := by
  cases ps with
  | nil => simp [argsAt] at found
  | cons p tail =>
    rw [argsAt,List.mem_append] at found
    rcases found with first|later
    · obtain ⟨q,uses,same⟩ := actual_under first
      exact ⟨0,p,q,rfl,by simpa using same,each_binder_address_records_a_literal_occurrence p (q,loc.2) uses⟩
    · obtain ⟨i,u,t,atChild,same,go⟩ := literal_binder_in_app_at_original_index (off+1) tail loc later
      have idx : off+1+i = off+(i+1) := by omega
      exact ⟨i+1,u,t,atChild,idx ▸ same,go⟩
termination_by sizeOf ps
end

theorem an_actual_ordinary_capture_index_links_to_an_exact_literal_binder_site
    {c interpretation p code root} {seen : List Occurrence} {i : Nat} {found : Occurrence}
    (compile : translate c interpretation p = some code)
    (walk : Walk .actual root code seen)
    (seenAt : seen[i]? = some found) :
    ∃ site, (bindersAt p)[i]? = some (site,found.binder) ∧ atSource p site = some (.var found.binder) := by
  have signature : seen.map Occurrence.binder = (bindersAt p).map Prod.snd :=
    (GeneralDeclarativeTermOccurrences322.source_binders compile walk).1.trans
      (written_binder_indices_keep_the_old_order_and_multiplicity p).symm
  have exactAt := congrArg (fun (xs : List Nat) => xs[i]?) signature
  cases written : (bindersAt p)[i]? with
  | none => simp [List.getElem?_map,seenAt,written] at exactAt
  | some result =>
    obtain ⟨site,binder⟩ := result
    have h : found.binder = binder := by simpa [List.getElem?_map,seenAt,written] using exactAt
    subst binder
    exact ⟨site,rfl,each_binder_address_records_a_literal_occurrence p _
      (List.mem_of_getElem? written)⟩

open GeneralDeclarativeInlineTrace331 (Read realize)
open GeneralDeclarationPatterns (normalize)

theorem a_supported_old_materialization_read_pins_the_normalized_written_capture
    {s c interpretation original code root done}
    {support : GeneralDeclarativeOrigins321.Supported s done} {used : List Occurrence} {n : Nat} {found : Occurrence}
    (compiled : translate c interpretation (normalize original) = some code)
    (source : Read (GeneralDeclarativeOrigins321.restriction support) .actual root code used)
    (selected : used[n]? = some found) :
    ∃ path, (bindersAt (normalize original))[n]? = some (path,found.binder) ∧
      atSource (normalize original) path = some (.var found.binder) := by
  obtain ⟨_,_,read⟩ := realize source
  exact an_actual_ordinary_capture_index_links_to_an_exact_literal_binder_site compiled read selected

end Yulang.C466WrittenBinderCoordinates

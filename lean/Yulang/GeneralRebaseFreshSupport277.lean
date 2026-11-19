import Yulang.GeneralRebaseCompiledEvidence277
import Yulang.GeneralRebaseRegistrySurface277

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 9200000
namespace Yulang.GeneralRebaseFreshSupport277
open GeneralDeclarations
open GeneralNominalState (State sources)
open GeneralNominalIdentities (Origin source source_identity source_above_seed)
open GeneralNominalVersionedAllocation231 (Fresh keys)
open GeneralRebaseDisplayChildFresh276 (keys_root)
open GeneralNominalExamples (state registry displayRoot)
open GeneralRebaseCompiledDisplay277 (compiled parent)
open GeneralRebaseCompiledChildFresh277 (old_support parentReserved)

def Support (s : State) (root : Nat) : Prop :=
  ∀ id ∈ sources s, id ≤ s.seed ∨
    ∃ key : Origin, source s.seed key = id ∧ (key ∈ s.allocated ∨ key.1 ≠ root)

theorem fresh_of_support {s : State} {root : Nat} (supported : Support s root)
    (reg : Registry) (bs : GeneralNominalAllocation.Bindings) : Fresh s reg root bs := by
  intro proposed owns appears
  rcases supported _ appears with small|⟨recorded,same,justified⟩
  · exact False.elim (Nat.not_le_of_gt (source_above_seed s.seed proposed) small)
  · have eq := (source_identity s.seed recorded proposed).mp same
    subst recorded
    exact justified.elim id (fun foreign => False.elim (foreign (keys_root owns)))

theorem original_support (root : Nat) : Support (state true) root := by
  intro id member
  exact Or.inl (GeneralRebaseDisplayFrame276.source_ids id member)

theorem compiled_support (root : Nat) : Support GeneralRebaseCompiledChild277.context.state root := by
  intro id member
  rcases old_support id member with small|reserved
  · exact Or.inl small
  · obtain ⟨key,owns,same⟩ := List.mem_map.mp reserved
    exact Or.inr ⟨key,same,Or.inl (List.mem_append_right _ owns)⟩

theorem fixture_fresh (reg : Registry) (root : Nat) (bs : GeneralNominalAllocation.Bindings) :
    Fresh GeneralRebaseCompiledChild277.context.state reg root bs :=
  fresh_of_support (compiled_support root) reg bs

def oldKey : Origin := GeneralNominalAllocation.origin displayRoot.identity 2 5 21 0

theorem original_key : oldKey ∈ keys registry displayRoot.identity [] := by decide +kernel

theorem compiled_no_key : oldKey ∉ keys compiled displayRoot.identity [] := by decide +kernel

def reservedOnly : State :=
  GeneralNominalState.extend (state true) [source (state true).seed oldKey] []

theorem reserved_support {id : Nat} (member : id ∈ sources reservedOnly) :
    id ≤ reservedOnly.seed ∨ id = source reservedOnly.seed oldKey := by
  change id ∈ List.ofFn (state true).base.source ++ List.ofFn (state true).base.rowSource ++
    ([] ++ [source (state true).seed oldKey]) ++ ([] ++ []).flatMap GeneralNominalState.atomSources at member
  simp only [List.nil_append,List.flatMap_nil,List.append_nil,List.mem_append] at member
  rcases member with (ty|row)|reserved
  · obtain ⟨slot,eq⟩ := List.mem_ofFn.mp ty
    change slot.val = id at eq
    have bound := slot.isLt
    exact Or.inl (by change id ≤ 1; omega)
  · obtain ⟨slot,eq⟩ := List.mem_ofFn.mp row
    change slot.val = id at eq
    have bound := slot.isLt
    exact Or.inl (by change id ≤ 1; omega)
  · exact Or.inr (List.mem_singleton.mp reserved)

theorem loses_fresh : ¬ Fresh reservedOnly registry displayRoot.identity [] := by
  intro holds
  have member : source reservedOnly.seed oldKey ∈ sources reservedOnly := by
    unfold sources
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_singleton_self _
  exact List.not_mem_nil (holds oldKey original_key member)

theorem compiled_fresh : Fresh reservedOnly compiled displayRoot.identity [] := by
  intro key owns seen
  rcases reserved_support seen with small|same
  · exact False.elim (Nat.not_le_of_gt (source_above_seed reservedOnly.seed key) small)
  · have eq := (source_identity reservedOnly.seed key oldKey).mp same
    subst key
    exact False.elim (compiled_no_key owns)

/-- This arbitrary extension is not claimed to be source-reachable. It
isolates why equal constructors and role-0 visibility do not imply that raw
global allocation freshness is registry independent at arbitrary states. -/
theorem freshness_counterexample :
    registry.constructors = compiled.constructors ∧
    (∀ d : Declaration, d.role = 0 → (d ∈ registry.declarations ↔ d ∈ compiled.declarations)) ∧
    ¬ Fresh reservedOnly registry displayRoot.identity [] ∧ Fresh reservedOnly compiled displayRoot.identity [] := by
  refine ⟨rfl,?_,loses_fresh,compiled_fresh⟩
  intro d role
  constructor
  · intro mem
    change d ∈ [GeneralNominalExamples.intDisplay,GeneralDeclarationExamples.display,GeneralDeclarationExamples.wrap] at mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_self)
    · cases role
  · intro present
    rcases GeneralRebaseCompiledDisplay277.compiled_members present role with rfl|rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_self)

end Yulang.GeneralRebaseFreshSupport277

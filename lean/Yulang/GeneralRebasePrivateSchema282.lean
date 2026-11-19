import Yulang.GeneralRebasePrivateHead282
import Yulang.GeneralNominalGeneratedSupport184

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebasePrivateSchema282
open GeneralNominalCenters (Plan Site)
open GeneralRebasePrivateKey282 (port Excludes different_purpose capture_private binder_private)
open GeneralRebasePrivateHead282 (output_private schema_private)
open GeneralRebaseAggregateTags281 (Tag fixedOrigin)
open GeneralNominalCenteredFrame179 (siteSources)
open GeneralNominalVersionedHeadFrame236 (variableSources schemaSources)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalGeneratedSupport184 (schemas_roots)
open GeneralNominalSaturationState (Packet)

def SiteSafe (site : Site roles) (target : Nat) : Prop :=
  ∀ index, target ≠ (site.occurrence.demand.arguments index).1 ∧
    target ≠ (site.occurrence.demand.arguments index).2 ∧ target ≠ site.center index

theorem site_private (safe : SiteSafe site target) : target ∉ siteSources site := by
  intro found
  obtain ⟨part,belongs,member⟩ := List.mem_flatten.mp found
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp belongs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with one|two|three
  · exact (safe index).1 one
  · exact (safe index).2.1 two
  · exact (safe index).2.2 three

theorem port_nonzero (seed owner decl : Nat) (tag : Tag) : port seed owner decl tag ≠ 0 := by
  have positive := GeneralNominalIdentities.source_above_seed seed (fixedOrigin owner decl tag)
  unfold port
  omega

theorem index_private (xs : List Nat) (target : Nat) (outside : target ∉ xs) (nonzero : target ≠ 0)
    (index : Nat) : target ≠ xs[index]?.getD 0 := by
  cases h : xs[index]? with
  | none => exact nonzero
  | some a =>
    intro equal
    have used := List.mem_of_getElem? h
    exact outside (equal.symm ▸ used)

theorem head_private (q : Plan roles) (apart : Excludes q.packet owner decl tag)
    (site : SiteSafe q.input (port q.packet.context.state.seed owner decl tag)) :
    port q.packet.context.state.seed owner decl tag ∉ schemaSources q q.headSchema := by
  let t := port q.packet.context.state.seed owner decl tag
  let pool := 0 :: List.ofFn q.input.center
  have absent : t ∉ pool := by
    intro h
    rcases List.mem_cons.mp h with zero|listed
    · exact port_nonzero _ _ _ _ zero
    · obtain ⟨idx,eq⟩ := List.mem_ofFn.mp listed
      exact (site idx).2.2 eq.symm
  have given : GeneralNominalGeneratedSupport184.Roots q.headSchema pool := by
    unfold Plan.headSchema
    apply schemas_roots
    intro k
    change (List.ofFn q.input.center)[k]?.getD 0 ∈ pool
    cases h : (List.ofFn q.input.center)[k]? with
    | none => exact List.mem_cons_self
    | some a => exact List.mem_cons_of_mem _ (List.mem_of_getElem? h)
  change port q.packet.context.state.seed owner decl tag ∉ pool at absent
  intro used
  rcases List.mem_append.mp used with tests|variables
  · obtain ⟨test,listed,eq⟩ := List.mem_map.mp tests
    exact absent (eq ▸ given.1 test listed)
  · obtain ⟨entry,listed,found⟩ := List.mem_flatMap.mp variables
    have root := given.2 entry listed
    unfold variableSources at found
    split at found
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at found
      exact found.elim (fun h => absent (h.symm ▸ root)) (binder_private apart entry.name)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at found
      rcases found with own|out|lo|hi
      · exact absent (own.symm ▸ root)
      · exact output_private q tag entry.name out
      · exact (capture_private apart entry.name).1 lo
      · exact (capture_private apart entry.name).2 hi

end Yulang.GeneralRebasePrivateSchema282

import Yulang.GeneralLatePeerDirectPlan311

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralLatePeerFresh311
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalSaturationState (Packet)
open GeneralNominalVersionedAllocation231 (keys Fresh)
open GeneralNominalVersionedInstallation231 (atoms reserved)
open GeneralNominalIdentities (source source_identity source_above_seed)
open GeneralDictionaryOrdinaryTransport (extend)
open GeneralNominalState (sources atomSources)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarationExamples (roles)
open GeneralLatePeerSource311 (compiled root initial initial_source)
open GeneralLatePeerRoot311 (direct branch z)
open GeneralLatePeerFirst311 (after)

def Pool (s : GeneralNominalState.State) (owners : List Nat) : Prop :=
  ∀ n ∈ sources s, n ≤ s.seed ∨ ∃ key : GeneralNominalIdentities.Origin,
    key.1 ∈ owners ∧ source s.seed key = n

theorem initial_pool : Pool initial.core.erased.current.context.state [] :=
  fun n present => .inl (initial_source.below_seed n present)

theorem extend_pool (ctx : GeneralNominalCandidates.Context) (p : Packet roles)
    (same : p.context = ctx) (pool : Pool ctx.state owners)
    (small : ∀ atom ∈ atoms p, ∀ n ∈ atomSources atom, n ≤ ctx.state.seed) :
    Pool (extend ctx (reserved p) (atoms p) (GeneralNominalVersionedInstallation231.allocated p)).state
      (p.site.occurrence.identity :: owners) := by
  intro n present
  have included : sources (GeneralNominalState.extend ctx.state (reserved p) (atoms p)) ⊆
      sources ctx.state ++ reserved p ++ (atoms p).flatMap atomSources :=
    GeneralNominalAllocationSupport.extend_sources _ _ _
      (fun _ h => List.mem_append_left _ (List.mem_append_left _ h))
      (fun _ h => List.mem_append_left _ (List.mem_append_right _ h))
      (fun atom mid n hit => List.mem_append_right _ (List.mem_flatMap.mpr ⟨atom,mid,hit⟩))
  have seen := included present
  simp only [List.mem_append] at seen
  rcases seen with (old|new)|ordinary
  · rcases pool n old with bounded|⟨key,registered,eq⟩
    · exact .inl bounded
    · exact .inr ⟨key,List.mem_cons_of_mem _ registered,eq⟩
  · obtain ⟨k,hit,eq⟩ := List.mem_map.mp new
    have owner := GeneralRebaseDisplayChildFresh276.keys_root hit
    have keyMember : k.1 ∈ p.site.occurrence.identity :: owners := by
      rw [owner]; exact List.mem_cons_self
    exact Or.inr ⟨k,keyMember,(congrArg (fun x => source x k)
      (congrArg (fun c : GeneralNominalCandidates.Context => c.state.seed) same).symm).trans eq⟩
  · obtain ⟨atom,listed,seen⟩ := List.mem_flatMap.mp ordinary
    exact .inl (small atom listed n seen)

theorem before : Pool after.core.erased.current.context.state [root.identity] := by
  apply extend_pool initial.core.erased.current.context GeneralLatePeerRoot311.packet rfl initial_pool
  have bounded : ∀ n ∈ (atoms GeneralLatePeerRoot311.packet).flatMap atomSources, n ≤ 2 := by
    unfold atoms
    rw [GeneralLatePeerRoot311.bindings_exact,GeneralLatePeerRoot311.report]
    decide +kernel
  exact fun atom mem n seen => bounded n (List.mem_flatMap.mpr ⟨atom,mem,seen⟩)

theorem fresh {s : GeneralNominalState.State} {owners : List Nat} (pool : Pool s owners)
    (r : Registry) (focus : Nat) (new : focus ∉ owners) (bs : GeneralNominalAllocation.Bindings) :
    Fresh s r focus bs := by
  intro key listed collision
  rcases pool _ collision with small|⟨old,member,eq⟩
  · exact False.elim ((Nat.not_lt_of_ge small) (source_above_seed _ _))
  · have same := (source_identity s.seed _ _).mp eq
    cases same
    exact False.elim (new ((GeneralRebaseDisplayChildFresh276.keys_root listed) ▸ member))

theorem direct_different : direct.occurrence.identity ≠ root.identity := by decide +kernel
theorem branch_different : branch.occurrence.identity ≠ root.identity := by decide +kernel
theorem distinct_child : branch.occurrence.identity ≠ direct.occurrence.identity := by decide +kernel

theorem no_alias_before {x y : Nat}
    (rel : GeneralNominalSaturationState.Alias after.core.erased.current x y) : x = y := by
  induction rel with
  | refl => rfl
  | edge h => cases h
  | symm _ ih => exact ih.symm
  | trans _ _ a b => exact a.trans b

end Yulang.GeneralLatePeerFresh311

import Yulang.CommonRoleSettledFrontier

namespace Yulang.CommonRoleSettledResolver
open CommonRoleSettledSyntax CommonRoleSettledConstraints CommonRoleSettledFrontier
open CommonRoleOutermostResolver (Child Tree Result Classify)

/-- A retained success came from this actual visible declaration and actual
captured payload; keys/children cannot be supplied independently of the head. -/
theorem trial_hit_origin (s : State n) (role : Nat) (t : Ty) (source d : Declaration) (payload : Ty)
    (h : trial s role t source = some (.hit d payload)) :
    source = d ∧ Inspect d.head t (.hit payload) := by
  unfold trial at h
  split at h
  · split at h
    · cases observed : inspect source.head t <;> simp [observed, encode] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, (inspect_exact ..).mp observed⟩
    · cases h
  · cases h

theorem scan_hit_origin (s : State n) (role : Nat) (t : Ty) (visible : List Declaration)
    (d : Declaration) (payload : Ty) (h : Trial.hit d payload ∈ scan s role t visible) :
    d ∈ visible ∧ Inspect d.head t (.hit payload) := by
  induction visible with
  | nil => cases h
  | cons first rest ih =>
      simp only [scan, List.mem_append] at h
      rcases h with firstHit | restHit
      · have observed : trial s role t first = some (.hit d payload) := by
          simpa using firstHit
        obtain ⟨rfl, inspected⟩ := trial_hit_origin s role t first d payload observed
        exact ⟨List.mem_cons_self, inspected⟩
      · obtain ⟨member, inspected⟩ := ih restHit
        exact ⟨List.mem_cons_of_mem _ member, inspected⟩

theorem mem_hits (results : List Trial) (d : Declaration) (payload : Ty) :
    (d, payload) ∈ hits results ↔ Trial.hit d payload ∈ results := by
  simp only [hits, List.mem_filterMap]
  constructor
  · rintro ⟨result, member, found⟩
    cases result <;> simp only [Option.some.injEq, Prod.mk.injEq] at found
    · cases found
    · cases found
    · obtain ⟨rfl, rfl⟩ := found; exact member
  · intro h; exact ⟨.hit d payload, h, rfl⟩

theorem selected_origin (visible : List Declaration) (q : Request n) (key : Nat)
    (cs : List (Request n)) (h : Local visible q (.selected key cs)) :
    ∃ t d payload, q.lower = some t ∧ d ∈ visible ∧ Inspect d.head t (.hit payload) ∧
      key = d.key ∧ cs = children q d payload := by
  cases h with
  | @ready t results _ lower _ _ scanned decision =>
      cases decision with
      | @selected d payload _ _ chosen =>
          have present : Trial.hit d payload ∈ results :=
            (mem_hits results d payload).mp (by rw [chosen]; exact List.mem_cons_self)
          rw [← scan_complete scanned] at present
          obtain ⟨member, inspected⟩ := scan_hit_origin _ _ _ _ d payload present
          exact ⟨_, d, payload, lower, member, inspected, rfl, rfl⟩

def weight (q : Request n) : Nat := (q.lower.map Ty.weight).getD 0

/-- Every child of every independently selected declaration descends by the
same declaration-time Paterson check. This includes pending/rejecting children. -/
theorem child_decreases (registry : Registry) (q child : Request n)
    (h : Child (Local registry.declarations) child q) : weight child < weight q := by
  obtain ⟨key, cs, selected, member⟩ := h
  obtain ⟨t, d, payload, lower, visible, inspected, _, rfl⟩ := selected_origin _ _ _ _ selected
  obtain ⟨r, required, rfl⟩ := List.mem_map.mp member
  have strict := checked_child_decreases d (registry.checked d visible) r required t payload inspected
  simpa [weight, Request.known, lower] using strict

/-- Accessibility is constructed for EVERY settled request over a registry
accepted by the declaration checker. Neither accessibility nor descent is
an input field of a request or a registry. -/
theorem accessible (registry : Registry) (q : Request n) :
    Acc (Child (Local registry.declarations)) q := by
  have all : ∀ measure, ∀ q : Request n, weight q = measure →
      Acc (Child (Local registry.declarations)) q := by
    intro measure
    induction measure using Nat.strongRecOn with
    | ind measure ih =>
        intro q equal
        constructor
        intro child edge
        exact ih (weight child) (by rw [← equal]; exact child_decreases registry q child edge) child rfl
  exact all (weight q) q rfl

/-- The single outer recursive entry, with both bridge proofs supplied here. -/
def resolve (registry : Registry) (q : Request n) : Tree :=
  CommonRoleOutermostResolver.resolve (protocol registry.declarations)
    (frontier_exact registry.declarations) q (accessible registry q)

def classify (registry : Registry) (q : Request n) : Result :=
  CommonRoleOutermostResolver.classification (resolve registry q)

theorem resolve_tree_exact (registry : Registry) (q : Request n) (tree : Tree) :
    resolve registry q = tree ↔ CommonRoleOutermostResolver.Resolves
      (Local registry.declarations) q tree :=
  CommonRoleOutermostResolver.resolve_tree_exact_of_frontier_exact
    (protocol registry.declarations) (frontier_exact _) q (accessible registry q) tree

/-- Unconditional on frontier exactness, accessibility, child success, fuel,
or a preselected dictionary. The domain is explicitly the settled fragment. -/
theorem resolve_exact (registry : Registry) (q : Request n) (result : Result) :
    classify registry q = result ↔ Classify (Local registry.declarations) q result :=
  CommonRoleOutermostResolver.resolve_exact_of_frontier_exact
    (protocol registry.declarations) (frontier_exact _) q (accessible registry q) result

/-- Executable unfold lemma for the outer entry used by the conformance cases. -/
theorem resolve_eq (registry : Registry) (q : Request n) :
    resolve registry q = match frontier registry.declarations q with
      | .pending => .pending
      | .rejected => .rejected
      | .ambiguous => .ambiguous
      | .selected key cs => .selected key (cs.map (resolve registry)) := by
  unfold resolve
  rw [CommonRoleOutermostResolver.resolve_unfold]
  dsimp only [protocol]
  split <;> rename_i observed <;> simp only [observed]
  rename_i key cs
  change Tree.selected key (cs.attach.map (fun child => resolve registry child.val)) =
    Tree.selected key (cs.map (resolve registry))
  simp only [List.map_attach_eq_pmap, List.pmap_eq_map]

/-- Literal snapshot closure: all children share the entire original state.
Together with generated_state_exact (for every model and actual payload),
no successful candidate adds an effective ordinary constraint. -/
theorem child_state_unchanged (q : Request n) (d : Declaration) (payload : Ty)
    (child : Request n) (member : child ∈ children q d payload) : child.state = q.state := by
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp member
  rfl

/-- Recollection in this fragment is a no-op for every original ordinary
model, not merely for a canonical solver model. No associated equations are
admitted, and fresh capture slots are disjoint from all original slots. -/
theorem where_state_recollection (q : Request n) (d : Declaration) (payload : Ty)
    (child : Request n) (member : child ∈ children q d payload)
    (assignment : Fin n → Core.PresenceGeneration.Comp Common.model)
    (actualPayload : Core.PresenceGeneration.Comp Common.model) :
    child.state = q.state ∧
      (PresenceNormalForm.All Common.model (Fin.cases actualPayload assignment)
        (q.state.atoms.map (PresenceNormalForm.Atom.rename Fin.succ) ++
          CommonRoleCandidateConstraints.generate (slots d.head.names)) ↔
        PresenceNormalForm.All Common.model assignment q.state.atoms) :=
  ⟨child_state_unchanged q d payload child member, generated_state_exact q.state d.head.names assignment actualPayload⟩

end Yulang.CommonRoleSettledResolver

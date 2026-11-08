import Yulang.CommonRoleOpenProducer

namespace Yulang.CommonRoleOpenProducerAccess
open CommonRoleSettledSyntax CommonRoleOpenProducer
open CommonRoleOutermostResolver (Child)

theorem trial_hit_origin (role : Nat) (lo hi : Ty) (source d : Declaration)
    (lowPayload highPayload : Ty)
    (h : trial role lo hi source = some (.hit d lowPayload highPayload)) :
    source = d ∧ source.role = role ∧ Inspect d.head lo (.hit lowPayload) ∧
      Inspect d.head hi (.hit highPayload) := by
  unfold trial at h
  split at h
  · rename_i same
    cases lower : inspect source.head lo <;> cases upper : inspect source.head hi <;>
      simp [lower, upper, encode] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, same, (inspect_exact ..).mp lower, (inspect_exact ..).mp upper⟩
  · cases h

theorem scan_hit_origin (role : Nat) (lo hi : Ty) (visible : List Declaration)
    (d : Declaration) (lp hp : Ty) (h : Trial.hit d lp hp ∈ scan role lo hi visible) :
    d ∈ visible ∧ d.role = role ∧ Inspect d.head lo (.hit lp) ∧ Inspect d.head hi (.hit hp) := by
  induction visible with
  | nil => cases h
  | cons first rest ih =>
      simp only [scan, List.mem_append] at h
      rcases h with firstHit | restHit
      · have observed : trial role lo hi first = some (.hit d lp hp) := by simpa using firstHit
        obtain ⟨rfl, same, inspected⟩ := trial_hit_origin role lo hi first d lp hp observed
        exact ⟨List.mem_cons_self, same, inspected⟩
      · obtain ⟨member, same, inspected⟩ := ih restHit
        exact ⟨List.mem_cons_of_mem _ member, same, inspected⟩

theorem mem_hits (results : List Trial) (d : Declaration) (lp hp : Ty) :
    (d, lp, hp) ∈ hits results ↔ Trial.hit d lp hp ∈ results := by
  simp only [hits, List.mem_filterMap]
  constructor
  · rintro ⟨result, member, found⟩
    cases result <;> simp only [Option.some.injEq, Prod.mk.injEq] at found
    · cases found
    · cases found
    · obtain ⟨rfl, rfl, rfl⟩ := found; exact member
  · intro h; exact ⟨.hit d lp hp, h, rfl⟩

theorem selected_origin (visible : List Declaration) (q : Request) (key : Nat)
    (cs : List Request) (h : Local visible q (.selected key cs)) :
    ∃ d lp hp, d ∈ visible ∧ d.role = q.role ∧
      Inspect d.head q.lower (.hit lp) ∧ Inspect d.head q.upper (.hit hp) ∧
      key = d.key ∧ cs = children q d lp hp := by
  cases h with
  | @ready results _ scanned decision =>
      cases decision with
      | @selected d lp hp _ _ chosen =>
          have present : Trial.hit d lp hp ∈ results :=
            (mem_hits results d lp hp).mp (by rw [chosen]; exact List.mem_cons_self)
          rw [← scan_complete scanned] at present
          obtain ⟨member, same, low, high⟩ := scan_hit_origin _ _ _ _ d lp hp present
          exact ⟨d, lp, hp, member, same, low, high, rfl, rfl⟩

theorem selected_production (visible : List Declaration) (q : Request) (key : Nat)
    (cs : List Request) (h : Local visible q (.selected key cs)) :
    ∃ d lp hp, production visible q = some (d, lp, hp) ∧
      key = d.key ∧ cs = children q d lp hp := by
  cases h with
  | @ready results _ scanned decision =>
      cases decision with
      | @selected d lp hp _ _ chosen =>
          refine ⟨d, lp, hp, ?_, rfl, rfl⟩
          simp [production, scan_complete scanned, chosen]

/-- Actual produced children embed in the independent two-endpoint transition. -/
theorem child_step (visible : List Declaration) (q child : Request)
    (h : Child (Local visible) child q) : CommonRoleOpenDescent.Step visible child q := by
  obtain ⟨key, cs, selected, member⟩ := h
  obtain ⟨d, lp, hp, visible, same, low, high, _, rfl⟩ := selected_origin _ _ _ _ selected
  obtain ⟨r, required, rfl⟩ := List.mem_map.mp member
  exact .requirement visible same low high required

theorem child_decreases (registry : Registry) (q child : Request)
    (h : Child (Local registry.declarations) child q) :
    CommonRoleOpenDescent.weight child < CommonRoleOpenDescent.weight q :=
  CommonRoleOpenDescent.step_decreases registry.declarations registry.checked child q (child_step _ _ _ h)

/-- Accessibility is derived for every actual producer request from checked declarations. -/
theorem accessible (registry : Registry) (q : Request) :
    Acc (Child (Local registry.declarations)) q := by
  have all : ∀ measure, ∀ q : Request, CommonRoleOpenDescent.weight q = measure →
      Acc (Child (Local registry.declarations)) q := by
    intro measure
    induction measure using Nat.strongRecOn with
    | ind measure ih =>
        intro q equal
        constructor
        intro child edge
        exact ih (CommonRoleOpenDescent.weight child)
          (by rw [← equal]; exact child_decreases registry q child edge) child rfl
  exact all _ q rfl

end Yulang.CommonRoleOpenProducerAccess

import Yulang.GeneralDictionary170NamedAccessible

/-! Fixed-journal dictionary edge paths have an explicit rank bound.
This is not a bound on saturation execution or total dictionary nodes. -/
namespace Yulang.GeneralDictionary170PathBound
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionary170NamedCoverage
open GeneralDictionary170NamedAccessible
variable {roles : Roles.RoleDecls}

/-- A chosen-child path records edges, so the empty path has length zero. -/
inductive Path (coverage : Coverage registry state domain) :
    Subtype domain → Subtype domain → Nat → Prop
  | nil (focus) : Path coverage focus focus 0
  | cons {parent child finish count} (edge : Child coverage child parent)
      (tail : Path coverage child finish count) : Path coverage parent finish (count + 1)

theorem rank_budget (coverage : Coverage registry state domain)
    (path : Path coverage start finish count) :
    count + rank state finish.val ≤ rank state start.val := by
  induction path with
  | nil focus => simp
  | @cons parent child finish count edge tail ih =>
    have step := child_rank coverage child parent edge
    omega

theorem length_le_rank (coverage : Coverage registry state domain)
    (path : Path coverage start finish count) : count ≤ rank state start.val := by
  have bound := rank_budget coverage path
  omega

theorem length_le_ceiling (coverage : Coverage registry state domain)
    (path : Path coverage start finish count) : count ≤ ceiling state + 1 := by
  have bound := length_le_rank coverage path
  unfold rank at bound
  omega

theorem no_positive_cycle (coverage : Coverage registry state domain)
    (path : Path coverage focus focus count) : count = 0 := by
  have bound := rank_budget coverage path
  omega

theorem rank_zero_terminal (coverage : Coverage registry state domain)
    (focus : Subtype domain) (zero : rank state focus.val = 0) :
    (coverage.node focus.val focus.property).children = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro child member
  have decrease := child_rank coverage ⟨child,coverage.closed focus.val focus.property child member⟩ focus member
  omega

/-- A node-count convention for a single path counts its root as well. -/
theorem vertices_le_rank_succ (coverage : Coverage registry state domain)
    (path : Path coverage start finish count) : count + 1 ≤ rank state start.val + 1 := by
  have bound := length_le_rank coverage path
  omega
end Yulang.GeneralDictionary170PathBound

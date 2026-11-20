import Yulang.GeneralRebaseEpochWindow284

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseWindowPaths284
open GeneralRebaseRoundMicro278 (Tick next)
open GeneralRebaseEpochWindow284 (Window view advance forward)

def RawEdge (first last : Tick) : Prop := last = next first
def QuotEdge (first last : Window) : Prop := last = advance first

def roundFuture (t : Tick) : Nat → Tick
  | 0 => t
  | n+1 => next (roundFuture t n)

def compactFuture (s : Window) : Nat → Window
  | 0 => s
  | n+1 => advance (compactFuture s n)

theorem every_future (t : Tick) (n : Nat) :
    compactFuture (view t) n = view (roundFuture t n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [roundFuture,compactFuture,ih,forward]

theorem map_routes {a b : Tick} (path : B4Target.Steps RawEdge a b) :
    B4Target.Steps QuotEdge (view a) (view b) := by
  induction path with
  | refl => exact .refl
  | tail earlier step ih =>
    exact .tail ih ((congrArg view step).trans (forward _))

theorem lift_routes {a : Tick} {b : Window}
    (path : B4Target.Steps QuotEdge (view a) b) :
    ∃ finish, B4Target.Steps RawEdge a finish ∧ view finish = b := by
  induction path with
  | refl => exact ⟨a,.refl,rfl⟩
  | @tail mid final earlier step ih =>
    obtain ⟨finish,old,same⟩ := ih
    exact ⟨next finish,.tail old rfl,(forward finish).trans ((congrArg advance same).trans step.symm)⟩

theorem route_iff (a : Tick) (s : Window) :
    B4Target.Steps QuotEdge (view a) s ↔
      ∃ finish, B4Target.Steps RawEdge a finish ∧ view finish = s := by
  refine ⟨lift_routes,?_⟩
  rintro ⟨u,path,rfl⟩
  exact map_routes path

theorem actual_routes {roles : Roles.RoleDecls} {reg : GeneralDeclarations.Registry}
    {root : GeneralSourceDictionaries.Occurrence roles}
    (raw : Tick → GeneralNominalVersionedJournal232.State roles)
    (real : ∀ t, GeneralNominalVersionedMixedKernel234.Step reg root (raw t) (raw (next t)))
    {a b : Tick} (path : B4Target.Steps RawEdge a b) :
    B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step reg root) (raw a) (raw b) := by
  induction path with
  | refl => exact .refl
  | tail old new ih =>
    exact .tail ih (new ▸ real _)

end Yulang.GeneralRebaseWindowPaths284

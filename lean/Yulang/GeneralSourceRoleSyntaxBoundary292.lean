import Yulang.GeneralSourceRoleManifest292

/-! A hand-off carrier describing only the relevant binary evidence of the real
CST interface. It is not the Rust CST, nor evidence that this producer is wired. -/
namespace Yulang.GeneralSourceRoleSyntaxBoundary292
open GeneralSourceRoleSpelling292 GeneralSourceRoleExport292

inductive Owner where
  | roleBodyDirect
  | other
  deriving DecidableEq, Repr

inductive Rhs where
  | absent
  | binder (s : String)
  | nullary (s : String)
  | recovery
  | unsupported
  deriving DecidableEq, Repr

structure Shape where
  spelling : String
  equalsToken : Bool
  rhs : Rhs
  clean : Bool
  deriving DecidableEq, Repr

inductive Admitted : Owner → Shape → Output → Prop
  | required (name : String) : Admitted .roleBodyDirect ⟨name,false,.absent,true⟩
      ⟨name,.required⟩
  | binder (name s : String) : Admitted .roleBodyDirect ⟨name,true,.binder s,true⟩
      ⟨name,.binder s⟩
  | nullary (name s : String) : Admitted .roleBodyDirect ⟨name,true,.nullary s,true⟩
      ⟨name,.nullary s⟩

def project : Owner → Shape → Option Output
  | .roleBodyDirect, ⟨name,false,.absent,true⟩ => some ⟨name,.required⟩
  | .roleBodyDirect, ⟨name,true,.binder s,true⟩ => some ⟨name,.binder s⟩
  | .roleBodyDirect, ⟨name,true,.nullary s,true⟩ => some ⟨name,.nullary s⟩
  | _, _ => none

theorem projection_exact (owner : Owner) (shape : Shape) (out : Output) :
    project owner shape = some out ↔ Admitted owner shape out := by
  constructor
  · intro h
    rcases shape with ⟨name,eq,rhs,clean⟩
    cases owner <;> cases eq <;> cases rhs <;> cases clean <;>
      simp [project] at h
    all_goals subst out; first | exact .required _ | exact .binder _ _ | exact .nullary _ _
  · intro h; cases h <;> rfl

theorem missing_rhs_not_required (name : String) (clean : Bool) :
    project .roleBodyDirect ⟨name,true,.absent,clean⟩ = none := by cases clean <;> rfl

theorem present_rhs_requires_equals (name s : String) (clean : Bool) :
    project .roleBodyDirect ⟨name,false,.binder s,clean⟩ = none ∧
    project .roleBodyDirect ⟨name,false,.nullary s,clean⟩ = none :=
  by cases clean <;> exact ⟨rfl,rfl⟩

theorem same_shape_needs_owner (name : String) :
    ¬ ∃ unowned : Shape → Option Output,
        ∀ own shape, unowned shape = project own shape := by
  rintro ⟨f,h⟩
  have bad := (h .roleBodyDirect ⟨name,false,.absent,true⟩).symm.trans
    (h .other ⟨name,false,.absent,true⟩)
  cases bad

structure Shell where
  name : String
  parameters : List String
  directTypeChildren : List Shape

def projectRole (s : Shell) : Option Role :=
  (collect (project .roleBodyDirect) s.directTypeChildren).map fun outputs =>
    ⟨s.name,s.parameters,outputs⟩

theorem projectRole_exact (s : Shell) (r : Role) :
    projectRole s = some r ↔ s.name = r.spelling ∧ s.parameters = r.binders ∧
      Aligned (Admitted .roleBodyDirect) s.directTypeChildren r.outputs := by
  unfold projectRole
  obtain ⟨name,params,outs⟩ := r
  simp only
  rw [←collect_exact _ _ (projection_exact .roleBodyDirect)]
  cases h : collect (project .roleBodyDirect) s.directTypeChildren <;> simp [Role.mk.injEq]

end Yulang.GeneralSourceRoleSyntaxBoundary292

import Yulang.GeneralSourceRoleSyntaxPipeline292

/-! Complete direct-child observation in an explicit finite hand-off. It is
not a substitute for an independently obtained complete parser-owned list. -/
namespace Yulang.GeneralSourceRoleChildCoverage292
open GeneralSourceRoleSpelling292 GeneralSourceRoleSyntaxBoundary292

/-- `other` must be independently established as a direct non-type member.
Unknown and recovery-bearing candidates must not be silently skipped. -/
inductive Child where
  | other
  | typeDecl : Shape → Child
  | unknown
  deriving DecidableEq, Repr

inductive Collects : List Child → List Shape → Prop
  | nil : Collects [] []
  | other {xs ts} : Collects xs ts → Collects (.other :: xs) ts
  | typeDecl {shape xs ts} : Collects xs ts → Collects (.typeDecl shape :: xs) (shape :: ts)

def scan : List Child → Option (List Shape)
  | [] => some []
  | .other :: xs => scan xs
  | .typeDecl shape :: xs => (scan xs).map (shape :: ·)
  | .unknown :: _ => none

theorem scan_exact (children : List Child) (members : List Shape) :
    scan children = some members ↔ Collects children members := by
  induction children generalizing members with
  | nil =>
    constructor
    · intro h; cases Option.some.inj h; exact .nil
    · intro h; cases h; rfl
  | cons child children ih =>
    constructor
    · intro h
      cases child with
      | other => exact .other ((ih members).mp h)
      | unknown => cases h
      | typeDecl shape =>
        cases res : scan children with
        | none => simp [scan,res] at h
        | some tail =>
          have e : shape :: tail = members := by simpa [scan,res] using h
          subst members
          exact .typeDecl ((ih tail).mp res)
    · intro h
      cases h with
      | other tail => exact (ih _).mpr tail
      | typeDecl tail => simp [scan,(ih _).mpr tail]

theorem member_exact {children : List Child} {members : List Shape}
    (h : Collects children members) (shape : Shape) :
    shape ∈ members ↔ Child.typeDecl shape ∈ children := by
  induction h with
  | nil => simp
  | other _ ih => simpa using ih
  | @typeDecl shape0 children members _ ih =>
    simp only [List.mem_cons,Child.typeDecl.injEq,ih]

theorem no_unknown {children : List Child} {members : List Shape}
    (h : Collects children members) : Child.unknown ∉ children := by
  induction h with
  | nil => simp
  | other _ ih => simpa using ih
  | typeDecl _ ih => simpa using ih

theorem scan_success_iff (children : List Child) :
    (∃ members, scan children = some members) ↔ Child.unknown ∉ children := by
  constructor
  · rintro ⟨members,scanned⟩
    exact no_unknown ((scan_exact ..).mp scanned)
  · induction children with
    | nil => exact fun _ => ⟨[],rfl⟩
    | cons ch cs ih =>
      intro h
      have rest : Child.unknown ∉ cs := fun p => h (List.mem_cons_of_mem _ p)
      obtain ⟨tail,success⟩ := ih rest
      cases ch with
      | other => exact ⟨tail,success⟩
      | typeDecl s => exact ⟨s :: tail,by simp [scan,success]⟩
      | unknown => exact False.elim (h List.mem_cons_self)

theorem ordered_members (children : List Child) (members : List Shape)
    (accepted : scan children = some members) :
    members = children.filterMap (fun c => match c with | .typeDecl s => some s | _ => none) := by
  have h := (scan_exact ..).mp accepted
  clear accepted
  induction h with
  | nil => rfl
  | other _ ih => exact ih
  | typeDecl _ ih => simp [ih]

end Yulang.GeneralSourceRoleChildCoverage292

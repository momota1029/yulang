import Yulang.GeneralSourceMetadataDeclarations291

/-! Default bodies must be enumerated separately from declarations.
An explicit completeness witness is necessary for arbitrary role maps. -/
namespace Yulang.GeneralSourceMetadataDefaults291
open GeneralSourceMetadataUse291
open GeneralSourceMetadataSyntax291 (terms term_exact)
open GeneralSourceMetadataDeclarations291 (explicitCheck explicit_exact)
open GeneralDeclarations (Registry)
open GeneralDeclarationPatterns (Constructors)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadWFSource (DefaultsCovered Coverage)

structure Default where
  role : Nat
  name : Nat
  body : Roles.Term
  deriving DecidableEq, Repr

def Manifest (roles : Roles.RoleDecls) (ds : List Default) : Prop :=
  ∀ role name rhs, (⟨role,name,rhs⟩ : Default) ∈ ds ↔ (roles role).assoc name = some (some rhs)

def defaultUses (ds : List Default) : List Use := ds.flatMap (fun d => terms d.body)

def defaultCheck (c : Constructors) (i : Interpretation) (ds : List Default) : Bool :=
  check c i (defaultUses ds)

theorem defaults_exact (c : Constructors) (i : Interpretation) (roles : Roles.RoleDecls)
    (ds : List Default) (manifest : Manifest roles ds) :
    defaultCheck c i ds = true ↔ DefaultsCovered c i roles := by
  simp only [defaultCheck,check_exact,defaultUses,use_flatMap,term_exact,DefaultsCovered]
  constructor
  · intro h role name rhs found
    exact h ⟨role,name,rhs⟩ ((manifest role name rhs).mpr found)
  · intro h d present
    exact h d.role d.name d.body ((manifest d.role d.name d.body).mp present)

def coverageCheck (r : Registry) (i : Interpretation) (ds : List Default) : Bool :=
  explicitCheck r i && defaultCheck r.constructors i ds

theorem coverage_exact (r : Registry) (i : Interpretation) (ds : List Default)
    (manifest : Manifest r.roles ds) :
    coverageCheck r i ds = true ↔ Coverage r i := by
  simp only [coverageCheck,Bool.and_eq_true,explicit_exact,defaults_exact _ _ _ _ manifest,Coverage]

end Yulang.GeneralSourceMetadataDefaults291

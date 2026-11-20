import Yulang.GeneralSourceMetadataBuildRoles291

/-! Data-only entry on resolved, non-parsed syntax. The only internally
generated proofs are the old positional role-scope conditions. -/
namespace Yulang.GeneralSourceMetadataBareBundle291
open GeneralSourceMetadataRows291 (Source)
open GeneralSourceMetadataBuildRoles291 (Input build_exact)
open GeneralSourceMetadataBundle291 (SourceBundle Certificate inspect)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataExprDomain291 (bind_success)

structure InputBundle where
  declared : Source
  snapshot : Source
  roles : Input
  declarations : List Declaration

def forget (bundle : SourceBundle) : InputBundle :=
  ⟨bundle.declared,bundle.snapshot,GeneralSourceMetadataBuildRoles291.forget bundle.roles,bundle.declarations⟩

def compile (bundle : InputBundle) : Option SourceBundle :=
  (GeneralSourceMetadataBuildRoles291.build bundle.roles).bind fun roles =>
    some ⟨bundle.declared,bundle.snapshot,roles,bundle.declarations⟩

def run (bundle : InputBundle) : Option Certificate := (compile bundle).map inspect

theorem preserves_input (source : InputBundle) (assembled : SourceBundle)
    (found : compile source = some assembled) :
    forget assembled = source ∧ GeneralSourceMetadataRoles291.Valid assembled.roles := by
  obtain ⟨out,foundRole,eq⟩ := bind_success found
  have first : (⟨source.declared,source.snapshot,out,source.declarations⟩ : SourceBundle) = assembled :=
    Option.some.inj eq
  subst assembled
  have role := (build_exact _ _).mp foundRole
  refine ⟨?_,role.2⟩
  cases source
  simp only [forget]
  rw [role.1]

theorem reassemble (source : SourceBundle) (valid : GeneralSourceMetadataRoles291.Valid source.roles) :
    compile (forget source) = some source := by
  have ready := (build_exact _ _).mpr ⟨rfl,valid⟩
  unfold compile forget
  rw [ready]
  cases source
  rfl

end Yulang.GeneralSourceMetadataBareBundle291

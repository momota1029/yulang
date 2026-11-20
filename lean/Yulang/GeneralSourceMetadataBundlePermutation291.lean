import Yulang.GeneralSourceMetadataDiagnosticProvenance291

/-! Reordering validated resolved input tables does not affect the
attached registry/context or the pack's readiness. Declarations retain
exact order; this does not rewrite an anchored receipt world. -/
namespace Yulang.GeneralSourceMetadataBundlePermutation291
open GeneralSourceMetadataBundle291 (SourceBundle Attached inspect ready_exact)
open GeneralSourceMetadataPermutation291 (source_perm)
open GeneralSourceMetadataRolePermutation291 (same_role_table valid_roles_reorder)
open GeneralDeclarations (Registry)
open GeneralNominalCandidates (Context)

structure Reordered (old new : SourceBundle) : Prop where
  declared : old.declared.rows.Perm new.declared.rows
  declaredFallback : old.declared.fallback = new.declared.fallback
  recorded : old.snapshot.rows.Perm new.snapshot.rows
  recordedFallback : old.snapshot.fallback = new.snapshot.fallback
  roleRows : old.roles.rows.Perm new.roles.rows
  roleFallback : old.roles.fallbackArity = new.roles.fallbackArity
  declarationsUnchanged : new.declarations = old.declarations

abbrev SourceValid := GeneralSourceMetadataValidation291.Valid
abbrev RolesValid := GeneralSourceMetadataRoles291.Valid

theorem attached_reordered {old new : SourceBundle} {r : Registry} {ctx : Context}
    (attached : Attached old r ctx) (order : Reordered old new)
    (d : SourceValid old.declared) (t : SourceValid old.snapshot)
    (roles : RolesValid old.roles) :
    Attached new r ctx ∧ SourceValid new.declared ∧ SourceValid new.snapshot ∧ RolesValid new.roles := by
  obtain ⟨dd,sameD,_⟩ := source_perm order.declared order.declaredFallback d
  obtain ⟨tt,sameT,sameInterp⟩ := source_perm order.recorded order.recordedFallback t
  have rr := valid_roles_reorder order.roleRows roles
  have sameRole := same_role_table order.roleRows order.roleFallback roles
  exact ⟨⟨⟨attached.tables.declaredCorrect.trans sameD,attached.tables.snapshotCorrect.trans sameT,
    attached.tables.interpretationCorrect.trans sameInterp⟩,sameRole.symm.trans attached.roles,
    order.declarationsUnchanged.trans attached.declarations⟩,dd,tt,rr⟩

theorem whole_ready_unchanged {old new : SourceBundle} {r : Registry} {ctx : Context}
    (attached : Attached old r ctx) (order : Reordered old new)
    (d : SourceValid old.declared) (t : SourceValid old.snapshot)
    (roles : RolesValid old.roles) :
    (inspect old).ready = (inspect new).ready := by
  obtain ⟨attachedNew,dd,tt,rr⟩ := attached_reordered attached order d t roles
  apply Bool.eq_iff_iff.mpr
  rw [ready_exact attached,ready_exact attachedNew]
  exact ⟨fun was => ⟨dd,tt,rr,was.2.2.2⟩,fun now => ⟨d,t,roles,now.2.2.2⟩⟩

end Yulang.GeneralSourceMetadataBundlePermutation291

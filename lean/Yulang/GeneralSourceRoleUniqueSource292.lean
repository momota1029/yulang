import Yulang.GeneralSourceRoleScopedShell292

/-! A successful table assigns each numeric role and role-local output ID to
one witnessed input entry. Equality here is of typed data, not Rust ranges. -/
namespace Yulang.GeneralSourceRoleUniqueSource292
open GeneralSourceRoleSpelling292 (Environment Output)
open GeneralSourceRoleExport292 (Aligned)
open GeneralSourceRoleScopedExport292 (ScopedRole Witness lower lower_exact)
open GeneralSourceMetadataRoles291 (RoleSource RoleRow)
open GeneralSourceRoleManifest292 (aligned_left)

theorem aligned_images {A B C : Type} {p : A → B → Prop}
    {xs : List A} {ys : List B} (align : Aligned p xs ys) (f : A → C) (g : B → C)
    (h : ∀ a b, p a b → f a = g b) :
    xs.map f = ys.map g := by
  induction align with
  | nil => rfl
  | cons head _ ih => simp only [List.map_cons,h _ _ head,ih]

theorem injective_on_members {A C : Type} (f : A → C) (xs : List A)
    (unique : (xs.map f).Nodup) {a b : A} (ha : a ∈ xs) (hb : b ∈ xs) (same : f a = f b) :
    a = b := by
  induction xs with
  | nil => cases ha
  | cons x xs ih =>
    simp only [List.map_cons,List.nodup_cons] at unique
    rcases List.mem_cons.mp ha with rfl | atail <;> rcases List.mem_cons.mp hb with rfl | btail
    · rfl
    · exact False.elim (unique.1 (List.mem_map.mpr ⟨b,btail,same.symm⟩))
    · exact False.elim (unique.1 (List.mem_map.mpr ⟨a,atail,same⟩))
    · exact ih unique.2 atail btail

theorem role_keys_nodup {Scope : Type} {env : Scope → Environment} {fallback : Nat}
    {input : List (ScopedRole Scope)} {out : RoleSource} (ok : lower env fallback input = some out) :
    (input.map (fun row => (env row.scope).role row.role.spelling)).Nodup := by
  have facts := (lower_exact ..).mp ok
  let f : ScopedRole Scope → Option Nat := fun row => (env row.scope).role row.role.spelling
  have images := aligned_images facts.2.1 f (fun row => some row.role) (fun _ _ h => h.2.1)
  change (input.map f).Nodup
  rw [images,List.map_map]
  change (out.rows.map (some ∘ RoleRow.role)).Nodup
  rw [← List.map_map (f := RoleRow.role) (g := some)]
  exact facts.2.2.1.map some (fun _ _ diff same => diff (Option.some.inj same))

theorem unique_role {Scope : Type} {env : Scope → Environment} {fallback : Nat}
    {input : List (ScopedRole Scope)} {out : RoleSource} (ok : lower env fallback input = some out)
    {left right : ScopedRole Scope} (l : left ∈ input) (r : right ∈ input)
    (same : (env left.scope).role left.role.spelling = (env right.scope).role right.role.spelling) :
    left = right :=
  injective_on_members _ input (role_keys_nodup ok) l r same

theorem unique_output {Scope : Type} {env : Scope → Environment} {fallback : Nat}
    {input : List (ScopedRole Scope)} {out : RoleSource} (ok : lower env fallback input = some out)
    {entry : ScopedRole Scope} (found : entry ∈ input) {key : Nat}
    (role : (env entry.scope).role entry.role.spelling = some key)
    {left right : Output} (l : left ∈ entry.role.outputs) (r : right ∈ entry.role.outputs)
    (same : (env entry.scope).output key left.spelling = (env entry.scope).output key right.spelling) :
    left = right := by
  have facts := (lower_exact ..).mp ok
  obtain ⟨raw,inTable,w⟩ := aligned_left facts.2.1 found
  obtain ⟨row,inSource,rfl⟩ := List.mem_map.mp inTable
  have roleID := Option.some.inj (role.symm.trans w.2.1)
  change key = row.role at roleID
  subst key
  let f : Output → Option Nat := fun o => (env entry.scope).output row.role o.spelling
  have images := aligned_images w.2.2.2 f (fun p => some p.1) (fun _ _ h => h.1)
  have valid : (entry.role.outputs.map f).Nodup := by
    rw [images]
    change (row.outputs.map (some ∘ Prod.fst)).Nodup
    rw [← List.map_map (f := Prod.fst) (g := some)]
    exact (facts.2.2.2 row inSource).map some (fun _ _ diff same => diff (Option.some.inj same))
  exact injective_on_members f entry.role.outputs valid l r same

open GeneralSourceRoleScopedShell292 (Packet run run_exact)
open GeneralSourceRoleSyntaxBoundary292 (Shape Admitted Owner)
open GeneralSourceRoleChildCoverage292 (Child)

theorem unique_packet {Scope : Type} {env : Scope → Environment} {fallback : Nat}
    {input : List (Packet Scope)} {out : RoleSource} (ok : run env fallback input = some out)
    {left right : Packet Scope} (l : left ∈ input) (r : right ∈ input)
    (same : (env left.scope).role left.source.name = (env right.scope).role right.source.name) :
    left = right := by
  obtain ⟨entries,shape,worked⟩ := (run_exact ..).mp ok
  let f : Packet Scope → Option Nat := fun p => (env p.scope).role p.source.name
  have correct := aligned_images shape f (fun q => (env q.scope).role q.role.spelling) (by
    rintro p q ⟨scope,shell,inv,assoc⟩
    change (env p.scope).role p.source.name = (env q.scope).role q.role.spelling
    rw [scope,inv.1,assoc.1])
  have nd : (input.map f).Nodup := correct ▸ role_keys_nodup worked
  exact injective_on_members f input nd l r same

theorem admitted_shape_unique {left right : Shape} {out : Output}
    (l : Admitted .roleBodyDirect left out) (r : Admitted .roleBodyDirect right out) :
    left = right := by
  cases l <;> cases r <;> rfl

theorem unique_packet_member {Scope : Type} {env : Scope → Environment} {fallback : Nat}
    {input : List (Packet Scope)} {out : RoleSource} (ok : run env fallback input = some out)
    {p : Packet Scope} (inPackets : p ∈ input)
    {rid : Nat} (key : (env p.scope).role p.source.name = some rid)
    {left right : Shape} (l : Child.typeDecl left ∈ p.source.directChildren)
    (r : Child.typeDecl right ∈ p.source.directChildren)
    {first second : Output}
    (lshape : Admitted .roleBodyDirect left first) (rshape : Admitted .roleBodyDirect right second)
    (same : (env p.scope).output rid first.spelling = (env p.scope).output rid second.spelling) :
    left = right := by
  obtain ⟨entries,supplied,worked⟩ := (run_exact ..).mp ok
  obtain ⟨entry,member,scope,shell,inventory,represent⟩ := aligned_left supplied inPackets
  have leftAt := (GeneralSourceRoleChildCoverage292.member_exact inventory.2.2 left).mpr l
  have rightAt := (GeneralSourceRoleChildCoverage292.member_exact inventory.2.2 right).mpr r
  obtain ⟨oL,lmem,lok⟩ := aligned_left represent.2.2 leftAt
  obtain ⟨oR,rmem,rok⟩ := aligned_left represent.2.2 rightAt
  have eqL : first = oL := Option.some.inj
    (((GeneralSourceRoleSyntaxBoundary292.projection_exact ..).mpr lshape).symm.trans
      ((GeneralSourceRoleSyntaxBoundary292.projection_exact ..).mpr lok))
  have eqR : second = oR := Option.some.inj
    (((GeneralSourceRoleSyntaxBoundary292.projection_exact ..).mpr rshape).symm.trans
      ((GeneralSourceRoleSyntaxBoundary292.projection_exact ..).mpr rok))
  rw [scope,inventory.1,represent.1] at key
  rw [scope,eqL,eqR] at same
  have eq := unique_output worked member key lmem rmem same
  exact admitted_shape_unique lok (eq.symm ▸ rok)

end Yulang.GeneralSourceRoleUniqueSource292

import YulangClosure.PaperCoreStep

/-!
Composition laws for the existing capture-avoiding paper term operations.
The raw operations intentionally leave omitted constructors opaque. These
equations describe those actual operations, not a new full-language traversal.
Typed applications below use the unchanged represented paper judgments.
-/
namespace YulangClosure.PaperTypes.PaperTermAlgebra

private theorem map_eq_self_iff {α : Type} (f : α → α) (xs : List α) :
    xs.map f = xs ↔ ∀ x ∈ xs, f x = x := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

private theorem map_attach_map_iff {α β : Type} (xs : List α)
    (f : {x // x ∈ xs} → β) (g : α → β) :
    xs.attach.map f = xs.map g ↔ ∀ x h, f ⟨x,h⟩ = g x := by
  rw [← List.attach_map_val (l := xs) (f := g), List.map_eq_map_iff]
  constructor
  · intro h x hx; exact h ⟨x,hx⟩ (List.mem_attach _ _)
  · intro h x _; exact h x.val x.property

private theorem rename_record (f : Nat → Nat) (fields : List (Label × Presence × Value)) :
    renameTermValue f (.record fields) =
      .record (fields.map fun x => (x.1, x.2.1, renameTermValue f x.2.2)) := by
  simp only [renameTermValue]
  exact congrArg Value.record (List.attach_map_val (l := fields)
    (f := fun x : Label × Presence × Value => (x.1, x.2.1, renameTermValue f x.2.2)))

@[simp] theorem liftRenaming_id : liftTermRenaming id = id := by
  funext n; cases n <;> rfl

@[simp] theorem liftRenamingN_id (n : Nat) : liftTermRenamingN n id = id := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [liftTermRenamingN, ih, liftRenaming_id]

theorem liftRenaming_comp (f g : Nat → Nat) :
    liftTermRenaming (f ∘ g) = liftTermRenaming f ∘ liftTermRenaming g := by
  funext n; cases n <;> rfl

theorem liftRenamingN_comp (n : Nat) (f g : Nat → Nat) :
    liftTermRenamingN n (f ∘ g) = liftTermRenamingN n f ∘ liftTermRenamingN n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [liftTermRenamingN, ih, liftRenaming_comp]

private theorem lift_comp_eta (f g : Nat → Nat) :
    (fun x => liftTermRenaming f (liftTermRenaming g x)) =
      liftTermRenaming (fun x => f (g x)) := (liftRenaming_comp f g).symm

private theorem liftN_comp_eta (n : Nat) (f g : Nat → Nat) :
    (fun x => liftTermRenamingN n f (liftTermRenamingN n g x)) =
      liftTermRenamingN n (fun x => f (g x)) := (liftRenamingN_comp n f g).symm

private structure RenameAt (n : Nat) : Prop where
  value : ∀ (v : Value), sizeOf v = n → ∀ (f g : Nat → Nat),
    renameTermValue f (renameTermValue g v) = renameTermValue (f ∘ g) v
  computation : ∀ (c : Computation), sizeOf c = n → ∀ (f g : Nat → Nat),
    renameTermComputation f (renameTermComputation g c) =
      renameTermComputation (f ∘ g) c

set_option linter.unusedSimpArgs false in
private theorem renameAt_all (n : Nat) : RenameAt n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hv (v : Value) (h : sizeOf v < n) (f g : Nat → Nat) :=
      (ih (sizeOf v) h).value v rfl f g
    have hc (c : Computation) (h : sizeOf c < n) (f g : Nat → Nat) :=
      (ih (sizeOf c) h).computation c rfl f g
    constructor
    · intro v hn f g
      cases v
      all_goals
        try rfl
        simp +arith at hn
        simp (config := { contextual := true }) (disch := first | omega | simp)
          [rename_record, renameTermValue, renameTermComputation,
           List.attach_map_val, List.attach_map, List.map_map, Function.comp_def,
           List.map_eq_map_iff, map_attach_map_iff, hv, hc, lift_comp_eta, liftN_comp_eta]
      all_goals
        first
        | (intro label presence value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact hv value (by omega) f g)
        | (intro value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           exact hv value (by omega) f g)
    · intro c hn f g
      cases c
      all_goals
        try rfl
        simp +arith at hn
        simp (config := { contextual := true }) (disch := first | omega | simp)
          [renameTermComputation, rename_record, renameTermValue,
           List.attach_map_val, List.attach_map, List.map_map, Function.comp_def,
           List.map_eq_map_iff, map_attach_map_iff, hv, hc, lift_comp_eta, liftN_comp_eta]
      all_goals
        intro value hmem
        have hsmall := List.sizeOf_lt_of_mem hmem
        exact hv value (by omega) f g

theorem renameValue_comp (f g : Nat → Nat) (v : Value) :
    renameTermValue f (renameTermValue g v) = renameTermValue (f ∘ g) v :=
  (renameAt_all (sizeOf v)).value v rfl f g

theorem renameComputation_comp (f g : Nat → Nat) (c : Computation) :
    renameTermComputation f (renameTermComputation g c) =
      renameTermComputation (f ∘ g) c :=
  (renameAt_all (sizeOf c)).computation c rfl f g

private structure IdentityAt (n : Nat) : Prop where
  value : ∀ (v : Value), sizeOf v = n → renameTermValue id v = v
  computation : ∀ (c : Computation), sizeOf c = n → renameTermComputation id c = c

set_option linter.unusedSimpArgs false in
private theorem identityAt_all (n : Nat) : IdentityAt n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hv (v : Value) (h : sizeOf v < n) := (ih (sizeOf v) h).value v rfl
    have hc (c : Computation) (h : sizeOf c < n) := (ih (sizeOf c) h).computation c rfl
    constructor
    · intro v hn
      cases v
      all_goals
        try rfl
        simp +arith at hn
        simp (config := { contextual := true }) (disch := first | omega | simp)
          [rename_record, renameTermValue, renameTermComputation,
           List.attach_map_val, map_eq_self_iff, hv, hc]
      all_goals
        first
        | (intro label presence value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact hv value (by omega))
        | (intro value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           exact hv value (by omega))
    · intro c hn
      cases c
      all_goals
        try rfl
        simp +arith at hn
        simp (config := { contextual := true }) (disch := first | omega | simp)
          [renameTermComputation, rename_record, renameTermValue,
           List.attach_map_val, map_eq_self_iff, hv, hc]
      all_goals
        intro value hmem
        have hsmall := List.sizeOf_lt_of_mem hmem
        exact hv value (by omega)

@[simp] theorem renameValue_id (v : Value) : renameTermValue id v = v :=
  (identityAt_all (sizeOf v)).value v rfl

@[simp] theorem renameComputation_id (c : Computation) : renameTermComputation id c = c :=
  (identityAt_all (sizeOf c)).computation c rfl

private theorem map_record (σ : Nat → Ty) (fields : List (Label × Presence × Value)) :
    mapPaperValue σ (.record fields) =
      .record (fields.map fun x => (x.1, x.2.1, mapPaperValue σ x.2.2)) := by
  simp only [mapPaperValue]
  exact congrArg Value.record (List.attach_map_val (l := fields)
    (f := fun x : Label × Presence × Value => (x.1, x.2.1, mapPaperValue σ x.2.2)))

private structure TypeRenameAt (n : Nat) : Prop where
  value : ∀ (v : Value), sizeOf v = n → ∀ (σ : Nat → Ty) (f : Nat → Nat),
    mapPaperValue σ (renameTermValue f v) = renameTermValue f (mapPaperValue σ v)
  computation : ∀ (c : Computation), sizeOf c = n → ∀ (σ : Nat → Ty) (f : Nat → Nat),
    mapPaperComputation σ (renameTermComputation f c) =
      renameTermComputation f (mapPaperComputation σ c)

set_option linter.unusedSimpArgs false in
private theorem typeRenameAt_all (n : Nat) : TypeRenameAt n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hv (v : Value) (h : sizeOf v < n) (σ : Nat → Ty) (f : Nat → Nat) :=
      (ih (sizeOf v) h).value v rfl σ f
    have hc (c : Computation) (h : sizeOf c < n) (σ : Nat → Ty) (f : Nat → Nat) :=
      (ih (sizeOf c) h).computation c rfl σ f
    constructor
    · intro v hn σ f
      cases v
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := first | omega | simp)
          [map_record, rename_record, mapPaperValue, renameTermValue,
           List.attach_map_val, List.attach_map, List.map_map, Function.comp_def,
           List.map_eq_map_iff, map_attach_map_iff, hv, hc]
      all_goals
        first
        | (intro label presence value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact hv value (by omega) σ f)
        | (intro value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           exact hv value (by omega) σ f)
    · intro c hn σ f
      cases c
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := first | omega | simp)
          [mapPaperComputation, renameTermComputation, map_record, rename_record,
           mapPaperValue, renameTermValue,
           List.attach_map_val, List.attach_map, List.map_map, Function.comp_def,
           List.map_eq_map_iff, map_attach_map_iff, hv, hc]
      all_goals
        intro value hmem
        have hsmall := List.sizeOf_lt_of_mem hmem
        exact hv value (by omega) σ f

theorem mapType_renameValue (σ : Nat → Ty) (f : Nat → Nat) (v : Value) :
    mapPaperValue σ (renameTermValue f v) = renameTermValue f (mapPaperValue σ v) :=
  (typeRenameAt_all (sizeOf v)).value v rfl σ f

theorem mapType_renameComputation (σ : Nat → Ty) (f : Nat → Nat) (c : Computation) :
    mapPaperComputation σ (renameTermComputation f c) =
      renameTermComputation f (mapPaperComputation σ c) :=
  (typeRenameAt_all (sizeOf c)).computation c rfl σ f

private theorem replace_record (rho : Nat → Value) (fields : List (Label × Presence × Value)) :
    replaceTermValue rho (.record fields) =
      .record (fields.map fun x => (x.1, x.2.1, replaceTermValue rho x.2.2)) := by
  simp only [replaceTermValue]
  exact congrArg Value.record (List.attach_map_val (l := fields)
    (f := fun x : Label × Presence × Value => (x.1, x.2.1, replaceTermValue rho x.2.2)))

private theorem precompose_lift (rho : Nat → Value) (f : Nat → Nat) :
    (fun n => liftTermSubstitution rho (liftTermRenaming f n)) =
      liftTermSubstitution (fun n => rho (f n)) := by
  funext n; cases n <;> rfl

private theorem precompose_liftN (k : Nat) (rho : Nat → Value) (f : Nat → Nat) :
    (fun n => liftTermSubstitutionN k rho (liftTermRenamingN k f n)) =
      liftTermSubstitutionN k (fun n => rho (f n)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [liftTermSubstitutionN, liftTermRenamingN, ih] using
      precompose_lift (liftTermSubstitutionN k rho) (liftTermRenamingN k f)

private theorem precompose_shift (rho : Nat → Value) (f : Nat → Nat) :
    (fun n => shiftTermSubstitution rho (f n)) =
      shiftTermSubstitution (fun n => rho (f n)) := rfl

private structure ReplaceRenameAt (n : Nat) : Prop where
  value : ∀ (v : Value), sizeOf v = n → ∀ (rho : Nat → Value) (f : Nat → Nat),
    replaceTermValue rho (renameTermValue f v) = replaceTermValue (fun n => rho (f n)) v
  computation : ∀ (c : Computation), sizeOf c = n → ∀ (rho : Nat → Value) (f : Nat → Nat),
    replaceTermComputation rho (renameTermComputation f c) =
      replaceTermComputation (fun n => rho (f n)) c

set_option linter.unusedSimpArgs false in
private theorem replaceRenameAt_all (n : Nat) : ReplaceRenameAt n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hv (v : Value) (h : sizeOf v < n) (rho : Nat → Value) (f : Nat → Nat) :=
      (ih (sizeOf v) h).value v rfl rho f
    have hc (c : Computation) (h : sizeOf c < n) (rho : Nat → Value) (f : Nat → Nat) :=
      (ih (sizeOf c) h).computation c rfl rho f
    constructor
    · intro v hn rho f
      cases v
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := first | omega | simp)
          [replace_record, rename_record, replaceTermValue, renameTermValue,
           List.attach_map_val, List.attach_map, List.map_map, Function.comp_def,
           List.map_eq_map_iff, map_attach_map_iff, hv, hc,
           precompose_lift, precompose_liftN, precompose_shift]
      all_goals
        first
        | (intro label presence value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact hv value (by omega) rho f)
        | (intro value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           exact hv value (by omega) rho f)
    · intro c hn rho f
      cases c
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := first | omega | simp)
          [replaceTermComputation, renameTermComputation, replace_record, rename_record,
           replaceTermValue, renameTermValue,
           List.attach_map_val, List.attach_map, List.map_map, Function.comp_def,
           List.map_eq_map_iff, map_attach_map_iff, hv, hc,
           precompose_lift, precompose_liftN, precompose_shift]
      all_goals
        intro value hmem
        have hsmall := List.sizeOf_lt_of_mem hmem
        exact hv value (by omega) rho f

theorem replace_renameValue (rho : Nat → Value) (f : Nat → Nat) (v : Value) :
    replaceTermValue rho (renameTermValue f v) = replaceTermValue (fun n => rho (f n)) v :=
  (replaceRenameAt_all (sizeOf v)).value v rfl rho f

theorem replace_renameComputation (rho : Nat → Value) (f : Nat → Nat) (c : Computation) :
    replaceTermComputation rho (renameTermComputation f c) =
      replaceTermComputation (fun n => rho (f n)) c :=
  (replaceRenameAt_all (sizeOf c)).computation c rfl rho f

private theorem rename_lift (rho : Nat → Value) (f : Nat → Nat) :
    (fun n => renameTermValue (liftTermRenaming f) (liftTermSubstitution rho n)) =
      liftTermSubstitution (fun n => renameTermValue f (rho n)) := by
  funext n
  cases n with
  | zero => simp [liftTermSubstitution, renameTermValue, liftTermRenaming]
  | succ n =>
    simp only [liftTermSubstitution, renameValue_comp]
    rfl

private theorem rename_liftN (k : Nat) (rho : Nat → Value) (f : Nat → Nat) :
    (fun n => renameTermValue (liftTermRenamingN k f) (liftTermSubstitutionN k rho n)) =
      liftTermSubstitutionN k (fun n => renameTermValue f (rho n)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [liftTermSubstitutionN, liftTermRenamingN, ih] using
      rename_lift (liftTermSubstitutionN k rho) (liftTermRenamingN k f)

private theorem rename_shift (rho : Nat → Value) (f : Nat → Nat) :
    (fun n => renameTermValue f (shiftTermSubstitution rho n)) =
      shiftTermSubstitution (fun n => renameTermValue f (rho n)) := by
  funext n
  exact (mapType_renameValue shiftTypeSubstitution f (rho n)).symm

private structure RenameReplaceAt (n : Nat) : Prop where
  value : ∀ (v : Value), sizeOf v = n → ∀ (f : Nat → Nat) (rho : Nat → Value),
    renameTermValue f (replaceTermValue rho v) =
      replaceTermValue (fun n => renameTermValue f (rho n)) v
  computation : ∀ (c : Computation), sizeOf c = n → ∀ (f : Nat → Nat) (rho : Nat → Value),
    renameTermComputation f (replaceTermComputation rho c) =
      replaceTermComputation (fun n => renameTermValue f (rho n)) c

set_option linter.unusedSimpArgs false in
private theorem renameReplaceAt_all (n : Nat) : RenameReplaceAt n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hv (v : Value) (h : sizeOf v < n) (f : Nat → Nat) (rho : Nat → Value) :=
      (ih (sizeOf v) h).value v rfl f rho
    have hc (c : Computation) (h : sizeOf c < n) (f : Nat → Nat) (rho : Nat → Value) :=
      (ih (sizeOf c) h).computation c rfl f rho
    constructor
    · intro v hn f rho
      cases v
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := first | omega | simp)
          [rename_record, replace_record, renameTermValue, replaceTermValue,
           List.attach_map_val, List.attach_map, List.map_map, Function.comp_def,
           List.map_eq_map_iff, map_attach_map_iff, hv, hc,
           rename_lift, rename_liftN, rename_shift]
      all_goals
        first
        | (intro label presence value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact hv value (by omega) f rho)
        | (intro value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           exact hv value (by omega) f rho)
    · intro c hn f rho
      cases c
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := first | omega | simp)
          [renameTermComputation, replaceTermComputation, rename_record, replace_record,
           renameTermValue, replaceTermValue,
           List.attach_map_val, List.attach_map, List.map_map, Function.comp_def,
           List.map_eq_map_iff, map_attach_map_iff, hv, hc,
           rename_lift, rename_liftN, rename_shift]
      all_goals
        intro value hmem
        have hsmall := List.sizeOf_lt_of_mem hmem
        exact hv value (by omega) f rho

theorem rename_replaceValue (f : Nat → Nat) (rho : Nat → Value) (v : Value) :
    renameTermValue f (replaceTermValue rho v) =
      replaceTermValue (fun n => renameTermValue f (rho n)) v :=
  (renameReplaceAt_all (sizeOf v)).value v rfl f rho

theorem rename_replaceComputation (f : Nat → Nat) (rho : Nat → Value) (c : Computation) :
    renameTermComputation f (replaceTermComputation rho c) =
      replaceTermComputation (fun n => renameTermValue f (rho n)) c :=
  (renameReplaceAt_all (sizeOf c)).computation c rfl f rho

private theorem mapType_lift (σ : Nat → Ty) (rho : Nat → Value) :
    (fun n => mapPaperValue σ (liftTermSubstitution rho n)) =
      liftTermSubstitution (fun n => mapPaperValue σ (rho n)) := by
  funext n
  cases n with
  | zero => simp [liftTermSubstitution, mapPaperValue]
  | succ n => exact mapType_renameValue σ Nat.succ (rho n)

private theorem mapType_liftN (k : Nat) (σ : Nat → Ty) (rho : Nat → Value) :
    (fun n => mapPaperValue σ (liftTermSubstitutionN k rho n)) =
      liftTermSubstitutionN k (fun n => mapPaperValue σ (rho n)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [liftTermSubstitutionN, ih] using
      mapType_lift σ (liftTermSubstitutionN k rho)

private theorem mapType_shift (σ : Nat → Ty) (rho : Nat → Value) :
    (fun n => mapPaperValue (liftSub σ) (shiftTermSubstitution rho n)) =
      shiftTermSubstitution (fun n => mapPaperValue σ (rho n)) := by
  funext n
  exact mapPaperValue_shift_substitution_commutes 0 σ (rho n)

private structure TypeReplaceAt (n : Nat) : Prop where
  value : ∀ (v : Value), sizeOf v = n → ∀ (σ : Nat → Ty) (rho : Nat → Value),
    mapPaperValue σ (replaceTermValue rho v) =
      replaceTermValue (fun n => mapPaperValue σ (rho n)) (mapPaperValue σ v)
  computation : ∀ (c : Computation), sizeOf c = n → ∀ (σ : Nat → Ty) (rho : Nat → Value),
    mapPaperComputation σ (replaceTermComputation rho c) =
      replaceTermComputation (fun n => mapPaperValue σ (rho n)) (mapPaperComputation σ c)

set_option linter.unusedSimpArgs false in
private theorem typeReplaceAt_all (n : Nat) : TypeReplaceAt n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hv (v : Value) (h : sizeOf v < n) (σ : Nat → Ty) (rho : Nat → Value) :=
      (ih (sizeOf v) h).value v rfl σ rho
    have hc (c : Computation) (h : sizeOf c < n) (σ : Nat → Ty) (rho : Nat → Value) :=
      (ih (sizeOf c) h).computation c rfl σ rho
    constructor
    · intro v hn σ rho
      cases v
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := first | omega | simp)
          [map_record, replace_record, mapPaperValue, replaceTermValue,
           List.attach_map_val, List.attach_map, List.map_map, Function.comp_def,
           List.map_eq_map_iff, map_attach_map_iff, hv, hc,
           mapType_lift, mapType_liftN, mapType_shift]
      all_goals
        first
        | (intro label presence value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact hv value (by omega) σ rho)
        | (intro value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           exact hv value (by omega) σ rho)
    · intro c hn σ rho
      cases c
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := first | omega | simp)
          [mapPaperComputation, replaceTermComputation, map_record, replace_record,
           mapPaperValue, replaceTermValue,
           List.attach_map_val, List.attach_map, List.map_map, Function.comp_def,
           List.map_eq_map_iff, map_attach_map_iff, hv, hc,
           mapType_lift, mapType_liftN, mapType_shift]
      all_goals
        intro value hmem
        have hsmall := List.sizeOf_lt_of_mem hmem
        exact hv value (by omega) σ rho

theorem mapType_replaceValue (σ : Nat → Ty) (rho : Nat → Value) (v : Value) :
    mapPaperValue σ (replaceTermValue rho v) =
      replaceTermValue (fun n => mapPaperValue σ (rho n)) (mapPaperValue σ v) :=
  (typeReplaceAt_all (sizeOf v)).value v rfl σ rho

theorem mapType_replaceComputation (σ : Nat → Ty) (rho : Nat → Value) (c : Computation) :
    mapPaperComputation σ (replaceTermComputation rho c) =
      replaceTermComputation (fun n => mapPaperValue σ (rho n)) (mapPaperComputation σ c) :=
  (typeReplaceAt_all (sizeOf c)).computation c rfl σ rho

theorem compose_lift (outer inner : Nat → Value) :
    composeTermSubstitution (liftTermSubstitution outer) (liftTermSubstitution inner) =
      liftTermSubstitution (composeTermSubstitution outer inner) := by
  funext n
  cases n with
  | zero => simp [composeTermSubstitution, liftTermSubstitution, replaceTermValue]
  | succ n =>
    simp only [composeTermSubstitution, liftTermSubstitution, replace_renameValue,
      rename_replaceValue]

theorem compose_liftN (k : Nat) (outer inner : Nat → Value) :
    composeTermSubstitution (liftTermSubstitutionN k outer) (liftTermSubstitutionN k inner) =
      liftTermSubstitutionN k (composeTermSubstitution outer inner) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [liftTermSubstitutionN, compose_lift, ih]

theorem compose_shift (outer inner : Nat → Value) :
    composeTermSubstitution (shiftTermSubstitution outer) (shiftTermSubstitution inner) =
      shiftTermSubstitution (composeTermSubstitution outer inner) := by
  funext n
  exact (mapType_replaceValue shiftTypeSubstitution outer (inner n)).symm

private structure CompositionAt (n : Nat) : Prop where
  value : ∀ (v : Value), sizeOf v = n → ∀ (outer inner : Nat → Value),
    replaceTermValue outer (replaceTermValue inner v) =
      replaceTermValue (composeTermSubstitution outer inner) v
  computation : ∀ (c : Computation), sizeOf c = n → ∀ (outer inner : Nat → Value),
    replaceTermComputation outer (replaceTermComputation inner c) =
      replaceTermComputation (composeTermSubstitution outer inner) c

set_option linter.unusedSimpArgs false in
private theorem compositionAt_all (n : Nat) : CompositionAt n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hv (v : Value) (h : sizeOf v < n) (outer inner : Nat → Value) :=
      (ih (sizeOf v) h).value v rfl outer inner
    have hc (c : Computation) (h : sizeOf c < n) (outer inner : Nat → Value) :=
      (ih (sizeOf c) h).computation c rfl outer inner
    constructor
    · intro v hn outer inner
      cases v
      case «variable» index => simp only [replaceTermValue, composeTermSubstitution]
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := first | omega | simp)
          [replace_record, replaceTermValue,
           List.attach_map_val, List.attach_map, List.map_map, Function.comp_def,
           List.map_eq_map_iff, map_attach_map_iff, hv, hc,
           compose_lift, compose_liftN, compose_shift]
      all_goals
        first
        | (intro label presence value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact hv value (by omega) outer inner)
        | (intro value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           exact hv value (by omega) outer inner)
    · intro c hn outer inner
      cases c
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := first | omega | simp)
          [replaceTermComputation, replace_record, replaceTermValue,
           List.attach_map_val, List.attach_map, List.map_map, Function.comp_def,
           List.map_eq_map_iff, map_attach_map_iff, hv, hc,
           compose_lift, compose_liftN, compose_shift]
      all_goals
        intro value hmem
        have hsmall := List.sizeOf_lt_of_mem hmem
        exact hv value (by omega) outer inner

/-- Exact simultaneous-vector composition, including term, response, tuple,
and type binders. No typing hypothesis or equation law is supplied as input. -/
theorem replaceValue_comp (outer inner : Nat → Value) (v : Value) :
    replaceTermValue outer (replaceTermValue inner v) =
      replaceTermValue (composeTermSubstitution outer inner) v :=
  (compositionAt_all (sizeOf v)).value v rfl outer inner

theorem replaceComputation_comp (outer inner : Nat → Value) (c : Computation) :
    replaceTermComputation outer (replaceTermComputation inner c) =
      replaceTermComputation (composeTermSubstitution outer inner) c :=
  (compositionAt_all (sizeOf c)).computation c rfl outer inner

private theorem lift_variables : liftTermSubstitution Value.variable = Value.variable := by
  funext n; cases n <;> simp [liftTermSubstitution, renameTermValue]

private theorem liftN_variables (k : Nat) :
    liftTermSubstitutionN k Value.variable = Value.variable := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [liftTermSubstitutionN, ih, lift_variables]

private theorem shift_variables : shiftTermSubstitution Value.variable = Value.variable := by
  funext n; simp [shiftTermSubstitution, mapPaperValue]

private structure ReplaceIdentityAt (n : Nat) : Prop where
  value : ∀ (v : Value), sizeOf v = n → replaceTermValue Value.variable v = v
  computation : ∀ (c : Computation), sizeOf c = n → replaceTermComputation Value.variable c = c

set_option linter.unusedSimpArgs false in
private theorem replaceIdentityAt_all (n : Nat) : ReplaceIdentityAt n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hv (v : Value) (h : sizeOf v < n) := (ih (sizeOf v) h).value v rfl
    have hc (c : Computation) (h : sizeOf c < n) := (ih (sizeOf c) h).computation c rfl
    constructor
    · intro v hn
      cases v
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := first | omega | simp)
          [replace_record, replaceTermValue, replaceTermComputation,
           List.attach_map_val, map_eq_self_iff, hv, hc,
           lift_variables, liftN_variables, shift_variables]
      all_goals
        first
        | (intro label presence value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact hv value (by omega))
        | (intro value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           exact hv value (by omega))
    · intro c hn
      cases c
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := first | omega | simp)
          [replaceTermComputation, replace_record, replaceTermValue,
           List.attach_map_val, map_eq_self_iff, hv, hc,
           lift_variables, liftN_variables, shift_variables]
      all_goals
        intro value hmem
        have hsmall := List.sizeOf_lt_of_mem hmem
        exact hv value (by omega)

@[simp] theorem replaceValue_id (v : Value) : replaceTermValue Value.variable v = v :=
  (replaceIdentityAt_all (sizeOf v)).value v rfl

@[simp] theorem replaceComputation_id (c : Computation) :
    replaceTermComputation Value.variable c = c :=
  (replaceIdentityAt_all (sizeOf c)).computation c rfl

theorem compose_associative (outer middle inner : Nat → Value) :
    composeTermSubstitution outer (composeTermSubstitution middle inner) =
      composeTermSubstitution (composeTermSubstitution outer middle) inner := by
  funext n
  exact replaceValue_comp outer middle (inner n)

@[simp] theorem compose_identity_left (rho : Nat → Value) :
    composeTermSubstitution Value.variable rho = rho := by
  funext n; exact replaceValue_id (rho n)

@[simp] theorem compose_identity_right (rho : Nat → Value) :
    composeTermSubstitution rho Value.variable = rho := by
  funext n; simp [composeTermSubstitution, replaceTermValue]

/-- Fresh graph identities survive substitution of captured term values.
The same formal order and the same literal graph identities occur on both sides. -/
theorem compose_graphFormals (formals : List (Nat × Ty)) (outer inner : Nat → Value) :
    composeTermSubstitution outer (graphFormalReplacements formals inner) =
      graphFormalReplacements formals (composeTermSubstitution outer inner) := by
  induction formals with
  | nil => rfl
  | cons formal rest ih =>
    funext n
    cases n with
    | zero => simp [composeTermSubstitution, graphFormalReplacements, replaceTermValue]
    | succ n => exact congrFun ih n

theorem graphFormals_computation (formals : List (Nat × Ty))
    (outer inner : Nat → Value) (body : Computation) :
    replaceTermComputation outer
      (replaceTermComputation (graphFormalReplacements formals inner) body) =
    replaceTermComputation
      (graphFormalReplacements formals (composeTermSubstitution outer inner)) body := by
  rw [replaceComputation_comp, compose_graphFormals]

/-- Replacing the response binder after capture substitution does not substitute
inside the saved captures a second time or capture their free variables. -/
theorem response_after_environment (rho : Nat → Value) (response : Value) (body : Computation) :
    replaceTermComputation (PaperCoreStep.singleReplacement response)
      (replaceTermComputation (liftTermSubstitution rho) body) =
    replaceTermComputation (fun n => match n with | 0 => response | k + 1 => rho k) body := by
  rw [replaceComputation_comp]
  congr 1
  funext n
  cases n with
  | zero => simp [composeTermSubstitution, liftTermSubstitution,
      replaceTermValue, PaperCoreStep.singleReplacement]
  | succ n =>
    simp only [composeTermSubstitution, liftTermSubstitution, replace_renameValue,
      PaperCoreStep.singleReplacement]
    exact replaceValue_id (rho n)

/-- The checked public partial API composes on the original represented typing
domain. Its second support check is proved by typed substitution, not assumed. -/
theorem typed_value_composition {d g source middle target v a inner outer}
    (hv : PaperValueTyped d g source v a)
    (hi : TermSubstitutionTyped d g source middle inner)
    (ho : TermSubstitutionTyped d g middle target outer) :
    (termSubstituteValue inner v).bind (termSubstituteValue outer) =
        termSubstituteValue (composeTermSubstitution outer inner) v ∧
      PaperValueTyped d g target (replaceTermValue (composeTermSubstitution outer inner) v) a := by
  constructor
  · simp [termSubstituteValue, hv.termSupported, (hv.termReplace hi).termSupported,
      replaceValue_comp]
  · exact hv.termReplace (hi.compose ho)

theorem typed_computation_composition {d g source middle target c a inner outer}
    (hc : PaperComputationTyped d g source c a)
    (hi : TermSubstitutionTyped d g source middle inner)
    (ho : TermSubstitutionTyped d g middle target outer) :
    (termSubstituteComputation inner c).bind (termSubstituteComputation outer) =
        termSubstituteComputation (composeTermSubstitution outer inner) c ∧
      PaperComputationTyped d g target
        (replaceTermComputation (composeTermSubstitution outer inner) c) a := by
  constructor
  · simp [termSubstituteComputation, hc.termSupported, (hc.termReplace hi).termSupported,
      replaceComputation_comp]
  · exact hc.termReplace (hi.compose ho)

end YulangClosure.PaperTypes.PaperTermAlgebra

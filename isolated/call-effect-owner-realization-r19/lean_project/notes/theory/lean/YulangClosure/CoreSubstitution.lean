import YulangClosure.CoreSyntax

namespace YulangClosure.Original

abbrev Renaming := Space → Nat → Nat

def liftRenaming (bound : Space) (r : Renaming) : Renaming := fun s i =>
  if s = bound then match i with | 0 => 0 | n+1 => r s n + 1 else r s i

mutual
  def renameRaw (r : Renaming) : Raw → Raw
    | .var s i => .var s (r s i)
    | .atom a => .atom a
    | .node k xs => .node k (renameForest r xs)
    | .bind s t => .bind s (renameRaw (liftRenaming s r) t)
  def renameForest (r : Renaming) : Forest → Forest
    | .nil => .nil
    | .cons t ts => .cons (renameRaw r t) (renameForest r ts)
end

abbrev Substitution := Space → Nat → Raw

def liftSubstitution (bound : Space) (s : Substitution) : Substitution := fun k i =>
  if k = bound then
    match i with
    | 0 => .var k 0
    | n+1 => renameRaw (fun j x => if j = bound then x+1 else x) (s k n)
  else renameRaw (fun j x => if j = bound then x+1 else x) (s k i)

mutual
  def substituteRaw (s : Substitution) : Raw → Raw
    | .var k i => s k i
    | .atom a => .atom a
    | .node k xs => .node k (substituteForest s xs)
    | .bind k t => .bind k (substituteRaw (liftSubstitution k s) t)
  def substituteForest (s : Substitution) : Forest → Forest
    | .nil => .nil
    | .cons t ts => .cons (substituteRaw s t) (substituteForest s ts)
end

/-- Even a value inserted under a TYPE binder must shift its free type variables. -/
theorem binder_substitution (s : Substitution) (k : Space) (body : Raw) :
    substituteRaw s (.bind k body) =
      .bind k (substituteRaw (liftSubstitution k s) body) := rfl

theorem immutable_identity (s : Substitution) (k : IdentityKind) (n : Nat) :
    substituteRaw s (.atom (.identity k n)) = .atom (.identity k n) := rfl

theorem liftRenaming_identity (b : Space) :
    liftRenaming b (fun _ i => i) = (fun _ i => i) := by
  funext s i
  unfold liftRenaming
  split
  · cases i <;> rfl
  · rfl

theorem liftRenaming_composition (b : Space) (r t : Renaming) :
    liftRenaming b (fun s i => r s (t s i)) =
      (fun s i => liftRenaming b r s (liftRenaming b t s i)) := by
  funext s i
  by_cases h : s = b
  · subst s
    cases i <;> simp only [liftRenaming, ↓reduceIte]
  · simp only [liftRenaming, h, ↓reduceIte]

mutual
  theorem renameRaw_identity (t : Raw) : renameRaw (fun _ i => i) t = t := by
    cases t with
    | var => rfl
    | atom => rfl
    | node k xs => exact congrArg (Raw.node k) (renameForest_identity xs)
    | bind b t =>
      simp only [renameRaw, liftRenaming_identity, renameRaw_identity t]
  theorem renameForest_identity (ts : Forest) :
      renameForest (fun _ i => i) ts = ts := by
    cases ts with
    | nil => rfl
    | cons t ts =>
      simp only [renameForest, renameRaw_identity t, renameForest_identity ts]
end

mutual
  theorem renameRaw_composition (t : Raw) (r q : Renaming) :
      renameRaw r (renameRaw q t) = renameRaw (fun s i => r s (q s i)) t := by
    cases t with
    | var => rfl
    | atom => rfl
    | node k xs => exact congrArg (Raw.node k) (renameForest_composition xs r q)
    | bind b t =>
      simp only [renameRaw, renameRaw_composition t, liftRenaming_composition]
  theorem renameForest_composition (ts : Forest) (r q : Renaming) :
      renameForest r (renameForest q ts) = renameForest (fun s i => r s (q s i)) ts := by
    cases ts with
    | nil => rfl
    | cons t ts =>
      simp only [renameForest, renameRaw_composition t, renameForest_composition ts]
end

theorem liftSubstitution_identity (b : Space) :
    liftSubstitution b Raw.var = Raw.var := by
  funext s i
  by_cases h : s = b
  · subst s
    cases i <;> simp only [liftSubstitution, renameRaw, ↓reduceIte]
  · simp only [liftSubstitution, renameRaw, h, ↓reduceIte]

def shift (b : Space) : Renaming := fun s i => if s = b then i+1 else i

theorem lifted_shift (b : Space) (r : Renaming) :
    (fun s i => liftRenaming b r s (shift b s i)) =
      (fun s i => shift b s (r s i)) := by
  funext s i
  by_cases h : s = b <;> simp only [shift, liftRenaming, h, ↓reduceIte]

theorem lift_rename_substitution (b : Space) (r : Renaming) (s : Substitution) :
    (fun k i => renameRaw (liftRenaming b r) (liftSubstitution b s k i)) =
      liftSubstitution b (fun k i => renameRaw r (s k i)) := by
  funext k i
  by_cases h : k = b
  · subst k
    cases i with
    | zero => simp only [liftSubstitution, renameRaw, liftRenaming, ↓reduceIte]
    | succ i =>
      simp only [liftSubstitution, ↓reduceIte]
      change renameRaw (liftRenaming b r) (renameRaw (shift b) (s b i)) =
        renameRaw (shift b) (renameRaw r (s b i))
      rw [renameRaw_composition, renameRaw_composition, lifted_shift]
  · simp only [liftSubstitution, h, ↓reduceIte]
    change renameRaw (liftRenaming b r) (renameRaw (shift b) (s k i)) =
      renameRaw (shift b) (renameRaw r (s k i))
    rw [renameRaw_composition, renameRaw_composition, lifted_shift]

theorem lift_substitution_rename (b : Space) (s : Substitution) (r : Renaming) :
    (fun k i => liftSubstitution b s k (liftRenaming b r k i)) =
      liftSubstitution b (fun k i => s k (r k i)) := by
  funext k i
  by_cases h : k = b
  · subst k
    cases i <;> simp only [liftSubstitution, liftRenaming, ↓reduceIte]
  · simp only [liftSubstitution, liftRenaming, h, ↓reduceIte]

mutual
  theorem rename_substitute (t : Raw) (r : Renaming) (s : Substitution) :
      renameRaw r (substituteRaw s t) =
        substituteRaw (fun k i => renameRaw r (s k i)) t := by
    cases t with
    | var => rfl
    | atom => rfl
    | node k xs => exact congrArg (Raw.node k) (rename_substitute_forest xs r s)
    | bind b t =>
      simp only [substituteRaw, renameRaw, rename_substitute t, lift_rename_substitution]
  theorem rename_substitute_forest (ts : Forest) (r : Renaming) (s : Substitution) :
      renameForest r (substituteForest s ts) =
        substituteForest (fun k i => renameRaw r (s k i)) ts := by
    cases ts with
    | nil => rfl
    | cons t ts =>
      simp only [substituteForest, renameForest, rename_substitute t, rename_substitute_forest ts]
end

mutual
  theorem substitute_rename (t : Raw) (s : Substitution) (r : Renaming) :
      substituteRaw s (renameRaw r t) =
        substituteRaw (fun k i => s k (r k i)) t := by
    cases t with
    | var => rfl
    | atom => rfl
    | node k xs => exact congrArg (Raw.node k) (substitute_rename_forest xs s r)
    | bind b t =>
      simp only [substituteRaw, renameRaw, substitute_rename t, lift_substitution_rename]
  theorem substitute_rename_forest (ts : Forest) (s : Substitution) (r : Renaming) :
      substituteForest s (renameForest r ts) =
        substituteForest (fun k i => s k (r k i)) ts := by
    cases ts with
    | nil => rfl
    | cons t ts =>
      simp only [substituteForest, renameForest, substitute_rename t, substitute_rename_forest ts]
end

theorem substitute_shift (t : Raw) (b : Space) (s : Substitution) :
    substituteRaw (liftSubstitution b s) (renameRaw (shift b) t) =
      renameRaw (shift b) (substituteRaw s t) := by
  rw [substitute_rename, rename_substitute]
  apply congrArg (fun σ => substituteRaw σ t)
  funext k i
  by_cases h : k = b <;> simp only [shift, liftSubstitution, h, ↓reduceIte] <;> rfl

theorem lift_substitution_composition (b : Space) (s q : Substitution) :
    (fun k i => substituteRaw (liftSubstitution b s) (liftSubstitution b q k i)) =
      liftSubstitution b (fun k i => substituteRaw s (q k i)) := by
  funext k i
  by_cases h : k = b
  · subst k
    cases i with
    | zero => simp only [liftSubstitution, substituteRaw, ↓reduceIte]
    | succ i =>
      simp only [liftSubstitution, ↓reduceIte]
      exact substitute_shift (q b i) b s
  · simp only [liftSubstitution, h, ↓reduceIte]
    exact substitute_shift (q k i) b s

mutual
  /-- Simultaneous substitution composes over the entire raw vocabulary,
  including nested value/type/evidence/control binders and unchanged atoms. -/
  theorem substituteRaw_composition (t : Raw) (s q : Substitution) :
      substituteRaw s (substituteRaw q t) =
        substituteRaw (fun k i => substituteRaw s (q k i)) t := by
    cases t with
    | var => rfl
    | atom => rfl
    | node k xs => exact congrArg (Raw.node k) (substituteForest_composition xs s q)
    | bind b t =>
      simp only [substituteRaw, substituteRaw_composition t, lift_substitution_composition]
  theorem substituteForest_composition (ts : Forest) (s q : Substitution) :
      substituteForest s (substituteForest q ts) =
        substituteForest (fun k i => substituteRaw s (q k i)) ts := by
    cases ts with
    | nil => rfl
    | cons t ts =>
      simp only [substituteForest, substituteRaw_composition t, substituteForest_composition ts]
end

mutual
  /-- Applies to every raw constructor, including all four binder namespaces.
  This is a syntax algebra theorem, not the missing full typing theorem. -/
  theorem substituteRaw_identity (t : Raw) : substituteRaw Raw.var t = t := by
    cases t with
    | var => rfl
    | atom => rfl
    | node k xs => exact congrArg (Raw.node k) (substituteForest_identity xs)
    | bind b t =>
      simp only [substituteRaw, liftSubstitution_identity, substituteRaw_identity t]
  theorem substituteForest_identity (ts : Forest) : substituteForest Raw.var ts = ts := by
    cases ts with
    | nil => rfl
    | cons t ts =>
      simp only [substituteForest, substituteRaw_identity t, substituteForest_identity ts]
end

/-- The executable full traversal above is not yet a full typed substitution theorem. -/
def up (r : Nat → Nat) : Nat → Nat | 0 => 0 | n+1 => r n + 1

mutual
  def renameVal (r : Nat → Nat) : Val → Val
    | .var i => .var (r i)
    | .unit => .unit
    | .bool v => .bool v
    | .int v => .int v
    | .floatBits v => .floatBits v
    | .string v => .string v
    | .bytes v => .bytes v
    | .path v => .path v
    | .char v => .char v
    | .delay m => .delay (renameComp r m)
    | .inLeft v => .inLeft (renameVal r v)
    | .inRight v => .inRight (renameVal r v)
    | .both v => .both (renameVal r v)
    | .top v => .top (renameVal r v)
  def renameComp (r : Nat → Nat) : Comp → Comp
    | .ret v => .ret (renameVal r v)
    | .force v => .force (renameVal r v)
    | .bind m n => .bind (renameComp r m) (renameComp (up r) n)
    | .unionCase v l body => .unionCase (renameVal r v) (renameComp (up r) l) (renameComp (up r) body)
    | .chooseLeft v => .chooseLeft (renameVal r v)
    | .chooseRight v => .chooseRight (renameVal r v)
    | .absurd v => .absurd (renameVal r v)
end

def lift (s : Nat → Val) : Nat → Val
  | 0 => .var 0
  | n+1 => renameVal Nat.succ (s n)

mutual
  def substVal (s : Nat → Val) : Val → Val
    | .var i => s i
    | .unit => .unit
    | .bool v => .bool v
    | .int v => .int v
    | .floatBits v => .floatBits v
    | .string v => .string v
    | .bytes v => .bytes v
    | .path v => .path v
    | .char v => .char v
    | .delay m => .delay (substComp s m)
    | .inLeft v => .inLeft (substVal s v)
    | .inRight v => .inRight (substVal s v)
    | .both v => .both (substVal s v)
    | .top v => .top (substVal s v)
  def substComp (s : Nat → Val) : Comp → Comp
    | .ret v => .ret (substVal s v)
    | .force v => .force (substVal s v)
    | .bind m n => .bind (substComp s m) (substComp (lift s) n)
    | .unionCase v l r => .unionCase (substVal s v) (substComp (lift s) l) (substComp (lift s) r)
    | .chooseLeft v => .chooseLeft (substVal s v)
    | .chooseRight v => .chooseRight (substVal s v)
    | .absurd v => .absurd (substVal s v)
end

mutual
  theorem renameVal_typed (h : ValTyped env v a)
      (hr : ∀ i, target (r i) = env i) : ValTyped target (renameVal r v) a := by
    cases h with
    | var he => exact .var ((hr _).trans he)
    | unit => exact .unit
    | bool => exact .bool
    | int => exact .int
    | floatBits => exact .floatBits
    | string => exact .string
    | bytes => exact .bytes
    | path => exact .path
    | char => exact .char
    | delay hm => exact .delay (renameComp_typed hm hr)
    | inLeft hv => exact .inLeft (renameVal_typed hv hr)
    | inRight hv => exact .inRight (renameVal_typed hv hr)
    | top hv => exact .top (renameVal_typed hv hr)
    | both ha hb => exact .both (renameVal_typed ha hr) (renameVal_typed hb hr)
  theorem renameComp_typed (h : CompTyped env m a)
      (hr : ∀ i, target (r i) = env i) : CompTyped target (renameComp r m) a := by
    cases h with
    | ret hv => exact .ret (renameVal_typed hv hr)
    | force hv => exact .force (renameVal_typed hv hr)
    | chooseLeft hv => exact .chooseLeft (renameVal_typed hv hr)
    | chooseRight hv => exact .chooseRight (renameVal_typed hv hr)
    | absurd hv => exact .absurd (renameVal_typed hv hr)
    | unionCase hv hl hrbody =>
      apply CompTyped.unionCase (renameVal_typed hv hr)
      · apply renameComp_typed hl
        intro i
        cases i <;> simp [up, extend, hr]
      · apply renameComp_typed hrbody
        intro i
        cases i <;> simp [up, extend, hr]
    | bind hm hn =>
      apply CompTyped.bind (renameComp_typed hm hr)
      apply renameComp_typed hn
      intro i
      cases i <;> simp [up, extend, hr]
end

mutual
  theorem substVal_typed (h : ValTyped env v a)
      (hs : ∀ i a, env i = some a → ValTyped target (s i) a) :
      ValTyped target (substVal s v) a := by
    cases h with
    | var he => exact hs _ _ he
    | unit => exact .unit
    | bool => exact .bool
    | int => exact .int
    | floatBits => exact .floatBits
    | string => exact .string
    | bytes => exact .bytes
    | path => exact .path
    | char => exact .char
    | delay hm => exact .delay (substComp_typed hm hs)
    | inLeft hv => exact .inLeft (substVal_typed hv hs)
    | inRight hv => exact .inRight (substVal_typed hv hs)
    | top hv => exact .top (substVal_typed hv hs)
    | both ha hb => exact .both (substVal_typed ha hs) (substVal_typed hb hs)
  theorem substComp_typed (h : CompTyped env m a)
      (hs : ∀ i a, env i = some a → ValTyped target (s i) a) :
      CompTyped target (substComp s m) a := by
    cases h with
    | ret hv => exact .ret (substVal_typed hv hs)
    | force hv => exact .force (substVal_typed hv hs)
    | chooseLeft hv => exact .chooseLeft (substVal_typed hv hs)
    | chooseRight hv => exact .chooseRight (substVal_typed hv hs)
    | absurd hv => exact .absurd (substVal_typed hv hs)
    | unionCase hv hl hrbody =>
      apply CompTyped.unionCase (substVal_typed hv hs)
      · apply substComp_typed hl
        intro i a he
        cases i with
        | zero =>
          simp only [extend, Option.some.injEq] at he
          subst a
          exact .var rfl
        | succ i => exact renameVal_typed (hs i a he) (fun _ => rfl)
      · apply substComp_typed hrbody
        intro i a he
        cases i with
        | zero =>
          simp only [extend, Option.some.injEq] at he
          subst a
          exact .var rfl
        | succ i => exact renameVal_typed (hs i a he) (fun _ => rfl)
    | bind hm hn =>
      apply CompTyped.bind (substComp_typed hm hs)
      apply substComp_typed hn
      intro i a he
      cases i with
      | zero =>
        simp only [extend, Option.some.injEq] at he
        subst a
        exact .var rfl
      | succ i => exact renameVal_typed (hs i a he) (fun _ => rfl)
end

def single (v : Val) : Nat → Val | 0 => v | n+1 => .var n

theorem substitute_top (hn : CompTyped (extend env a) n b) (hv : ValTyped env v a) :
    CompTyped env (substComp (single v) n) b := by
  apply substComp_typed hn
  intro i a he
  cases i with
  | zero =>
    simp only [extend, Option.some.injEq] at he
    subst a
    exact hv
  | succ i => exact .var he

mutual
  theorem renameVal_raw (v : Val) (r : Nat → Nat) (q : Renaming)
      (hq : ∀ i, q .value i = r i) :
      renameRaw q v.raw = (renameVal r v).raw := by
    cases v with
    | var i => simp only [Val.raw, renameVal, renameRaw, hq]
    | unit => rfl
    | bool v => rfl
    | int v => rfl
    | floatBits v => rfl
    | string v => rfl
    | bytes v => rfl
    | path v => rfl
    | char v => rfl
    | inLeft v =>
      simp only [Val.raw, renameVal, rawIn, Forest.two, renameRaw, renameForest,
        renameVal_raw v r q hq]
    | inRight v =>
      simp only [Val.raw, renameVal, rawIn, Forest.two, renameRaw, renameForest,
        renameVal_raw v r q hq]
    | both v =>
      simp only [Val.raw, renameVal, rawProofBoth, Forest.one, renameRaw, renameForest,
        renameVal_raw v r q hq]
    | top v =>
      simp only [Val.raw, renameVal, rawTop, Forest.one, renameRaw, renameForest,
        renameVal_raw v r q hq]
    | delay m =>
      simpa only [Val.raw, rawDelay, Forest.one, renameRaw, renameForest, renameVal]
        using congrArg (fun x => rawDelay x) (renameComp_raw m r q hq)
  theorem renameComp_raw (m : Comp) (r : Nat → Nat) (q : Renaming)
      (hq : ∀ i, q .value i = r i) :
      renameRaw q m.raw = (renameComp r m).raw := by
    cases m with
    | ret v =>
      simpa only [Comp.raw, rawRet, Forest.one, renameRaw, renameForest, renameComp]
        using congrArg rawRet (renameVal_raw v r q hq)
    | force v =>
      simpa only [Comp.raw, rawForce, Forest.one, renameRaw, renameForest, renameComp]
        using congrArg rawForce (renameVal_raw v r q hq)
    | chooseLeft v =>
      simp only [Comp.raw, renameComp, rawChoose, Forest.two, renameRaw, renameForest,
        renameVal_raw v r q hq]
    | chooseRight v =>
      simp only [Comp.raw, renameComp, rawChoose, Forest.two, renameRaw, renameForest,
        renameVal_raw v r q hq]
    | absurd v =>
      simp only [Comp.raw, renameComp, rawAbsurd, Forest.one, renameRaw, renameForest,
        renameVal_raw v r q hq]
    | unionCase v l rbody =>
      have hu : ∀ i, liftRenaming .value q .value i = up r i := by
        intro i
        cases i <;> simp only [liftRenaming, up, ↓reduceIte, hq]
      simp only [Comp.raw, renameComp, rawUnionCase, Forest.two, renameRaw, renameForest,
        renameVal_raw v r q hq, renameComp_raw l (up r) (liftRenaming .value q) hu,
        renameComp_raw rbody (up r) (liftRenaming .value q) hu]
    | bind m n =>
      have hu : ∀ i, liftRenaming .value q .value i = up r i := by
        intro i
        cases i <;> simp only [liftRenaming, up, ↓reduceIte, hq]
      simp only [Comp.raw, rawLet, Forest.two, renameRaw, renameForest, renameComp,
        renameComp_raw m r q hq, renameComp_raw n (up r) (liftRenaming .value q) hu]
end

mutual
  /-- The typed-fragment substitution really is the full raw traversal on its
  embedding. This supplies the executable substitution used by raw beta rules. -/
  theorem substVal_raw (v : Val) (s : Nat → Val) (q : Substitution)
      (hq : ∀ i, q .value i = (s i).raw) :
      substituteRaw q v.raw = (substVal s v).raw := by
    cases v with
    | var i => exact hq i
    | unit => rfl
    | bool v => rfl
    | int v => rfl
    | floatBits v => rfl
    | string v => rfl
    | bytes v => rfl
    | path v => rfl
    | char v => rfl
    | inLeft v =>
      simp only [Val.raw, substVal, rawIn, Forest.two, substituteRaw, substituteForest,
        substVal_raw v s q hq]
    | inRight v =>
      simp only [Val.raw, substVal, rawIn, Forest.two, substituteRaw, substituteForest,
        substVal_raw v s q hq]
    | both v =>
      simp only [Val.raw, substVal, rawProofBoth, Forest.one, substituteRaw, substituteForest,
        substVal_raw v s q hq]
    | top v =>
      simp only [Val.raw, substVal, rawTop, Forest.one, substituteRaw, substituteForest,
        substVal_raw v s q hq]
    | delay m =>
      simpa only [Val.raw, rawDelay, Forest.one, substituteRaw, substituteForest, substVal]
        using congrArg rawDelay (substComp_raw m s q hq)
  theorem substComp_raw (m : Comp) (s : Nat → Val) (q : Substitution)
      (hq : ∀ i, q .value i = (s i).raw) :
      substituteRaw q m.raw = (substComp s m).raw := by
    cases m with
    | ret v =>
      simpa only [Comp.raw, rawRet, Forest.one, substituteRaw, substituteForest, substComp]
        using congrArg rawRet (substVal_raw v s q hq)
    | force v =>
      simpa only [Comp.raw, rawForce, Forest.one, substituteRaw, substituteForest, substComp]
        using congrArg rawForce (substVal_raw v s q hq)
    | chooseLeft v =>
      simp only [Comp.raw, substComp, rawChoose, Forest.two, substituteRaw, substituteForest,
        substVal_raw v s q hq]
    | chooseRight v =>
      simp only [Comp.raw, substComp, rawChoose, Forest.two, substituteRaw, substituteForest,
        substVal_raw v s q hq]
    | absurd v =>
      simp only [Comp.raw, substComp, rawAbsurd, Forest.one, substituteRaw, substituteForest,
        substVal_raw v s q hq]
    | unionCase v l rbody =>
      have hu : ∀ i, liftSubstitution .value q .value i = (lift s i).raw := by
        intro i
        cases i with
        | zero => rfl
        | succ i =>
          simp only [liftSubstitution, ↓reduceIte, hq, lift]
          exact renameVal_raw (s i) Nat.succ _ (fun _ => rfl)
      simp only [Comp.raw, substComp, rawUnionCase, Forest.two, substituteRaw, substituteForest,
        substVal_raw v s q hq, substComp_raw l (lift s) (liftSubstitution .value q) hu,
        substComp_raw rbody (lift s) (liftSubstitution .value q) hu]
    | bind m n =>
      have hu : ∀ i, liftSubstitution .value q .value i = (lift s i).raw := by
        intro i
        cases i with
        | zero => rfl
        | succ i =>
          simp only [liftSubstitution, ↓reduceIte, hq, lift]
          exact renameVal_raw (s i) Nat.succ _ (fun _ => rfl)
      simp only [Comp.raw, rawLet, Forest.two, substituteRaw, substituteForest, substComp,
        substComp_raw m s q hq, substComp_raw n (lift s) (liftSubstitution .value q) hu]
end

def rawSingle (v : Raw) : Substitution := fun space i =>
  if space = .value then match i with | 0 => v | n+1 => .var .value n
  else .var space i

theorem single_raw (m : Comp) (v : Val) :
    substituteRaw (rawSingle v.raw) m.raw = (substComp (single v) m).raw := by
  apply substComp_raw
  intro i
  cases i <;> rfl

end YulangClosure.Original

namespace YulangClosure.TypedCall

open YulangClosure.Original

/-- Standard de Bruijn lifting for the finite Call fragment. -/
def upCall (r : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => r n + 1

mutual
  def renameCallValue (r : Nat → Nat) : Value → Value
    | .var i => .var (r i)
    | .original value => .original value
    | .delay body => .delay (renameCallComp r body)
    | .view value occurrence => .view (renameCallValue r value) occurrence
  def renameCallComp (r : Nat → Nat) : Comp → Comp
    | .original body => .original body
    | .ret value => .ret (renameCallValue r value)
    | .bind first body => .bind (renameCallComp r first)
        (renameCallComp (upCall r) body)
    | .force value => .force (renameCallValue r value)
    | .scope owner body => .scope owner (renameCallComp r body)
    | .expose effectView resultView body =>
        .expose effectView resultView (renameCallComp r body)
    | .request opInstance payload continuation =>
        .request opInstance (renameCallValue r payload)
          (renameCallComp (upCall r) continuation)
    | .fail reason => .fail reason
end

mutual
  theorem renameCallValue_typed {env target : Original.Context} {r : Nat → Nat}
      {value : Value} {a : Original.Ty} (h : ValueTyped env value a)
      (hr : ∀ i, target (r i) = env i) :
      ValueTyped target (renameCallValue r value) a := by
    cases h with
    | var he => exact .var ((hr _).trans he)
    | original hv => exact .original hv
    | delay hc => exact .delay (renameCallComp_typed hc hr)
    | view hv => exact .view (renameCallValue_typed hv hr)
  theorem renameCallComp_typed {env target : Original.Context} {r : Nat → Nat}
      {body : Comp} {a : Original.Ty} (h : CompTyped env body a)
      (hr : ∀ i, target (r i) = env i) :
      CompTyped target (renameCallComp r body) a := by
    cases h with
    | original hc => exact .original hc
    | ret hv => exact .ret (renameCallValue_typed hv hr)
    | bind hm hn =>
        exact .bind (renameCallComp_typed hm hr) (renameCallComp_typed hn (by
          intro i
          cases i <;> simp [upCall, Original.extend, hr]))
    | force hv => exact .force (renameCallValue_typed hv hr)
    | scope hc => exact .scope (renameCallComp_typed hc hr)
    | expose effectView resultView hc =>
        exact .expose effectView resultView (renameCallComp_typed hc hr)
    | request hp hk =>
        exact .request (renameCallValue_typed hp hr)
          (renameCallComp_typed hk (by
            intro i
            cases i <;> simp [upCall, Original.extend, hr]))
    | fail => exact .fail
end

/-- Lift a value substitution through a Call-local value binder. -/
def liftCallSubstitution (s : Nat → Value) : Nat → Value
  | 0 => .var 0
  | n + 1 => renameCallValue Nat.succ (s n)

mutual
  def substituteCallValue (s : Nat → Value) : Value → Value
    | .var i => s i
    | .original value => .original value
    | .delay body => .delay (substituteCallComp s body)
    | .view value occurrence => .view (substituteCallValue s value) occurrence
  def substituteCallComp (s : Nat → Value) : Comp → Comp
    | .original body => .original body
    | .ret value => .ret (substituteCallValue s value)
    | .bind first body => .bind (substituteCallComp s first)
        (substituteCallComp (liftCallSubstitution s) body)
    | .force value => .force (substituteCallValue s value)
    | .scope owner body => .scope owner (substituteCallComp s body)
    | .expose effectView resultView body =>
        .expose effectView resultView (substituteCallComp s body)
    | .request opInstance payload continuation =>
        .request opInstance (substituteCallValue s payload)
          (substituteCallComp (liftCallSubstitution s) continuation)
    | .fail reason => .fail reason
end

private theorem liftedCallSubstitution_typed
    {env target : Original.Context} {s : Nat → Value} {a : Original.Ty}
    (hs : ∀ i ty, env i = some ty → ValueTyped target (s i) ty) :
    ∀ i ty, (Original.extend env a) i = some ty →
      ValueTyped (Original.extend target a) (liftCallSubstitution s i) ty := by
  intro i ty hi
  cases i with
  | zero =>
      simp only [Original.extend, Option.some.injEq] at hi
      subst ty
      exact .var rfl
  | succ i =>
      have he : env i = some ty := hi
      exact renameCallValue_typed (hs i ty he) (by intro j; rfl)

mutual
  theorem substituteCallValue_typed {env target : Original.Context} {s : Nat → Value}
      {value : Value} {a : Original.Ty} (h : ValueTyped env value a)
      (hs : ∀ i ty, env i = some ty → ValueTyped target (s i) ty) :
      ValueTyped target (substituteCallValue s value) a := by
    cases h with
    | var he => exact hs _ _ he
    | original hv => exact .original hv
    | delay hc => exact .delay (substituteCallComp_typed hc hs)
    | view hv => exact .view (substituteCallValue_typed hv hs)
  theorem substituteCallComp_typed {env target : Original.Context} {s : Nat → Value}
      {body : Comp} {a : Original.Ty} (h : CompTyped env body a)
      (hs : ∀ i ty, env i = some ty → ValueTyped target (s i) ty) :
      CompTyped target (substituteCallComp s body) a := by
    cases h with
    | original hc => exact .original hc
    | ret hv => exact .ret (substituteCallValue_typed hv hs)
    | bind hm hn =>
        exact .bind (substituteCallComp_typed hm hs)
          (substituteCallComp_typed (s := liftCallSubstitution s) hn
            (liftedCallSubstitution_typed hs))
    | force hv => exact .force (substituteCallValue_typed hv hs)
    | scope hc => exact .scope (substituteCallComp_typed hc hs)
    | expose effectView resultView hc =>
        exact .expose effectView resultView (substituteCallComp_typed hc hs)
    | request hp hk =>
        exact .request (substituteCallValue_typed hp hs)
          (substituteCallComp_typed (s := liftCallSubstitution s) hk
            (liftedCallSubstitution_typed hs))
    | fail => exact .fail
end

/-- Adapter and Computation-entry substitutions share the actual Call syntax
traversal above, whose closed Original subterms are retained verbatim. -/
def executeAdapterBody (adapter : Adapter) (value : Value) : Comp :=
  substituteCallComp (fun i => if i = 0 then value else .var (i - 1)) adapter.body

theorem executeAdapterBody_typed (adapter : Adapter) (value : Value)
    (hv : ValueTyped Original.emptyContext value adapter.input) :
    CompTyped Original.emptyContext (executeAdapterBody adapter value) adapter.output := by
  apply substituteCallComp_typed adapter.typed
  intro i ty hi
  cases i with
  | zero => simp only [Original.extend, Option.some.injEq] at hi; subst ty; exact hv
  | succ i => exact .var hi

/-- Computation entry substitutes the received thunk carrier itself. -/
def computationEntryBody (body : Comp) (carrier : Value) : Comp :=
  substituteCallComp (fun i => if i = 0 then carrier else .var (i - 1)) body

theorem computationEntryBody_typed {a b : Original.Ty} {body : Comp}
    (bodyTyped : CompTyped
      (Original.extend Original.emptyContext (.thunk a)) body b)
    {carrier : Value}
    (carrierTyped : ValueTyped Original.emptyContext carrier (.thunk a)) :
    CompTyped Original.emptyContext (computationEntryBody body carrier) b := by
  apply substituteCallComp_typed bodyTyped
  intro i ty hi
  cases i with
  | zero => simp only [Original.extend, Option.some.injEq] at hi; subst ty; exact carrierTyped
  | succ i => exact .var hi

end YulangClosure.TypedCall

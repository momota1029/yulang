import Yulang.CommonRoleSettledSyntax

/-! Centreless normalization of finite endpoint descriptions. No interval
consistency or candidate applicability is asserted by this syntactic pass. -/
namespace Yulang.CommonRoleOpenNormalization
open CommonRoleSettledSyntax

inductive Normal where
  | interval (lower upper : Ty)
  | wrap (constructor : Constructor) (payload : Normal)
  deriving DecidableEq, Repr

def Normal.lower : Normal → Ty
  | .interval lo _ => lo
  | .wrap c payload => .wrap c payload.lower

def Normal.upper : Normal → Ty
  | .interval _ up => up
  | .wrap c payload => .wrap c payload.upper

/-- True precisely when a common outer wrapper can be exposed. -/
def SameWrap : Ty → Ty → Prop
  | .wrap c _, .wrap d _ => c = d
  | _, _ => False

def normalize : Ty → Ty → Normal
  | .wrap c lo, .wrap d up =>
      if c = d then .wrap c (normalize lo up) else .interval (.wrap c lo) (.wrap d up)
  | lo, up => .interval lo up

inductive Normalizes : Ty → Ty → Normal → Prop where
  | interval : ¬ SameWrap lo up → Normalizes lo up (.interval lo up)
  | wrap : Normalizes lo up result →
      Normalizes (.wrap c lo) (.wrap c up) (.wrap c result)

@[simp] theorem normalize_same (c : Constructor) (lo up : Ty) :
    normalize (.wrap c lo) (.wrap c up) = .wrap c (normalize lo up) := by
  simp [normalize]

theorem normalize_different (c d : Constructor) (lo up : Ty) (different : c ≠ d) :
    normalize (.wrap c lo) (.wrap d up) = .interval (.wrap c lo) (.wrap d up) := by
  simp [normalize, different]

theorem normalize_interval (lo up : Ty) (different : ¬ SameWrap lo up) :
    normalize lo up = .interval lo up := by
  cases lo <;> cases up <;> simp_all [SameWrap, normalize]

theorem normalize_sound (lo up : Ty) : Normalizes lo up (normalize lo up) := by
  induction lo generalizing up with
  | wrap c lo ih =>
      cases up with
      | wrap d up =>
          by_cases same : c = d
          · subst d
            simpa only [normalize_same] using Normalizes.wrap (c := c) (ih up)
          · simpa only [normalize_different c d lo up same] using
              Normalizes.interval (lo := .wrap c lo) (up := .wrap d up) same
      | unknown | atom | variantLoop | recordLoop => exact .interval (by simp [SameWrap])
  | unknown | atom | variantLoop | recordLoop => exact .interval (by simp [SameWrap])

theorem normalize_complete (derivation : Normalizes lo up result) : normalize lo up = result := by
  induction derivation with
  | interval different => exact normalize_interval _ _ different
  | wrap _ ih => simp only [normalize_same, ih]

theorem normalize_exact (lo up : Ty) (result : Normal) :
    normalize lo up = result ↔ Normalizes lo up result :=
  ⟨fun equal => equal ▸ normalize_sound lo up, normalize_complete⟩

theorem endpoints_preserved (derivation : Normalizes lo up result) :
    result.lower = lo ∧ result.upper = up := by
  induction derivation with
  | interval => exact ⟨rfl, rfl⟩
  | wrap _ ih => simp only [Normal.lower, Normal.upper, ih.1, ih.2, and_self]

@[simp] theorem normalize_lower (lo up : Ty) : (normalize lo up).lower = lo :=
  (endpoints_preserved (normalize_sound lo up)).1

@[simp] theorem normalize_upper (lo up : Ty) : (normalize lo up).upper = up :=
  (endpoints_preserved (normalize_sound lo up)).2

/-- Any finite constructor wrapPrefix, without a fixed depth bound. -/
def wrapPrefix (constructors : List Constructor) (payload : Ty) : Ty :=
  constructors.foldr Ty.wrap payload

def normalPrefix (constructors : List Constructor) (payload : Normal) : Normal :=
  constructors.foldr Normal.wrap payload

theorem normalize_prefix (constructors : List Constructor) (lo up : Ty) :
    normalize (wrapPrefix constructors lo) (wrapPrefix constructors up) =
      normalPrefix constructors (normalize lo up) := by
  induction constructors with
  | nil => rfl
  | cons c rest ih =>
      simpa only [wrapPrefix, normalPrefix, List.foldr_cons, normalize_same] using
        (congrArg (Normal.wrap c) ih)

end Yulang.CommonRoleOpenNormalization

import Yulang.CommonSyntax
import Yulang.RowFlowSchemes
import Yulang.SourcePrincipalInference

/-!
# A concrete regular presence carrier and its demand order

Rows are sets of named signed occurrences. The finite list of integer weights
retains every boundary coordinate of an occurrence; the row itself may be
infinite. M1 uses only empty, union and inclusion. No row is defaulted to empty.

Environments assign finite or regular common syntax to demand names. Finite
assignments retain the entire finite type; regular assignments use the same
constructor approximation as the producer. All approximations and all negative
ranks are quantified. The same environment enters negative arrow observations.
No bounded probing or successful solver is a premise.
-/

namespace Yulang.Common

abbrev Occurrence := Nat × List Int
abbrev Row := Occurrence → Prop

def rowEmpty : Row := fun _ => False
def rowJoin (first last : Row) : Row := fun occurrence => first occurrence ∨ last occurrence
def rowLe (first last : Row) : Prop := ∀ occurrence, first occurrence → last occurrence

theorem rowLe_refl (row : Row) : rowLe row row := fun _ member => member
theorem rowLe_trans {first middle last : Row}
    (before : rowLe first middle) (after : rowLe middle last) : rowLe first last :=
  fun occurrence member => after occurrence (before occurrence member)
theorem rowLe_antisymm {first last : Row} (forward : rowLe first last) (backward : rowLe last first) :
    first = last := funext fun occurrence => propext ⟨forward occurrence, backward occurrence⟩
theorem rowEmpty_le (row : Row) : rowLe rowEmpty row := fun _ impossible => False.elim impossible
theorem rowJoin_le_iff (first last upper : Row) :
    rowLe (rowJoin first last) upper ↔ rowLe first upper ∧ rowLe last upper :=
  ⟨fun below => ⟨fun occurrence member => below occurrence (Or.inl member),
      fun occurrence member => below occurrence (Or.inr member)⟩,
    fun below occurrence member => member.elim (below.1 occurrence) (below.2 occurrence)⟩

def rowAlgebra : RowFlowSchemes.Algebra Row where
  empty := rowEmpty
  join := rowJoin
  le := rowLe
  refl := rowLe_refl
  trans := rowLe_trans
  empty_le := rowEmpty_le
  join_le_iff := rowJoin_le_iff

abbrev Ty := CommonSyntax.Ty Row
abbrev Demand := CommonFinite.Demand Row
abbrev Observation := CommonFinite.Observation Row

def observeTy (depth : Nat) (type : Ty) : CommonFinite.Ty Row :=
  type.evalAt depth (CommonSyntax.observe (CommonSyntax.graph Row) depth)

/-- Both alternatives contain actual type syntax, never a list of tests or an
arbitrary predicate on types. A demand name may refer to any regular graph. -/
inductive Parameter where
  | finite : CommonFinite.Ty Row → Parameter
  | regular : Ty → Parameter

def Parameter.atDepth (depth : Nat) : Parameter → CommonFinite.Ty Row
  | .finite type => type
  | .regular type => observeTy depth type

structure Environment where
  types : Nat → Parameter
  roles : Nat → List ProducerContextual.Head

def Environment.atDepth (depth : Nat) (environment : Environment) : CommonFinite.Environment Row :=
  ⟨fun name => (environment.types name).atDepth depth, environment.roles⟩

def Environment.ofFinite (environment : CommonFinite.Environment Row) : Environment :=
  ⟨fun name => .finite (environment.types name), environment.roles⟩

def Environment.ofRegular (types : Nat → Ty) (roles : Nat → List ProducerContextual.Head) : Environment :=
  ⟨fun name => .regular (types name), roles⟩

@[simp] theorem Environment.atDepth_ofFinite (depth : Nat) (environment : CommonFinite.Environment Row) :
    (Environment.ofFinite environment).atDepth depth = environment := by
  cases environment
  rfl

def AcceptAt (depth rank : Nat) (env : Environment) (type : Ty) (demand : Demand) : Prop :=
  CommonFinite.AcceptAt rowLe rank (env.atDepth depth) (observeTy depth type) demand

theorem acceptAt_regular_environment (depth rank : Nat) (parameters : Nat → Ty)
    (roles : Nat → List ProducerContextual.Head) (type : Ty) (demand : Demand) :
    AcceptAt depth rank (Environment.ofRegular parameters roles) type demand ↔
      CommonFinite.AcceptAt rowLe rank
        ⟨fun name => observeTy depth (parameters name), roles⟩ (observeTy depth type) demand := Iff.rfl

def Subtype (source target : Ty) : Prop :=
  ∀ depth, CommonFinite.ProducerLe rowLe (observeTy depth source) (observeTy depth target)

def Equivalent (source target : Ty) : Prop := Subtype source target ∧ Subtype target source

def pair (first last : Ty) : Ty := .pair (.node first) (.node last)
def arrow (arg : Ty) (argRow : Row) (result : Ty) (resultRow : Row) : Ty :=
  .arrow (.node arg) argRow (.node result) resultRow
def emptyRecord : Ty := .emptyRecord
def exactEmpty : Ty := .exactEmpty
def record (label : Nat) (payload rest : Ty) : Ty := .record label (.node payload) rest
def required (label : Nat) (payload : Ty) : Ty := record label payload emptyRecord
def recordDefault (label : Nat) (source fallback : Ty) : Ty :=
  .recordDefault label source (.node fallback)
def variant (label : Nat) (payload : Ty) : Ty := .variant label (.node payload)
def mask (hidden : List Nat) (type : Ty) : Ty := .mask hidden type
abbrev embedOld := CommonSyntax.embedOld (Row := Row)

def model : Core.PresenceGeneration.Model where
  Ty := Ty
  Row := Row
  base := .base
  bottom := .bottom
  top := .top
  union := .union
  inter := .inter
  pair := pair
  emptyRecord := emptyRecord
  exactEmpty := exactEmpty
  required := required
  record := record
  recordDefault := recordDefault
  variant := variant
  arrow := arrow
  empty := rowEmpty
  join := rowJoin
  subTy := Subtype
  subRow := rowLe

theorem common_subtype_exact (source target : Ty) :
    model.subTy source target ↔
      ∀ depth rank env demand, AcceptAt depth rank env target demand →
        AcceptAt depth rank env source demand := by
  constructor
  · intro below depth rank env demand
    exact below depth rank (env.atDepth depth) demand
  · intro below depth rank env demand
    simpa only [AcceptAt, Environment.atDepth_ofFinite] using
      below depth rank (Environment.ofFinite env) demand

theorem subtype_refl (type : Ty) : Subtype type type :=
  fun _ => CommonFinite.producerLe_refl _

theorem subtype_trans {first middle last : Ty}
    (before : Subtype first middle) (after : Subtype middle last) : Subtype first last :=
  fun depth => CommonFinite.producerLe_trans (before depth) (after depth)

theorem equivalent_refl (type : Ty) : Equivalent type type := ⟨subtype_refl _, subtype_refl _⟩
theorem equivalent_symm {first last : Ty} (same : Equivalent first last) : Equivalent last first :=
  ⟨same.2, same.1⟩
theorem equivalent_trans {first middle last : Ty}
    (before : Equivalent first middle) (after : Equivalent middle last) : Equivalent first last :=
  ⟨subtype_trans before.1 after.1, subtype_trans after.2 before.2⟩

theorem quote_observe_le {first last : Ty} (below : Subtype first last) (depth : Nat) :
    CommonFinite.ProducerLe rowLe
      (CommonSyntax.observe (CommonSyntax.graph Row) depth (.node first))
      (CommonSyntax.observe (CommonSyntax.graph Row) depth (.node last)) := by
  cases depth with
  | zero => exact CommonFinite.producerLe_refl _
  | succ depth => exact below depth

theorem common_arrow_iff (arg arg' result result' : Ty)
    (argRow argRow' resultRow resultRow' : Row) :
    model.subTy (arrow arg argRow result resultRow) (arrow arg' argRow' result' resultRow') ↔
      model.subTy arg' arg ∧ rowLe argRow' argRow ∧
      model.subTy result result' ∧ rowLe resultRow resultRow' := by
  constructor
  · intro below
    have split := fun depth => (CommonFinite.producerLe_arrow_iff
      rowLe_refl rowLe_trans _ _ _ _ _ _ _ _).mp (below depth)
    exact ⟨fun depth => (split (depth + 1)).1, (split 0).2.1,
      fun depth => (split (depth + 1)).2.2.1, (split 0).2.2.2⟩
  · rintro ⟨argument, incoming, output, outgoing⟩ depth
    exact (CommonFinite.producerLe_arrow_iff rowLe_refl rowLe_trans _ _ _ _ _ _ _ _).mpr
      ⟨quote_observe_le argument depth, incoming, quote_observe_le output depth, outgoing⟩

theorem common_pair_iff (first last first' last' : Ty) :
    model.subTy (pair first last) (pair first' last') ↔
      model.subTy first first' ∧ model.subTy last last' := by
  constructor
  · intro below
    exact ⟨fun depth => (CommonFinite.producerLe_pair_iff _ _ _ _).mp (below (depth + 1)) |>.1,
      fun depth => (CommonFinite.producerLe_pair_iff _ _ _ _).mp (below (depth + 1)) |>.2⟩
  · rintro ⟨first, last⟩ depth
    exact (CommonFinite.producerLe_pair_iff _ _ _ _).mpr
      ⟨quote_observe_le first depth, quote_observe_le last depth⟩

theorem common_variant_iff (label : Nat) (first last : Ty) :
    model.subTy (variant label first) (variant label last) ↔ model.subTy first last := by
  constructor
  · intro below depth
    exact (CommonFinite.producerLe_variant_iff label _ _).mp (below (depth + 1))
  · intro below depth
    exact (CommonFinite.producerLe_variant_iff label _ _).mpr (quote_observe_le below depth)

theorem required_as_width_tail (label : Nat) (payload : Ty) :
    record label payload emptyRecord = required label payload := rfl

def CompEquivalent (first last : Core.PresenceGeneration.Comp model) : Prop :=
  Equivalent first.1 last.1 ∧ rowLe first.2 last.2 ∧ rowLe last.2 first.2

def embedComp (old : Inference.Comp (SourcePrincipalInference.model rowAlgebra)) :
    Core.PresenceGeneration.Comp model := (embedOld old.1, old.2)

end Yulang.Common

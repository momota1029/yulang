import Yulang.GeneralDeclarativeTaggedSources340
import Yulang.GeneralDeclarativeAlternativeNeeds333

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTaggedNamed340
open GeneralDeclarativeHead320 (State Models environment)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeEntailment320 (Entails)
open GeneralDeclarativeEqualities322 (Derives entails semantic)
open GeneralDeclarativeAlternativeView333 (Index Offer)
open GeneralDeclarativeAlternativeNeeds333 (Need Planned Eventually eventually_one eventually_step eventually_pair finiteIndex)
open GeneralDeclarativeTaggedSources340 (Groups Read decodes)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCommonBridge (Assignment variant_merge)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans union_congr)
open CommonNominalFullCarrier (Equivalent)

/-- Independently sourced normalization of a grouped variant's outer
branches. Never inspect a leaf payload to split it across binders.
Names can use any source-backed alias and stored row; no first hit. -/
inductive Source (s : State) (tag : Nat) : Expr → Expr → Prop where
  | tagged : Source s tag (.variant tag a) a
  | join : Source s tag a x → Source s tag b y → Source s tag (.join a b) (.join x y)
  | named (offer : Offer s n) : Source s tag offer.rhs a → Source s tag (.variable n) a

theorem by_group {s : State} (seen : Groups tag source payload) : Source s tag source payload := by
  induction seen with
  | single => exact .tagged
  | join _ _ one two => exact .join one two

theorem sound {s : State} (seen : Source s tag input payload) (m : Assignment) (fit : Models s m) :
    Equivalent (value (environment m) .actual input) (value (environment m) .actual (.variant tag payload)) := by
  induction seen with
  | tagged => exact eqv_refl _
  | join _ _ one two => exact eqv_trans (union_congr one two) (variant_merge _ _ _)
  | named offer _ next =>
    exact eqv_trans (semantic (.trans (.congruent (.variable offer.linked)) (.row offer.stored)) m fit) next

theorem entails_read {s : State} {p : Supported s done}
    (seen : Source (restriction p) tag (.variable x) payload) : Entails s ⟨x,.variant tag payload⟩ :=
  fun m fit => sound seen m (GeneralDeclarativeOrigins321.restrict_models p m fit)

theorem prior {s : State} {p : Supported s done} (seen : Read p n tag payload) :
    Source (restriction p) tag (.variable n) payload := by
  obtain ⟨exp,⟨owner,alias,body⟩,printed⟩ := seen.source
  exact .named ⟨owner,exp,alias,body⟩ (by_group ((decodes _ _ _).mp printed))

structure Result (s : State) (tag : Nat) (input : Expr) where
  payload : Expr
  source : Source s tag input payload

def run (src : Index s) (tag : Nat) : Nat → (source : Expr) → List (Result s tag source)
  | 0,_ => []
  | _f+1,.variant k x =>
    if h : k = tag then [⟨x,h.symm ▸ .tagged⟩] else []
  | f+1,.join a b =>
    (run src tag f a).flatMap fun one =>
      (run src tag f b).map fun two => ⟨.join one.payload two.payload,.join one.source two.source⟩
  | f+1,.variable n =>
    (src n).flatMap fun offer =>
      (run src tag f offer.rhs).map fun got => ⟨got.payload,.named offer got.source⟩
  | _+1,_ => []

abbrev Persists (src : Index s) (seen : Source s tag input payload) :=
  Eventually (fun fuel => (⟨payload,seen⟩ : Result s tag input) ∈ run src tag fuel input)

/-- Every real finite witness determines a finite packet of actually
supported offers; increasing fuel through the packet retains it. This
is not a first-hit policy or an unbounded solver termination result. -/
theorem plans {s : State} (seen : Source s tag input payload) :
    Planned (fun index : Index s => Persists index seen) := by
  induction seen with
  | tagged =>
    exact Planned.pure (fun _ => eventually_one (fun _ => by simp [run]))
  | join left right ih jh =>
    apply (ih.both jh).map
    intro src both
    apply eventually_step (eventually_pair both.1 both.2)
    intro f printed
    exact List.mem_flatMap.mpr ⟨⟨_,left⟩,printed.1,List.mem_map.mpr ⟨⟨_,right⟩,printed.2,rfl⟩⟩
  | named offer inner ih =>
    let wanted : Need s := ⟨_,offer⟩
    exact ih.add wanted (fun src listed bounded => eventually_step bounded (fun f actual =>
      List.mem_flatMap.mpr ⟨offer,listed,List.mem_map.mpr ⟨⟨_,inner⟩,actual,rfl⟩⟩))

theorem finite {s : State} (seen : Source s tag input payload) :
    ∃ needed : List (Need s), Persists (finiteIndex needed) seen := (plans seen).finite

end Yulang.GeneralDeclarativeTaggedNamed340

import Yulang.GeneralPresenceQueryTransport245
/-! Passive observation bundles travel with every actual table rebase in a
finite certified plan. This does not model callbacks, cache invalidation,
active inspection scheduling or operational historical-origin dependencies. -/
namespace Yulang.GeneralPresenceObservedPlan245
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralPresenceOwnerTable244 GeneralPresenceReadback245
open GeneralPresenceModelCongruence245 GeneralPresencePreorderExtension245
open GeneralPresenceRebasePlan245 GeneralPresenceQueryTransport245
variable {Name Owner Tag : Type} [DecidableEq Name] [DecidableEq Owner]

def Stable (model : Model) (observe : Tag → Comp model → Prop) : Prop :=
 ∀ tag first last, ValueEq model first last → (observe tag first ↔ observe tag last)

def Observed (model : Model) (observe : Tag → Comp model → Prop)
 (assignment : Name → Comp model) (bundle : List (Tag × CompTerm Name)) : Prop :=
 ∀ item ∈ bundle, observe item.1 (item.2.eval model assignment)

def Outcome (model : Model) (observe : Tag → Comp model → Prop) (sharedNames : Name → Prop)
 (boundary : Name → Comp model) (state : State Name Owner) (bundle : List (Tag × CompTerm Name)) : Prop :=
 ∃ assignment, Models state model assignment ∧ Agrees sharedNames model assignment boundary ∧ Observed model observe assignment bundle

theorem step_observed (model : Model) (laws : Laws model) (observe : Tag → Comp model → Prop)
 (stable : Stable model observe) (sharedNames : Name → Prop) (boundary : Name → Comp model)
 (state : State Name Owner) (edit : Edit Name Owner) (safe : Safe sharedNames state edit)
 (bundle : List (Tag × CompTerm Name)) :
 Outcome model observe sharedNames boundary state bundle ↔
 Outcome model observe sharedNames boundary (rebase state edit.owner edit.fresh)
   (bundleSubst (state.entries edit.owner) bundle) := by
 constructor
 · rintro ⟨assignment,valid,agree,observed⟩
   refine ⟨readback edit.fresh model assignment,
     models_extension state edit.owner edit.fresh safe.present safe.disjoint safe.oldExternal safe.oldCoherent
       safe.freshExternal safe.freshCoherent safe.within model laws assignment valid,?_,?_⟩
   · intro name shared
     rw [outside_preserved edit.fresh model assignment name]
     · exact agree name shared
     · intro entry member
       obtain ⟨old,oldMem,equal⟩ := safe.within entry member
       rw [← equal]
       exact safe.privateTargets name shared old oldMem
   · intro item member
     obtain ⟨original,present,equal,values⟩ := bundle_forward _ _ safe.oldExternal safe.oldCoherent safe.within
       model laws assignment (valid.2 edit.owner safe.present) bundle item member
     rw [equal]
     exact (stable original.1 _ _ values).mpr (observed original present)
 · rintro ⟨assignment,valid,agree,observed⟩
   refine ⟨readback (state.entries edit.owner) model assignment,
     models_readback state edit.owner edit.fresh safe.present safe.disjoint safe.oldExternal safe.oldCoherent
       model laws.refl assignment valid,?_,?_⟩
   · intro name shared
     rw [outside_preserved _ model assignment name (safe.privateTargets name shared)]
     exact agree name shared
   · intro item member
     have held := observed (item.1,querySubst (state.entries edit.owner) item.2)
       (List.mem_map.mpr ⟨item,member,rfl⟩)
     simpa only [query_readback] using held

def runObserved (state : State Name Owner) (bundle : List (Tag × CompTerm Name)) :
 List (Edit Name Owner) → State Name Owner × List (Tag × CompTerm Name)
 | [] => (state,bundle)
 | edit :: rest => runObserved (rebase state edit.owner edit.fresh)
   (bundleSubst (state.entries edit.owner) bundle) rest

theorem table_projection (state : State Name Owner) (bundle : List (Tag × CompTerm Name))
 (plan : List (Edit Name Owner)) : (runObserved state bundle plan).1 = run state plan := by
 induction plan generalizing state bundle with
 | nil => rfl
 | cons edit rest ih => exact ih _ _

theorem tags_preserved (state : State Name Owner) (bundle : List (Tag × CompTerm Name))
 (plan : List (Edit Name Owner)) : (runObserved state bundle plan).2.map Prod.fst = bundle.map Prod.fst := by
 induction plan generalizing state bundle with
 | nil => rfl
 | cons edit rest ih => exact (ih _ _).trans (bundle_tags _ bundle)

theorem plan_observed (model : Model) (laws : Laws model) (observe : Tag → Comp model → Prop)
 (stable : Stable model observe) (sharedNames : Name → Prop) (boundary : Name → Comp model)
 (state : State Name Owner) (plan : List (Edit Name Owner)) (safe : SafePlan sharedNames state plan)
 (bundle : List (Tag × CompTerm Name)) :
 Outcome model observe sharedNames boundary state bundle ↔
 Outcome model observe sharedNames boundary (runObserved state bundle plan).1 (runObserved state bundle plan).2 := by
 induction safe generalizing bundle with
 | nil state => rfl
 | cons state edit rest head tail ih =>
   exact (step_observed model laws observe stable sharedNames boundary state edit head bundle).trans (ih _)
end Yulang.GeneralPresenceObservedPlan245

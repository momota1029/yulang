import Yulang.GeneralDeclarativeWitnessNonpointPortModel362

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 70000
set_option maxHeartbeats 76000000
namespace Yulang.GeneralDeclarativeWitnessNonpointReceiver362
open GeneralDeclarativeWitnessThreeNative362 (Run run authority)
open GeneralDeclarativeWitnessNonpointPort362 (Transport forward receiver)
open GeneralDeclarativeWitnessNonpointPortModel362 (stage extended extended_fits exact exact_model_iff)
open GeneralDeclarativeWitnessNativePreparation360 (Layout Prepared prepare context)
open GeneralDeclarativeWitnessNativeInstall360 (World Fits NativeViews)
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey slots)
open GeneralDeclarativeWitnessCompiler350 (Finished execute trip printDemand)
open GeneralDeclarativeWitnessLiteral349 (preserves preserves_iff)
open GeneralDeclarativeGrowth327 (restrict)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (subtype_refl)
open PresenceNormalForm (Atom)

def owner : FrameKey := ⟨[10,0],98,1⟩

def layout {contra r gate} (p : @Transport contra r gate) (s : Capture) : Layout :=
  ⟨p.world.ordinary,[(92,s)],[60,61,62,201,202,203,210,211,212,213],fun _ => ⟨0,0,0⟩,fun _ _ => 0⟩

structure Applied {contra : Bool} {r : Run contra} {gate}
    (p : Transport r gate) where
  before : Capture
  input : p.child.arguments = [before]
  prepared : Prepared p.environment owner p.child (layout p before)
  properSource : prepared.impl = receiver
  cap : Capture
  actualBinder : slots [prepared.captures] owner 92 = some cap
  actualCenter : cap.center = before.center
  body : Finished
  moved : execute (context p.environment p.child prepared.impl (layout p before)) = some body
  fixed : body.fixed = []
  noKids : body.kids = []
  kept : preserves p.world.ordinary body.state = true

def receive {contra} {r : Run contra} {gate} (p : Transport r gate) : Option (Applied p) := do
  match seen : p.child.arguments with
  | [before] =>
    let out ← prepare p.environment owner p.child (layout p before)
    if src : out.impl = receiver then
      match bound : slots [out.captures] owner 92 with
      | none => none
      | some cap =>
        if center : cap.center = before.center then
          match exec : execute (context p.environment p.child out.impl (layout p before)) with
          | none => none
          | some body =>
            if exact : body.fixed = [] ∧ body.kids = [] ∧ preserves p.world.ordinary body.state = true then
              some ⟨before,seen,out,src,cap,bound,center,body,exec,exact.1,exact.2.1,exact.2.2⟩
            else none
        else none
    else none
  | _ => none

def Applied.world {contra r gate p} (a : @Applied contra r gate p) : World := ⟨a.body.state,p.world.board⟩

def rows : List (Atom Nat) :=
  [(202,202),(202,202),(214,210),(210,214),(215,211),(211,215),(214,202),(202,215)].map
    fun p => .tyLe (.var p.1) (.var p.2)

def state (contra : Bool) : State :=
  let initial := stage contra
  ⟨⟨initial.normal.ordinary ++ rows,initial.normal.intervals⟩,initial.equations⟩

def exactBody {contra r gate p} (a : @Applied contra r gate p) : Bool :=
  decide (trip a.before = (210,202,211) ∧ trip a.cap = (214,202,215)) &&
    exact a.world.ordinary (state contra)

theorem actual_source_receiver_keeps_nonpoint_positions (contra : Bool) :
    ((run contra).bind fun r => (forward r authority).bind fun p =>
      (receive p).map exactBody).getD false = true := by cases contra <;> decide +kernel

def fitting (contra u : Bool) : Assignment := fun n =>
  if n = 214 then extended contra u 210 else if n = 215 then extended contra u 211 else extended contra u n

theorem fitting_state (contra u : Bool) : Models (state contra) (fitting contra u) := by
  have fresh : (stateNames (stage contra)).all
      (fun n => decide (n ≠ 214 ∧ n ≠ 215)) = true := by cases contra <;> decide +kernel
  have exact (n : Nat) (used : n ∈ stateNames (stage contra)) : extended contra u n = fitting contra u n := by
    obtain ⟨n14,n15⟩ := of_decide_eq_true (List.all_eq_true.mp fresh n used)
    simp [fitting,n14,n15]
  have past := (preserves_models _ exact).mp (extended_fits contra u)
  refine ⟨⟨?_,past.1.2⟩,past.2⟩
  intro a stored
  rcases (List.mem_append.mp stored : a ∈ (stage contra).normal.ordinary ∨ a ∈ rows) with before|new
  · exact past.1.1 a before
  · simp only [rows,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at new
    rcases new with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact subtype_refl _

theorem returned_body_retains_prior_fit {contra} {r : Run contra} {gate} {p : Transport r gate}
    (a : Applied p) (m : Assignment) (v : NativeViews) (fit : Fits a.world m v) :
    Fits p.world m v ∧ Fits r.final m v := by
  have compressed : Fits p.world m v := ⟨restrict ((preserves_iff ..).mp a.kept) m fit.1,fit.2⟩
  exact ⟨compressed,
    (GeneralDeclarativeWitnessNativePreparation360.same_model_of_prepared p.source m compressed.1).1,fit.2⟩

end Yulang.GeneralDeclarativeWitnessNonpointReceiver362

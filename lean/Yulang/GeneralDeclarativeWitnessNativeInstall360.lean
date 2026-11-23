import Yulang.GeneralDeclarativeWitnessNativeValue360

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessNativeInstall360
open GeneralDeclarativeWitnessNativePreparation360 (Prepared)
open GeneralDeclarativeWitnessNativeValue360 (Write Address Value Code Compiled owner)
open GeneralDeclarativeWitnessTypedRelease354 (Stamp position)
open GeneralDeclarativeHead320 (State Models)
open GeneralNominalCommonBridge (Assignment)

structure Board where
  active : List Stamp
  writes : List Write

structure World where
  ordinary : State
  board : Board

abbrev NativeViews := Nat → Option Value

def atTarget (board : Board) (name : Nat) : Option Write :=
  board.writes.find? fun row => row.address.target == name

def interpreted (board : Board) (m : Assignment) : NativeViews :=
  fun name => (atTarget board name).map (fun row => row.code.eval m)

def Fits (w : World) (m : Assignment) (v : NativeViews) : Prop :=
  Models w.ordinary m ∧ ∀ n,v n = interpreted w.board m n

/-- Preserve an independently supplied active occurrence/version and make
a fresh typed commit in the native observation table only. -/
structure Committed (board : Board) (written : Write) : Prop where
  active : written.address.owner ∈ board.active
  unique : (board.active.map position).Nodup
  fresh : atTarget board written.address.target = none

def check (board : Board) (written : Write) : Bool :=
  decide (written.address.owner ∈ board.active ∧ (board.active.map position).Nodup) &&
    (atTarget board written.address.target).isNone

theorem check_exact {board written} : check board written = true ↔ Committed board written := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq,Option.isNone_iff_eq_none]
  exact ⟨fun h => ⟨h.1.1,h.1.2,h.2⟩,fun h => ⟨⟨h.active,h.unique⟩,h.fresh⟩⟩

def add (board : Board) (row : Write) : Board :=
  {board with writes := board.writes ++ [row]}

def current {e frame d l} (p : Prepared e frame d l) (board : Board) (row : Write) : World :=
  ⟨p.stage,add board row⟩

theorem authored_target_appears {board row} (installed : Committed board row) :
    atTarget (add board row) row.address.target = some row := by
  have absent := installed.fresh
  unfold atTarget at absent
  simp [atTarget,add,List.find?_append,absent]

theorem other_target_unchanged (board : Board) (row : Write) (n : Nat)
    (distinct : n ≠ row.address.target) : atTarget (add board row) n = atTarget board n := by
  have ne : (row.address.target == n) = false := by simp [Ne.symm distinct]
  simp [atTarget,add,List.find?_append,ne]

def install {e frame d l} (p : Prepared e frame d l) {table wire version}
    (written : Compiled p table wire version) (base : Board) : Option World :=
  if check base written.write then some (current p base written.write) else none

theorem actual_installation {e frame d l} (p : Prepared e frame d l) {table wire version}
    (written : Compiled p table wire version) {base final} (made : install p written base = some final)
    (m : Assignment) (v : NativeViews) (fit : Fits final m v) :
    v wire.target = some (written.code.eval m) ∧
    Models l.named m ∧ ∀ row ∈ p.whereRows,GeneralDeclarativeEntailment320.Holds m row := by
  unfold install at made
  split at made
  · rename_i checked
    have state := Option.some.inj made
    subst final
    have exactScope : Committed base written.write := check_exact.mp checked
    have seen := fit.2 wire.target
    change v wire.target = (atTarget (add base written.write) written.write.address.target).map _ at seen
    rw [authored_target_appears exactScope] at seen
    exact ⟨seen,GeneralDeclarativeWitnessNativePreparation360.same_model_of_prepared p m fit.1⟩
  · cases made

theorem no_ordinary_override {e frame d l} (p : Prepared e frame d l) {table wire version}
    (written : Compiled p table wire version) {base final} (made : install p written base = some final) :
    final.ordinary = p.stage := by
  unfold install at made
  split at made
  · exact (congrArg World.ordinary (Option.some.inj made)).symm
  · cases made

theorem fit_after_install {e frame d l} (p : Prepared e frame d l) {table wire version}
    (written : Compiled p table wire version) {base final} (made : install p written base = some final)
    (m : Assignment) (prior : Models p.stage m) : Fits final m (interpreted final.board m) :=
  ⟨no_ordinary_override p written made ▸ prior,fun _ => rfl⟩

end Yulang.GeneralDeclarativeWitnessNativeInstall360

import Yulang.GeneralDeclarativeMerge320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14500
set_option maxHeartbeats 4300000
namespace Yulang.GeneralDeclarativeCaptureClosure320
open GeneralDeclarations (Declaration Checked)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture InInterval)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeMerge320 (Merge shared_center)
open GeneralDeclarativeEntailment320 (Entails)
open GeneralNominalCommonBridge (Assignment)
open PresenceNormalForm (Atom All)
open CommonNominalFullCarrier (model)

def withOrdinary (s : State) (extra : List (Atom Nat)) : State :=
  ⟨{ s.normal with ordinary := s.normal.ordinary ++ extra },s.equations⟩

theorem ordinary_models {s : State} {extra : List (Atom Nat)} (m : Assignment) :
    Models (withOrdinary s extra) m ↔ Models s m ∧ All model m extra := by
  constructor
  · intro v
    have atoms := (PresenceNormalForm.all_append ..).mp v.1.1
    exact ⟨⟨⟨atoms.1,v.1.2⟩,v.2⟩,atoms.2⟩
  · rintro ⟨v,h⟩
    exact ⟨⟨(PresenceNormalForm.all_append ..).mpr ⟨v.1.1,h⟩,v.1.2⟩,v.2⟩

theorem preserve_bound {normal : GeneralDeclarativeWhere319.State} {a b : Nat}
    (proof : Bound normal a b) (extra : List (Atom Nat)) :
    Bound { normal with ordinary := normal.ordinary ++ extra } a b := by
  induction proof with
  | interval listed => exact .interval listed
  | constraint listed => exact .constraint (List.mem_append_left _ listed)
  | refl a => exact .refl a
  | trans _ _ first last => exact .trans first last

def atoms (c : Capture) : List (Atom Nat) :=
  [.tyLe (.var c.lower) (.var c.center),.tyLe (.var c.center) (.var c.upper)]

def Origin (s : State) (capture : Capture) : Prop :=
  Bounds s capture ∨ ∃ first rest, Merge s first rest capture

theorem capture_fits {s : State} {capture : Capture} (origin : Origin s capture)
    (m : Assignment) (valid : Models s m) :
    InInterval (m capture.lower).1 (m capture.upper).1 (m capture.center).1 := by
  rcases origin with own|⟨first,rest,merged⟩
  · exact bounds_sound own m valid
  · exact (shared_center merged m valid).1

def compilation (decl : Declaration) (capture : Nat → Capture) : List (Atom Nat) :=
  decl.inputNames.flatMap fun name => atoms (capture name)

theorem all_capture_atoms {s decl capture}
    (known : ∀ name ∈ decl.inputNames, Origin s (capture name))
    (m : Assignment) (valid : Models s m) : All model m (compilation decl capture) := by
  intro atom included
  obtain ⟨name,there,used⟩ := List.mem_flatMap.mp included
  have fits := capture_fits (known name there) m valid
  change atom ∈ atoms (capture name) at used
  rcases List.mem_cons.mp used with rfl|tail
  · exact fits.1
  · cases List.mem_singleton.mp tail
    exact fits.2

theorem conservative_capture {s decl capture}
    (known : ∀ name ∈ decl.inputNames, Origin s (capture name)) (m : Assignment) :
    Models (withOrdinary s (compilation decl capture)) m ↔ Models s m :=
  (ordinary_models m).trans ⟨And.left,fun valid => ⟨valid,all_capture_atoms known m valid⟩⟩

theorem available_bounds (s : State) (decl : Declaration) (capture : Nat → Capture) :
    ∀ name ∈ decl.inputNames, Bounds (withOrdinary s (compilation decl capture)) (capture name) := by
  intro n visible
  have lift (atom : Atom Nat) (used : atom ∈ atoms (capture n)) :
      atom ∈ (withOrdinary s (compilation decl capture)).normal.ordinary :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨n,visible,used⟩)
  exact ⟨.constraint (lift _ List.mem_cons_self),
    .constraint (lift _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))⟩

/-- All merged capture bounds are compiled from their per-occurrence and
shared-center facts. Adding these derived variable inequalities does not
change the ordinary models, and the normal equation compiler can now use
them without a separate external capture-bounds premise. -/
theorem batch_from_origins {s r interp capture decl d kids facts}
    (checked : Checked r) (visible : decl ∈ r.declarations)
    (origins : ∀ n ∈ decl.inputNames, Origin s (capture n))
    (bounds : ∀ arg ∈ d.arguments, Bounds s arg)
    (compiled : GeneralDeclarativeNodeFacts320.nodeFacts r interp capture decl d kids = some facts)
    (settled : ∀ row ∈ facts, Entails s row)
    (m : Assignment) (valid : Models s m) :
    GeneralDeclarativeAssembly320.Node r interp m d decl.id kids := by
  let extended := withOrdinary s (compilation decl capture)
  have vc : Models extended m := (conservative_capture origins m).mpr valid
  have arg (a) (used : a ∈ d.arguments) : Bounds extended a :=
    ⟨preserve_bound (bounds a used).1 _,preserve_bound (bounds a used).2 _⟩
  have en (row) (used : row ∈ facts) : Entails extended row :=
    fun model valid => settled row used model ((conservative_capture origins model).mp valid)
  exact ⟨decl,capture,rfl,GeneralDeclarativeEntailment320.entailed_batch_sound checked visible
    (available_bounds s decl capture) arg compiled en m vc⟩

end Yulang.GeneralDeclarativeCaptureClosure320

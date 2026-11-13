import Yulang.GeneralNominalActualBudget

/-! Unary nominal peeling retains the actual input origin even when refreshed
descriptors have strict intervals. A fixed finite source spine bounds every
observable retained projection. -/
namespace Yulang.GeneralNominalPeelingOrigins
open GeneralNominalRecursiveInspection GeneralNominalSharedCaptures
open GeneralNominalSaturationState
open GeneralNominalInspection (Bounds queries)
open CommonNominalFullCarrier

def path (name : Nat) (root : Origin) : Nat → Origin
  | 0 => root
  | depth+1 => .nominal (path name root depth) name 0

def tower (name : Nat) (base : Inference.Base) : Nat → Ty
  | 0 => .base base
  | depth+1 => nominal name [.inl (tower name base depth)]

theorem base_not_nominal (base : Inference.Base) (name : Nat) (arguments : List Argument) :
    ¬ Subtype (.base base) (nominal name arguments) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead name arguments.length) (by exact ⟨rfl,by simp⟩)

theorem observed_path {model : GeneralNominalCommonBridge.Assignment}
    (rootValue : Equivalent (model identity).1 (tower name base length))
    (seen : Observes model (path name (.source identity) depth) value) :
    ∃ remaining, length = depth+remaining ∧ Equivalent value (tower name base remaining) := by
  induction depth generalizing value with
  | zero => cases seen; exact ⟨length,by omega,rootValue⟩
  | succ depth ih =>
    cases seen with
    | nominal parent equal found =>
      obtain ⟨remaining,count,actual⟩ := ih parent
      cases remaining with
      | zero =>
        exact False.elim (base_not_nominal base name _ (subtype_trans actual.2 equal.1))
      | succ remaining =>
        have same := (nominal_regular_invariant_exact _ _ _ _).mp (subtype_trans actual.2 equal.1)
        have argument := same.2.2 0 (.inl (tower name base remaining)) (.inl value) rfl found
        exact ⟨remaining,by omega,⟨argument.2,argument.1⟩⟩

theorem observed_depth {model : GeneralNominalCommonBridge.Assignment}
    (rootValue : Equivalent (model identity).1 (tower name base length))
    (seen : Observes model (path name (.source identity) depth) value) : depth ≤ length := by
  obtain ⟨remaining,equal,_⟩ := observed_path rootValue seen
  omega

def CapturesAt (result : Report state) (origin : Origin) : Prop :=
  ∀ capture ∈ result.captures, capture.origin = some origin

private theorem append_captures (one : CapturesAt (first : Report state) origin)
    (two : CapturesAt (last : Report state) origin) : CapturesAt (first.append last) origin := by
  intro capture member
  rcases List.mem_append.mp member with present | present
  · exact one capture present
  · exact two capture present

private theorem variable_many (state : GeneralNominalState.State) (binder : Nat)
    (bounds : List (Bounds state)) (origins : Nat → Option Origin) (index : Nat)
    (known : origins index = some origin) :
    CapturesAt (inspectMany state [.variables [binder]] bounds origins index) origin := by
  cases bounds with
  | nil => intro capture member; simp [inspectMany] at member
  | cons head tail =>
    simp only [inspectMany,inspect,Report.append,known,List.map_cons,List.map_nil]
    intro capture member
    rcases List.mem_append.mp member with present | present
    · cases List.mem_singleton.mp present; rfl
    · cases tail <;> simp [inspectMany] at present

theorem nominal_captures (state : GeneralNominalState.State) (binder name : Nat)
    (bounds : Bounds state) (origin : Origin) :
    CapturesAt (inspect state (.nominal name [.variables [binder]]) bounds (some origin))
      (.nominal origin name 0) := by
  simp only [inspect,Report.visit]
  split
  · split <;> (intro capture member; cases member)
  · split
    · split
      · intro capture member; cases member
      · split
        · exact variable_many state binder _ _ 0 rfl
        · split
          · intro capture member; cases member
          · split
            · split
              · intro capture member; cases member
              · exact append_captures (variable_many state binder _ _ 0 rfl)
                  (variable_many state binder _ _ 0 rfl)
            · intro capture member; cases member
    · intro capture member; cases member

theorem inherited_captures (packet : Packet roles)
    (query : queries packet.context.state packet.context.interpretation packet.declaration =
      [.nominal name [.variables [binder]]])
    (recorded : packet.site.inputs[0]? = some (some origin)) :
    CapturesAt (inheritedReport packet) (.nominal origin name 0) := by
  unfold inheritedReport
  rw [query]
  cases packet.bounds with
  | nil => intro capture member; simp [inspectMany] at member
  | cons head tail =>
    simp only [inspectMany,recorded,Option.join_some]
    apply append_captures (nominal_captures packet.context.state binder name head origin)
    cases tail <;> (intro capture member; simp [inspectMany] at member)

theorem usable_origin (packet : Packet roles)
    (query : queries packet.context.state packet.context.interpretation packet.declaration =
      [.nominal name [.variables [binder]]])
    (recorded : packet.site.inputs[0]? = some (some origin))
    (usable : Usable packet captureName actual) : actual = .nominal origin name 0 := by
  obtain ⟨capture,member,_,equal⟩ := usable.1.1
  exact Option.some.inj (equal.symm.trans (inherited_captures packet query recorded capture member))

end Yulang.GeneralNominalPeelingOrigins

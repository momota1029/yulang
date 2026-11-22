import Yulang.GeneralDeclarativeWitnessSpineFront355
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessSpineLedger355
open GeneralDeclarativeWitnessSpineNode355 (Node Step Author Send next)
open GeneralDeclarativeWitnessNominalSpine355 (Code Checked read)
open GeneralDeclarativeWitnessTypedRelease354 (Key Authority position)
open GeneralDeclarativeHead320 (State)
open GeneralSourceMetadataExprDomain291 (bind_success)
open GeneralDeclarativeWitnessTypedOutput354 (Write)

def Checked.authors {s : State} {p : Node s} : Checked p → List Author
  | .leaf _ => []
  | .send a _ _ tail => a :: authors tail

def Checked.original {s : State} {p : Node s} : Checked p → Code
  | .leaf _ => .leaf
  | .send _ code _ tail => .send code (original tail)

def Checked.keys {s : State} {p : Node s} : Checked p → List Key
  | .leaf _ => []
  | .send a _ edge tail => p.address a.write edge.accepted.item.demand :: keys tail

def Checked.nodePaths {s : State} {p : Node s} (ok : Checked p) : List (List Nat) :=
  ok.nodes.map (fun n => n.origin.path)

def Validated (key : Key) (source : Author) : Prop :=
  key.ordinal = source.write ∧
  key ∈ source.authority.released ∧
  key.stamp ∈ source.authority.active ∧
  (source.authority.active.map position).Nodup

theorem every_release_is_authorized {s : State} {p : Node s} (ok : Checked p) :
    CommonRoleOutermostResolver.All₂ Validated (Checked.keys ok) (Checked.authors ok) := by
  induction ok with
  | leaf => exact .nil
  | send source code edge rest ih =>
    exact .cons ⟨rfl,edge.accepted.grants,edge.accepted.controlled,edge.accepted.single⟩ ih

theorem exact_source_vector {s : State} {p : Node s} {source : List Author} {code : Code} {ok : Checked p}
    (decoded : read p source code = some ok) :
    Checked.authors ok = source ∧ Checked.original ok = code := by
  induction code generalizing p source with
  | leaf =>
    cases source with
    | nil =>
      rw [read.eq_def] at decoded
      change (if h : p.proof.compiled.children.isEmpty = true then some (.leaf (List.isEmpty_iff.mp h)) else none) =
        some ok at decoded
      split at decoded
      · cases Option.some.inj decoded
        exact ⟨rfl,rfl⟩
      · cases decoded
    | cons first rest =>
      rw [read.eq_def] at decoded
      change none = some ok at decoded
      cases decoded
  | send here more ih =>
    cases source with
    | nil =>
      rw [read.eq_def] at decoded
      cases decoded
    | cons first rest =>
      rw [read.eq_def] at decoded
      obtain ⟨edge,_,ran⟩ := bind_success decoded
      obtain ⟨tail,checked,found⟩ := bind_success ran
      cases Option.some.inj found
      have eq := ih checked
      exact ⟨congrArg (List.cons first) eq.1,congrArg (Code.send here) eq.2⟩

theorem every_source_release {s : State} {p : Node s} {source : List Author} {code : Code} {ok : Checked p}
    (decoded : read p source code = some ok) : CommonRoleOutermostResolver.All₂ Validated (Checked.keys ok) source :=
  (exact_source_vector decoded).1 ▸ every_release_is_authorized ok

theorem path_lengths {s : State} {p : Node s} (ok : Checked p) :
    List.Pairwise (fun x y : List Nat => x.length < y.length) (Checked.nodePaths ok) ∧
    ∀ here ∈ Checked.nodePaths ok, p.origin.path.length ≤ here.length := by
  induction ok with
  | leaf =>
    exact ⟨by simp [Checked.nodePaths,GeneralDeclarativeWitnessNominalSpine355.Checked.nodes],
      by simp [Checked.nodePaths,GeneralDeclarativeWitnessNominalSpine355.Checked.nodes]⟩
  | @send p plan wire edge rest ih =>
    have nextLength : edge.node.origin.path.length = p.origin.path.length + 1 := by
      change wire.path.length = _
      rw [edge.place,List.length_append]
      rfl
    change List.Pairwise _ (p.origin.path :: Checked.nodePaths rest) ∧
      ∀ here ∈ p.origin.path :: Checked.nodePaths rest, _
    have tailStrict : ∀ q ∈ Checked.nodePaths rest, p.origin.path.length < q.length := by
      intro q h
      have bound := ih.2 q h
      rw [nextLength] at bound
      omega
    refine ⟨List.pairwise_cons.mpr ⟨tailStrict,ih.1⟩,?_⟩
    intro loc h
    rcases List.mem_cons.mp h with rfl|later
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (tailStrict loc later)

end Yulang.GeneralDeclarativeWitnessSpineLedger355

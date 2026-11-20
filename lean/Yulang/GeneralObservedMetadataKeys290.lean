import Yulang.GeneralRebaseReceiptCheckedReplay289

/-! A syntactic upper bound on constructor keys of a normalized candidate
head. It deliberately also includes keys in branches that translate to
deferred; binder names and field/variant labels are not constructor keys. -/
namespace Yulang.GeneralObservedMetadataKeys290
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarations (Declaration)

mutual
 def keys : Pattern → List Nat
  | .var _ => []
  | .app key args => key :: keysMany args
  | .record _ payload tail => keys payload ++ keys tail
  | .variant _ payload => keys payload
  | .join first last => keys first ++ keys last
 def keysMany : List Pattern → List Nat
  | [] => []
  | p :: ps => keys p ++ keysMany ps
end

theorem member_many {p : Pattern} {ps : List Pattern} (hp : p ∈ ps)
    {n : Nat} (hn : n ∈ keys p) : n ∈ keysMany ps := by
  induction ps with
  | nil => cases hp
  | cons first rest ih =>
    unfold keysMany
    rcases List.mem_cons.mp hp with rfl | h
    · exact List.mem_append_left _ hn
    · exact List.mem_append_right _ (ih h)

theorem app_self (key : Nat) (args : List Pattern) : key ∈ keys (.app key args) :=
  List.mem_cons_self ..

theorem app_nested {key : Nat} {args : List Pattern} {p : Pattern} (hp : p ∈ args)
    {n : Nat} (hn : n ∈ keys p) : n ∈ keys (.app key args) :=
  List.mem_cons_of_mem _ (member_many hp hn)

def headKeys (d : Declaration) := keysMany d.normalHead

def candidateKeys (ds : List Declaration) : List Nat := ds.flatMap headKeys

theorem candidate_key {ds : List Declaration} {d : Declaration} {k : Nat}
    (declaration : d ∈ ds) (found : k ∈ headKeys d) : k ∈ candidateKeys ds :=
  List.mem_flatMap.mpr ⟨d,declaration,found⟩

end Yulang.GeneralObservedMetadataKeys290

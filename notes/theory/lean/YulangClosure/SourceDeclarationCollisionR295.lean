import YulangClosure.SourceDeclarationRetentionR295

/-!
Concrete abstract-graph counterexample to reflection of R295's relation extension.

The original graph already has an insertion at node 1 with labels (7, 9).
R295 appends another insertion with those labels at node 3. Its new global
forwarding witness also applies at node 1, which therefore gains a contribution.
Both judgments below use the SAME installed graph and operator contracts.

This does not refute R295's old-witness inclusion. The empty original forwarding
relation and the declaration identities are abstract inputs, not authenticated
typed source contracts. No source-qualified semantics defect, EI result,
whole-language soundness result or production authority is asserted.
-/
namespace YulangClosure.SourceDeclarationCollisionR295

open OriginalSource SourceSignatureConstruction SourceContributionConstruction
open SourceDeclarationRetentionR295

def catalogue : Catalogue Unit :=
  ⟨Unit, fun _ _ => Unit, [], fun _ => 0⟩

def introduction : Introduction Unit :=
  ⟨0, 0, .primitive, catalogue, fun _ _ _ => Unit⟩

/-- The existing insertion's child 0 is already present in the original graph. -/
def original : Graph Unit :=
  ⟨[.primitive introduction, .insertion 7 9 0 catalogue],
    fun _ => 0, fun _ whole => whole⟩

def declaration : DeclarationData Unit :=
  ⟨7, 9, 0, 0, .primitive introduction⟩

def installed : Graph Unit := install original declaration

/-- No claim identifies this empty relation with lawful source semantics. -/
def old : Relations installed where
  alternative := fun _ _ _ {_ _} _ _ => Empty
  conjunction := fun _ _ {_ _ _} _ _ _ => Empty
  forward := fun _ _ {_ _} _ _ => Empty

def emptyContract (node : Node Unit) : OperatorContract installed node where
  Evidence := fun _ _ => Empty
  Field := fun _ _ _ => Empty
  governed := fun _ _ evidence => nomatch evidence

def operators : Operators installed where
  image := fun _ _ _ _ _ => emptyContract _
  call := fun _ _ _ _ _ _ _ => emptyContract _

def packet : Packet catalogue () := ⟨(), ()⟩

theorem old_node_unchanged : installed.node 1 = original.node 1 := rfl

theorem new_insertion_lookup :
    installed.node 3 = some (.insertion 7 9 2 catalogue) := rfl

theorem old_forward_empty :
    ¬ Nonempty (old.forward (.insertion 7 9) () packet packet) := by
  intro witness
  exact witness.elim (fun evidence => nomatch evidence)

/-- The new insertion relation also acts at the pre-existing node 1. -/
def newContribution :
    DeclContribution installed (retainedRelations original declaration old) operators
      1 () (.insertion 7 9 0 catalogue) packet := by
  let child : DeclContribution installed (retainedRelations original declaration old) operators
      0 () (.primitive introduction) packet :=
    DeclContribution.primitive (graph := installed) (index := 0) (intro := introduction)
      (by rfl) packet ()
  apply DeclContribution.forward (by rfl) Forward.insertion child packet
  apply Sum.inr
  change RetainedForward original declaration
    (.insertion declaration.root declaration.declaration) () packet packet
  exact @RetainedForward.insertion Unit original declaration () packet

theorem no_old_contribution
    (derivation : DeclContribution installed old operators
      1 () (.insertion 7 9 0 catalogue) packet) : False := by
  cases derivation with
  | forward _ _ _ _ evidence => exact nomatch evidence

theorem new_contribution :
    Nonempty (DeclContribution installed (retainedRelations original declaration old) operators
      1 () (.insertion 7 9 0 catalogue) packet) :=
  ⟨newContribution⟩

/-- Hence old-node contribution reflection fails for these abstract inputs. -/
theorem no_reflection :
    ¬ (Nonempty (DeclContribution installed (retainedRelations original declaration old) operators
        1 () (.insertion 7 9 0 catalogue) packet) →
      Nonempty (DeclContribution installed old operators
        1 () (.insertion 7 9 0 catalogue) packet)) := by
  intro reflection
  exact (reflection new_contribution).elim no_old_contribution

end YulangClosure.SourceDeclarationCollisionR295

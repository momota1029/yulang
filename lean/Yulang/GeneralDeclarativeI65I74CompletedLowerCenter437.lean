import Yulang.GeneralDeclarativeI65I72CompletedUnaryTrace406
import Yulang.GeneralDeclarativeI65Origins367

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.CompletedConsumer437

open GeneralDeclarativeI65
open PresenceNormalForm (Atom)

structure ReadCenter {s q row needs forest}
    (choice : PreselectedUnary406 s q row (needs := needs) forest) (ordinal : Nat) where
  center : OriginalPayload406 choice
  found : s.core.origins[ordinal]? = some center.source
  issuer : center.source.issuer = q.occurrence

/-- Read the actual center only after election. An upper endpoint,
a different issuer at the same name, or a missing bound does not
manufacture a center or a source-language diagnostic. -/
def readCenterAt {s q row needs forest}
    (choice : PreselectedUnary406 s q row (needs := needs) forest)
    (ordinal : Nat) : Option (ReadCenter choice ordinal) :=
  match found : s.core.origins[ordinal]? with
  | none => none
  | some read =>
    if tracked : routeMember s.core choice.gate.arg.center read = true then
      if same : read.issuer = q.occurrence then
        match payload : literalUnaryPayloadName406 choice.gate.key read.endpoint with
        | none => none
        | some name =>
          if bounds :
            Atom.tyLe (.var choice.gate.lowerPayload) (.var name) ∈ s.core.current.ordinary.normal.ordinary ∧
            Atom.tyLe (.var name) (.var choice.gate.upperPayload) ∈ s.core.current.ordinary.normal.ordinary then
            some ⟨⟨read,List.mem_of_getElem? found,actual_route_iff.mp tracked,name,payload,
              ⟨.constraint bounds.1,.constraint bounds.2⟩⟩,found,same⟩
          else none
      else none
    else none

private theorem noOutputIndex437 {q : Request} (bare : q.demand.outputs = [])
    (index : Fin q.demand.outputs.length) : False := by
  have size := index.isLt
  have zero : q.demand.outputs.length = 0 := congrArg List.length bare
  exact Nat.not_lt_zero index.val (Nat.lt_of_lt_of_le size (Nat.le_of_eq zero))

/-- For the literal empty consumer body only, keep the read center
and the original elected support, with no invented child or write. -/
def buildEmptyInvocation {s q row needs forest}
    (chosen : PreselectedUnary406 s q row (needs := needs) forest) {j : Nat}
    (observed : ReadCenter chosen j) (whereEmpty : row.requirements = []) (outputsEmpty : q.demand.outputs = []) :
    CompletedInvocation406 s q [] := by
  let body : CompletedBody406 observed.center :=
    ⟨fun i => False.elim (noOutputIndex437 outputsEmpty i)⟩
  have kids : frameWhereKids400 (originalNativeFrame406 chosen observed.center) = [] := by
    simp [frameWhereKids400,AuthoredBodyFrame393.clauses,originalNativeFrame406,frameAtSource395,
      whereEmpty,children]
  refine {
    row := row
    needs := needs
    forest := forest
    chosen := chosen
    actualPayload := observed.center
    body := body
    fixed := fun i => False.elim (noOutputIndex437 outputsEmpty i)
    clauses := ?_
    children := ?_ }
  · intro c h
    rw [whereEmpty] at h
    cases h
  · exact kids.symm ▸ .nil

theorem exact_empty_invocation_reads_original_capture437 {s q row needs forest}
    (chosen : PreselectedUnary406 s q row (needs := needs) forest) {j : Nat}
    (observed : ReadCenter chosen j) (w : row.requirements = []) (o : q.demand.outputs = [])
    (m : I72.Model) (fit : I72.Fits s m) :
    CompletedInvocationMeaning406 (buildEmptyInvocation chosen observed w o) m :=
  completed_invocation_means_one_state_and_model406 _ m fit

end Yulang.GeneralDeclarativeI65.I72.CompletedConsumer437

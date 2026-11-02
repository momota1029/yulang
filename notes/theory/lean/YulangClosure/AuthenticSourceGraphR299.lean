import YulangClosure.SourceGraphBuilderR298
import YulangClosure.PrimitiveOperationInstance

/-!
R299: source-qualified diagnosis of the first unavailable IF §6 input.

This file does NOT construct an authentic source graph. It checks the actual
primitive constructor and the proposed original-checking-declaration route.
The latter leaves the source primitive's independent atom entirely external.
No toy Graph, assumed closure, substituted license, or invented formation
record is used to stand in for that unavailable input.
-/
namespace YulangClosure.AuthenticSourceGraphR299

open OriginalSource OriginalScopedClosure SourceGraphRegistrationR297
open OriginalSourceInterpretation OriginalSourceEnvironment OriginalSourceChecking

/-- The exact unannotated original primitive atom, including its actual
declaration identity and incoming source context. -/
def primitiveAtom (context : Context) (site : Site) (declaration : Declaration) : Atom :=
  {(atom .primitiveDeclarationInstance site context) with declaration := some declaration}

/-- The actual first-pass source table retains the declaration ID and complete
syntax, but performs no lookup of an independently typed contract. -/
theorem primitive_inventory (origin : Declaration) (context : Context)
    (site : Site) (declaration : Declaration) :
    sourceInventory origin context (.primitive ⟨site, none⟩ declaration) =
      [⟨.rule ⟨origin, [], [], []⟩ .primitive site context
        [.atom (primitiveAtom context site declaration)] .nil, []⟩] := by
  simp only [sourceInventory, source, sourceRules]
  rfl

/-- Exact original source-rule meaning. This is an inversion/reconstruction
theorem, not a new primitive license or a typed declaration supplier. -/
theorem primitive_source_iff (original : Kernel Value) (environment : Environment Value)
    (context : Context) (site : Site) (declaration : Declaration) :
    SourceJudgment original environment context (.primitive ⟨site, none⟩ declaration) ↔
      original.atom environment (primitiveAtom context site declaration) := by
  simp only [SourceJudgment, sourceRules]
  constructor
  · intro source
    cases source with
    | rule locals children =>
      have localProof := locals (.atom (primitiveAtom context site declaration)) (by simp [primitiveAtom])
      cases localProof with
      | atom valid => exact valid
  · intro valid
    apply Judgment.rule
    · intro premise present
      simp only [List.mem_singleton] at present
      subst premise
      exact Local.atom valid
    · exact Judgments.nil

/-- Supplying the existing independently proved finite checking declarations
does not supply the distinct source primitive contract. The exact missing
owner is original.atom at primitiveDeclarationInstance, not declarations.check.
All original semantic domains and the original incoming environment remain.
-/
theorem checking_registry_does_not_supply_source_primitive
    {s : Sorts} (inputs : Inputs s) (registry : GuardRegistry inputs)
    (declarations : Declarations inputs registry) (reading : Reading s Value)
    (original : Kernel Value) (environment : Environment Value)
    (context : Context) (site : Site) (declaration : Declaration) :
    SourceJudgment (kernel inputs registry declarations reading original)
        environment context (.primitive ⟨site, none⟩ declaration) ↔
      original.atom environment (primitiveAtom context site declaration) :=
  primitive_source_iff _ environment context site declaration

/-- Actual source ownership installation computes the Call owner list while
retaining every incoming interface readout. Thus this alternative constructor
is not a supplier of the original complete typed result schemas either.
-/
theorem source_installation_readback {s : Sorts} {View : Type}
    (root : Root s View) (context : Context) (raw : Source category) :
    (root.withSource context raw).decoded.callOwners = sourceCallOwners context raw ∧
      (root.withSource context raw).decoded.interfaces = root.interfaces ∧
      (root.withSource context raw).decoded.assignment = root.assignment ∧
      (root.withSource context raw).decoded.carriers = root.carriers ∧
      (root.withSource context raw).decoded.viewMeaning = root.viewMeaning ∧
      (root.withSource context raw).decoded.installed = root.installed :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The existing constructive original-declaration interpreter is not the
missing complete supplier: every callable result falls outside its documented
ground signature domain. This is a fact about that partial interpreter, not
a rejection rule or a counterexample to IF. All keys and annotation fields
are arbitrary; no toy declaration identity or semantic model is selected.
-/
theorem existing_interpreter_callable_result_absent
    {Key Effect Hole : Type} [DecidableEq Key] (keys : List Key)
    (declaration : PrimitiveOperation.Declaration Key Effect Hole)
    (argument parameter result : PrimitiveOperation.Annotation Effect Hole)
    (effects : Option Effect)
    (shape : declaration.signature =
      .function none argument (.function effects parameter result)) :
    PrimitiveOperation.interpret keys declaration = none := by
  simp only [PrimitiveOperation.interpret, shape, PrimitiveOperation.decode]
  cases PrimitiveOperation.number keys declaration.identity <;>
    cases PrimitiveOperation.primitive argument <;> rfl

end YulangClosure.AuthenticSourceGraphR299

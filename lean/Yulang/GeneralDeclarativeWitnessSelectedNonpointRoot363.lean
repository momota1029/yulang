import Yulang.GeneralDeclarativeWitnessLocatedElection363

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 76000
set_option maxHeartbeats 92000000
namespace Yulang.GeneralDeclarativeWitnessSelectedNonpointRoot363
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run)
open GeneralDeclarativeWitnessBackedNativeInput363 (Backed verify)
open GeneralDeclarativeWitnessNonpointGraph363 (Safe graph graph_exact_positive)
open GeneralDeclarativeWitnessLocatedElection363 (Chosen choose exact_compiler_must_use_chosen_row)
open GeneralDeclarativeWitnessNonpointPort362 (author frame env whereSource)
open GeneralDeclarativeWitnessCrossOwnerReceiver362 (asked layout native)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessNativePreparation360 (Layout Prepared prepare context)
open GeneralDeclarativeWitnessNativeInstall360 (World)
open GeneralDeclarativeWitnessCompiler350 (printDemand portNames trip)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)

def selectedLayout (w : World) {e : Environment} (chosen : Chosen e asked frame) : Layout :=
  {layout w with spans := chosen.fitBare.captures}

/-- The resolver's positive answer is checked before the compiler and
its capture list is given to the compiler. A later source-ordinal check
ties the preexisting answer to the emitted literal where clause. -/
structure Root {contra : Bool} (x : Ordered contra) (e : Environment) where
  ready : Backed x e
  noRecurrence : Safe x.after.final
  chosen : Chosen e asked frame
  body : Prepared e frame asked (selectedLayout x.after.final chosen)
  actual : body.impl = chosen.impl
  exactAuthor : body.impl = author
  occurrence : Demand
  ordered : body.kids = [occurrence]
  input : occurrence.arguments =
    [(portNames (context e asked body.impl (selectedLayout x.after.final chosen)) body.ports).input 90]

def emit {contra} (x : Ordered contra) (e : Environment) : Option (Root x e) := do
  let ready ← verify x e
  if acyclic : graph x.after.final then
    let success ← choose e asked frame
    let body ← prepare e frame asked (selectedLayout x.after.final success)
    if src : body.impl = author then
      match co : body.kids with
      | [child] =>
        have childArg : child.arguments =
            [(portNames (context e asked body.impl (selectedLayout x.after.final success)) body.ports).input 90] := by
          have described := congrArg (List.map Demand.arguments) co
          simpa [Prepared.kids,GeneralDeclarativeEmissionForest322.children,src,author,whereSource,
            GeneralDeclarativeSourceEmission322.demand,GeneralDeclarativeSourceEmission322.inputs,
            GeneralDeclarativeSourceEmission322.useArg,GeneralDeclarationPatterns.normalize] using described.symm
        some ⟨ready,graph_exact_positive acyclic,success,body,
          exact_compiler_must_use_chosen_row success body,src,child,co,childArg⟩
      | _ => none
    else none
  else none

def Root.world {contra x e} (r : @Root contra x e) : World := ⟨r.body.stage,x.after.final.board⟩

def Root.span {contra x e} (p : @Root contra x e) : Capture :=
  (portNames (context e asked p.body.impl (selectedLayout x.after.final p.chosen)) p.body.ports).input 90

def actual {contra x e} (r : @Root contra x e) : Bool :=
  decide (r.chosen.impl.id = 97 ∧ r.chosen.fitBare.binders = [90,91] ∧
    printDemand r.occurrence = (11,[(310,302,311)],[]))

theorem exact_authored_root (contra : Bool) :
    ((run contra).map fun x => (env.map fun e => ((emit x e).map actual).getD false).getD false).getD false = true := by
  cases contra <;> decide +kernel

end Yulang.GeneralDeclarativeWitnessSelectedNonpointRoot363

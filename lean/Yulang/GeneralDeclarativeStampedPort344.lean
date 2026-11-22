import Yulang.GeneralDeclarativeLiteralPorts344
import Yulang.GeneralDeclarativeAmbient344

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStampedPort344
open GeneralNominalCenters (Plan Site)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Registry)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeClauseBatch327 (Port)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeCommitPackage344 (Witness)
open GeneralDeclarativeCommitPosition344 (current_stamp clauses signature source_at)
open GeneralDeclarativeCommitSuffix344 (child_at)
open GeneralDeclarativeReplayOrder344 (actual_ports)
open GeneralDeclarativeLiteralPorts344 (Literal Rows read)
open GeneralDeclarativeRawCapture344 (rawCap)
open GeneralDeclarativeNormalizedPort344 (prepared_code)
open GeneralDeclarativeGrowth327 (facts trans)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeEmissionOperands322 (Compound)
open GeneralDeclarativeClausePlacement327 (portAt located)
open GeneralWhereVersionInstall317 (Journal InstallStep install emitted)
open GeneralWhereVersionCompiler317 (child children)

/-- Produces literal ordinary rows from a real commit and the computed
ordinary batch, with the plan-stamp, canonical clause position and
physical occurrence all explicit. One may retain each mode separately;
known equations alone do not create an authored input source. -/
theorem stamped_input {r : Registry} {before : Journal rs} {ctx : GeneralNominalCandidates.Context}
    {p : Plan rs} (taken : InstallStep r before (install before ctx p))
    {m n : Assignment} {keep : List Nat} {prepared s : State} {ports : List Port}
    {whereRows rootRows : List Equation}
    (w : Witness (install before ctx p) p m n keep prepared s ports whereRows rootRows)
    {ord : Nat} {site : Site rs} (emittedAt : (emitted p)[ord]? = some site) :
    ∃ c port, (clauses p)[ord]? = some c ∧ site = child p c.val (signature p c) ∧
      (install before ctx p).versionedWhere[before.versionedWhere.length]? = some p ∧
      (install before ctx p).mixed.core.sites[before.mixed.core.sites.length+ord]? = some site ∧
      (children p)[ord]? = some site.occurrence ∧
      portAt p.packet.declaration.requirements ports c.val = some port ∧
      ∀ idx pat, c.val.arguments[idx]? = some pat → Compound pat →
        ∃ code, port.code[idx]? = some code ∧
          translate p.packet.registry.constructors p.packet.context.interpretation (normalize pat) = some code ∧
          Rows s (rawCap p) (port.input idx) code := by
  have receipt := current_stamp r before ctx p taken n w.raw
  obtain ⟨c,canonical,childExact⟩ := source_at p emittedAt
  have listed := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr c.property
  obtain ⟨port,found,inputChecked,_⟩ := actual_ports p w.inputBatch c.val listed
  obtain ⟨localPort,localFound,exactWritten⟩ :=
    located (read w.inputBatch).2 p.packet.checked.identified.1 listed
  have eq : localPort = port := Option.some.inj (localFound.symm.trans found)
  subst localPort
  have staying := child_at receipt emittedAt
  refine ⟨c,port,canonical,childExact,receipt.stamp,staying.1,staying.2,found,?_⟩
  intro idx pat atPos complex
  obtain ⟨code,recorded,normal⟩ := prepared_code inputChecked atPos
  refine ⟨code,recorded,normal,?_⟩
  obtain ⟨lo,ctr,hi⟩ := exactWritten idx pat code atPos recorded complex
  have included : prepared.equations ⊆ s.equations := by
    rw [w.shape]
    exact fun _ row => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ row))
  exact ⟨included lo,included ctr,included hi⟩

end Yulang.GeneralDeclarativeStampedPort344

import Yulang.GeneralDeclarativeWitnessTypedSound354
import Yulang.GeneralDeclarativeWitnessCovariantBoundary352
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTypedLegacyCut354
open GeneralSourceMetadataRows291 (Row Source primitives invariants primitiveRows invariantRows interpretation)
open GeneralObservedMetadataOverlay290 (overlay)
open GeneralDeclarativeWitnessCovariantMetadata353 (Checked findRow)
open GeneralDeclarativeWitnessTypedChild354 (Linked)
open GeneralDeclarativeWitnessCompiler350 (fixedBatch portNames)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDictionaryAssociatedProvenance (lookup)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)

theorem exact_lookup {α : Type} (default : Nat → α) (f : Row → α)
    {rows : List Row} {name : Nat} {selected : Row}
    (found : rows.find? (fun x => x.key == name) = some selected) :
    overlay default (rows.map fun x => (x.key,f x)) name = f selected := by
  induction rows with
  | nil => cases found
  | cons x rest ih =>
    by_cases atKey : x.key = name
    · have e : x = selected := by simpa [List.find?_cons,atKey] using found
      cases e
      simp [overlay,atKey]
    · have showing : rest.find? (fun x => x.key == name) = some selected := by
        simpa [List.find?_cons,atKey] using found
      simpa [overlay,Ne.symm atKey] using ih showing

theorem source_not_invariant {p k} (m : Checked p k) :
    (interpretation m.source.snapshot).invariantNominal k = false ∧
    (interpretation m.source.snapshot).primitives k = none := by
  have previous := m.snapshot_row
  change m.source.snapshot.rows.find? (fun x => x.key == k) = some m.snapshot at previous
  change invariants m.source.snapshot k = false ∧ primitives m.source.snapshot k = none
  unfold invariants primitives invariantRows primitiveRows
  rw [exact_lookup _ _ previous,exact_lookup _ _ previous,m.snapshot_unclassified]
  exact ⟨rfl,rfl⟩

theorem old_output_is_absent {i s w} (b : Linked i s w) :
    one b.writer.output.source.ctx.registry b.writer.output.source.ctx.interp
      b.writer.output.source.ctx.decl b.writer.output.source.ctx.demand
      (portNames b.writer.output.source.ctx b.writer.output.ports).input b.emitted.atWrite.demand = none := by
  let out := b.emitted.atWrite.typed
  have old := source_not_invariant out.declared
  have same := Option.some.inj (out.declared.assembled.symm.trans b.writer.output.source.anchor.metadataProof.assembled)
  rw [same] at old
  change b.writer.output.source.ctx.interp.invariantNominal out.box = false ∧
    b.writer.output.source.ctx.interp.primitives out.box = none at old
  have absent := GeneralDeclarativeWitnessCovariantBoundary352.existing_tagged_source_reader_cannot_encode
    b.writer.output.source.ctx.registry.constructors b.writer.output.source.ctx.interp out.tag out.box out.binder
    old.1 old.2
  have shaped : translate b.writer.output.source.ctx.registry.constructors b.writer.output.source.ctx.interp
      (normalize out.authored.rhs) = none := by
    rw [out.written]
    exact absent
  have seen := out.found
  simp [one,seen,bodyPattern,shaped]

/-- This genuine checked typed writer cannot be replayed as an old
ordinary fixed batch with the same declared interpretation. -/
theorem old_fixed_batch_is_absent {i s w} (b : Linked i s w) :
    fixedBatch b.writer.output.source.ctx b.writer.output.ports = none := by
  cases legacy : fixedBatch b.writer.output.source.ctx b.writer.output.ports with
  | none => rfl
  | some rows =>
    unfold fixedBatch at legacy
    have included : b.emitted.atWrite.demand ∈ b.writer.output.source.ctx.demand.outputs :=
      List.mem_iff_getElem?.mpr ⟨_,b.emitted.atWrite.indexed⟩
    obtain ⟨_,ran,_⟩ := GeneralDeclarativeBatch320.collect_sound legacy _ included
    rw [old_output_is_absent b] at ran
    cases ran

end Yulang.GeneralDeclarativeWitnessTypedLegacyCut354

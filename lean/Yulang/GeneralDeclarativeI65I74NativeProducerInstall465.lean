import Yulang.GeneralDeclarativeI65I74NativeProducerPhaseOrigin465
import Yulang.GeneralDeclarativeI65I74ProjectionBatchInput464

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NativeProducer465
open Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessAssociatedDescriptor359 (Described describe Wire)
open GeneralDeclarativeWitnessNativePreparation360 (Prepared)
open GeneralDeclarativeWitnessNativeValue360 (Compiled compile associates Write)
open GeneralDeclarativeWitnessNativeInstall360 (Board World Committed install current check_exact no_ordinary_override)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority)
open NamedProjection464 (exactOrdinaryState exact_ordinary_snapshot_iff)

theorem exact_authored_description_replays {e table frames key d wire}
    (a : Described e table frames key d wire) : describe e table frames key d wire = some a := by
  rcases a with ⟨declaration,located,identity,unique,requested,indexed,fixed,licensed,authored,
    lookup,eq,written,endpoint,compilation⟩
  unfold describe
  split
  · rename_i missing; rw [located] at missing; cases missing
  · rename_i seen read
    have agree := Option.some.inj (read.symm.trans located)
    subst seen
    simp only [dite_eq_left identity,dite_eq_left unique]
    split
    · rename_i absent; rw [indexed] at absent; cases absent
    · rename_i out index
      have agree := Option.some.inj (index.symm.trans indexed)
      subst out
      simp only [dite_eq_left fixed,dite_eq_left licensed]
      split
      · rename_i body present
        have agree := Option.some.inj (present.symm.trans lookup)
        have eqBody := GeneralDictionaryAssociatedProvenance.Body.explicit.inj agree
        subst body
        simp only [dite_eq_left eq,dite_eq_left written]
        split
        · rename_i actual got
          cases Option.some.inj (got.symm.trans compilation)
          rfl
        · rename_i bad
          rw [compilation] at bad
          cases bad
      · rename_i unavailable
        exact (unavailable authored lookup).elim

theorem actual_native_compilation_replays_from_independent_described_code
    {e frame d layout table w v} {p : Prepared e frame d layout}
    (compiled : Compiled p table w v) : compile p table w v = some compiled := by
  rcases compiled with ⟨description,identity,code,emitted⟩
  have same : associates p table w = some description := exact_authored_description_replays description
  simp only [compile,same]
  split
  · rename_i absent; rw [emitted] at absent; cases absent
  · rename_i read seen
    cases Option.some.inj (seen.symm.trans emitted)
    rfl

theorem compiler_install_exactly_commits_given_actual_source
    {e frame d layout table w version} {p : Prepared e frame d layout}
    (compiled : Compiled p table w version) (board : Board) :
    install p compiled board = some (current p board compiled.write) ↔
    Committed board compiled.write := by
  simp [install,check_exact]

/-- Call the actual existing producer, install its exact Write in the
supplied active board, and then link that precise phase to the source
ledger's already-issued row. No primary path or native issuer is chosen
here, and there is no fallback that synthesizes missing source origins. -/
def checkProducedOrigin {s : GeneralDeclarativeI65.State} {frame d layout}
    (prepared : Prepared s.current.environment frame d layout)
    (base : Board) (gate : ReleaseAuthority) (w : Wire) (version logical ordinal : Nat) : Bool :=
  match compile prepared s.modes w version with
  | none => false
  | some authored =>
    match install prepared authored base with
    | none => false
    | some world =>
      if phase : exactOrdinaryState world.ordinary s.current.ordinary = true then
        checkPhaseOrigin ⟨world,(exact_ordinary_snapshot_iff ..).mp phase,gate⟩ authored.write logical ordinal
      else false

def ProducedAndPlaced {s : GeneralDeclarativeI65.State} {frame d layout}
    (prepared : Prepared s.current.environment frame d layout)
    (base : Board) (gate : ReleaseAuthority) (w : Wire) (version logical ordinal : Nat) : Prop :=
  ∃ source : Compiled prepared s.modes w version,
    Committed base source.write ∧
    ∃ samePhase : prepared.stage = s.current.ordinary,
      PhaseOriginAt ⟨current prepared base source.write,samePhase,gate⟩ source.write logical ordinal

theorem actual_producer_and_same_phase_placement_iff_finite_data
    {s : GeneralDeclarativeI65.State} {frame d layout}
    (p : Prepared s.current.environment frame d layout) (base : Board) (gate : ReleaseAuthority)
    (w : Wire) (version logical ordinal : Nat) :
    checkProducedOrigin p base gate w version logical ordinal = true ↔
      ProducedAndPlaced p base gate w version logical ordinal := by
  constructor
  · intro accepted
    cases comp : compile p s.modes w version with
    | none => simp [checkProducedOrigin,comp] at accepted
    | some code =>
      by_cases inBoard : Committed base code.write
      · have run := (compiler_install_exactly_commits_given_actual_source code base).mpr inBoard
        by_cases together : p.stage = s.current.ordinary
        · have cond : exactOrdinaryState (current p base code.write).ordinary s.current.ordinary = true :=
            (exact_ordinary_snapshot_iff ..).mpr together
          have precise : checkPhaseOrigin ⟨current p base code.write,together,gate⟩
              code.write logical ordinal = true := by simpa [checkProducedOrigin,comp,run,cond] using accepted
          exact ⟨code,inBoard,together,(finite_phase_origin_check_iff_literal_placed_active_row ..).mp precise⟩
        · have cond : exactOrdinaryState (current p base code.write).ordinary s.current.ordinary ≠ true :=
            fun same => together ((exact_ordinary_snapshot_iff ..).mp same)
          simp [checkProducedOrigin,comp,run,cond] at accepted
      · have absent : install p code base = none := by
          have no : GeneralDeclarativeWitnessNativeInstall360.check base code.write ≠ true :=
            fun yes => inBoard (check_exact.mp yes)
          simp [install,no]
        simp [checkProducedOrigin,comp,absent] at accepted
  · rintro ⟨source,inBoard,same,authentic⟩
    have comp := actual_native_compilation_replays_from_independent_described_code source
    have run := (compiler_install_exactly_commits_given_actual_source source base).mpr inBoard
    have phase : exactOrdinaryState (current p base source.write).ordinary s.current.ordinary = true :=
      (exact_ordinary_snapshot_iff ..).mpr same
    have ok := (finite_phase_origin_check_iff_literal_placed_active_row ..).mpr authentic
    simp [checkProducedOrigin,comp,run,phase,ok]

theorem checked_installed_origin_is_really_the_original_compiler_payload
    {s : GeneralDeclarativeI65.State} {frame d layout}
    {p : Prepared s.current.environment frame d layout} {base : Board} {gate : ReleaseAuthority}
    {w : Wire} {version logical ordinal : Nat}
    (pass : checkProducedOrigin p base gate w version logical ordinal = true) :
    ∃ c : Compiled p s.modes w version,
      s.origins[ordinal]? = some (originalOfWrite c.write) ∧
      OriginRoute s (originalOfWrite c.write) logical ∧
      c.write.address.target = w.target ∧ c.write.address.owner.path = frame.occurrence ∧
      EmittedSyntax (originalOfWrite c.write).endpoint := by
  obtain ⟨c,_,_,placed,route,_⟩ := (actual_producer_and_same_phase_placement_iff_finite_data ..).mp pass
  exact ⟨c,placed,route,rfl,rfl,every_emitted_node_has_its_literal_compiler_grammar c.code⟩

end Yulang.GeneralDeclarativeI65.I72.NativeProducer465

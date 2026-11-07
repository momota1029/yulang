import Yulang.CommonSymbolicRecordProfiles
import Yulang.CommonPresenceConstraintGraph
import Yulang.CommonRecordTargetProfiles

/-!
# Symbolic profiles of actual shared source nodes

The existing collector supplies every identifier. No assignment is read by
`ofNode`, and a proper child or same-depth reference is never reallocated.
The lowering has literal equality with the independently interpreted source
equation body, before imposing any equation or invoking a solver.

For an arbitrary realization of those source equations, the compiled field
and optional profiles describe all node observations. Realizers are related
by demand equivalence, not by equality of their projected syntax.
-/

namespace Yulang.CommonSymbolicSourceProfiles

open Common (Ty Row)
open Core.PresenceGeneration (TyTerm RowTerm)
open PresenceOpenTailGenerationLowering (Pool subterms)
open CommonSymbolicRecordProfiles

variable {m : Nat}

/-- Actual source constructor syntax, with the original shared identifiers
in both same-depth and guarded positions. Arrow rows keep their input IDs. -/
def ofNode (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    OpenLayer (RowTerm (Fin m)) (Fin pool.size) (Fin pool.size) :=
  match term with
  | .var index => .ref (pool.input index)
  | .base scalar => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union first last =>
      .union (.ref (pool.child _ member first (by simp [subterms])))
        (.ref (pool.child _ member last (by simp [subterms])))
  | .inter first last =>
      .inter (.ref (pool.child _ member first (by simp [subterms])))
        (.ref (pool.child _ member last (by simp [subterms])))
  | .pair first last =>
      .pair (pool.child _ member first (by simp [subterms]))
        (pool.child _ member last (by simp [subterms]))
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .required label payload =>
      .record label (pool.child _ member payload (by simp [subterms])) .emptyRecord
  | .record label payload tail =>
      .record label (pool.child _ member payload (by simp [subterms]))
        (.ref (pool.child _ member tail (by simp [subterms])))
  | .recordDefault label source fallback =>
      .recordDefault label (.ref (pool.child _ member source (by simp [subterms])))
        (pool.child _ member fallback (by simp [subterms]))
  | .variant label payload => .variant label (pool.child _ member payload (by simp [subterms]))
  | .arrow input incoming output outgoing =>
      .arrow (pool.child _ member input (by simp [subterms])) incoming
        (pool.child _ member output (by simp [subterms])) outgoing

theorem ofNode_eval (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) :
    (ofNode pool term member).eval (CommonPresenceConstraintGraph.rowEval rows) values values =
      (CommonPresenceConstraintGraph.lowerNode pool term member).eval rows values := by
  cases term <;> rfl

def ofSlot (pool : Pool m) (slot : Fin pool.size) :
    OpenLayer (RowTerm (Fin m)) (Fin pool.size) (Fin pool.size) :=
  ofNode pool (pool.termAt slot) (pool.at_mem slot)

theorem ofSlot_eval (pool : Pool m) (slot : Fin pool.size)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) :
    (ofSlot pool slot).eval (CommonPresenceConstraintGraph.rowEval rows) values values =
      (CommonPresenceConstraintGraph.graph pool slot).eval rows values :=
  ofNode_eval pool _ _ rows values

def compileNode (pool : Pool m) (hidden : List Nat) (label : Nat)
    (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    Summary (Fin pool.size) (Fin pool.size) :=
  compile hidden label (ofNode pool term member)

def compileSlot (pool : Pool m) (hidden : List Nat) (label : Nat) (slot : Fin pool.size) :
    Summary (Fin pool.size) (Fin pool.size) :=
  compile hidden label (ofSlot pool slot)

/-- Independent assignments are unrestricted; the theorem is about the
original constructor body's interpretation, not an assumed solution. -/
theorem compileNode_exact (pool : Pool m) (hidden : List Nat) (label : Nat)
    (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) :
    (compileNode pool hidden label term member).eval values values =
      meaning hidden label ((CommonPresenceConstraintGraph.lowerNode pool term member).eval rows values) := by
  exact (compile_exact (CommonPresenceConstraintGraph.rowEval rows) values values hidden label _).trans
    (congrArg (meaning hidden label) (ofNode_eval pool term member rows values))

theorem compileSlot_exact (pool : Pool m) (hidden : List Nat) (label : Nat)
    (slot : Fin pool.size) (rows : Fin m → Row) (values : Fin pool.size → Ty) :
    (compileSlot pool hidden label slot).eval values values =
      meaning hidden label ((CommonPresenceConstraintGraph.graph pool slot).eval rows values) :=
  compileNode_exact pool hidden label _ _ rows values

/-- Equivalence is transported through the same outer mask and through all
depths and negative ranks. No literal equality of projected types is used. -/
theorem masked_probe_congr {first last : Ty} (same : Common.Equivalent first last)
    (hidden : List Nat) (depth rank : Nat) (env : CommonFinite.Environment Row)
    (obs : Common.Observation) :
    CommonFinite.MaskedProbeAt Common.rowLe rank env hidden (Common.observeTy depth first) obs ↔
      CommonFinite.MaskedProbeAt Common.rowLe rank env hidden (Common.observeTy depth last) obs := by
  have changed := Common.common_mask_type_congr hidden same
  have forward := (CommonFinite.producerLe_iff_probe _ _).mp (changed.2 depth) rank env obs
  have backward := (CommonFinite.producerLe_iff_probe _ _).mp (changed.1 depth) rank env obs
  have probes : CommonFinite.ProbeAt Common.rowLe rank env (Common.observeTy depth (Common.mask hidden first)) obs ↔
      CommonFinite.ProbeAt Common.rowLe rank env (Common.observeTy depth (Common.mask hidden last)) obs :=
    ⟨forward, backward⟩
  simpa only [Common.observeTy, Common.mask, CommonSyntax.Layer.evalAt, CommonFinite.probeAt_mask] using probes

theorem realized_field_profile_exact (pool : Pool m) (rows : Fin m → Row)
    (values : Fin pool.size → Ty) (realizes : CommonPresenceConstraintGraph.Realizes pool rows values)
    (slot : Fin pool.size) (hidden : List Nat) (label depth rank : Nat)
    (env : CommonFinite.Environment Row) (obs : Common.Observation) :
    CommonFinite.MaskedProbeAt Common.rowLe rank env hidden
        (Common.observeTy (depth + 1) (values slot)) (.field label obs) ↔
      CommonPayloadProjection.ProfileAt depth rank env
        ((compileSlot pool hidden label slot).field.eval values values) obs := by
  have compiled := congrArg Meaning.field (compileSlot_exact pool hidden label slot rows values)
  change (compileSlot pool hidden label slot).field.eval values values = _ at compiled
  rw [compiled]
  exact (masked_probe_congr (Common.equivalent_symm (realizes slot)) hidden (depth + 1) rank env _).trans
    (CommonPayloadProjection.field_type_exact hidden label _ depth rank env obs)

theorem realized_optional_profile_exact (pool : Pool m) (rows : Fin m → Row)
    (values : Fin pool.size → Ty) (realizes : CommonPresenceConstraintGraph.Realizes pool rows values)
    (slot : Fin pool.size) (hidden : List Nat) (label depth rank : Nat)
    (env : CommonFinite.Environment Row) (obs : Common.Observation) :
    CommonFinite.MaskedProbeAt Common.rowLe rank env hidden
        (Common.observeTy (depth + 1) (values slot)) (.optional label obs) ↔
      CommonPayloadProjection.ProfileAt depth rank env
        ((compileSlot pool hidden label slot).optional.eval values values) obs := by
  have compiled := congrArg Meaning.optional (compileSlot_exact pool hidden label slot rows values)
  change (compileSlot pool hidden label slot).optional.eval values values = _ at compiled
  rw [compiled]
  exact (masked_probe_congr (Common.equivalent_symm (realizes slot)) hidden (depth + 1) rank env _).trans
    (CommonPayloadProjection.optional_type_exact hidden label _ depth rank env obs)

theorem presence_congr {first last : Ty} (same : Common.Equivalent first last)
    (hidden : List Nat) (label : Nat) :
    CommonDefaultRequired.fieldPresence hidden label first =
      CommonDefaultRequired.fieldPresence hidden label last := by
  let env : CommonFinite.Environment Row := ⟨fun _ => .bottom, fun _ => []⟩
  have positive (source : Ty) :
      CommonFinite.MaskedProbeAt Common.rowLe 0 env hidden (Common.observeTy 1 source) (.field label .trivial) ↔
        CommonDefaultRequired.fieldPresence hidden label source = true :=
    CommonDefaultRequired.fieldPresence_exact Common.rowLe env _ _ 0 hidden label source
  have truth := (positive first).symm.trans
    ((masked_probe_congr same hidden 1 0 env (.field label .trivial)).trans (positive last))
  simpa using truth

theorem realized_presence_exact (pool : Pool m) (rows : Fin m → Row)
    (values : Fin pool.size → Ty) (realizes : CommonPresenceConstraintGraph.Realizes pool rows values)
    (slot : Fin pool.size) (hidden : List Nat) (label : Nat) :
    (compileSlot pool hidden label slot).present.eval values =
      CommonDefaultRequired.fieldPresence hidden label (values slot) :=
  (congrArg Meaning.present (compileSlot_exact pool hidden label slot rows values)).trans
    (presence_congr (realizes slot) hidden label)

/-- The actual finite profile expression is the only field obligation. It
already contains unknown-presence choices and whole-default fallback tests. -/
theorem required_exact (rows : Rows → Row) (nodes : Node → Ty) (children : Child → Ty)
    (source : OpenLayer Rows Node Child) (label : Nat) (payload : CommonPayloadProjection.Payload Child) :
    Common.Subtype (source.eval rows nodes children) (Common.required label (payload.evalLayer children)) ↔
      CommonPayloadProjection.ProfileBelow ((compile [] label source).field.eval nodes children)
        (payload.evalLayer children) := by
  rw [compile_field_exact]
  exact CommonRecordTargetProfiles.subtype_required_iff _ _ label

theorem emptyRecord_exact (rows : Rows → Row) (nodes : Node → Ty) (children : Child → Ty)
    (source : OpenLayer Rows Node Child) :
    Common.Subtype (source.eval rows nodes children) Common.emptyRecord ↔
      (compile [] 0 source).records.eval nodes = true := by
  have shaped := congrArg Meaning.records (compile_exact rows nodes children [] 0 source)
  change (compile [] 0 source).records.eval nodes = _ at shaped
  rw [shaped]
  exact CommonRecordTargetProfiles.subtype_emptyRecord_iff _

/-- Every actual packed source node is compiled with its original children,
for arbitrary independent rows and values; no `Realizes` premise is needed. -/
theorem node_required_exact (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) (label : Nat)
    (payload : CommonPayloadProjection.Payload (Fin pool.size)) :
    Common.Subtype ((CommonPresenceConstraintGraph.lowerNode pool term member).eval rows values)
        (Common.required label (payload.evalLayer values)) ↔
      CommonPayloadProjection.ProfileBelow ((compileNode pool [] label term member).field.eval values values)
        (payload.evalLayer values) := by
  rw [← ofNode_eval]
  exact required_exact (CommonPresenceConstraintGraph.rowEval rows) values values _ label payload

theorem node_emptyRecord_exact (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) :
    Common.Subtype ((CommonPresenceConstraintGraph.lowerNode pool term member).eval rows values) Common.emptyRecord ↔
      (compileNode pool [] 0 term member).records.eval values = true := by
  rw [← ofNode_eval]
  exact emptyRecord_exact (CommonPresenceConstraintGraph.rowEval rows) values values _

/-- The source equation is used only for equivalence transport. Every
regular realizer of the original equations is covered, not just one solver's
canonical interpretation. -/
theorem realized_required_exact (pool : Pool m) (rows : Fin m → Row)
    (values : Fin pool.size → Ty) (realizes : CommonPresenceConstraintGraph.Realizes pool rows values)
    (slot : Fin pool.size) (label : Nat) (payload : CommonPayloadProjection.Payload (Fin pool.size)) :
    Common.Subtype (values slot) (Common.required label (payload.evalLayer values)) ↔
      CommonPayloadProjection.ProfileBelow ((compileSlot pool [] label slot).field.eval values values)
        (payload.evalLayer values) := by
  have compiled := node_required_exact pool (pool.termAt slot) (pool.at_mem slot) rows values label payload
  constructor
  · intro below
    exact compiled.mp (Common.subtype_trans (realizes slot).1 below)
  · intro inspected
    exact Common.subtype_trans (realizes slot).2 (compiled.mpr inspected)

theorem realized_emptyRecord_exact (pool : Pool m) (rows : Fin m → Row)
    (values : Fin pool.size → Ty) (realizes : CommonPresenceConstraintGraph.Realizes pool rows values)
    (slot : Fin pool.size) :
    Common.Subtype (values slot) Common.emptyRecord ↔
      (compileSlot pool [] 0 slot).records.eval values = true := by
  have compiled := node_emptyRecord_exact pool (pool.termAt slot) (pool.at_mem slot) rows values
  constructor
  · intro below
    exact compiled.mp (Common.subtype_trans (realizes slot).1 below)
  · intro inspected
    exact Common.subtype_trans (realizes slot).2 (compiled.mpr inspected)

end Yulang.CommonSymbolicSourceProfiles

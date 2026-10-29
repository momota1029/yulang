import YulangClosure.FormalPermissionAuthenticatedNativeDecode

/-! R6 successful source transcription, ending at candidate_formal_value_pair
return. This is not a Rust execution relation. Successful reserve/copy/term
helpers and the erasure of their effects on the projected coordinates remain
an execution-to-transcription obligation. Error paths and enclosing annotation
link admission/propagation are outside this cut. -/
namespace YulangClosure.FormalPermissionSourceAllocation
open FormalPermissionSourceOrigin FormalPermissionCaptureConstruction
open FormalPermissionConstructorRealization FormalPermissionExportWitness
open FormalPermissionSiteTraversal
open FormalPermissionLiveCapture (prependPath atPort shift)
noncomputable section

/-- Successful reservation capacity conditions. Preservation of contents by
Rust Vec::try_reserve is part of the execution-to-transcription bridge.
No assertion that a real allocator will return successfully is made. -/
structure Reserved (length : Nat) where
  oldCapacity : Nat
  capacity : Nat
  oldFits : length ≤ oldCapacity
  monotone : oldCapacity ≤ capacity
  slot : length + 1 ≤ capacity

/-- Four successful reservations following the successful u32 conversion.
These are witnesses for a successful path, not availability guarantees. -/
structure FreshReady (length : Nat) where
  ordinalFits : length < 2^32
  bounds : Reserved length
  levels : Reserved length
  metadata : Reserved length
  marks : Reserved length

/-- The four vectors are aligned on entry, and each successful push appends
one entry. Payload contents are immaterial to the allocator coordinate. -/
theorem fresh_success_ordinal {α β γ δ : Type} (bounds : List α)
    (levels : List β) (metadata : List γ) (marks : List δ)
    (b : α) (l : β) (m : γ) (z : δ)
    (_ready : FreshReady bounds.length)
    (hl : levels.length = bounds.length)
    (hm : metadata.length = bounds.length)
    (hz : marks.length = bounds.length) :
    bounds.length < 2^32 ∧
    (bounds ++ [b]).length = bounds.length + 1 ∧
    (levels ++ [l]).length = bounds.length + 1 ∧
    (metadata ++ [m]).length = bounds.length + 1 ∧
    (marks ++ [z]).length = bounds.length + 1 := by
  exact ⟨_ready.ordinalFits, by simp, by simp [hl], by simp [hm], by simp [hz]⟩

/-- Project effect-row count and a local retained-permission delta. The full
preexisting permission prefix is not included: preservation and reattachment
of that prefix belong to the execution bridge. Real resource counters,
capacities, terms and callbacks are not modeled by this projection. -/
structure Projection where
  effectLength : Nat
  permissions : List Retained

/-- This premise must be supplied for each executed nonallocating helper.
It is deliberately an explicit equality, not a concrete helper instance. -/
inductive HelperFrames : Projection → Projection → Prop where
  | nil (s : Projection) : HelperFrames s s
  | cons {s m t : Projection} (rows : s.effectLength = m.effectLength)
      (entries : s.permissions = m.permissions) (rest : HelperFrames m t) :
      HelperFrames s t

theorem nonallocating_helpers_frame {s t : Projection} (frames : HelperFrames s t) :
    s.effectLength = t.effectLength ∧ s.permissions = t.permissions := by
  induction frames with
  | nil => exact ⟨rfl, rfl⟩
  | cons rows entries rest ih => exact ⟨rows.trans ih.1, entries.trans ih.2⟩

/-- Chronological fresh ordinals: append composes exactly at the prior end. -/
inductive AllocationTrace : Nat → List Nat → Nat → Prop where
  | nil (n : Nat) : AllocationTrace n [] n
  | step (n : Nat) {xs : List Nat} {last : Nat}
      (tail : AllocationTrace (n + 1) xs last) : AllocationTrace n (n :: xs) last

theorem AllocationTrace.append {n m k : Nat} {xs ys : List Nat}
    (a : AllocationTrace n xs m) (b : AllocationTrace m ys k) :
    AllocationTrace n (xs ++ ys) k := by
  revert b
  induction a with
  | nil => intro b; exact b
  | step n tail ih => intro b; exact .step n (ih b)

/-- Independent four-Vec allocator data; permissions are a separate sequence.
The projection forgets payloads but the transition below actually appends. -/
structure Allocator where
  bounds : List Unit
  levels : List Nat
  metadata : List Unit
  marks : List Nat
  permissions : List Retained

def Allocator.push (a : Allocator) (level : Nat) : Allocator :=
  { a with
    bounds := a.bounds ++ [()]
    levels := a.levels ++ [level]
    metadata := a.metadata ++ [()]
    marks := a.marks ++ [0] }

structure FreshStep (n : Nat) where
  before : Allocator
  level : Nat
  length : before.bounds.length = n
  levelsAligned : before.levels.length = before.bounds.length
  metadataAligned : before.metadata.length = before.bounds.length
  marksAligned : before.marks.length = before.bounds.length
  ready : FreshReady before.bounds.length

def FreshStep.ordinal {n : Nat} (a : FreshStep n) : Nat := a.before.bounds.length
def FreshStep.next {n : Nat} (a : FreshStep n) : Nat := (a.before.push a.level).bounds.length

theorem fresh_step_equations {n : Nat} (a : FreshStep n) :
    a.ordinal = n ∧ a.next = n + 1 ∧
    (a.before.push a.level).permissions = a.before.permissions := by
  have pushes := fresh_success_ordinal a.before.bounds a.before.levels
    a.before.metadata a.before.marks () a.level () 0 a.ready
    a.levelsAligned a.metadataAligned a.marksAligned
  exact ⟨a.length, pushes.2.1.trans (congrArg (fun k => k + 1) a.length), rfl⟩

/-- Port output is derived from the independent Vec push and then the supplied
helper frame, including preservation of the permission delta. No concrete
Rust helper is asserted to inhabit that frame. -/
inductive SourcePortSuccess (c : Context) : Bool → Option SourceRow → State →
    SourcePort → PortResult → List Nat → Prop where
  | omitted (p : Bool) (s : State) (allocation : FreshStep s.nextEffect)
      (finish : Projection)
      (helpers : HelperFrames ⟨allocation.next, []⟩ finish) :
      SourcePortSuccess c p none s .omitted
        ⟨sharedPorts allocation.ordinal, finish.permissions.map (fun e => ⟨e.metadata, e.allocatedRow⟩), [],
          {s with nextEffect := finish.effectLength}⟩ [allocation.ordinal]
  | concrete (s : State) (row : SourceRow) (allocation : FreshStep s.nextEffect)
      (nonempty : row.concrete ≠ []) (noVariables : row.variables = [])
      (finish : Projection)
      (helpers : HelperFrames
        ⟨allocation.next, [⟨c.metadata row.position row.concrete, [], allocation.ordinal⟩]⟩ finish) :
      SourcePortSuccess c false (some row) s (.explicit row.position row.concrete none)
        ⟨sharedPorts allocation.ordinal (some (c.metadata row.position row.concrete)),
          finish.permissions.map (fun e => ⟨e.metadata, e.allocatedRow⟩), [],
          {s with nextEffect := finish.effectLength}⟩ [allocation.ordinal]

theorem source_port_event {c : Context} {p : Bool} {row : Option SourceRow} {s : State}
    {code : SourcePort} {out : PortResult} {births : List Nat}
    (run : SourcePortSuccess c p row s code out births) :
    PortEvent c p code s out births := by
  cases run with
  | omitted p s allocation finish helpers =>
      obtain ⟨rows, entries⟩ := nonallocating_helpers_frame helpers
      obtain ⟨ordinal, next, _⟩ := fresh_step_equations allocation
      simp only at rows entries
      rw [← rows, ← entries, ordinal, next]
      exact .omitted p s
  | concrete s row allocation nonempty noVariables finish helpers =>
      obtain ⟨rows, entries⟩ := nonallocating_helpers_frame helpers
      obtain ⟨ordinal, next, _⟩ := fresh_step_equations allocation
      simp only at rows entries
      rw [← rows, ← entries, ordinal, next]
      exact .concrete s row.position row.concrete nonempty

/-- Ordered source Vec guard, independently of decoder success. -/
def NoElementEffects : Annotations → Prop
  | .nil => True
  | .cons a rest => a.effects = none ∧ NoElementEffects rest

/- These constructors transcribe successful source calls. Helper calls are
projected away, conditional on their explicit HelperFrames obligations above.
Int/Unit alone inhabit the atomic fragment. Top rows are retained in Annotation
but are read only when that node is a Function port. -/
mutual
  inductive SourcePair (c : Context) : (p : Bool) → Annotation → ValueCode →
      (s : State) → ValueDecoded c p s → Prop where
    | int (p : Bool) (s : State) (row : Option SourceRow)
        (helpers : HelperFrames ⟨s.nextEffect, []⟩ ⟨s.nextEffect, []⟩) :
        SourcePair c p (.leaf row .int) (.scalar 0) s
          ⟨.atom 0, [], s, [], .scalar p s 0⟩
    | unit (p : Bool) (s : State) (row : Option SourceRow)
        (helpers : HelperFrames ⟨s.nextEffect, []⟩ ⟨s.nextEffect, []⟩) :
        SourcePair c p (.leaf row .unit) (.scalar 1) s
          ⟨.atom 1, [], s, [], .scalar p s 1⟩
    | function {p : Bool} {s : State} {a r : Annotation} {ac rc : ValueCode}
        {av : ValueDecoded c (!p) s} {rv : ValueDecoded c p av.state}
        {ae re : SourcePort} {ao ro : PortResult} {ab rb : List Nat}
        (row : Option SourceRow)
        (argument : SourcePair c (!p) a ac s av)
        (result : SourcePair c p r rc av.state rv)
        (argumentEffect : SourcePortSuccess c (!p) a.effects rv.state ae ao ab)
        (resultEffect : SourcePortSuccess c p r.effects ao.state re ro rb)
        (helpers : HelperFrames
          ⟨ro.state.nextEffect, prependPath .argument av.entries ++ prependPath .result rv.entries ++
            atPort .argument ao.entries ++ atPort .result ro.entries⟩
          ⟨ro.state.nextEffect, prependPath .argument av.entries ++ prependPath .result rv.entries ++
            atPort .argument ao.entries ++ atPort .result ro.entries⟩) :
        SourcePair c p (.function row a r) (.function ac rc ae re) s
          ⟨.function av.shape ao.ports rv.shape ro.ports,
            prependPath .argument av.entries ++ prependPath .result rv.entries ++
              atPort .argument ao.entries ++ atPort .result ro.entries,
            ro.state, av.births ++ rv.births ++ ab ++ rb,
            .function av.events rv.events (source_port_event argumentEffect) (source_port_event resultEffect)⟩
    | tuple {p : Bool} {s : State} {xs : Annotations} {cs : TupleCode}
        {out : TupleDecoded c p s} (row : Option SourceRow)
        (children : SourceTuples c p xs cs s out)
        (guard : NoElementEffects xs) (nonempty : out.elements ≠ [])
        (helpers : HelperFrames ⟨out.state.nextEffect, out.entries⟩ ⟨out.state.nextEffect, out.entries⟩) :
        SourcePair c p (.tuple row xs) (.tuple cs) s
          ⟨.tuple out.elements, out.entries, out.state, out.births,
            .tuple out.events nonempty⟩
  inductive SourceTuples (c : Context) : (p : Bool) → Annotations → TupleCode →
      (s : State) → TupleDecoded c p s → Prop where
    | nil (p : Bool) (s : State) : SourceTuples c p .nil .nil s ⟨[], [], s, [], .nil p s⟩
    | cons {p : Bool} {s : State} {a : Annotation} {xs : Annotations}
        {ac : ValueCode} {cs : TupleCode} {av : ValueDecoded c p s}
        {rest : TupleDecoded c p av.state}
        (head : SourcePair c p a ac s av) (tail : SourceTuples c p xs cs av.state rest) :
        SourceTuples c p (.cons a xs) (.cons ac cs) s
          ⟨av.shape :: rest.elements, prependPath (.element 0) av.entries ++ shift rest.entries,
            rest.state, av.births ++ rest.births, .cons av.events rest.events⟩
end

theorem port_decoder {c : Context} {p : Bool} {row : Option SourceRow} {s : State}
    {code : SourcePort} {out : PortResult} {births : List Nat}
    (run : SourcePortSuccess c p row s code out births) :
    ∃ d, decodePort c p code s = some d ∧ d.out = out ∧ d.births = births := by
  cases run with
  | omitted p s allocation finish helpers =>
      obtain ⟨rows, entries⟩ := nonallocating_helpers_frame helpers
      obtain ⟨ordinal, next, _⟩ := fresh_step_equations allocation
      simp only at rows entries
      rw [← rows, ← entries, ordinal, next]
      exact ⟨_, rfl, rfl, rfl⟩
  | concrete s row allocation nonempty noVariables finish helpers =>
      obtain ⟨rows, entries⟩ := nonallocating_helpers_frame helpers
      obtain ⟨ordinal, next, _⟩ := fresh_step_equations allocation
      simp only at rows entries
      rw [← rows, ← entries, ordinal, next]
      simp [decodePort, nonempty]

theorem source_port_allocation {c : Context} {p : Bool} {row : Option SourceRow}
    {s : State} {code : SourcePort} {out : PortResult} {births : List Nat}
    (run : SourcePortSuccess c p row s code out births) :
    AllocationTrace s.nextEffect births out.state.nextEffect := by
  cases run with
  | omitted p s allocation finish helpers =>
      obtain ⟨rows, _⟩ := nonallocating_helpers_frame helpers
      obtain ⟨ordinal, next, _⟩ := fresh_step_equations allocation
      simp only at rows
      rw [← rows, ordinal, next]
      exact .step _ (.nil _)
  | concrete s row allocation nonempty noVariables finish helpers =>
      obtain ⟨rows, _⟩ := nonallocating_helpers_frame helpers
      obtain ⟨ordinal, next, _⟩ := fresh_step_equations allocation
      simp only at rows
      rw [← rows, ordinal, next]
      exact .step _ (.nil _)

/-- Both motives quantify polarity and all changing indices. The induction is
on source derivations, so Function arguments use the reversed polarity and
sequential child states directly; no code-size recursive wrapper is used. -/
private theorem source_pair_checks {c : Context} {p : Bool} {a : Annotation}
    {code : ValueCode} {s : State} {out : ValueDecoded c p s}
    (run : SourcePair c p a code s out) :
    decodeValue c p s code = some out ∧
      AllocationTrace s.nextEffect out.births out.state.nextEffect := by
  induction run using SourcePair.rec
    (motive_2 := fun p _ code s out _ =>
      decodeTuple c p s code = some out ∧
        AllocationTrace s.nextEffect out.births out.state.nextEffect) with
  | int => exact ⟨rfl, .nil _⟩
  | unit => exact ⟨rfl, .nil _⟩
  | function row argument result ae re helpers argumentIH resultIH =>
      constructor
      · obtain ⟨ad, had, hao, hab⟩ := port_decoder ae
        -- Eliminate the first output equality before constructing a witness
        -- whose type depends on its state. This transports the entire context.
        cases hao
        obtain ⟨rd, hrd, hro, hrb⟩ := port_decoder re
        cases hro
        cases hab
        cases hrb
        simp [decodeValue, argumentIH.1, resultIH.1, had, hrd]
      · exact ((argumentIH.2.append resultIH.2).append
          (source_port_allocation ae)).append (source_port_allocation re)
  | tuple row children guard nonempty helpers childrenIH =>
      exact ⟨by simp [decodeValue, childrenIH.1, nonempty], childrenIH.2⟩
  | nil => exact ⟨rfl, .nil _⟩
  | cons head tail headIH tailIH =>
      exact ⟨by simp [decodeTuple, headIH.1, tailIH.1], headIH.2.append tailIH.2⟩

/-- The companion elimination uses the same paired motives, with context fixed
and polarity, annotations, code, entry state and output all varying. -/
private theorem source_tuples_checks {c : Context} {p : Bool} {xs : Annotations}
    {code : TupleCode} {s : State} {out : TupleDecoded c p s}
    (run : SourceTuples c p xs code s out) :
    decodeTuple c p s code = some out ∧
      AllocationTrace s.nextEffect out.births out.state.nextEffect := by
  induction run using SourceTuples.rec
    (motive_1 := fun p _ code s out _ =>
      decodeValue c p s code = some out ∧
        AllocationTrace s.nextEffect out.births out.state.nextEffect) with
  | int => exact ⟨rfl, .nil _⟩
  | unit => exact ⟨rfl, .nil _⟩
  | function row argument result ae re helpers argumentIH resultIH =>
      constructor
      · obtain ⟨ad, had, hao, hab⟩ := port_decoder ae
        cases hao
        obtain ⟨rd, hrd, hro, hrb⟩ := port_decoder re
        cases hro
        cases hab
        cases hrb
        simp [decodeValue, argumentIH.1, resultIH.1, had, hrd]
      · exact ((argumentIH.2.append resultIH.2).append
          (source_port_allocation ae)).append (source_port_allocation re)
  | tuple row children guard nonempty helpers childrenIH =>
      exact ⟨by simp [decodeValue, childrenIH.1, nonempty], childrenIH.2⟩
  | nil => exact ⟨rfl, .nil _⟩
  | cons head tail headIH tailIH =>
      exact ⟨by simp [decodeTuple, headIH.1, tailIH.1], headIH.2.append tailIH.2⟩

theorem source_pair_decoder_correspondence {c : Context} {p : Bool} {a : Annotation}
    {code : ValueCode} {s : State} {out : ValueDecoded c p s}
    (run : SourcePair c p a code s out) : decodeValue c p s code = some out :=
  (source_pair_checks run).1

theorem source_tuples_decoder {c : Context} {p : Bool} {xs : Annotations}
    {code : TupleCode} {s : State} {out : TupleDecoded c p s}
    (run : SourceTuples c p xs code s out) : decodeTuple c p s code = some out :=
  (source_tuples_checks run).1

theorem successful_pair_allocation_footprint {c : Context} {p : Bool} {a : Annotation}
    {code : ValueCode} {s : State} {out : ValueDecoded c p s}
    (run : SourcePair c p a code s out) :
    AllocationTrace s.nextEffect out.births out.state.nextEffect :=
  (source_pair_checks run).2

theorem successful_tuples_allocation {c : Context} {p : Bool} {xs : Annotations}
    {code : TupleCode} {s : State} {out : TupleDecoded c p s}
    (run : SourceTuples c p xs code s out) :
    AllocationTrace s.nextEffect out.births out.state.nextEffect :=
  (source_tuples_checks run).2

/-- The SAME entry retains owner/occurrence/parameter/scope, full structural
path, exact source row/concrete operands and its actual transcription birth. -/
theorem successful_pair_permission_entries {c : Context} {p : Bool} {a : Annotation}
    {code : ValueCode} {s : State} {out : ValueDecoded c p s}
    (_run : SourcePair c p a code s out) :
    ∀ entry ∈ out.entries, Origin out.shape p entry.path entry.allocatedRow entry.metadata ∧
      Owned c entry.metadata ∧ entry.allocatedRow ∈ out.births :=
  event_origins_and_births out.events

/-- Application to the exact R5 tree, universally in entry State. A successful
source transcription remains explicit here: it is not native execution and
requires the helper-frame/availability bridge. No native entry 21 is observed. -/
theorem r5_source_allocation_instance (s : State)
    (out : ValueDecoded FormalPermissionAuthenticatedNativeDecode.context false s)
    (run : SourcePair FormalPermissionAuthenticatedNativeDecode.context false FormalPermissionAuthenticatedNativeDecode.tree (FormalPermissionAuthenticatedNativeDecode.code 0 1) s out) :
    out = FormalPermissionAuthenticatedNativeDecode.output s 0 1 ∧ out.entries = FormalPermissionAuthenticatedNativeDecode.retained s.nextEffect ∧
    out.births = [s.nextEffect, s.nextEffect + 1, s.nextEffect + 2, s.nextEffect + 3] ∧
    out.state = {s with nextEffect := s.nextEffect + 4} := by
  have same : out = FormalPermissionAuthenticatedNativeDecode.output s 0 1 := Option.some.inj
    ((source_pair_decoder_correspondence run).symm.trans (FormalPermissionAuthenticatedNativeDecode.output_equations s 0 1).1)
  subst out
  exact ⟨rfl, (FormalPermissionAuthenticatedNativeDecode.output_equations s 0 1).2⟩

end
end YulangClosure.FormalPermissionSourceAllocation

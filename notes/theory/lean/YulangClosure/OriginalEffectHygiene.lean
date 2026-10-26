import YulangClosure.OriginalSourceGeneration
import YulangClosure.SourceFunctionMembership
import YulangClosure.PaperTypeSubstitution

/-!
Original publication/replay provenance and the native receipt lifetime seam.

Sources: the selected Source-Generalize construction, §§3--6 of
`2026-10-08-source-generalize-definition-and-proof.md`; the retained typed
transport/lifetime results in annotation-effect-hygiene-integration §3; and
the corrected source-owner distinction in `yulang-source-type-safety-ja.tex`,
`sec:owners`. These proofs use the existing constructors verbatim.

The results establish that successful original publication lookup and fixed
execution read their original stored frames, including the whole event
payload. A source new-use applies that result to its independently reconstructed
source judgment. The native owned return really deactivates the old owner;
a subsequent actual Name read retains every old receipt and cannot reactivate
that owner. No effect meaning is inferred from a receipt's mere existence.

This is a constructor/consumer bridge, not the whole effect-hygiene theorem.
OriginalSourceInterpretation.Inputs still requires the independently defined
profile/path/observation clauses. In particular no theorem here supplies all
source annotations, cooccurrence recipes, current-world resumption, or the
complete original effect/permission interpretation. Paper operation identity
is only its existing type-substitution representation, not an effect semantics.
-/
namespace YulangClosure.OriginalEffectHygiene

open OriginalSource

/-- Invert the original constructor. Its completed capture environment and
fixed history are obtained from the actual source scope, while replay entry
comes from the earlier initializer snapshot. They are not exchanged. -/
theorem publication_candidate_provenance {Value : Type}
    {environment : Environment Value} {site : Site}
    {identity : PublicationId Value} {record : PublicationRecord Value}
    (constructed : environment.publicationCandidate site = some (identity, record)) :
    record.identity = identity ∧ record.captures = environment.names ∧
      record.fixedFrames = (environment.prefixAtShared site).filter
        (fun frame => frame.binder.isFixed) ∧
      (∀ frame ∈ record.fixedFrames, frame.binder.isFixed = true) ∧
      ∃ entry,
        (environment.initializers.dropWhile (fun entry => entry.site != site)).head? = some entry ∧
        record.entryPath = entry.path ∧ record.entryNames = entry.names ∧
        record.entryFrames = entry.frames ∧
        record.initializers = environment.initializers.dropWhile (fun entry => entry.site != site) := by
  classical
  unfold Environment.publicationCandidate at constructed
  cases entered : (environment.initializers.dropWhile (fun entry => entry.site != site)).head? with
  | none => simp [entered] at constructed
  | some entry =>
      cases sharedAt : (environment.prefixAtShared site).getLast? with
      | none => simp [entered, sharedAt] at constructed
      | some shared =>
          cases returnedAt : (environment.prefixAtShared site).reverse.find? (fun frame =>
              frame.binder.site == site && frame.binder.kind == .returnRebind) with
          | none => simp [entered, sharedAt, returnedAt] at constructed
          | some returned =>
              simp only [Option.bind_eq_bind, Option.pure_def, entered, sharedAt,
                returnedAt, Option.bind_some] at constructed
              split at constructed
              · cases constructed
              · cases constructed
                refine ⟨rfl, rfl, rfl, ?_, entry, rfl, rfl, rfl, rfl, rfl⟩
                intro frame member
                exact (List.mem_filter.mp member).2

/-- Invert the actual lookup, including both authenticity checks performed
by `atPublication`. No well-formed saved record is supplied as a premise. -/
theorem publication_lookup_provenance {Value : Type}
    {environment restored : Environment Value} {name : Name}
    (found : environment.atPublication name = some restored) :
    ∃ identity record,
      environment.publicationName name = some identity ∧
      environment.publications identity = some record ∧
      record.identity = identity ∧
      (∀ frame ∈ record.fixedFrames, frame.binder.isFixed = true) ∧
      restored = environment.restore record := by
  classical
  unfold Environment.atPublication at found
  cases named : environment.publicationName name with
  | none => simp [named] at found
  | some identity =>
      cases stored : environment.publications identity with
      | none => simp [named, stored] at found
      | some record =>
          simp only [Option.bind_eq_bind, Option.pure_def, named, stored, Option.bind_some] at found
          split at found
          · cases found
          · rename_i valid
            have authentic := Classical.not_not.mp valid
            have restoredEq := Option.some.inj found
            exact ⟨identity, record, rfl, stored, authentic.1,
              List.all_eq_true.mp authentic.2, restoredEq.symm⟩

/-- A replay read retrieves one complete frame at the same original binder
and entry path. Equality of type descriptions is not a lookup key. -/
theorem execution_lookup_provenance {Value : Type}
    {environment : Environment Value} {binder : Binder} {value : ScopedValue Value}
    (found : environment.executionValue binder = some value) :
    ∃ history frame,
      environment.replay = some history ∧ frame ∈ history ∧
      frame.binder = binder ∧ frame.entryPath = environment.eventPath ∧
      frame.value = value := by
  classical
  unfold Environment.executionValue at found
  cases saved : environment.replay with
  | none => simp [saved] at found
  | some history =>
      cases selected : history.find? (fun frame =>
          decide (frame.binder = binder ∧ frame.entryPath = environment.eventPath)) with
      | none =>
          simp only [Option.bind_eq_bind, Option.pure_def, saved,
            Option.bind_some, selected, Option.bind_none] at found
          cases found
      | some frame =>
          have member := List.mem_of_find?_eq_some selected
          have matching := List.find?_some selected
          have key : frame.binder = binder ∧ frame.entryPath = environment.eventPath :=
            of_decide_eq_true matching
          have valueEq : frame.value = value := by
            simpa only [Option.bind_eq_bind, Option.pure_def, saved,
              Option.bind_some, selected, Option.some.injEq] using found
          exact ⟨history, frame, rfl, member, key.1, key.2, valueEq⟩

/-- The actual source publication precondition constructs both the published
name and its successful replay restoration. In particular the stored history
check is proved from `publicationCandidate`, not assumed separately. -/
theorem source_publication_constructs_replay {Value : Type}
    (environment : Environment Value) (name : Name) (site : Site)
    (valid : environment.publicationValid [(name, site)]) :
    ∃ identity record published restored,
      environment.publicationCandidate site = some (identity, record) ∧
      environment.publications identity = some record ∧
      environment.publish [(name, site)] = some published ∧
      published.atPublication name = some restored ∧
      record.captures = environment.names ∧
      restored.eventPath = record.entryPath ∧ restored.names = record.entryNames ∧
      restored.replay = some record.fixedFrames ∧
      restored.anchors = environment.anchors ∧
      restored.publications = environment.publications := by
  classical
  obtain ⟨identity, record, candidate, stored⟩ := valid (name, site) (by simp)
  obtain ⟨authentic, captures, _, fixed, _⟩ := publication_candidate_provenance candidate
  let published : Environment Value := {environment with names := (name, identity) :: environment.names}
  refine ⟨identity, record, published, published.restore record, candidate, stored,
    ?_, ?_, captures, rfl, rfl, rfl, rfl, rfl⟩
  · simp [Environment.publish, candidate, published]
  · simp [Environment.atPublication, Environment.publicationName, published,
      stored, authentic]
    exact fixed

/-- A foreign entry path cannot consume a saved event even if its static
binder and value description agree. -/
theorem replay_rejects_foreign_path {Value : Type}
    {environment : Environment Value} {history : List (Frame Value)} {binder : Binder}
    (saved : environment.replay = some history)
    (foreign : ∀ frame ∈ history, frame.binder = binder →
      frame.entryPath ≠ environment.eventPath) :
    environment.executionValue binder = none := by
  cases found : environment.executionValue binder with
  | none => rfl
  | some value =>
      obtain ⟨actual, frame, actualSaved, member, sameBinder, samePath, _⟩ :=
        execution_lookup_provenance found
      have same : actual = history := Option.some.inj (actualSaved.symm.trans saved)
      subst actual
      exact False.elim (foreign frame member sameBinder samePath)

/-- Extending the description does not rewrite the stored execution lookup.
This includes view logic, published instances and other non-event binders. -/
theorem description_extension_keeps_replay {Value : Type}
    (environment : Environment Value) (description target : Binder)
    (candidate : ScopedValue Value) (logical : description.isEvent = false) :
    (environment.extend description candidate).executionValue target =
      environment.executionValue target := by
  cases description with
  | mk site kind arity =>
      cases kind <;>
        simp_all [Binder.isEvent, Environment.extend, Environment.executionValue] <;> rfl

/-- Actual future invocation, operation and response scopes reopen history.
Their events cannot be obtained by replaying a former initializer. -/
theorem future_scope_has_no_replay_value {Value : Type}
    (environment : Environment Value) (site arity : Nat) (kind : BinderKind)
    (candidate : ScopedValue Value) (target : Binder)
    (future : kind = .invocation ∨ kind = .rigidOperation ∨ kind = .response) :
    (environment.extend ⟨site, kind, arity⟩ candidate).executionValue target = none := by
  rcases future with rfl | rfl | rfl <;>
    simp [Environment.extend, Environment.executionValue]

/-- Apply the two real consumer inversions. The selected saved event is
fixed, retains the whole payload/occurrence, and continues its original path. -/
theorem published_replay_provenance {Value : Type}
    {environment restored : Environment Value} {name : Name}
    {binder : Binder} {value : ScopedValue Value}
    (publication : environment.atPublication name = some restored)
    (execution : restored.executionValue binder = some value) :
    ∃ identity record frame,
      environment.publicationName name = some identity ∧
      environment.publications identity = some record ∧ record.identity = identity ∧
      frame ∈ record.fixedFrames ∧ frame.binder = binder ∧
      frame.entryPath = record.entryPath ∧ frame.value = value ∧
      binder.isFixed = true ∧
      restored.root = environment.root ∧ restored.anchors = environment.anchors ∧
      restored.publications = environment.publications ∧
      (binder.isEvent = true → (restored.extend binder value).eventPath = frame.exitPath) := by
  obtain ⟨identity, record, named, stored, authentic, fixed, restoredEq⟩ :=
    publication_lookup_provenance publication
  obtain ⟨history, frame, saved, member, sameBinder, samePath, sameValue⟩ :=
    execution_lookup_provenance execution
  subst restored
  have sameHistory : history = record.fixedFrames := Option.some.inj saved.symm
  subst history
  refine ⟨identity, record, frame, named, stored, authentic, member, sameBinder,
    samePath, sameValue, ?_, rfl, rfl, rfl, ?_⟩
  · simpa only [sameBinder] using fixed frame member
  · intro actual
    simp only [Environment.extend, actual, ↓reduceIte]
    simp only [Frame.exitPath, sameBinder, sameValue, samePath]

/-- For an actual fixed execution judgment, recover the stored value and
its independent body judgment. The open-execution case is impossible after
successful publication lookup. -/
theorem published_execution_judgment {Value : Type} (kernel : Kernel Value)
    {environment restored : Environment Value} {name : Name}
    {binder : Binder} {body : RuleTree}
    (publication : environment.atPublication name = some restored)
    (derivation : Judgment kernel restored (.executionE binder body)) :
    ∃ value identity record frame,
      kernel.admitted restored binder value ∧
      Judgment kernel (restored.extend binder value) body ∧
      environment.publicationName name = some identity ∧
      environment.publications identity = some record ∧ record.identity = identity ∧
      frame ∈ record.fixedFrames ∧ frame.binder = binder ∧
      frame.entryPath = record.entryPath ∧ frame.value = value ∧ binder.isFixed = true := by
  obtain ⟨identity, record, _, _, _, _, restoredEq⟩ :=
    publication_lookup_provenance publication
  cases derivation with
  | executionOpen openHistory _ =>
      rw [restoredEq] at openHistory
      cases openHistory
  | executionFixed history fixedHistory value lookup admitted proof =>
      obtain ⟨identity, record, frame, named, stored, authentic, member,
        sameBinder, samePath, sameValue, fixed, _⟩ :=
          published_replay_provenance publication lookup
      exact ⟨value, identity, record, frame, admitted, proof, named, stored,
        authentic, member, sameBinder, samePath, sameValue, fixed⟩

/-- Apply provenance to the original generated `newUse`, without assuming
its source derivation. One instance frame supplies both the source and client;
the former restores the previously registered publication and its fixed events. -/
theorem generated_new_use_keeps_original_publication {Value : Type}
    (kernel : Kernel Value) (environment : Environment Value) (context : Context)
    (site : Site) (definition : Definition) (instanceName : Name) (rest : Client)
    (solution : Satisfies kernel environment
      (BuildJoint context (.newUse site definition instanceName rest))) :
    ∃ candidate restored aliased identity record,
      kernel.admitted environment ⟨site, .publishedInstance, 0⟩ candidate ∧
      SourceJudgment kernel restored definition.context definition.source ∧
      JointJudgment kernel aliased (bindNames context site .local [instanceName]) rest ∧
      environment.publicationName definition.anchor = some identity ∧
      environment.publications identity = some record ∧ record.identity = identity ∧
      (∀ frame ∈ record.fixedFrames, frame.binder.isFixed = true) ∧
      restored.root = environment.root ∧ restored.anchors = environment.anchors ∧
      restored.publications = environment.publications ∧
      restored.eventPath = record.entryPath ∧ restored.names = record.entryNames ∧
      restored.replay = some record.fixedFrames ∧
      aliased.publicationName instanceName = some identity := by
  obtain ⟨candidate, admitted, _, ⟨restored, publication, source⟩,
      ⟨aliased, aliasLookup, client⟩⟩ :=
    (new_use_checks_source_and_client_in_one_frame kernel environment context site
      definition instanceName rest).mp solution
  obtain ⟨identity, record, named, stored, authentic, fixed, restoredEq⟩ :=
    publication_lookup_provenance publication
  have originalName : environment.publicationName definition.anchor = some identity := named
  have aliasSame := alias_keeps_publication_identity
    (environment.extend ⟨site, .publishedInstance, 0⟩ candidate)
    definition.anchor instanceName identity named
  rw [aliasLookup] at aliasSame
  have aliasName : aliased.publicationName instanceName = some identity :=
    Option.some.inj aliasSame
  refine ⟨candidate, restored, aliased, identity, record, admitted, source, client,
    originalName, stored, authentic, fixed, ?_, ?_, ?_, ?_, ?_, ?_, aliasName⟩ <;>
    rw [restoredEq] <;> rfl

namespace Native

open NativeClosureEnvironment SourceIdentityWorld SourceFunctionMembership

/-- This follows from successful raw `leave`, not from a supplied lifetime
law or from the mere absence/presence of a receipt. -/
theorem owned_return_expires {Site : Type} {before after : Control Site}
    {id : Nat} {previous : Owner}
    (returned : before.leave id previous = some after) :
    ¬ OwnerActive after (.invocation id) := by
  unfold Control.leave at returned
  split at returned
  · cases stack : before.active with
    | nil => simp [stack] at returned
    | cons top rest =>
        cases found : before.invocations.cell id with
        | none => simp [stack, found] at returned
        | some invocation =>
            simp only [stack, found] at returned
            split at returned
            · cases returned
              simp [OwnerActive, deactivate]
            · cases returned
  · cases returned

/-- Actual successful Name reads preserve control, all old complete receipts,
and all stored view data. In particular they cannot revive an expired owner. -/
theorem name_preserves_historical_evidence {Site : Type} [DecidableEq K] [DecidableEq V]
    {before after : World K D V ViewData Site Rest} {environment : Nat} {key : K}
    {site : Site} {dispatch : Option Nat} {result : Received V}
    (read : observeName before environment key site dispatch = some (after, result)) :
    after.control = before.control ∧ after.receiving.views = before.receiving.views ∧
    (∀ receipt, Recorded before.receiving receipt → Recorded after.receiving receipt) ∧
    (∀ owner, ¬ OwnerActive before.control owner → ¬ OwnerActive after.control owner) := by
  unfold observeName at read
  cases fetched : observe (fun k => decide (k = key)) before.environments environment
      before.cells.cell with
  | none => simp [fetched] at read
  | some packet =>
      cases viewed : before.receiving.views.cell packet.view with
      | none => simp [fetched, viewed] at read
      | some view =>
          by_cases aligned : view.value = packet.value
          · simp [fetched, viewed, aligned] at read
            obtain ⟨rfl, rfl⟩ := read
            refine ⟨rfl, rfl, ?_, fun _ inactive => inactive⟩
            intro receipt recorded
            exact (recorded_after_read before.receiving before.control.current
              packet.view site receipt).mpr (.inl recorded)
          · simp [fetched, viewed, aligned] at read

/-- The relevant owned-return/Name seam uses the current post-return control
while retaining old receipt identity; it cannot resurrect protection by reading
the same captured view again. Protection's complete path interpretation remains
the separate original typed-boundary premise. -/
theorem return_then_name_cannot_revive {Site : Type} [DecidableEq K] [DecidableEq V]
    {before returned after : World K D V ViewData Site Rest}
    {id : Nat} {previous : Owner} {value returnedValue result : Received V}
    {environment : Nat} {key : K} {site : Site} {dispatch : Option Nat}
    (returnStep : returnOwned before id previous value = some (returned, returnedValue))
    (nameStep : observeName returned environment key site dispatch = some (after, result)) :
    ¬ OwnerActive after.control (.invocation id) ∧
      (∀ receipt, Recorded before.receiving receipt → Recorded after.receiving receipt) := by
  unfold returnOwned at returnStep
  cases leave : before.control.leave id previous with
  | none => simp [leave] at returnStep
  | some control =>
      simp [leave] at returnStep
      obtain ⟨rfl, rfl⟩ := returnStep
      obtain ⟨controlEq, _, receipts, inactive⟩ := name_preserves_historical_evidence nameStep
      exact ⟨inactive _ (owned_return_expires leave), receipts⟩

end Native

/-- Existing Paper substitution changes static type coordinates together;
it cannot replace the operation declaration identity. This representation
lemma supplies no original profile/permission interpretation. -/
theorem operation_substitution_keeps_declaration
    (operation : PaperTypes.OperationInstance) (substitution : Nat → PaperTypes.Ty) :
    (operation.subst substitution).identity = operation.identity := rfl

theorem substitution_cannot_identify_distinct_operations
    (first second : PaperTypes.OperationInstance) (left right : Nat → PaperTypes.Ty)
    (different : first.identity ≠ second.identity) :
    first.subst left ≠ second.subst right := by
  intro same
  have identityEq : (first.subst left).identity = (second.subst right).identity :=
    congrArg PaperTypes.OperationInstance.identity same
  exact different identityEq

end YulangClosure.OriginalEffectHygiene

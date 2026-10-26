# Native Context callback construction r5: constructor-derived child emissions

Date: 2026-10-26. Status: constructed and kernel checked; independent review
pending. Producer: context_completion_r5. No parent gate is closed here.

## 1. Original target and frozen authority

The unchanged SourceProblem.InferenceSoundness root in Contracts.lean is:

```text
for every supported source s, original scope x, generated constraints d,
and solution a, there is one witness e such that
sourceJudgment s x e and sameScoped s x e a.
```

MERGE-EXPANSION-COVER-1 retains every historical Replay child, its original
factored expansion, current exact Context/carriers, recursively justified
children, and the actual accepted drain/ordered acknowledgements. Full Value
ports, optional records, method selection, complete Call, effects/hygiene,
generalization, and shared source scope/witness remain in the parent scope.
Neither the proposition definition nor a conditional composition proves it.

Governing authority is notes/design/2026-10-11-yulang-inference-top-level-principles.md.
The packet adds no source restriction, compiler implementation, language rule,
semantic callback, dependency/configuration change, or Git operation.

The isolated project started from repository revision
f67e402f7b89980d699260df1b28218f1cd43fd7. Accepted frozen direct dependencies:

| Dependency | SHA256 |
| --- | --- |
| NativeContextCompletion.lean | 5bc4bb4151087462cfbede6f0d6accece70c41ea5061f1ef100ad081e28344b4 |
| NativeContextReadback.lean | 321d087c8d2df5099f67beb75e4316d44114806bbfae2aa64ebda22a34bd83f2 |

The predecessor readback is published at ee61ba0b68789e2dea9eac024130f21c5a4e6453;
this leaf does not alter either dependency or its acceptance status.

## 2. Exact premise eliminated

Stage 1's finish_after_callbacks and callbacks_settled_readback required the
caller to supply an equality between body.children and the emitted child keys.
This packet computes that list from actual constructors and proves the equality.

leafPairs reads the ordered pairs from the actual Effect.checkOperand outcome
only when the callback's actual leaf is children. Other leaves emit no plain
child tasks. checkPairs selects the actual inline allowance boundary. bodyPairs
concatenates all inline checks in parser order and then the exact continuation.
body_emissions_exact proves:

```lean
body.children =
  (bodyPairs t q parent body).map (admittedChild (admissionTables t) q parent)
```

Its premise is the actual successful decompose computation, with no supplied
child-list equality, semantic coverage invariant, or completed-body callback.
The proof uses the actual collect/admit results; Availability.enqueue=true is
never treated as a work ownership certificate.

emissions pairs plans pairs each computed raw child pair with its actual
selected relation/task IDs and front/reservation fields. enqueueBody validates
the full plan vector length before selecting the callback traversal, preventing
zip truncation from dropping a child. The accepted stage-1 callbacks then
construct actual native queue events and one forward readback Run.

batch_completes_from_guards additionally derives traversal completion from raw
caller-frame, table/interner, source and reservation guards. A successful-batch
predicate is not an independent premise of the final application root.
batch_receipt_serials computes the exact consecutive serial stream; repeated
relation IDs cannot merge distinct work occurrences, including a stopped prefix.

## 3. Direct owner/settlement application

fresh_finish_emissions connects an actual prepare and finishPrefix at the same
representative map through staged_expand, obtaining the constructor-derived
whole body list. constructed_finish_after_callbacks and
constructed_callbacks_settled instantiate the accepted stage-1 consumers using
that derived equality. The caller supplies no favorable emitted/body list.

guarded_finished_children_settled is the strongest application root. Starting
with one prior actual readback history, it uses actual prepare/finish results,
raw caller/table/resource guards, and exact plan length to derive the callback
batch, the completed owner seal, and each child's genuinely issued occurrence.
It then consumes the same explicit later forward history to read every child
back through a resolved receipt and original Context/Derived route. All
transferred Replay tickets have diagnosed acknowledgement receipts.

The later history may contain merges and duplicates. Its existence is still an
operational premise, rather than a termination or native-extraction theorem.
The complete source-local Context, original parent sources, and entire scoped
transformer remain in admittedChild; no default payload is substituted.

## 4. Constructor and source-owner census

| Constructor/path | Representation and evidence |
| --- | --- |
| Leaf.localReturn | Emits no plain child pair; exact empty list. |
| Leaf.bound | Emits no plain child pair; its real bound fiber is retained by the original Body. Bound-origin/Replay callbacks are separate owners. |
| Leaf.conflict | Emits no plain child pair; conflict handling is retained rather than relabeled a successful typing. |
| Leaf.children | Uses the actual ordered checkOperand pairs and collect/admit result, including empty and duplicate lists. |
| Registered inline allowance | Existing applyFilter bound branch; no fabricated plain child callback. |
| Unregistered inline allowance | filter_children_from_apply links the actual applyEffect call at context zero to its exact emitted pairs. |
| Every weight/check | check_filter_exact selects the actual weight payload/boundary and callback result. All checks are traversed in native parser order. |
| Consumed upper endpoint | The actual absent continuation contributes no pairs. |
| Nonconsumed residual | The exact successful continuation applyEffect follows every inline check and contributes its actual pairs. |
| Identity/empty filter Context | Existing decompose/prepare behavior is used; no new parser or source cap is introduced. |
| Reused interned relation | Stage-1 callback still issues a new serial occurrence; it does not replace memo ownership. |
| Failed callback/reservation | Existing batch retains earlier receipts and explicit failed suffix; serial theorem includes partial prefixes. |
| Diagnostics/acknowledgements | Existing later drain history establishes diagnosed ordered receipts; no queue admission is treated as completion. |

Native owners read: candidate_context.rs candidate_context_admit,
candidate_context_execute_relation, candidate_zero_word_filters and
candidate_context_transport_task; candidate_effect.rs candidate_enqueue_evidence;
lib.rs enqueue_item, pair_is_current, dispatch_live_item and step_typed_drain.
The native order remains admission/dependency, queue reserve/transfer/insertion,
Context before Dispatch, and Diagnostics before acknowledgement.

The packet proves a constructor-to-queue projection. It does not authenticate
that projection from arbitrary Rust execution, nor prove that batching the
purely observed inline-child list is a native timing refinement. In particular,
prefix publication and synchronous bound callbacks retain their real earlier
cuts; no theorem silently moves those native side effects after publication.
The source-to-event correspondence still has to associate each actual inline
callback with its actual chronological queue event.

## 5. Precise remaining seams and parent application

The earlier supplied whole-body emitted-list equality is removed for the fresh
staged prepare/finish construction represented here. The strongest root also
removes a separately supplied batch-completion premise by deriving it from raw
operational guards. These are substantive reductions of the child-issuance seam.

The first remaining application premise is extraction of those raw selected
interner/task IDs and chronological callback events from the actual native
owner, including its real resource/cancellation boundary. The predecessor has
no child-admission Derived event; stage-1 dependency emissions remain separate.
NativeValueDrain owns the related admission/history integration; this packet
adds no competing Derived extension. Actual forest history to Step.merge is
separately owned by the primary.

Cached/already-discharged prefixes and transported recipes are not generally
fresh prepare results at the same representative map. They require retaining
their earlier actual emitted occurrences through the forward history, rather
than rerunning callbacks or assuming equality with a fresh body. This root does
not close that timing/source correspondence, table lifetime across cancellation,
physical bound/Replay callback construction, Replay-bearing enqueue callbacks,
Value structured ports, termination, or native accepted-return refinement.

MERGE-EXPANSION-COVER-1, SourceProblem.NativeCorrespondence, and
SourceProblem.InferenceSoundness remain OPEN at their original full scope.
No new LocalLaws, assumed child-currentness, hidden completion invariant, semantic
callback, custom axiom, or source-domain reduction is introduced.

## 6. Checker evidence and failure preservation

Pinned native toolchain: /workspace/scratch/c10e953a5453/toolchains/lean-4.35.0-linux/bin/lake.
Checker reports Lake 5.0.0-src+eb6cafb and Lean 4.35.0. Exact full commands and
all raw output are preserved under:

```text
/workspace/scratch/c10e953a5453/context-callback-r5/check-01.log
/workspace/scratch/c10e953a5453/context-callback-r5/check-02.log
/workspace/scratch/c10e953a5453/context-callback-r5/check-03.log
/workspace/scratch/c10e953a5453/context-callback-r5/check-04.log
/workspace/scratch/c10e953a5453/context-callback-r5/audit-plain.log
```

check-01 failed on a reserved identifier, incomplete map normalization and a
let-bound split. check-02 repaired those and passed; check-03 added raw-guard
completion/serial construction and passed; check-04 added the final direct
owner/settlement application and passed. The final skill audit passed all 21
authored roots, confirming theorem kind, exact full types, and complete
transitive axiom lists. Raw earlier failures were not overwritten.

Five focused checker invocations were used, within the 12-check grant. Each
uses the isolated project/cache, at most one Lean process, -j1 -M1024,
LEAN_NUM_THREADS=1, and a 120-second total command bound. No timeout occurred.
The native checker needed the previously authorized exact-command execution
escalation; no toolchain/dependency installation or update was attempted.
No default-root build or independent review was performed by this producer.
No source code, compiler test expectation, shared status/root import/config or
Git state was edited. Supplementary source scan found no authored sorry, admit,
custom axiom, debug.skipKernelTC, or unchecked native-evaluation bypass.

New Lean SHA256:
b90e44fbbf4c268e1b3dc73c32dfb0de542b640207e2feda6c8acf68d89cbb98.
Audit SHA256:
0d55f35bd35b4bd25236c62c6a2061f04bc8c65f4ce516de5d5acca7019607f4.

## 7. Authored-root origin and full axiom census

All names below are in YulangClosure.NativeContextCallbackConstruction. Standard
axioms are reported as actually collected; no empty-list claim is inferred from
the absence of explicit project axioms.

| Theorem | Constructive origin | Full axiom list |
| --- | --- | --- |
| admissions_exact_keys | Aligned.cons; admit_payload computes the admitted key | propext |
| operand_emission_exact | apply_children_admitted; actual Effect.checkOperand children | propext, Quot.sound |
| emissions_pairs | List.zip/map with exact plan-length validation | propext, Classical.choice, Quot.sound |
| collected_callbacks_issue_all | collect_exact; admissions_exact_keys; actual enqueueChildren run | propext, Classical.choice, Quot.sound |
| apply_emissions_exact | All four Leaf constructors; actual applyEffect result | propext, Quot.sound |
| filter_emissions_exact | All four Leaf constructors; filter_children_from_apply for children | propext, Quot.sound |
| check_emissions_exact | check_filter_exact raw weight/boundary readback | propext, Quot.sound |
| flatMap_pointwise | List.nil/cons structural induction | propext |
| body_emissions_exact | decompose_exact actual checks and optional continuation | propext, Quot.sound |
| fresh_finish_emissions | staged_expand and actual prepare/finishPrefix computations | propext, Quot.sound |
| enqueue_body_exact | Executable exact length guard and selected batch | propext, Quot.sound |
| emissions_mapped | emissions_pairs; map composition | propext, Classical.choice, Quot.sound |
| fresh_body_callbacks | fresh_finish_emissions; actual batch receipt keys and issued work | propext, Classical.choice, Quot.sound |
| constructed_finish_after_callbacks | Derived fresh body list instantiates accepted finish_after_callbacks | propext, Classical.choice, Quot.sound |
| constructed_callbacks_settled | Derived fresh body list instantiates accepted callbacks_settled_readback | propext, Classical.choice, Quot.sound |
| enqueue_from_guards | Actual callback branches; raw frame/table/resource guards | propext, Quot.sound |
| raw_guard_context_data | Exact map/relation/task equality from unchanged callback context data | propext, Quot.sound |
| batch_completes_from_guards | Actual per-child successful enqueue; unchanged caller and raw tables | propext, Quot.sound |
| batch_receipt_serials | Actual Work.serial allocation and nextWork increment | propext, Quot.sound |
| batch_receipt_serials_distinct | batch_receipt_serials; List.nodup_range' | propext, Classical.choice, Quot.sound |
| guarded_finished_children_settled | Computed emissions + raw-guard traversal + actual finish + same later run | propext, Classical.choice, Quot.sound |

## 8. Complete printed theorem types and transitive axiom output

The following is the unabridged ordered theorem-audit region from the accepted
21-root checker run. It is evidence under the printed hypotheses, not an
independent source-correspondence or inference-soundness certificate.

```text
YULANG_AUDIT_BEGIN YulangClosure.NativeContextCallbackConstruction.admissions_exact_keys
@YulangClosure.NativeContextCallbackConstruction.admissions_exact_keys : ∀
  {t : YulangClosure.NativeContextExpansion.Tables} {a : YulangClosure.NativeContextExpansion.Availability}
  {q : Nat → Nat} {parent : YulangClosure.NativeMergeExpansion.Key}
  {pairs : List YulangClosure.NativeReplayCurrent.Pair} {keys : List YulangClosure.NativeMergeExpansion.Key},
  YulangClosure.NativeContextExpansion.Aligned
      (fun pair key => YulangClosure.NativeContextExpansion.admit t a q parent pair = Option.some key) pairs keys →
    keys =
      List.map
        (YulangClosure.NativeReplayCurrent.admittedChild (YulangClosure.NativeContextExpansion.admissionTables t) q
          parent)
        pairs
'YulangClosure.NativeContextCallbackConstruction.admissions_exact_keys' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeContextCallbackConstruction.admissions_exact_keys
YULANG_AUDIT_BEGIN YulangClosure.NativeContextCallbackConstruction.operand_emission_exact
@YulangClosure.NativeContextCallbackConstruction.operand_emission_exact : ∀
  {t : YulangClosure.NativeContextExpansion.Tables} {a : YulangClosure.NativeContextExpansion.Availability}
  {levels q : Nat → Nat} {parent : YulangClosure.NativeMergeExpansion.Key} {context : Nat}
  {pair : YulangClosure.NativeReplayCurrent.Pair} {keys : List YulangClosure.NativeMergeExpansion.Key},
  YulangClosure.NativeContextExpansion.applyEffect t a levels q parent context pair =
      Option.some (YulangClosure.NativeContextExpansion.Leaf.children keys) →
    ∃ pairs,
      YulangClosure.NativeMergeExpansion.Effect.checkOperand q (YulangClosure.NativeContextExpansion.effectTables t)
            pair.fst pair.snd =
          YulangClosure.NativeMergeExpansion.Effect.Outcome.children pairs ∧
        keys =
          List.map
            (YulangClosure.NativeReplayCurrent.admittedChild (YulangClosure.NativeContextExpansion.admissionTables t) q
              parent)
            pairs
'YulangClosure.NativeContextCallbackConstruction.operand_emission_exact' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeContextCallbackConstruction.operand_emission_exact
YULANG_AUDIT_BEGIN YulangClosure.NativeContextCallbackConstruction.emissions_pairs
YulangClosure.NativeContextCallbackConstruction.emissions_pairs : ∀
  (pairs : List YulangClosure.NativeReplayCurrent.Pair) (plans : List YulangClosure.NativeContextCompletion.Plan),
  pairs.length = plans.length →
    List.map YulangClosure.NativeContextCompletion.Emission.pair
        (YulangClosure.NativeContextCallbackConstruction.emissions pairs plans) =
      pairs
'YulangClosure.NativeContextCallbackConstruction.emissions_pairs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeContextCallbackConstruction.emissions_pairs
YULANG_AUDIT_BEGIN YulangClosure.NativeContextCallbackConstruction.collected_callbacks_issue_all
@YulangClosure.NativeContextCallbackConstruction.collected_callbacks_issue_all : ∀
  {t : YulangClosure.NativeContextExpansion.Tables} {s : YulangClosure.NativeContextCompletion.CallbackState t}
  (parent : YulangClosure.NativeMergeExpansion.Key) (processing : Nat)
  (a : YulangClosure.NativeContextExpansion.Availability) (pairs : List YulangClosure.NativeReplayCurrent.Pair)
  (keys : List YulangClosure.NativeMergeExpansion.Key) (plans : List YulangClosure.NativeContextCompletion.Plan),
  YulangClosure.NativeContextExpansion.collect
        (YulangClosure.NativeContextExpansion.admit t a s.native.effectMap parent) pairs =
      Option.some keys →
    pairs.length = plans.length →
      (YulangClosure.NativeContextCompletion.enqueueChildren parent processing s
              (YulangClosure.NativeContextCallbackConstruction.emissions pairs plans)).remaining =
          [] →
        YulangClosure.NativeContextReadback.Run t s.native
            (YulangClosure.NativeContextCompletion.enqueueChildren parent processing s
                  (YulangClosure.NativeContextCallbackConstruction.emissions pairs plans)).state.native ∧
          List.map YulangClosure.NativeContextCompletion.Receipt.key
                (YulangClosure.NativeContextCompletion.enqueueChildren parent processing s
                    (YulangClosure.NativeContextCallbackConstruction.emissions pairs plans)).receipts =
              keys ∧
            ∀ (child : YulangClosure.NativeMergeExpansion.Key),
              child ∈ keys →
                ∃ receipt,
                  receipt ∈
                      (YulangClosure.NativeContextCompletion.enqueueChildren parent processing s
                          (YulangClosure.NativeContextCallbackConstruction.emissions pairs plans)).receipts ∧
                    receipt.key = child ∧
                      receipt.work ∈
                        (YulangClosure.NativeContextCompletion.enqueueChildren parent processing s
                                  (YulangClosure.NativeContextCallbackConstruction.emissions pairs
                                    plans)).state.native.control.issued
'YulangClosure.NativeContextCallbackConstruction.collected_callbacks_issue_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeContextCallbackConstruction.collected_callbacks_issue_all
YULANG_AUDIT_BEGIN YulangClosure.NativeContextCallbackConstruction.apply_emissions_exact
@YulangClosure.NativeContextCallbackConstruction.apply_emissions_exact : ∀
  {t : YulangClosure.NativeContextExpansion.Tables} {a : YulangClosure.NativeContextExpansion.Availability}
  {levels q : Nat → Nat} {parent : YulangClosure.NativeMergeExpansion.Key} {context : Nat}
  {pair : YulangClosure.NativeReplayCurrent.Pair} {leaf : YulangClosure.NativeContextExpansion.Leaf},
  YulangClosure.NativeContextExpansion.applyEffect t a levels q parent context pair = Option.some leaf →
    leaf.childKeys =
      List.map
        (YulangClosure.NativeReplayCurrent.admittedChild (YulangClosure.NativeContextExpansion.admissionTables t) q
          parent)
        (YulangClosure.NativeContextCallbackConstruction.leafPairs t q pair leaf)
'YulangClosure.NativeContextCallbackConstruction.apply_emissions_exact' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeContextCallbackConstruction.apply_emissions_exact
YULANG_AUDIT_BEGIN YulangClosure.NativeContextCallbackConstruction.filter_emissions_exact
@YulangClosure.NativeContextCallbackConstruction.filter_emissions_exact : ∀
  {t : YulangClosure.NativeContextExpansion.Tables} {a : YulangClosure.NativeContextExpansion.Availability}
  {levels q : Nat → Nat} {parent : YulangClosure.NativeMergeExpansion.Key} {view : Nat}
  {leaf : YulangClosure.NativeContextExpansion.Leaf},
  YulangClosure.NativeContextExpansion.applyFilter t a levels q parent view = Option.some leaf →
    leaf.childKeys =
      List.map
        (YulangClosure.NativeReplayCurrent.admittedChild (YulangClosure.NativeContextExpansion.admissionTables t) q
          parent)
        (YulangClosure.NativeContextCallbackConstruction.leafPairs t q
          ((YulangClosure.NativeReplayCurrent.currentPair q parent).fst,
            YulangClosure.NativeMergeExpansion.Endpoint.allowance view)
          leaf)
'YulangClosure.NativeContextCallbackConstruction.filter_emissions_exact' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeContextCallbackConstruction.filter_emissions_exact
YULANG_AUDIT_BEGIN YulangClosure.NativeContextCallbackConstruction.check_emissions_exact
@YulangClosure.NativeContextCallbackConstruction.check_emissions_exact : ∀
  {t : YulangClosure.NativeContextExpansion.Tables} {a : YulangClosure.NativeContextExpansion.Availability}
  {levels q : Nat → Nat} {parent : YulangClosure.NativeMergeExpansion.Key} {weight : Nat}
  {check : YulangClosure.NativeContextExpansion.Check},
  YulangClosure.NativeContextExpansion.checkFilter t a levels q parent weight = Option.some check →
    check.leaf.childKeys =
      List.map
        (YulangClosure.NativeReplayCurrent.admittedChild (YulangClosure.NativeContextExpansion.admissionTables t) q
          parent)
        (YulangClosure.NativeContextCallbackConstruction.checkPairs t q parent check)
'YulangClosure.NativeContextCallbackConstruction.check_emissions_exact' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeContextCallbackConstruction.check_emissions_exact
YULANG_AUDIT_BEGIN YulangClosure.NativeContextCallbackConstruction.flatMap_pointwise
@YulangClosure.NativeContextCallbackConstruction.flatMap_pointwise : ∀ {α β : Type} {xs : List α} {f g : α → List β},
  (∀ (x : α), x ∈ xs → f x = g x) → List.flatMap f xs = List.flatMap g xs
'YulangClosure.NativeContextCallbackConstruction.flatMap_pointwise' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeContextCallbackConstruction.flatMap_pointwise
YULANG_AUDIT_BEGIN YulangClosure.NativeContextCallbackConstruction.body_emissions_exact
@YulangClosure.NativeContextCallbackConstruction.body_emissions_exact : ∀
  {t : YulangClosure.NativeContextExpansion.Tables} {a : YulangClosure.NativeContextExpansion.Availability}
  {levels q : Nat → Nat} {parent : YulangClosure.NativeMergeExpansion.Key}
  {parsed : YulangClosure.NativeContextExpansion.Parsed} {body : YulangClosure.NativeContextExpansion.Body},
  YulangClosure.NativeContextExpansion.decompose t a levels q parent parsed = Option.some body →
    body.children =
      List.map
        (YulangClosure.NativeReplayCurrent.admittedChild (YulangClosure.NativeContextExpansion.admissionTables t) q
          parent)
        (YulangClosure.NativeContextCallbackConstruction.bodyPairs t q parent body)
'YulangClosure.NativeContextCallbackConstruction.body_emissions_exact' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeContextCallbackConstruction.body_emissions_exact
YULANG_AUDIT_BEGIN YulangClosure.NativeContextCallbackConstruction.fresh_finish_emissions
@YulangClosure.NativeContextCallbackConstruction.fresh_finish_emissions : ∀
  {t : YulangClosure.NativeContextExpansion.Tables} {a : YulangClosure.NativeContextExpansion.Availability}
  {levels q : Nat → Nat} {fuel : Nat} {parent : YulangClosure.NativeMergeExpansion.Key}
  {segment : YulangClosure.NativeContextReadback.Prefix} {body : YulangClosure.NativeContextExpansion.Body},
  YulangClosure.NativeContextReadback.prepare t a levels q fuel parent = Option.some segment →
    YulangClosure.NativeContextReadback.finishPrefix t a levels q parent segment = Option.some body →
      a.publish = Bool.true →
        body.children =
          List.map
            (YulangClosure.NativeReplayCurrent.admittedChild (YulangClosure.NativeContextExpansion.admissionTables t) q
              parent)
            (YulangClosure.NativeContextCallbackConstruction.bodyPairs t q parent body)
'YulangClosure.NativeContextCallbackConstruction.fresh_finish_emissions' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeContextCallbackConstruction.fresh_finish_emissions
YULANG_AUDIT_BEGIN YulangClosure.NativeContextCallbackConstruction.enqueue_body_exact
@YulangClosure.NativeContextCallbackConstruction.enqueue_body_exact : ∀
  {t : YulangClosure.NativeContextExpansion.Tables} {s : YulangClosure.NativeContextCompletion.CallbackState t}
  {parent : YulangClosure.NativeMergeExpansion.Key} {processing : Nat}
  {body : YulangClosure.NativeContextExpansion.Body} {plans : List YulangClosure.NativeContextCompletion.Plan}
  {batch : YulangClosure.NativeContextCompletion.BatchResult t},
  YulangClosure.NativeContextCallbackConstruction.enqueueBody s parent processing body plans = Option.some batch →
    (YulangClosure.NativeContextCallbackConstruction.bodyPairs t s.native.effectMap parent body).length = plans.length ∧
      batch =
        YulangClosure.NativeContextCompletion.enqueueChildren parent processing s
          (YulangClosure.NativeContextCallbackConstruction.emissions
            (YulangClosure.NativeContextCallbackConstruction.bodyPairs t s.native.effectMap parent body) plans)
'YulangClosure.NativeContextCallbackConstruction.enqueue_body_exact' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeContextCallbackConstruction.enqueue_body_exact
YULANG_AUDIT_BEGIN YulangClosure.NativeContextCallbackConstruction.emissions_mapped
@YulangClosure.NativeContextCallbackConstruction.emissions_mapped : ∀ {t : YulangClosure.NativeContextExpansion.Tables}
  (q : Nat → Nat) (parent : YulangClosure.NativeMergeExpansion.Key)
  (pairs : List YulangClosure.NativeReplayCurrent.Pair) (plans : List YulangClosure.NativeContextCompletion.Plan),
  pairs.length = plans.length →
    List.map
        (fun input =>
          YulangClosure.NativeReplayCurrent.admittedChild (YulangClosure.NativeContextExpansion.admissionTables t) q
            parent input.pair)
        (YulangClosure.NativeContextCallbackConstruction.emissions pairs plans) =
      List.map
        (YulangClosure.NativeReplayCurrent.admittedChild (YulangClosure.NativeContextExpansion.admissionTables t) q
          parent)
        pairs
'YulangClosure.NativeContextCallbackConstruction.emissions_mapped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeContextCallbackConstruction.emissions_mapped
YULANG_AUDIT_BEGIN YulangClosure.NativeContextCallbackConstruction.fresh_body_callbacks
@YulangClosure.NativeContextCallbackConstruction.fresh_body_callbacks : ∀
  {t : YulangClosure.NativeContextExpansion.Tables} {s : YulangClosure.NativeContextCompletion.CallbackState t}
  (parent : YulangClosure.NativeMergeExpansion.Key) (processing : Nat)
  (a : YulangClosure.NativeContextExpansion.Availability) (levels : Nat → Nat) (fuel : Nat)
  (segment : YulangClosure.NativeContextReadback.Prefix) (body : YulangClosure.NativeContextExpansion.Body)
  (plans : List YulangClosure.NativeContextCompletion.Plan),
  YulangClosure.NativeContextReadback.prepare t a levels s.native.effectMap fuel parent = Option.some segment →
    YulangClosure.NativeContextReadback.finishPrefix t a levels s.native.effectMap parent segment = Option.some body →
      a.publish = Bool.true →
        ∀ (batch : YulangClosure.NativeContextCompletion.BatchResult t),
          YulangClosure.NativeContextCallbackConstruction.enqueueBody s parent processing body plans =
              Option.some batch →
            batch.remaining = [] →
              YulangClosure.NativeContextReadback.Run t s.native batch.state.native ∧
                List.map YulangClosure.NativeContextCompletion.Receipt.key batch.receipts = body.children ∧
                  (∀ (child : YulangClosure.NativeMergeExpansion.Key),
                      child ∈ body.children →
                        ∃ receipt,
                          receipt ∈ batch.receipts ∧
                            receipt.key = child ∧ receipt.work ∈ batch.state.native.control.issued) ∧
                    YulangClosure.NativeContextCompletion.contextData batch.state.native =
                        YulangClosure.NativeContextCompletion.contextData s.native ∧
                      batch.state.native.control.frames = s.native.control.frames
'YulangClosure.NativeContextCallbackConstruction.fresh_body_callbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeContextCallbackConstruction.fresh_body_callbacks
YULANG_AUDIT_BEGIN YulangClosure.NativeContextCallbackConstruction.constructed_finish_after_callbacks
@YulangClosure.NativeContextCallbackConstruction.constructed_finish_after_callbacks : ∀
  {t : YulangClosure.NativeContextExpansion.Tables} {s : YulangClosure.NativeContextCompletion.CallbackState t},
  YulangClosure.NativeContextReadback.Run t (YulangClosure.NativeContextReadback.initial t) s.native →
    ∀ (owner : YulangClosure.NativeContextReadback.Owner t) (a : YulangClosure.NativeContextExpansion.Availability)
      (levels : Nat → Nat) (fuel : Nat) (body : YulangClosure.NativeContextExpansion.Body)
      (plans : List YulangClosure.NativeContextCompletion.Plan),
      YulangClosure.NativeContextReadback.prepare t a levels s.native.effectMap fuel owner.key =
          Option.some owner.ready.packet.segment →
        ∀
          (finished :
            YulangClosure.NativeContextReadback.finishPrefix t a levels s.native.effectMap owner.key
                owner.ready.packet.segment =
              Option.some body),
          a.publish = Bool.true →
            (YulangClosure.NativeContextCallbackConstruction.bodyPairs t s.native.effectMap owner.key body).length =
                plans.length →
              (YulangClosure.NativeContextCompletion.enqueueChildren owner.key owner.relation s
                      (YulangClosure.NativeContextCallbackConstruction.emissions
                        (YulangClosure.NativeContextCallbackConstruction.bodyPairs t s.native.effectMap owner.key body)
                        plans)).remaining =
                  [] →
                ∀ (f : YulangClosure.NativeDrainOwnership.Frame) (fs : List YulangClosure.NativeDrainOwnership.Frame),
                  s.native.control.frames = f :: fs →
                    f.phase = YulangClosure.NativeDrainOwnership.Phase.working →
                      f.current = Option.some owner.work →
                        f.processing = Option.some owner.relation →
                          s.native.owners owner.work = Option.some owner →
                            ∀ (transitions : Nat),
                              have batch :=
                                YulangClosure.NativeContextCompletion.enqueueChildren owner.key owner.relation s
                                  (YulangClosure.NativeContextCallbackConstruction.emissions
                                    (YulangClosure.NativeContextCallbackConstruction.bodyPairs t s.native.effectMap
                                      owner.key body)
                                    plans);
                              have packet := { key := owner.key, body := body, construction := ⋯ };
                              have final :=
                                YulangClosure.NativeContextReadback.finishOwner batch.state.native f fs owner packet
                                  transitions;
                              YulangClosure.NativeContextReadback.Run t (YulangClosure.NativeContextReadback.initial t)
                                  final ∧
                                (owner, packet) ∈ final.seals ∧
                                  ∀ (child : YulangClosure.NativeMergeExpansion.Key),
                                    child ∈ body.children →
                                      ∃ receipt,
                                        receipt ∈ batch.receipts ∧
                                          receipt.key = child ∧ receipt.work ∈ final.control.issued
'YulangClosure.NativeContextCallbackConstruction.constructed_finish_after_callbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeContextCallbackConstruction.constructed_finish_after_callbacks
YULANG_AUDIT_BEGIN YulangClosure.NativeContextCallbackConstruction.constructed_callbacks_settled
@YulangClosure.NativeContextCallbackConstruction.constructed_callbacks_settled : ∀
  {t : YulangClosure.NativeContextExpansion.Tables} {s : YulangClosure.NativeContextCompletion.CallbackState t},
  YulangClosure.NativeContextReadback.Run t (YulangClosure.NativeContextReadback.initial t) s.native →
    ∀ (parent : YulangClosure.NativeMergeExpansion.Key) (processing : Nat)
      (a : YulangClosure.NativeContextExpansion.Availability) (levels : Nat → Nat) (fuel : Nat)
      (segment : YulangClosure.NativeContextReadback.Prefix) (body : YulangClosure.NativeContextExpansion.Body)
      (plans : List YulangClosure.NativeContextCompletion.Plan),
      YulangClosure.NativeContextReadback.prepare t a levels s.native.effectMap fuel parent = Option.some segment →
        YulangClosure.NativeContextReadback.finishPrefix t a levels s.native.effectMap parent segment =
            Option.some body →
          a.publish = Bool.true →
            (YulangClosure.NativeContextCallbackConstruction.bodyPairs t s.native.effectMap parent body).length =
                plans.length →
              (YulangClosure.NativeContextCompletion.enqueueChildren parent processing s
                      (YulangClosure.NativeContextCallbackConstruction.emissions
                        (YulangClosure.NativeContextCallbackConstruction.bodyPairs t s.native.effectMap parent body)
                        plans)).remaining =
                  [] →
                ∀ (settled : YulangClosure.NativeContextReadback.State t),
                  YulangClosure.NativeContextReadback.Run t
                      (YulangClosure.NativeContextCompletion.enqueueChildren parent processing s
                            (YulangClosure.NativeContextCallbackConstruction.emissions
                              (YulangClosure.NativeContextCallbackConstruction.bodyPairs t s.native.effectMap parent
                                body)
                              plans)).state.native
                      settled →
                    settled.control.queue = [] →
                      settled.control.frames = [] →
                        YulangClosure.NativeContextReadback.Run t (YulangClosure.NativeContextReadback.initial t)
                            settled ∧
                          (∀ (child : YulangClosure.NativeMergeExpansion.Key),
                              child ∈ body.children →
                                ∃ emitted,
                                  emitted ∈
                                      (YulangClosure.NativeContextCompletion.enqueueChildren parent processing s
                                          (YulangClosure.NativeContextCallbackConstruction.emissions
                                            (YulangClosure.NativeContextCallbackConstruction.bodyPairs t
                                              s.native.effectMap parent body)
                                            plans)).receipts ∧
                                    emitted.key = child ∧
                                      ∃ receipt,
                                        receipt ∈ settled.receipts ∧
                                          receipt.work = emitted.work ∧
                                            YulangClosure.NativeContextReadback.Resolved settled receipt ∧
                                              YulangClosure.NativeContextReadback.RouteValid settled receipt.route) ∧
                            ∀ (ticket : YulangClosure.NativeDrainOwnership.Ticket),
                              ticket ∈ settled.control.transferred →
                                ∃ receipt,
                                  receipt ∈ settled.control.acknowledgements ∧
                                    receipt.ticket = ticket ∧ receipt.diagnosed = Bool.true
'YulangClosure.NativeContextCallbackConstruction.constructed_callbacks_settled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeContextCallbackConstruction.constructed_callbacks_settled
YULANG_AUDIT_BEGIN YulangClosure.NativeContextCallbackConstruction.enqueue_from_guards
@YulangClosure.NativeContextCallbackConstruction.enqueue_from_guards : ∀
  {t : YulangClosure.NativeContextExpansion.Tables} (s : YulangClosure.NativeContextCompletion.CallbackState t)
  (parent : YulangClosure.NativeMergeExpansion.Key) (processing : Nat)
  (input : YulangClosure.NativeContextCompletion.Emission) (f : YulangClosure.NativeDrainOwnership.Frame)
  (fs : List YulangClosure.NativeDrainOwnership.Frame),
  s.native.control.frames = f :: fs →
    f.phase = YulangClosure.NativeDrainOwnership.Phase.working →
      f.current.isSome = Bool.true →
        f.processing = Option.some processing →
          YulangClosure.NativeContextCompletion.rawGuard s.native parent processing input.pair input.plan = Bool.true →
            input.plan.reserved = Bool.true →
              (YulangClosure.NativeContextCompletion.enqueueChild s parent processing input).receipt =
                Option.some
                  {
                    key :=
                      YulangClosure.NativeReplayCurrent.admittedChild
                        (YulangClosure.NativeContextExpansion.admissionTables t) s.native.effectMap parent input.pair,
                    work :=
                      YulangClosure.NativeDrainOwnership.work s.native.control input.plan.task input.plan.relation
                        Option.none }
'YulangClosure.NativeContextCallbackConstruction.enqueue_from_guards' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeContextCallbackConstruction.enqueue_from_guards
YULANG_AUDIT_BEGIN YulangClosure.NativeContextCallbackConstruction.raw_guard_context_data
@YulangClosure.NativeContextCallbackConstruction.raw_guard_context_data : ∀
  {t : YulangClosure.NativeContextExpansion.Tables} {s u : YulangClosure.NativeContextReadback.State t},
  YulangClosure.NativeContextCompletion.contextData s = YulangClosure.NativeContextCompletion.contextData u →
    ∀ (parent : YulangClosure.NativeMergeExpansion.Key) (processing : Nat)
      (input : YulangClosure.NativeContextCompletion.Emission),
      YulangClosure.NativeContextCompletion.rawGuard s parent processing input.pair input.plan =
        YulangClosure.NativeContextCompletion.rawGuard u parent processing input.pair input.plan
'YulangClosure.NativeContextCallbackConstruction.raw_guard_context_data' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeContextCallbackConstruction.raw_guard_context_data
YULANG_AUDIT_BEGIN YulangClosure.NativeContextCallbackConstruction.batch_completes_from_guards
@YulangClosure.NativeContextCallbackConstruction.batch_completes_from_guards : ∀
  {t : YulangClosure.NativeContextExpansion.Tables} (s : YulangClosure.NativeContextCompletion.CallbackState t)
  (parent : YulangClosure.NativeMergeExpansion.Key) (processing : Nat)
  (inputs : List YulangClosure.NativeContextCompletion.Emission) (f : YulangClosure.NativeDrainOwnership.Frame)
  (fs : List YulangClosure.NativeDrainOwnership.Frame),
  s.native.control.frames = f :: fs →
    f.phase = YulangClosure.NativeDrainOwnership.Phase.working →
      f.current.isSome = Bool.true →
        f.processing = Option.some processing →
          (∀ (input : YulangClosure.NativeContextCompletion.Emission),
              input ∈ inputs →
                YulangClosure.NativeContextCompletion.rawGuard s.native parent processing input.pair input.plan =
                    Bool.true ∧
                  input.plan.reserved = Bool.true) →
            (YulangClosure.NativeContextCompletion.enqueueChildren parent processing s inputs).remaining = []
'YulangClosure.NativeContextCallbackConstruction.batch_completes_from_guards' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeContextCallbackConstruction.batch_completes_from_guards
YULANG_AUDIT_BEGIN YulangClosure.NativeContextCallbackConstruction.batch_receipt_serials
@YulangClosure.NativeContextCallbackConstruction.batch_receipt_serials : ∀
  {t : YulangClosure.NativeContextExpansion.Tables} (s : YulangClosure.NativeContextCompletion.CallbackState t)
  (parent : YulangClosure.NativeMergeExpansion.Key) (processing : Nat)
  (inputs : List YulangClosure.NativeContextCompletion.Emission),
  List.map (fun receipt => receipt.work.serial)
      (YulangClosure.NativeContextCompletion.enqueueChildren parent processing s inputs).receipts =
    List.range' s.native.control.nextWork
      (YulangClosure.NativeContextCompletion.enqueueChildren parent processing s inputs).receipts.length
'YulangClosure.NativeContextCallbackConstruction.batch_receipt_serials' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeContextCallbackConstruction.batch_receipt_serials
YULANG_AUDIT_BEGIN YulangClosure.NativeContextCallbackConstruction.batch_receipt_serials_distinct
@YulangClosure.NativeContextCallbackConstruction.batch_receipt_serials_distinct : ∀
  {t : YulangClosure.NativeContextExpansion.Tables} (s : YulangClosure.NativeContextCompletion.CallbackState t)
  (parent : YulangClosure.NativeMergeExpansion.Key) (processing : Nat)
  (inputs : List YulangClosure.NativeContextCompletion.Emission),
  (List.map (fun receipt => receipt.work.serial)
      (YulangClosure.NativeContextCompletion.enqueueChildren parent processing s inputs).receipts).Nodup
'YulangClosure.NativeContextCallbackConstruction.batch_receipt_serials_distinct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeContextCallbackConstruction.batch_receipt_serials_distinct
YULANG_AUDIT_BEGIN YulangClosure.NativeContextCallbackConstruction.guarded_finished_children_settled
@YulangClosure.NativeContextCallbackConstruction.guarded_finished_children_settled : ∀
  {t : YulangClosure.NativeContextExpansion.Tables} {s : YulangClosure.NativeContextCompletion.CallbackState t},
  YulangClosure.NativeContextReadback.Run t (YulangClosure.NativeContextReadback.initial t) s.native →
    ∀ (owner : YulangClosure.NativeContextReadback.Owner t) (a : YulangClosure.NativeContextExpansion.Availability)
      (levels : Nat → Nat) (fuel : Nat) (body : YulangClosure.NativeContextExpansion.Body)
      (plans : List YulangClosure.NativeContextCompletion.Plan),
      YulangClosure.NativeContextReadback.prepare t a levels s.native.effectMap fuel owner.key =
          Option.some owner.ready.packet.segment →
        ∀
          (finished :
            YulangClosure.NativeContextReadback.finishPrefix t a levels s.native.effectMap owner.key
                owner.ready.packet.segment =
              Option.some body),
          a.publish = Bool.true →
            (YulangClosure.NativeContextCallbackConstruction.bodyPairs t s.native.effectMap owner.key body).length =
                plans.length →
              ∀ (f : YulangClosure.NativeDrainOwnership.Frame) (fs : List YulangClosure.NativeDrainOwnership.Frame),
                s.native.control.frames = f :: fs →
                  f.phase = YulangClosure.NativeDrainOwnership.Phase.working →
                    f.current = Option.some owner.work →
                      f.processing = Option.some owner.relation →
                        s.native.owners owner.work = Option.some owner →
                          (∀ (input : YulangClosure.NativeContextCompletion.Emission),
                              input ∈
                                  YulangClosure.NativeContextCallbackConstruction.emissions
                                    (YulangClosure.NativeContextCallbackConstruction.bodyPairs t s.native.effectMap
                                      owner.key body)
                                    plans →
                                YulangClosure.NativeContextCompletion.rawGuard s.native owner.key owner.relation
                                      input.pair input.plan =
                                    Bool.true ∧
                                  input.plan.reserved = Bool.true) →
                            ∀ (transitions : Nat) (settled : YulangClosure.NativeContextReadback.State t),
                              (have batch :=
                                  YulangClosure.NativeContextCompletion.enqueueChildren owner.key owner.relation s
                                    (YulangClosure.NativeContextCallbackConstruction.emissions
                                      (YulangClosure.NativeContextCallbackConstruction.bodyPairs t s.native.effectMap
                                        owner.key body)
                                      plans);
                                have packet := { key := owner.key, body := body, construction := ⋯ };
                                YulangClosure.NativeContextReadback.Run t
                                  (YulangClosure.NativeContextReadback.finishOwner batch.state.native f fs owner packet
                                    transitions)
                                  settled) →
                                settled.control.queue = [] →
                                  settled.control.frames = [] →
                                    have batch :=
                                      YulangClosure.NativeContextCompletion.enqueueChildren owner.key owner.relation s
                                        (YulangClosure.NativeContextCallbackConstruction.emissions
                                          (YulangClosure.NativeContextCallbackConstruction.bodyPairs t
                                            s.native.effectMap owner.key body)
                                          plans);
                                    have packet := { key := owner.key, body := body, construction := ⋯ };
                                    have completed :=
                                      YulangClosure.NativeContextReadback.finishOwner batch.state.native f fs owner
                                        packet transitions;
                                    YulangClosure.NativeContextReadback.Run t
                                        (YulangClosure.NativeContextReadback.initial t) settled ∧
                                      (owner, packet) ∈ completed.seals ∧
                                        (∀ (child : YulangClosure.NativeMergeExpansion.Key),
                                            child ∈ body.children →
                                              ∃ emitted,
                                                emitted ∈ batch.receipts ∧
                                                  emitted.key = child ∧
                                                    ∃ receipt,
                                                      receipt ∈ settled.receipts ∧
                                                        receipt.work = emitted.work ∧
                                                          YulangClosure.NativeContextReadback.Resolved settled receipt ∧
                                                            YulangClosure.NativeContextReadback.RouteValid settled
                                                              receipt.route) ∧
                                          ∀ (ticket : YulangClosure.NativeDrainOwnership.Ticket),
                                            ticket ∈ settled.control.transferred →
                                              ∃ receipt,
                                                receipt ∈ settled.control.acknowledgements ∧
                                                  receipt.ticket = ticket ∧ receipt.diagnosed = Bool.true
'YulangClosure.NativeContextCallbackConstruction.guarded_finished_children_settled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeContextCallbackConstruction.guarded_finished_children_settled
```

## 9. Freeze and handoff

Delivered module and this evidence are frozen for primary intake. All producer
writes are stopped; no Lean/checker process remains active. Replay callback
construction is queued as subsequent work rather than mixed into this plain
constructor/list-seam checkpoint. The primary owns review, integration, progress
synchronization, commits and pushes.

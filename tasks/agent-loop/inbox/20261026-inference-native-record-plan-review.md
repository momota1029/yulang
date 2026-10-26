# Native record-plan bridge: independent M3 review

Date: 2026-10-26. Assignment ID:
`20261026-inference-native-record-plan-review`; revision **1**.
Reviewer: `/root/native_record_plan_review`, fresh generic leaf fallback,
nonauthor of the Lean module, companion paper and native source construction.
No contributing descendants.

## Decision and unchanged scope

**ACCEPT the frozen native record-plan construction and its joint connection
to the accepted native query derivation. No BLOCKING, major or mandatory
finding; no repair requested.**

This accepts the first-match indexed shape construction, its exact one-resolver
compiler equation, the conditional normal-result applications and the genuine
formal's constructed identity instance. It is an independent mathematical,
Lean-source and native-source review using the producer's verified checker
evidence. It is not a new checker run, a Rust execution result, a full native
history theorem or production semantic approval.

The parent remains the original `SourceProblem.InferenceSoundness` at
`notes/theory/lean/YulangClosure/Contracts.lean:128`: every supported original
source and scope with a generated solved problem must produce an original
source judgment and the corresponding **same** scoped witness. Reading
`CoreComposition.lean:92–106` confirms that `native_success_elaborates`
composes separately supplied native correspondence, inference soundness and
elaboration. None of those complete obligations is discharged by this packet.

Primary-reported baseline: branch `yulang3`, HEAD
`f7c7dcfc5cf2b55aedea5625470e81483d0561b8`. Git was forbidden and was not
used to verify that ref. Reviewed file identities were independently verified
by SHA-256.

## Frozen identities and inherited source evidence

| Artifact | Verified SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/NativeRecordPlan.lean` | `3cf43fdb754748b83a6816791d640752dda491b87f7e2513a27548a950b27d43` |
| `notes/theory/2026-10-26-native-record-plan-construction.md` | `a8cf460f72dbbe521761d1e09c4095c44d471538f4f0fb9c6d1c120e0603446f` |
| `tasks/agent-loop/inbox/20261026-inference-native-record-plan.md` | `80ec857a08d2528f6871ebfd9167be2242af813ef48b97dcf5cc867a95b55b12` |
| `notes/theory/lean/YulangClosure/RecordBoundaryPreservation.lean` | `1bde9224c1b0d568d5cc73d84a5ccc5f1157452c87ea2ff428096c1dbd50d056` |
| `notes/theory/2026-10-26-native-record-query-correspondence.md` — current accepted revision | `7e903edc8348d900954d655f82d9cadb623b47e8224e525602b3cef42777ccd1` |
| `tasks/agent-loop/inbox/20261026-inference-native-record-query-review.md` — including delta acceptance | `743bc17fbceacf5382a4a3d9e11208af563ff87870a6efdfd921205961acb52c` |

The producer's 23-entry `frozen-inputs-checks.json` was checked against actual
bytes. Its only differing current path is the expressly authorized native
query paper: recorded historical SHA
`120b380acae1cf96c45f810f76ab56b375c84b23278c9904b94ffdc60c0e3bc8`,
current accepted SHA shown above. The final native source review verifies that
the delta consists only of the already-typed raw-query equation and local
annotation allocation-order wording. This review read the corrected paper and
that acceptance. The historical producer identity is valid evidence of its
checked input, not an unnoticed source mutation.

All thirteen input hashes in the current native query paper independently
match, including the eleven Rust/HIR files, original manuscript and accepted
Lean consumer. All five isolated project copies also match the repository:
the two Lean modules, `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`. The project remains Lean 4.35.0 with no external packages
and `moreLeanArgs = ["-j1", "-M1024"]`.

The native source review is reused for its full construction/metadata/history
audit. This joint review additionally read the actual record dispatch and
admission owners, source formal/default constructors, Replay construction,
source-label/order preservation and annotation datatype at the critical seams.
No claim of a second native execution is made.

## Independent mathematical and source findings

### 1. First lookup and both original indices

`lookupIndexed` agrees with the actual increasing source enumeration and
`HashMap.entry(...).or_insert(index)` at `lib.rs:14598–14600`. The successful
lookup has both its actual source-list occurrence and the exclusion of every
earlier equal label. `lookupIndexed_signature` erases only the index and
returns the existing first-name signature.

The complete `shape` retains one slot per target in target order, including
missing optional targets. `ValidShape` independently records the lookup,
fixed metadata, target and presence disjunction. `shape_valid`,
`validShape_targets`, `validShape_indexed` and `validShape_child` establish
the advertised invariants. In particular, a slot at position `k` has upper
index `start + k`; projecting out absent slots does not renumber children.
The lower index still identifies the original source occurrence. The general
theorems handle duplicate source labels by selecting the first occurrence.

`Witness.original_upper_index_gap` retains upper index 1 after absent target
0. `Witness.first_duplicate_source` retains the first optional source
specification even when a later same-name source is required. These are
effective discriminators for the two indexing/lookup mistakes.

### 2. Optional payloads and failure precedence

The four `shapeField` cases match `lib.rs:14604–14619`. A missing optional
target creates an absence slot with no child; a common optional target keeps
its payload child. Optionality never excuses a common payload comparison.
Optional-source/required-target is rejected without inventing a presence bit.

`shape` short-circuits at the first bad target and discards any accumulated
prefix on either failure. On the native fresh-dispatch path, missing required
records its direct diagnostic and returns Rust `Ok(())` before diagnostic
child edges or `RecordDispatch` installation (`lib.rs:14621–14641`).
Optional-to-required returns `RecordAdaptationUnavailable` before that new
pair-memo admission. `rustOk` and `diagnostic` model exactly this distinction,
under the explicitly retained allocation/readback/receipt availability
qualification. They do not equate diagnostic recovery with semantic success.

`missing_is_diagnostic_not_admission`, `unavailable_is_not_rustOk` and
`failed_shape_no_children` have the claimed types. The concrete diagnostic
witness contains a successful first child before the missing required field;
it genuinely checks prefix discard. The separate presence witness checks the
unavailable branch. No successful-shape or semantic theorem is inferred from
either failure.

### 3. Metadata and the exact resolver equation

`Hole.boundary : Meta` remains separate from semantic `Ty`, and successful
shape validity proves that every child retains the same supplied metadata
value. The quantification over `Meta` can preserve the entire authentic event
product from the source paper. It does not construct/authenticate that product
or identify a reused relation with the manuscript's semantic boundary `j`.
Original indices and the retained native slices allow the source mapping to
keep raw queries distinct from canonical relation endpoints.

At `candidate_context.rs:3603–3633`, RecordPort admission uses the actual
processing parent, canonical task pair, inherited post-check context, sources
and scoped flow, then records the paired original indices. The Value-child
path cannot take the allowance-only local-context branch. The accepted native
paper's uninterrupted-block interning result supplies syntactic consistency;
the paper correctly does not infer semantic cast agreement across histories
or generations from it.

The new theorem actually proves the complete optional-computation equality:

```lean
shape boundary source index targets = .ok slots →
  fill resolve slots =
    RecordBoundary.compile (RecordBoundary.signature source)
      (fun _ => false) (resolve boundary) targets
```

Its resolver is a single function `Meta → Ty → Ty → Option Cast`. Each
`fillSlot` uses the same boundary and the actual source/target payload types.
No field, index or boundary stamp is hidden in `Ty`; no separately chosen
child casts replace this agreement. `shapeField_fill` uses the first-lookup
erasure and actual admissibility disjunction, and list induction establishes
`shape_fill_compile`. The equality includes resolution failure. Successful
compilation follows only when the independent filling equation is supplied to
`filled_compile`.

### 4. Normal preservation and visible-field survival

The accepted consumer's actual definitions retain independent `ViewTyped`,
`PresenceValid`, `ChildSound` and `Run`; typing is not defined as successful
execution. In `filled_run_preserves`, the all-false known-presence function
makes `PresenceValid` vacuous and does not grant optional-to-required
permission. The other inputs remain explicit:

1. the successful indexed shape;
2. its successful filling;
3. independently typed input under `signature source`;
4. the normal child contract for **the same** `resolve boundary`;
5. an actual run of the constructed plan.

The result is independent visible-output typing under `signature targets`.
`filled_run_survivors` retains shape, fill, input typing and actual run and
correctly needs no child type-preservation premise. It proves, for every label,

```lean
(visible output label).isSome =
  ((input label).isSome && (signature targets label).isSome)
```

The execution reads the current visible input, so neither absent optional
fields nor hidden backing fields are recreated. These are normal-result
properties. They neither establish child termination nor the stronger
request-prefix/typed-resumption contract in the original manuscript. The
existing nontransitivity and distinct accepted-path witnesses remain intact.

### 5. Admission order is only a sibling queue result

`candidate_step_record_dispatch` at `lib.rs:15007–15029` admits children in
reverse vector order, retaining a pending item before front-enqueue.
`enqueue_item` uses `push_front`, and `pop_worklist` uses `pop_front`.
The proved `frontEnqueue_eq` and `reverse_admission_order` therefore have the
advertised application: after all sibling admissions, the queue is the original
child order followed by the old queue. The paper expressly excludes global
descendant scheduling, resumed histories and runtime effect order from that
equation; it does not use queue order as child semantic evidence.

### 6. The source formal and its identity execution are genuine

The exact fixture `my f {required, fallback = required} = fallback` exists at
`candidate_effect.rs:2918–2939`. The HIR and source-action owners retain field
order and binders. At `candidate_effect.rs:1581–1607`, the defaulted second
field gets an incoming row distinct from its fallback binder; default links
occupy source slots 258/259, and the positive/negative record bounds occupy
43/44. The positive and negative payload terms use the same required/incoming
rows. Source occurrence and cause are created by the actual wide-slot link
owner, rather than inferred from payload equality.

`candidate_apply_value` inserts the two opposite bounds, and
`candidate_replay_bound`/`candidate_context_begin_replay` retain their exact
BoundKeys and construct the record query. Its children are `(0,0,r≤r)` and
`(1,1,i≤i)` under the shared row interpretation. The second, optional child
survives. Source-set `None` follows from the seed lookup and Apply-slot-only
checking registration; no fake source singleton is introduced. The default
is not treated as input-presence evidence.

`Witness.formal_shape`, `formal_fill` and `formal_compiles` construct the
exact two-field skeleton and identity filling. The final root has the explicit
`[DecidableEq Ty]` parameter and is uniform in the shared `required`/`incoming`
interpretation and arbitrary independent payload typing. Its pure identity
child contract is proved by `identity_child_sound`; `execute_runs` constructs
the actual run. `Witness.formal_normal_preserves` thus requires independently
typed input, but no supplied child-soundness or run hypothesis. It does not
derive source-input typing or assert that formal generation executes this
mathematical adaptation.

### 7. Original semantic boundary remains an honest residual

The manuscript at lines 356–425 and 479–552 requires actual boundary identity,
one resolver, visible-view semantics, source-qualified unchanged flow and
distinct adaptation output ports. The native formal owner retains a negative
domain and creates constraints; it does not attach executable `RecMap_j`.
The actual `SourceAnnotationValue` datatype has no Record constructor.
The packet therefore does not manufacture a record-annotation example or use
reference/SCC incidence as proof of unchanged-view flow.

The first remaining original-source obligation is still:

```text
elaborate(original source boundary)
  = check/adapt at j(actual input visible port,
                    distinct output visible port,
                    RecMap_j(filled exact native skeleton))
```

The original source/native owner must establish this equation and authenticate
`j`, scope, occurrence/cause and selected child evidence, or classify the action
as only constraint/unchanged-view flow by its source rule. General resolved
child casts, contextual meaning, full request/resumption contracts,
generation-currentness/reuse transport and the complete native Call certificate
remain with their existing owners. This is an explicit incomplete application
of a proved component, not a changed source domain or a new production rule.

## Complete checker-evidence audit

Evidence root:
`/workspace/scratch/f98087c7ac1a/inference-native-record-plan/`.
The audit program was read, not merely its totals: it selects constants by
actual originating-module index, includes private/generated constants, rejects
originating axioms, requires every named root to be theorem-valued, prints each
type and transitive axiom list, and rejects dependencies outside the permitted
standard set. The script is tied to the frozen source and isolated build.

A read-only parser independently verified **251 unique matched begin/end
declaration blocks**, each with its type and axiom result, including **32
private declarations**. The audited environment reports **122 theorem
constants** and **28 required authored roots**. All required names are present;
their full printed types were inspected, and their extracted blocks match the
complete audit byte-for-byte. Definitions, generated declarations and theorem
counts are not conflated.

| Complete transitive axiom set | Originating declarations |
| --- | ---: |
| None | 202 |
| `propext` | 35 |
| `propext`, `Quot.sound` | 13 |
| `Quot.sound` | 1 |

No `Classical.choice`, nonstandard/project axiom, `sorryAx` or unchecked native
evaluation dependency occurs. The new module and accepted direct dependency
also have no source matches for proof holes, project axioms, unsafe replacement,
`implemented_by`, `native_decide` or kernel-check bypasses. The final audit
contains no error or warning marker.

| Evidence | Verified SHA-256 |
| --- | --- |
| `project/NativeRecordPlanAudit.lean` | `d796400704556f33dc9b84e3a537b45d141e61735a339906ce14289203b98cae` |
| `audit02.log` | `593c06e6201329431854fb8197ab8c10679f5154a3161ffef25671d6dc12aea6` |
| `named-root-audit.txt` | `a1038c834a28ee6453cfb54ffbee8ceb3c31f441af81e02cb65cc34a4e9d80cc` |
| `named-roots.txt` | `3d5b6dbde205daec5e2970bbd9e72e69390e34c0e4888560778bafd40d6c98df` |
| `check04.log` | `99b245f20c5a84bb43db3aa13c7a0a0060d17ddfd395484b3f928afb0c7785a4` |
| `commands.jsonl` | `e4228268db73e92a91e43d7645867d6950b38c54d6c964797b85c20113353f65` |

All eight command-log hashes match their manifest entries. The actual version
logs identify Lake `5.0.0-src+eb6cafb` and Lean `4.35.0`, Release commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. The final focused build exits 0
with three jobs; the complete audit exits 0. The producer consumed six
build/audit calls and two version calls, under its recorded 120-second,
single-thread, 1-GiB Lean bounds. The failed first/third builds and initial
audit are retained and match the described elaboration/tactic and audit-print/
memory failures. No timeout or failure was hidden by the final success.

The integration import/default-target check remains the primary's task. The
review found no evidence discrepancy requiring an additional checker grant.

## Authority, resources and cessation

Read the root operating maps, design authority, top-level inference principles,
goal-driven/M3 rules, full current native-inference progress note, assignment
handoffs, `yulang-lean-proofs` and its source/execution references, actual
original contracts and selected manuscript clauses. The selected manuscript
remains research semantics; this review grants no new compiler authority.

Review budget: **900 seconds**. Consumed **zero Lean/Lake invocations, zero
Cargo/native tests or probes**. Work used bounded source/log reads, searches,
SHA-256 comparisons and parsing of already-produced audit output. No Git,
producer/Lean/Rust/configuration/import edits, shared status writes, child
agents or background process were used. Requested specialist model/effort and
observed runtime model metadata were not supplied in the assignment; no model
execution claim is made.

Exact write lease used: this receipt only. The granted scratch directory
`/workspace/scratch/f98087c7ac1a/inference-native-record-plan-review` was not
needed. Producer artifacts and accepted dependencies remain untouched.
Primary owns adjudication, integration, publication and remaining source
obligations. **Writes stopped after freezing this revision. No descendants,
unresolved subleases or background work remain.**

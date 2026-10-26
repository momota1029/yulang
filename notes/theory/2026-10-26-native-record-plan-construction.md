# Constructing the exact native record plan

Date: 2026-10-26. Research-only constructive component; submitted for fresh
nonauthor M3 review. Producer: `/root/native_record_plan_construction`, generic
leaf fallback for the unavailable registered `lean_prover`. The primary owns
Git, imports, shared progress and review. The original
`SourceProblem.InferenceSoundness` remains **OPEN** with its original source
domain, shared witness, complete Call, hygiene and semantic premises unchanged.

## 1. Original claim and constructed result

The original target is `SourceProblem.InferenceSoundness` in
`YulangClosure/Contracts.lean:128`: every supported source and scope, generated
constraint and successful solution must yield an original source derivation
and `sameScoped` witness. `native_success_elaborates` in `CoreComposition.lean`
composes that obligation with native correspondence and elaboration; it does
not prove any of those inputs.

This packet reduces a specific record-boundary construction premise. The
original manuscript's section beginning at
`docs/yulang-whole-language-semantics-ja-expanded-20261023.tex:356` requires one
resolver at a boundary, every common optional payload comparison, target-order
execution and visible-view survival. The previously committed
`RecordBoundaryPreservation.lean` supplies the compiler, independent typing,
normal execution and survivor consumers. The new `NativeRecordPlan.lean`
constructs the preceding indexed scan and proves exact compiler agreement.

For arbitrary `Meta`, `Ty`, `Cast`, source and target field lists, start index,
fixed boundary `boundary : Meta`, and **one** resolver
`resolve : Meta → Ty → Ty → Option Cast`, the checked root is:

```lean
shape boundary source index targets = .ok slots →
  fill resolve slots =
    RecordBoundary.compile (RecordBoundary.signature source)
      (fun _ => false) (resolve boundary) targets
```

This is `YulangClosure.NativeRecordPlan.shape_fill_compile`. It is an equality
of the complete optional computation, including resolution failure, not an
assumption that the resulting compiler call succeeds. `filled_compile` derives
the successful compiler equation from a constructed `fill = some plan`.
`filled_run_preserves` and `filled_run_survivors` immediately apply the committed
consumers with explicit independent typing/execution premises. The genuine
source formal has a fully constructed identity filling and normal-preservation
instance, described below.

## 2. Exact native correspondence

The frozen source derivation is
[Native record queries](2026-10-26-native-record-query-correspondence.md),
SHA-256 `120b380acae1cf96c45f810f76ab56b375c84b23278c9904b94ffdc60c0e3bc8`.
The actual dispatch owners were also inspected directly:
`crates/yu-solver/src/lib.rs:14593–14653`, `:15007–15029`, and
`candidate_context.rs:3603–3633`. No native tests or Rust changes were made.

| Native operation | Constructed representation and checked property |
| --- | --- |
| Increasing source enumeration, `HashMap.entry(...).or_insert(index)` | `lookupIndexed` selects the first matching name. `lookupIndexed_signature` proves erasure to the existing signature; `lookupIndexed_occurrence` recovers the original list occurrence; `lookupIndexed_first` excludes every earlier equal label. |
| Increasing target enumeration | `shape` scans targets in order, increments the original upper index even for an absent optional target, and retains the full slot list. |
| Missing optional target | `Slot.absent upperIndex target` survives in the full skeleton and fills to `FieldPlan.absent`; it contributes no child query. |
| Admissible common field | `Slot.child Hole` retains fixed boundary metadata, original lower/upper indices, source specification and target field. Both optional declarations still produce a child. |
| Optional source to required target | `Failure.unavailablePresence lower upper`; no presence assumption is invented. |
| Missing required target | `Failure.diagnosticMissing upper`; the entire scan is classified as diagnostic recovery, with no admitted prefix children. |
| `RecordPort` incidence | `validShape_child` recovers the exact boundary, original source occurrence and target occurrence at the original upper index. |
| Reverse child admissions and front enqueue | `reverse_admission_order` proves the initial sibling queue equals the original child order followed by the old queue. It does not assert global descendant or runtime-effect order. |

`Hole` keeps metadata separate from `Ty`. To apply it to an actual event,
`Meta` must contain the source/action identity, occurrence/cause, selected and
transported processing relation, raw query/record slices, post-check context,
sources and scoped flow already identified by the frozen source derivation.
The theorem is uniform in that whole product and preserves it verbatim. It does
not authenticate an arbitrary supplied `Meta`, identify a RelationId with an
original semantic boundary, or equate raw and canonical payload identities.
The native `Dependency::RecordPort` name and its paired original indices are
preserved at the correspondence layer; compacted child-vector indices are not
substituted for them.

Actual finite labels may be encoded injectively by the consumer's `Nat` labels.
A fixed payload interpretation supplies `Ty`; no boundary, label or index is
inserted into semantic payload types to force resolver agreement. The source
lookup here is a simple recursive proof-side transcription; its output matches
the first-match table. No native complexity claim or production replacement
follows from that representation.

### Successful shape validity

`shape_valid` constructs `ValidShape` by induction over the actual scan.
`validShape_targets` proves that the full slots project exactly to the target
list. `validShape_indexed` proves every slot at position `k` is valid at original
upper index `start + k`. For a child `hole`, `validShape_child` gives:

```lean
hole.boundary = boundary ∧
source[hole.lowerIndex]? = some (hole.targetField.1, hole.sourceSpec) ∧
∃ position, hole.upperIndex = start + position ∧
  targets[position]? = some hole.targetField
```

The underlying validity additionally retains first lookup and the source-
required/target-optional admissibility disjunction. Consequently the common
field cannot disappear merely because its runtime optional value is absent.

### Failure and order limits

The mathematical `Except Failure` uses `.error` for either nonaccepted scan
outcome. It must not be confused with the Rust `Result`: `rustOk` and
`diagnostic` explicitly expose that missing-required returns Rust `Ok` with a
diagnostic, while unavailable presence is a Rust availability error.
`missing_is_diagnostic_not_admission` proves diagnostic `Ok`, the exact missing
index, zero admitted children and impossibility of a successful shape.
`unavailable_is_not_rustOk` proves its separate classification. These flags
classify the two record-specific branches under availability of the native
allocation/readback/receipt operations; they do not model unrelated resource
failures.

`failed_shape_no_children` covers a failure after any prefix. The concrete
`Witness.diagnostic_discards_prefix` has a real first child followed by a
missing required field. Its result contains no partial skeleton. The scan
short-circuits in original target order; later failures do not replace the
first one. The queue theorem covers reverse admission/front enqueue only;
per-child transport, descendants, interruption/resumption and effectful child
execution remain with their existing owners.

## 3. One resolver and the consumer application

`fillSlot` calls `resolve hole.boundary sourceTy targetTy`; `shape_valid`
ensures every child has the same boundary. Hence erasing metadata does not
permit different answers to an equal payload pair at that boundary. Arbitrary
individually preserving casts cannot replace this one-resolver obligation.

`shapeField_fill` proves the field equation from lookup erasure and admissible
presence. Induction over the full target list gives `shape_fill_compile`,
retaining absence slots and exactly every common child. No known-presence bit
is set: the consumer receives `fun _ => false` throughout.

`filled_run_preserves` has exactly these independent inputs:

1. `shape boundary source index targets = .ok slots`;
2. `fill resolve slots = some plan`;
3. `ViewTyped typed (signature source) input`;
4. `ChildSound typed (resolve boundary) child`;
5. `Run child input plan trace output`.

Its conclusion is `ViewTyped typed (signature targets) (visible output)`.
The false known-presence function makes `PresenceValid` vacuous, rather than
supplying input-specific presence facts. Existing source typing still ensures
required source fields actually exist.

`filled_run_survivors` uses the same shape/fill equations, independent input
typing and actual run, and needs no child type-preservation assumption. For each
label it concludes the exact equation:

```lean
(visible output label).isSome =
  ((input label).isSome && (signature targets label).isSome)
```

These are normal-result statements. They neither prove child termination nor
supply the manuscript's stronger contract over request prefixes and typed
resumptions. They add no direct record-comparison transitivity rule.

## 4. Constructed original-source formal instance

The genuine fixture is:

```yulang
my f {required, fallback = required} = fallback
```

The frozen source derivation traces the real RecordParameter action, binder
identities and incoming default row. It yields
`R+ = [required!:r+, fallback?:i+]` and
`R- = [required!:r-, fallback?:i-]`; source slot 43 inserts the producer bound
and slot 44 the demand on the same formal row. The real opposite-bound Replay
constructs their record query. This is not a hypothetical record annotation:
`SourceAnnotationValue` has no Record constructor. The default expression is
not a presence witness for `fallback`.

Under one shared row interpretation, `Witness.formalFields required incoming`
encodes the two labels as 0 and 1. `Witness.formal_shape` computes exactly:

```text
child(boundary, lower=0, upper=0, required ≤ required)
child(boundary, lower=1, upper=1, incoming ≤ incoming)
```

The optional incoming child is retained. For any `DecidableEq Ty`,
`Witness.identityResolve` returns the unit identity cast on equal payload types.
`Witness.formal_fill` constructs both casts; `Witness.formal_compiles` derives
the committed compiler equation. `Witness.identity_child_sound` proves normal
preservation for actual pure identity child execution, for arbitrary independent
payload typing. No child-soundness hypothesis is supplied for this instance.

The final required source-instance root is:

```text
YulangClosure.NativeRecordPlan.Witness.formal_normal_preserves
```

For every fixed boundary, shared required/incoming payload interpretation and
independently well-typed input view, it proves that executing the constructed
identity plan returns a well-typed view of the formal record. The input typing
premise remains explicit. The result describes the constructed consumer plan;
it does not assert that formal-domain generation executes that adaptation.

Additional checked discriminators are `Witness.original_upper_index_gap`
(missing optional target 0 followed by a child whose upper index remains 1),
`Witness.first_duplicate_source` (the first duplicate specification wins),
`Witness.diagnostic_discards_prefix`, and `Witness.presence_unavailable`.

## 5. Exact remaining source obligation

The full original source proof still needs the genuine source-elaboration
connection:

```text
elaborate(original source boundary)
  = adapt/check at j(actual input visible port,
                     distinct output visible port,
                     RecMap_j(filled exact native skeleton))
```

The `j`, ports, scope, occurrence/cause and selected child evidence must come
from their actual original owners. The record formal constructs domain/default
constraints and retains a negative formal domain; this does not establish an
executable `RecMap_j` or a new output port. If an action is only a constraint or
unchanged-view flow, its source rule must classify it accordingly. Reference/
SCC incidence alone cannot supply that classification.

The existing source/native owner must discharge that equation; the semantic
child owner must supply general resolved casts and the full request/resumption
contract, and the complete native Call certificate producer remains separate.
Generation-sensitive reuse and resumed/reconstructed histories also remain
separate. This packet does not narrow source syntax, optional records,
open-row/default/spread behavior, context/effect hygiene or complete Call.

## 6. Checker evidence, complete audit and failed attempts

The isolated project is
`/workspace/scratch/f98087c7ac1a/inference-native-record-plan/project`.
It contains exact copies of the three committed project configuration files,
the frozen `RecordBoundaryPreservation.lean` dependency and the delivered new
module. No shared build cache, root import, configuration, toolchain or package
was changed. The pin is Lean 4.35.0 with no external dependencies.

Native executable:
`/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
Actual versions: Lake `5.0.0-src+eb6cafb` (Lean 4.35.0), Lean `4.35.0`, x86_64,
commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release.
The known sandbox self-location issue required approved native subprocess
execution. Every subprocess used `subprocess.run(timeout=120)`,
`LEAN_NUM_THREADS=1`, and project/explicit `-j1 -M1024`. No limit was increased.

| Invocation | Outcome | Seconds |
| --- | --- | --- |
| `version` — Lake version | exit 0 | 0.067 |
| `lean-version` — Lean version | exit 0 | 0.294 |
| `check01` — First focused build | exit 1 | 4.908 |
| `check02` — Repaired focused build | exit 0 | 3.116 |
| `check03` — Strengthened proof build | exit 1 | 3.138 |
| `check04` — Final clean focused build | exit 0 | 3.472 |
| `audit01` — Initial all-constant audit | exit 1 | 6.961 |
| `audit02` — Final all-constant audit | exit 0 | 1.485 |

There were six focused build/audit invocations out of 18 granted, plus two
version lookups (eight bounded native invocations if counting all commands).
No Cargo runs, native tests/probes, children, Git operations or Rust edits.

`check01` exposed a function-composition simplification, constructor binder
order and underconstrained index/failure binders; these were repaired without
changing the claims. `check03` found an extra tactic after simplification had
already closed the goal; removing it produced `check04`'s clean build.
`audit01` failed on unsupported `pp.maxDepth` and excessive memory during the
initial audit command elaboration. The repair used the repository's established
minimal audit imports/options and explicit array types; limits were unchanged.
The original script is retained as `audit01.lean`, with its failed log. No
failure was relabeled as a theorem counterexample or erased.

`audit02` enumerates every constant by its actual originating module and prints
its type and transitive axiom inventory. It rejects originating project axioms,
missing named theorem roots and any axiom outside the standard permitted set.
It covers **251 total originating declarations**, including **122 theorem
constants** and **all 28 authored theorem roots**; private and generated
constants are included. These counts are deliberately separate.

Across all 251 declarations: 202 have no axioms, 35 use only `propext`, 13 use
`propext` and `Quot.sound`, and one uses only `Quot.sound`. No `Classical.choice`,
project axiom, `sorryAx`, unchecked native evaluation or checker bypass occurs.
A source scan of the new module and direct dependency finds no proof holes,
project axioms or bypasses. Standard axioms are reported, not described as an
axiom-free result.

The complete printed output is `audit02.log`; all 28 named-root blocks are also
retained in `named-root-audit.txt`. No further optional checks were run after
this complete successful audit. Fresh independent review and the integrated
import/default build belong to the primary.

### Exact named roots

All names have the `YulangClosure.NativeRecordPlan` namespace prefix:

- `lookupIndexed_signature`
- `lookupIndexed_occurrence`
- `lookupIndexed_first`
- `shapeField_valid`
- `shape_valid`
- `validShape_targets`
- `validShape_indexed`
- `child_mem_slots`
- `validShape_child`
- `failed_shape_no_children`
- `missing_is_diagnostic_not_admission`
- `unavailable_is_not_rustOk`
- `frontEnqueue_eq`
- `reverse_admission_order`
- `shapeField_fill`
- `shape_fill_compile`
- `filled_compile`
- `filled_run_preserves`
- `filled_run_survivors`
- `Witness.formal_shape`
- `Witness.formal_fill`
- `Witness.formal_compiles`
- `Witness.identity_child_sound`
- `Witness.formal_normal_preserves`
- `Witness.original_upper_index_gap`
- `Witness.first_duplicate_source`
- `Witness.diagnostic_discards_prefix`
- `Witness.presence_unavailable`

## 7. Frozen identities

SHA-256 of the final Lean source, direct dependency, original source inputs and
three configuration files:

| Repository path | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/NativeRecordPlan.lean` | `3cf43fdb754748b83a6816791d640752dda491b87f7e2513a27548a950b27d43` |
| `notes/theory/lean/YulangClosure/RecordBoundaryPreservation.lean` | `1bde9224c1b0d568d5cc73d84a5ccc5f1157452c87ea2ff428096c1dbd50d056` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `cab85ff9a8a7dc5103fe932739dcea0dfc02e6420b1277565449882c802473bd` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| `notes/theory/2026-10-26-native-record-query-correspondence.md` | `120b380acae1cf96c45f810f76ab56b375c84b23278c9904b94ffdc60c0e3bc8` |
| `tasks/agent-loop/inbox/20261026-inference-native-record-query.md` | `5abf9e4a683a2e75d064f78d8e5bab7df3a03a88ad0bdfe85e21067a9adbed89` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| `docs/yulang-whole-language-semantics-ja-expanded-20261023.tex` | `28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65` |

All following evidence files are in
`/workspace/scratch/f98087c7ac1a/inference-native-record-plan/`:

| File | SHA-256 |
| --- | --- |
| `project/NativeRecordPlanAudit.lean` | `d796400704556f33dc9b84e3a537b45d141e61735a339906ce14289203b98cae` |
| `run.py` | `92ad1740d2010dcb03565ffc924df52bb48bdc99e2a66c463f6358cee2f1d351` |
| `commands.jsonl` | `e4228268db73e92a91e43d7645867d6950b38c54d6c964797b85c20113353f65` |
| `named-roots.txt` | `3d5b6dbde205daec5e2970bbd9e72e69390e34c0e4888560778bafd40d6c98df` |
| `named-root-audit.txt` | `a1038c834a28ee6453cfb54ffbee8ceb3c31f441af81e02cb65cc34a4e9d80cc` |
| `check01.log` | `41309cc5e8bcf5e5fd6c385e5785490d9d586334fb8e6e51f0abc3f60c8cf921` |
| `check02.log` | `9234aafd25fd228a8c64ef01bc15ae826bdb526cf2f197d75bcc062244aad8fe` |
| `check03.log` | `fd71a95bbaad0988178956d4436383987abb6b0db96660c59a6235149b70ede7` |
| `check04.log` | `99b245f20c5a84bb43db3aa13c7a0a0060d17ddfd395484b3f928afb0c7785a4` |
| `audit01.log` | `f6ffb91052d8fcd9097b330c7a74ce38bf904cb3692d861cc643c986fd6e700e` |
| `audit02.log` | `593c06e6201329431854fb8197ab8c10679f5154a3161ffef25671d6dc12aea6` |
| `version.log` | `165f92ed239a8c7db772bf5ee9d58c59357b489951582a12c86dc9d8e06b23a2` |
| `lean-version.log` | `eb22144228dd41cd51a0c84af4f976cd0cef473102dcf99b60be756b11f2b95a` |

The JSON manifest `frozen-inputs-checks.json` retains the same exact paths and
hashes. The companion handoff freezes this note's hash and cessation receipt.
Only the exact leased Lean module, this note, the handoff and own scratch were
written. The Lean source was frozen before documentation; all writes cease
when the handoff is emitted. No independent review acceptance or whole-source
closure is claimed by this producer.

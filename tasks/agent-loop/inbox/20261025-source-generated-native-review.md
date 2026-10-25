# Independent source/native review — frozen revision 1

Sprint SOURCE-GENERATED-INTERACTION-20261025/r3-evidence, contract SHA-256
`f608e1280fae70fd60f983399426dc1786c6f9c59578a95c64a667cf7efff7d2`.
Reviewer `/root/isolated_native_review_01a17247`; parent session
`01a17247-73d1-7663-9c3b-ff5b5b9c2ef1`. Requested gpt-6-astra/medium;
observed model/effort UNKNOWN. Nonauthor, sole author of this review, no children.
Baseline `0132d07ca7e149b59f529469d1479a1c8cfa577a`; exclusive checkout
`/tmp/yulang-source-interaction-01a17247-20261025`, branch
`codex/source-interaction-01a17247-20261025`. Only write lease: this file.
All relative source references below resolve inside that checkout.

## Verdict and findings

ACCEPT the frozen low-route evidence as a provisional source/native experiment,
with the limitations below. Native immutable-extension correspondence remains
BLOCKED. No production change, compiler-bug classification, paper theorem,
original Simple-sub A/B closure, or ordinary-execution acceptance is certified.

1. **Blocking correspondence finding:** repeated pending-local publication is
   not a globally fresh immutable extension. The decisive operation is the
   second publication into the saved `Frame::Local.cell`, not the later fresh
   allocation of the recursive closure. Static source equations substantiate
   the mechanism; the integer 56 alone would not do so.
2. **Material harness/evidence defect:** both public calls use a filename without
   `.yu`. Their `StructuralProjection` is explainable at source export indexing
   before runtime. These receipts do not establish refusal of the source family
   under a valid filename. The ordinary route with a valid filename is UNTESTED.
   All four authorized attempts remain consumed. No repair or rerun was made.
3. **Evidence limitation:** same-HIR candidate conflicts=[] does not certify
   diagnostic-free typing or preservation. Both low runs retain three HIR
   diagnostics; useful local provider rows explicitly have
   `captures_truncated=true`, `replay_child_receipt=false`, and
   `preservation_complete=false`. Many other provider queries return
   `ArtifactMismatch`. These are preserved limitations, not successful proofs.

## Frozen evidence and provenance

Independently read and matched these SHA-256 values:

| Artifact | SHA-256 |
| --- | --- |
| example `tools/inference-playground/examples/source_generated_interaction_20261025.rs` | `d65f979a94001ee393e6075b227c793368231bb9d98c12373db1a758673a0c09` |
| native r1 handoff | `227c601d2bb26186196b421933be91f0e0f78d2c77c8d4df0bd9b8ae0cf0517b` |
| native r2-isolated handoff | `2478ec05454474a8f84e0b42d580f3ed11e0dfe8c1935c875283dcd5bf7698f6` |
| verification JSONL | `132cab00236c36c7072d5fdf11eccb86681fc6ebc2c34a6351887e89282a0b43` |
| runtime/machine.rs | `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e` |
| runtime/program.rs | `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907` |
| runtime/continuation.rs | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| playground src/lib.rs | `45bf78af436efa50e02ca97ba3b639c11f7dd88272d87c47f2822643786653d4` |
| crates/yu-hir/src/module.rs | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` |
| crates/yu-hir/src/module/source_exports.rs | `03727fd3918738a48afde7f7a875de60b63b43ac2cc620896a4ed73d8b0a9179` |

The eight-row ledger retains commands, timestamps, stdout/stderr, source text,
input hashes before/after and output hashes. All eight before/after input maps
are equal. Native rows 5–8 follow the single successful locked/offline/-j1 build
(row 4, 43.781650 seconds); intervals are disjoint and timeout flags false.
The four run durations total 1.066472 seconds. Binary hash recorded by the runs
is `1ba1b6588641dc3833ae3d0b351499f51bafc65353b2d5a7c0e3825e53bf4ce2`.
I audited those stored receipts; I did not independently rerun the executable.

| Row | Case / route | Recorded outcome |
| --- | --- | --- |
| 5 | immediate / default research | integer44, 126 steps, exit0 |
| 6 | immediate / public | source imports unavailable: StructuralProjection, exit1 |
| 7 | escaping / default research | integer56, 128 steps, target44 mismatch, exit1 |
| 8 | escaping / public | same preparation refusal, exit1 |

Example lines79–99 parse with empty syntax environment, reject syntax recovery,
lower with local source and empty imports, retain diagnostics, solve the same
Arc<HirModule> and check candidate identity/conflicts. Lines106–146 expose
retained binder/expression identities and bounded solver provenance. Lines149–160
pass that HIR to `RuntimeProgram::from_hir` with DEFAULT evidence, then start and
step the actual Machine. The candidate itself is not the evidence supplied to
RuntimeProgram. This is the stated research route, not `from_candidate_world`.
Three diagnostics in each run are UnsupportedItem on the act declaration and
UnsupportedExpression on relay/main. Their presence was not erased.

## Source construction and concrete native equations

Example lines59–76 generate actual handler source: `first = k 11`, then
`second = k 23`; before the request `old = 5`; afterward
`recur again = if again: recur false else: int_add response old`.
Immediate resumes return `recur true`; escaping resumes return `recur`, and
both closure invocations occur only after the second resume. The observed HIR
has k uses resolving to CatchBinder ordinal1, old/response/recur resolving to
main local ordinals0/1/2, and recur's self use resolving to that same local2.
For immediate, recur call occurrence37 has a provider row targeting local2;
escaping calls occurrences16/20 target relay local0/1. Debug source keys and
owner payloads include `{ .. }`; they are not complete externally decoded IDs.

The following source-derived symbolic cells are explanatory names, NOT claimed
observed private numeric IDs:

- `program.rs:605–645,749–763` finds the actual self-resolved local during its
  parameterized initializer walk and marks its LocalBinding recursive.
- `machine.rs:2520–2538` reserves a fresh cell before each local initializer.
  Thus old is already published when response's initializer requests tick;
  response has a pending Local frame with reserved cell c. The request unwinder
  retains ordinary frames (`2315–2317`), and `capture_template:1859–1868` clones
  that Local frame, including c and its environment, into the template.
- Internal Continuation application (`1211–1223`, ResumeArgument `1063–1077`)
  creates the invocation, forces/checks its response, and enters the saved
  template with an empty control map. It does not allocate a new response cell.
- `enter_template:1932–1951` clones/pushes the saved Bind frame. Its only frame
  rewrite here concerns a callback ValueEntry owner, not Local.cell.
  Owner nodes (`1954–1986`) reuse active owners or create fresh invocations;
  their control map does not rename cells. View nodes (`2010–2016`) retain
  view/receipt lineage, not a cell-store snapshot.
- `Frame::Local:1541–1559` writes `self.cells[cell] = Some(ReceivedValue { ... })`
  unconditionally. First replay writes response11 into c and extends a new
  environment referring to c. The suffix then reaches begin_local for recur,
  allocating fresh self cell r1. Lambda (`864–885`) stores that environment;
  recursive publication retains it. Second replay of the same pending response
  frame writes response23 into c, then allocates fresh recursive self cell r2.
  Fresh r1/r2 and closure values do not make their shared response reference fresh.
- Lookup (`785–815`, `2585–2594`) selects a cell by exact binder through environment
  parents, then reads its CURRENT ReceivedValue. Both escaping closures retain
  an environment path to c; both retain a path to the already-published old5.
  Their true invocation takes their own self edge once, then false reads captures.
  Immediate's first capture read occurs before the second publication; escaping's
  first read occurs after it. This explains 16+28 versus 28+28 at the source-equation
  level, rather than inferring cell identity from the numeric output.

No hidden dispatch snapshot compensates on this route: RuntimeEvidence derives
Default (`program.rs:90–104`), so contextual_dispatch=false and dictionaries=None
(`1243–1252`). `initializer_environment`, `substitute_environment`, and
`dispatch_name` (`machine.rs:2601–2624`) consequently preserve parent/environment
or current ReceivedValue. Even when enabled, substitute_environment appends a
binder-free dispatch environment; no cell copy occurs in that equation.
`consume:2475–2495` checks view/value consistency and records a receiving receipt
for the value already selected from the cell. It does not recover an old cell
content. This supports HIGH confidence in the low-route mechanism. It is not
an authenticated per-transition private-store trace or a general correspondence
proof for all dictionary/receiving configurations. Internal repeatable source k
is separate from one-use host resume (`machine.rs:599`); this probe uses no host
resume entry.

## Exact public StructuralProjection producer/consumer

The harness calls `execute(&source, case, ...)` at example.rs:39, with case equal
to `immediate` or `escaping`. `lib.rs:495` only changes the special name `-`;
`lib.rs:522` installs the unchanged name as FileKey path. At `lib.rs:523`,
`with_source_imports_and_role_indexes` calls `resolve_source_imports`
(`crates/yu-hir/src/module.rs:820`), whose selected implementation calls
`index_source_exports` at module.rs:360. That index delegates to
source_exports::index (`module.rs:2329`), which requires module_label at
`source_exports.rs:728`. `module_label:1062–1064` requires a `.yu` suffix.
Neither passed case name has one, so None becomes StructuralProjection.

`lib.rs:525–540` consumes that error and attempts an empty-import fallback. The
source has no explicit imports, but local lowering retains the three HIR errors;
the fallback requires errors().is_empty(), so returns the printed preparation
failure. `execute_runtime:271–275` never reaches from_candidate_world or
execute_program after that Err. This is a concrete invalid-name preparation
boundary. Correcting the filename could expose another refusal or succeed;
those possibilities have no execution receipt here. Do not claim the current
public results establish an inherent effect-source import limitation.

## Parent application, exact residual and falsifier

Original parent remains the immutable-extension lemma and thm:safety in
`docs/yulang-operational-type-safety-ja.tex`, with its original quantifiers,
all relevant arena entries, arbitrary reference sorts, finite recursive families
including zero, source typing, full-operation matching and repeated resumes.
The separately defined Lean sourceFresh/localcycle theorem is not refuted by a
native transition that has not been related to its constructors. Its hypotheses
must be established at the native/source owners; do not silently narrow them.

TODO SOURCE-GENERATED-NATIVE-CELL-1, owner primary source/proof intake: establish
binder → environment → cell → published value → closure capture/read → replay
and receiving-view/dispatch correspondence, accounting for second publication
of an existing pending cell and all historical closure/arena entries. A naive
relation that fixes old-node denotations and represents each resumed binding as
an immutable fresh extension fails at the second `cells[c]` publication: the
first escaping closure's retained edge now reads23 rather than11. Moving c's
abstract interpretation without preserving that old edge is not an extension
proof. The exact falsifier is the paired publication/read transition above,
conditional on that proposed relation, not merely output56 or a blanket claim
that no possible relation can exist. A replacement relation or runtime semantic
change requires primary authority and fresh independent review.

Public-route follow-up owner: primary native evidence intake. A future separately
authorized packet must use valid module filenames and retain any subsequent
source/admission failures; the exhausted four-run grant is not renewed here.
Full native bridge, immutable-extension parent, thm:safety/full paper and original
A/B remain OPEN; this specific naive native correspondence is BLOCKED.

## Resource and STOP receipt

Read-only source/receipt/hash inspection only, within the300-active-second grant;
no renewal. No Cargo, tests, Lean, source execution, formatter, scratch files,
Git mutation, production edit, process left running, or descendant was started.
Two shell lookup errors and unavailable `python` were followed by narrow corrected
reads and `python3` ledger parsing; no verification run was attempted.
Only this report was written, inside the exclusive isolated checkout.
Independent certification covers this review only, not producer or primary prose.
Writes STOP after this frozen revision; zero outstanding processes, zero children,
zero unresolved descendant leases. Final SHA and final clock accompany delivery.

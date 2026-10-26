# Native Value relation execution — independent review r4

## Verdict and independence

**ACCEPT for the exact relation-call/decoded-admission/shared-control component
below. No BLOCKING, major or minor correctness finding remains in that scope.**
This does not accept whole native inference correspondence, semantic Value/Effect
soundness, conflict-free diagnostics, termination, or the original
`SourceProblem.InferenceSoundness` parent. Those remain OPEN.

Reviewer: `/root/value_drain_review_r4`; producer: `/root`. The reviewer did not
author or coauthor this module and supplied no repair to its proof. Prior
independent reviews of its frozen interner and drain dependencies are distinct
from this fresh composition review. Source inspection, original Rust cuts,
complete elaborated contracts and independent boundary probes supplied the
review evidence; the producer's narrative was checked against those sources.

Exact repository write lease: this receipt only. Scratch lease:
`/workspace/scratch/f98087c7ac1a/value-relation-review-r4/**`.
No Git, producer edits, shared import/status/config edits, children or delegated
writers were used. `AGENTS.md`, preserved base rules, the Lean proof skill and
its execution/source map, compiler-referee guidance, original closure contract,
and actual `Contracts.lean` parent definitions govern this review. Observed
reviewer model: GPT-6 Astra Pro; exact sampled reasoning effort unavailable.

Review started 2026-10-26 13:38:15 UTC, with a 1200-second wall bound and at most
two focused bundles. Both bundles are complete; no further Lean call is needed.

## Accepted frozen bytes

| Artifact | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/NativeValueRelationExecution.lean` | `118138bd45cef3db837a0742010944cdd0c513e9d352302d23889e497a89c4ea` |
| `notes/theory/2026-10-26-native-value-relation-execution.md` | `ec65e8d612d3f5ddf0561c806975fbc562ace199fa7304af3888460bedb7dfc5` |
| `tasks/agent-loop/inbox/20261026-native-value-relation-execution-r4.md` | `631eaa5be9fc74c845742b59149cc9a206194cd353d8939e220f4eff4bda49ab` |
| `value-relation-r4/freeze.json` | `695aab34dd5f304b6ce1172fbbefeaad75a8426434fabe7dd7bba3037f8b71f7` |
| Producer artifact manifest | `0bdbd0ba7dea44934a1f6b42eba58b43ce44a1fe67c709cd8987632630fa6d8d` |
| Producer dependency/configuration manifest | `00e1a16e2fb26946d793ec8a5a50c8c20ee01c02365cdc8fb6564aaad74f3701` |
| Producer original-source/authority manifest | `66b94a1e9264f0968eee673061c34ac0507c4c6a605924bfdb717ef1bfc741c2` |
| Complete originating census log | `46355122ddd0ff711136197490bfabcba425305b4b452c47f1b40a034cd22d53` |

The final reconciliation independently verified all 152 scratch artifact hashes,
all 14 fixed dependency/configuration hashes against both repository and copied
project, all ten native/authority inputs, and the exact twelve-module import
cone including the target. All eleven dependency `.olean` files in the reviewer
copy equal the frozen producer artifacts. No unreviewed downstream module was
included. Repository output hashes are unchanged from the producer's explicit
13:37:53.919279 UTC writer stop.

Frozen baseline is the producer's recorded
`a9c746f31cc0eabeba9ebf5b673b6f121ed0ca82` on `yulang3`; this reviewer performed
no Git operation. The original parent keeps its supported-source quantifiers,
generation/solution hypotheses, original source judgment and same-scoped witness.

## Source correspondence and actual theorem contracts

The reviewed source cut is `candidate_context.rs` 2630–2656 (Context interning),
2795–2815 (scope-transformer interning), 3062–3094 (physical relation call), and
3511–3669 (four port admissions); `candidate_scope.rs` 269–280 (retained capacity
bytes); `candidate_source.rs` 217–246 (inventory charge and `from_plan`); and
`lib.rs` 14261–14287, 14344–14352, 14955–15054, 15223–15250 (preflight, Transport,
structured child stages and enqueue). The exact four Rust hashes are retained
in the verified source manifest. The proofs and accepted dependencies were read
against those implementation operations, including their failure order.

### Physical allocation constructs the decoded receipt

`Store.arena` is computed from one `Native` interner and its Context/transformer
vectors. No independently chosen relation vector appears in `Store`. `prepare`
uses full raw-task renaming, the source-weight view, child-local Context outside
the inherited post-check operation, the original sources field, and complete
Flow/demand behavior of the exact port. Preparatory constructors preserve the
relation vector. `prepared_physical_tables` establishes equality of the entire
prepared Arena with the physical store's decoded tables, not a subset of keys.

`physical_relation_constructs_admission` quantifies over stores, views, maps,
complete parent/child/key, post Context, derived flag, prepared tables, resources
and raw ID. Its premises are `NativeHistory store.native`, the actual successful
`prepare` equation and `allocate (store.tables prepared) resources key =
(after, ok id)`. It concludes the original `NativeValuePorts.admit` equation
with exactly `after.arena` and `id`, output NativeHistory, physical `readback id
= some key`, and the full `AdmissionResult`. No chosen reflection equation,
finished child body, semantic subtyping premise, local safety oracle or selected
matching middle state is assumed.

The construction uses the already independently accepted
`native_ok_refines_arena` at its actual call output. `registered_is_physical_readback`
then turns any retained Arena receipt into the physical RawKey/FlowId readback
by constructor-derived history. Ghost `Entry.origin` is not presumed equal to
physical decoding; the interner history proves that equality. Physical map
lookup/allocation does not consult ghost origin/birth or occurrence serials.

### Resource and failure boundary

`Funding.preparationWork` remains the observed successful external preparatory
inventory amount. `inventory` checks both integer maximum and the 65536 work
bound, updates the same physical counter and constructs `NativeRun.inventory`.
`admit` passes the actual prepared Context-vector length to `allocate`, overriding
the caller's Context count. It does not authorize an invalid post Context by
accepting an exaggerated resource field. Native Context assertion is reified as
an assertion boundary; it is not an ordinary availability success.

After this call is reached, `Some (after, Except.error failure)` retains its real
new Flow and charged work. `admission_attempt_keeps_history` covers both outcomes.
`admission_success_refines` assumes the actual `.ok` result and supplies the same
Arena output/receipt, physical decoding and full AdmissionResult. `drive` cannot
turn an `.error` into a receipt. The loop is a successful projection and returns
`None` on failure; complete failure-store extraction belongs to the lower admission
cut and remaining whole-trace owner. The note states this distinction correctly.

This review does not infer `preparationWork` from logical transformer cardinality.
Rust uses retained capacities, size arithmetic and reservation paths, with reuse
before fresh allocation. Initial `ScopeInventory::from_plan` also preserves
`plan.scoped_work_used` before its extra inventory charge. Their authentic input
suppliers remain explicit; no real initial store is silently identified with a
zero-work empty model.

### One physical state, occurrence history and computed outer branch

`State.decoded`, `admitted_decoded` and `enqueued_decoded` equate the same state's
full cursor, complete raw-task table, receipts and control projection. Enqueue
uses the receipt's immutable admitted relation, pushes a fresh occurrence to the
front of the arbitrary old queue and advances the source cursor. Existing frames
and their current processing relation are preserved. `ParentPresent` reads
`frame.processing` separately from immutable `frame.current` occurrence identity,
so native Transport is not collapsed into a false identity equation.

`drive_refines_emit` assumes an initial NativeHistory and the actual successful
physical drive equation. It derives output NativeHistory and exact equality with
the existing decoded `emit`. It is a one-way success refinement: pure Arena
allocation does not prove physical resource availability.

`physical_children_pipeline` additionally requires the prior control Run from
initial, the actual processing parent lookup, successful `prepareAll`, and the
actual computed drive output. It constructs the middle Run. For every subsequent
Run starting at that exact emitted control state, empty queue and frames imply
source-order jobs with matching whole raw tasks, complete AdmissionResults,
physical readback at each receipt's same raw ID, and occurrences in diagnosed,
`returnReady`, empty-pending/current returned frames. Neither the continuation's
existence nor termination or diagnostic conflict freedom is concluded.

`context_execution_inputs` derives the identity-transformer/candidate guards,
actual structural family and child vector, real preflight and exact drive equation
from `executeChildrenAfterContext = some emitted`. `context_physical_pipeline`
uses those computed items; a caller does not select a favorable child list or
independently matching middle state. Duplicate, canonical/retained rewrites,
shortcut, diagnostic, unavailable and fallback branches retain their source owners.
The adapter's `None` on these routes does not narrow the original language or
redefine native acceptance.

## Complete declaration and axiom audit

The census enumerator selects declarations by originating module index, not just
namespace prefix. This includes delayed generated equations whose printed names
belong to imported namespaces, private matcher equations and generated structure
operations. It rejects originating axioms and collects transitive axioms for every
entry. Every BEGIN/END block, complete type and exact-name axiom report was checked;
all blocks equal the preserved producer JSON records, with no omissions,
replacement characters, truncated terms, warning or error in final checks.

| Population | Count | No axioms | `propext` | `propext`, `Quot.sound` | All three permitted axioms |
| --- | ---: | ---: | ---: | ---: | ---: |
| All originating declarations | 180 | 134 | 32 | 6 | 8 |
| Theorem constants | 63 | 31 | 19 | 5 | 8 |
| Authored theorem roots | 29 | 6 | 10 | 5 | 8 |

There are 22 private declarations, including 15 private theorem constants.
All three means `propext`, `Classical.choice`, `Quot.sound`. No project axiom,
accepted `sorryAx`, native-evaluation assumption or kernel bypass occurs. The
source scan of the exact import cone found only an explanatory comment mentioning
an axiom; the ordinary function named `admit` is not a proof hole. Complete source
contracts and all elaborated type/axiom records are retained in
`value-relation-review-r4/all-origin-types-and-axioms.txt`.

Producer checks07/08 pass on the exact final source. Checks01/02/04–06 retain
their real syntax, dependent-elimination, normalization, namespace, implicit
Store and decidable-instance failures, including diagnostics generated by failed
elaboration. Check03 is the superseded earlier success. Every check's log and
source snapshot digest, exit and measured limits was independently reconciled.
No failed or superseded check is presented as final proof evidence.

## Independent focused verification

The reviewer copied the frozen project/cache into the exclusive scratch lease.
Pinned Lake `5.0.0-src+eb6cafb` and Lean `4.35.0`, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, were confirmed directly. No dependency,
global setting or repository configuration was changed. Each bundle had a
119-second aggregate wall bound, one CPU/thread, `-j1 -M1024`, and 1280-MiB
aggregate descendant RSS ceiling. Output was captured through EOF.

Focused01: target recompilation exited zero; the independent probe file exited
one because `decide` failed to synthesize the eight-field tuple equality's
Decidable instance. This was a reviewer-only proof elaboration failure, not a
producer counterexample. The exact first probe and its full failed output remain
preserved. Only that scratch proof changed to kernel definitional equality (`rfl`).
Focused02 rechecked the probes without rebuilding the target and exited zero,
with no warning, error, omission or nonstandard axiom. Both calls are charged to
the two-call budget.

Nine independent probes establish:

1. Enqueue retains an arbitrary old control queue as its exact suffix.
2. It uses the receipt's admitted relation and preserves current processing frames.
3. Two identical child keys reuse raw ID zero while producing distinct occurrence
   serials one and two; front queue serials are `[2,1,0]`, old relation999 remains,
   and issued serials are `[0,1,2]`. Second-call allocation flags are disabled;
   existing Flow/key reuse still succeeds with exactly one Flow/relation/work unit.
4. Preparatory work65537 is rejected by the 65536 bound.
5. Preparatory work7 is rejected with an integer maximum6.
6. Preparatory work65536 remains recorded when the subsequent new Flow exhausts
   the work limit, yielding an error and no Flow or relation.
7. Actual outer Context/Function dispatch computes four physical child receipts
   with IDs1–4 and work13 without a child-list input.
8. That outer computation has a constructed NativeHistory and one control Run
   from initial, using the pipeline's actual premises.
9. An actual duplicate outer route cannot become successful child execution.

The arbitrary-old-queue computation is a transition/projection test, not a claim
that its arbitrary fixture is an authenticated native prefix. The separate outer
history witness supplies genuine constructors of both formal histories. Work13
uses explicit model resource observations, not a claim about Rust ABI capacities.

Final probe axioms are six `propext` only, two `propext` plus `Quot.sound`, and
one all three permitted axioms. Complete printed types and lists are in the log.
The two bundles took 8.978125600995554 and 2.0780483780035865 seconds; aggregate
checker wall time11.05617397899914 seconds. Peak aggregate RSS957595648 bytes.

| Independent artifact | SHA-256 |
| --- | --- |
| First probe snapshot | `7f5e47d11d16fda6d58e6cb27aadbb9b8cf7721cea1fb57a468c62cca8f7ba1d` |
| First full log | `5498f5b5f62d12060927153d1f44c1907f6b7df60173ea1282d4030c1fa60731` |
| Final probe snapshot | `187feb4dc043f8db71bf7423488bcfead6639ad69563fcba10fdfba12d9e11d8` |
| Final full log | `a54a27d8f360d69728ecbc2b5746683a30328061a442925f382e3fbbeb88cf82` |

Exact commands, versions, individual exits, PIDs and resource measurements are in
`value-relation-review-r4/focused01.json`, `focused02.json` and the corresponding
logs. `integrity.json` and `focused-summary.json` retain independent reconciliation.

## Parent application and remaining original owners

The decoded-Arena/physical-relation output seam is now closed within this
successful projected child loop. Whole-execution extraction still needs authentic
initial native/control histories and their chronological relationship; actual
`from_plan` retained work; canonical maps and complete raw term/table readbacks;
the true post-check Context and derived-mode observations; physical Context/scope
allocation, capacity-derived work and preparation failure traces; post-relation
Dependency publication, lifecycle/source-support invalidation, sampling and
enqueue/undo reservations; and global rollback/table-lifetime integration.

The original semantic owners still need complete Value/Effect meanings, conflict-
free acceptance, full source Kernel clauses, general recursive introduction and
one authentic same-scoped source witness. No receipt or diagnosed quiescent return
is substituted for these obligations. The accepted note and handoff preserve
these boundaries; no producer repair was requested or made during this review.

## Cessation

Final live/frozen hash reconciliation passed. Every recorded producer and reviewer
checker PID is absent, all output readers reached EOF, and no descendant exists.
Both permitted focused bundles have been used. After this receipt is written and
hashed, all reviewer writes and processes stop. Primary `/root` alone owns
publication, Git, shared reconciliation and any subsequent assignment.

Writes-stopped receipt UTC: `2026-10-26T13:47:12.219175+00:00`.

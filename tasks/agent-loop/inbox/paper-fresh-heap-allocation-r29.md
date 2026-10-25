# R29 worker handoff — revision 1

Sprint: PAPER-FRESH-HEAP-ALLOCATION-R29/r1. Contract SHA-256
`1859d9a005b9bfbff2fd98de5bf7e2d984b48f890cd42ca37b5909f5439d8c70`.
Baseline supplied by primary: `79b7a88a0cca341306d399dbb0b788d298540612`.
Checkout: `/tmp/yulang-r29-fresh-heap`.
Author: `/root/r29_registered_lean_prover`; no descendants or coauthors.
Requested role: registered `lean_prover`. Effective model/effort: UNKNOWN.
Primary launch acknowledgment was received before reads, construction or checks.

## Outcome and source boundary

Outcome class: conditional intermediate; focused module build ACCEPTED;
complete printed-type/axiom audit NOT_RUN; independent review NOT_RUN;
source/native and production authority OPEN.

Original parent: manuscript `docs/yulang-operational-type-safety-ja.tex:324–326`
(rec fresh simultaneous allocation) and `:981–990` (immutable graph extension).
Manuscript SHA-256 `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
The opening 2026-10-23 correction explicitly leaves whole-language source
correspondence open; the machine-specific source-owner correction is not erased.
The manuscript is a research source, not production semantic approval.

The original claim allocates all recursive RHSs together, preserves old nodes,
extends their graph types and requires the resulting graph guard. This module
constructs only finite payload typing/allocation for an explicitly ordered
`List (Nat × Ty × Value)` input. Head is de Bruijn index zero by definition.
`HeapPayloadTyped` requires every stored pair to have a graph lookup and a
`PaperValueTyped` derivation; it is not the omitted manuscript heap judgment.

Parent application: `YulangClosure.PaperTypes.FreshHeap.finite_allocation` consumes
one block's nodup IDs, graph/heap disjointness, its exact per-entry RHS derivations,
the one shared `TermSubstitutionTyped` tail, and old payload typing. It proves
old graph lookup preservation, exact new graph lookups, actual public whole-list
Option substitution success, exact new-list length/prefix/suffix, exact per-entry
new heap lookup, all successful old heap lookups and all-node payload typing.
`each_rhs_substitution` separately proves the actual per-RHS public Option success
and the unchanged matching entry type. No independent type/RHS list or zip is
accepted. `formals`, RHS/type lists and output nodes all map the same block.

First remaining application premise: a real source rec block must correspond to
this de Bruijn ordered block and its shared source context, fresh identities,
old heap payload derivations and tail substitution. Owner: Luna/source-order
proof lane. The next independent graph premise is the checked source rec guard
implying guardedness after this allocation; owner: Luna/graph guard proof lane.
No theorem here proves that premise. Body substitution and full omitted raw
forms remain outside R29. Original A/B, inference/executor preservation,
source/native correspondence and production stay OPEN.

Represented: the existing R28 supported partial `PaperValueTyped` constructors,
including variables/references/literals, tuples/sequences/records with their
existing presence constraints, delay, both lambda entries, wraps, sum/view forms,
continuations, type abstraction/application and recursive type roll, with the
represented computation/continuation cases supplied transitively by R27/R28.
Omitted: variant/nominal typing, handlers/mappers, recursive term typing,
full pattern/primitive/template-body typing, full term/type/name substitution,
source-formal ordering, native allocation, and guarded cycles. No represented
source constructor or quantifier was removed to prove a theorem.

## Changed paths and frozen source hashes

Changed/new source: `notes/theory/lean/YulangClosure/PaperFreshHeapAllocation.lean`
SHA-256 `7cd87b8e5fd43eea0206401de6ed91e817755f3d1ad2c5aeee1caf0dd1732925`.
Audit path `notes/theory/lean/.lake/R29Audit.lean` is ABSENT: generation failed.
Checks log: `tasks/agent-loop/inbox/paper-fresh-heap-allocation-r29-worker-checks.txt`
SHA-256 `ec4283642d9431019043a0024eab0372babb2ed4b4f89b4558968946c364284c`. This handoff is the only other worker-written path.
Cache outputs are confined to leased `notes/theory/lean/.lake/build`.
No root import, compiler/Rust, tests, shared status, rules, configuration,
manifests/lockfiles, dependencies, questions or other workers' files were edited.
No Git, network, installation, nested CLI or runtime probe was used.

Imported source cone (read-only dependencies except the new module):

- `notes/theory/lean/YulangClosure/PaperFreshHeapAllocation.lean`: `7cd87b8e5fd43eea0206401de6ed91e817755f3d1ad2c5aeee1caf0dd1732925`
- `notes/theory/lean/YulangClosure/PaperTermSubstitution.lean`: `a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f`
- `notes/theory/lean/YulangClosure/PaperExecutionGraphWeakening.lean`: `b0ff39ad89fcb83559cca3147ae55fa7e7f6c31c1b130ec9cd7608e33d1f696e`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`: `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41`
- `notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean`: `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a`
- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`: `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`
- `notes/theory/lean/YulangClosure/PaperTypeFormation.lean`: `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`
- `notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean`: `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`
- `notes/theory/lean/YulangClosure/DeclSubst.lean`: `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`

## Actual checker evidence and material failures

Native Lake was resolved by read-only `elan which lake` to
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Pin read from `lean-toolchain`: `leanprover/lean4:v4.35.0`.
Worker ran no version query: primary said its two pinned-version calls had
already been consumed. Their literal version output was not present in this
isolated checkout, so this handoff does not invent that receipt.

All commands ran in `notes/theory/lean` with `LEAN_NUM_THREADS=1`;
`lakefile.toml` supplied `-j1 -M1024` to module Lean processes.
Full stdout/stderr and command argv are preserved in the checks log.

1. Native `lake build +YulangClosure.PaperFreshHeapAllocation`: exit 1,
   25.554 s. Dependencies built; construction failed on reserved identifier
   `prefix`, map composition reduction and insufficiently fixed membership
   elaboration. Complete diagnostics retained.
2. Same focused target after actual source repair: exit 1, 0.638 s.
   Four residual diagnostics: membership inverse inference and function
   composition reduction for mapped identity lists. Complete diagnostics retained.
3. Same focused target after those repairs and finite parent application:
   exit 0, 0.736 s. Final module accepted; no proof edits followed.
4. Native `lake env lean -j1 -M1024 .lake/R29Audit.lean`: exit 1,
   0.493 s. File missing. The preceding Python attempt to reuse the skill's
   `audit_source` function raised `NameError: name '__file__' is not defined`
   because its execution namespace supplied `__name__` but omitted `__file__`.
   The next shell command still invoked Lean. Both the exception and exact
   missing-file diagnostic are preserved. This is the third failed checker
   invocation and triggers mandatory STOP. No retry or further Lean/Lake call.

Worker total: 4 literal Lean/Lake invocations; 27.421 checker seconds;
3 failed checks. Cap: 10 calls / 120 checker seconds / 900 active seconds.
Observed aggregate active-work duration: UNKNOWN (no runtime duration metadata).
The STOP rule fired before the call/checker caps. No full/default build or tests.

Source scan: 9 imported modules, pattern recorded in checks log;
0 matches. This scan is not an indirect axiom audit.
The successful module build is kernel acceptance of declarations, not the
complete theorem/axiom audit or independent certification.

## Exact audit handoff

All 21 public theorems require their printed full types and `#print axioms`.
Complete axiom results: UNKNOWN / NOT_RUN for every name below. Reject
`sorryAx`, project axioms, `Classical.choice` and any axiom beyond `propext` and
`Quot.sound`. Definitions/abbreviations also need printed types and axiom reports.
Do not infer empty dependencies from source scanning or successful build.
Namespace prefix for every following theorem:
`YulangClosure.PaperTypes.FreshHeap.`

- `graph_old_lookup`
- `graph_new_lookup`
- `rhs_values_typed`
- `block_substitution`
- `each_rhs_substitution`
- `nodes_length`
- `exact_front_suffix`
- `heap_new_lookup`
- `heap_unallocated_lookup`
- `heap_old_success`
- `old_payload_transport`
- `allocation_payload_typed`
- `finite_allocation`
- `duplicate_graph_falsifier`
- `old_collision_falsifier`
- `zip_truncation_falsifier`
- `two_formal_order`
- `swapped_replacements_heap`
- `sequential_heap_falsifier`
- `self_alias_payload`
- `self_alias_block`


The discriminator theorems cover duplicate graph shadowing, old identity
collision, zip truncation, two-formal order, swapped replacements, sequential
substitution changing an actual heap, and a self alias with actual lookup.
`self_alias_block` computes the actual allocated block; `self_alias_payload`
shows that its payload relation accepts the self edge. This is not a
counterexample to the paper's guarded allocation rule. Guard remains OPEN;
`ValueGraph.guarded` is never used in the new module.

Suggested primary preparation under a newly accepted exact audit-path lease:
load the skill checker helper with both `__file__` and `__name__` defined,
call its pure `audit_source` for all 21 names, write only `.lake/R29Audit.lean`,
and tighten the helper's axiom whitelist by removing `Classical.choice`.
Append `#check @name` / `#print axioms name` for all public definitions.
Then run the reserved pinned audit command once. The helper's default CLI would
write a temporary file outside this worker lease and repeat version/build calls;
that is why manual leased audit generation was attempted. This is a handoff,
not authorization for extra worker checks. Primary must adjudicate its own
first-failed-final-check stop rule before spending any reserved verification.

## Cache manifest and cessation

Cache files: 72. Canonical manifest format: sorted relative-to-project
file paths, one `SHA256  path` line per regular file, UTF-8, trailing newlines.
Manifest SHA-256: `4d5f44291a2bf8f60c6c3eccf08c5b2d1da6e846e8c4d42f69962cb60f2ed10b`.
Compiled import artifacts:

- `.lake/build/lib/lean/YulangClosure/DeclSubst.olean`: `fc92b93c9fc06c2c46f2e24b2bbf2bad9b91f2a72cad342915aa1b1ebb757d84`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionBinderLaws.olean`: `227e35771697e5b3d9a80d8084c5adc97a0335e34f1a3416208f102729814e92`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionGraphWeakening.olean`: `7740b9e6364575a0cc854e2f10e1414c5f6ea49fd0835c2bb40d220459dc422c`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionSyntax.olean`: `ac07871e5a744591d3061c0c8cec2f8028af94f7effc357b426d6fd18d7cbc95`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionTypingSubstitution.olean`: `163355c3adc9fe16419de6f123b82ecbf8a60abd5eba8edee2c52947708480ad`
- `.lake/build/lib/lean/YulangClosure/PaperFreshHeapAllocation.olean`: `f0bb0a8313fda6abfebf50f823a7fbaf3e2a63b56dc90930415a554442a68135`
- `.lake/build/lib/lean/YulangClosure/PaperTermSubstitution.olean`: `060abefba49155cab1a46847b4080bd8de4c03bf9616f6f7971df6f0ec716799`
- `.lake/build/lib/lean/YulangClosure/PaperTypeFormation.olean`: `29ee574dd7be22f9897457c3a3b98481a8126e88fcfd254d68bc84aae9b78497`
- `.lake/build/lib/lean/YulangClosure/PaperTypeSubstitution.olean`: `7f1a41d6dd1b5c6b4924f27d8e9bddedab0ae9e2468377cfc2f9dfd6811bd2f9`


At 2026-10-25T17:51:39.590826+00:00, all worker checker subprocesses had returned via `communicate`;
a read-only `ps -eo pid=,comm=,args=` found no `lean` or `lake` process.
Descendants: none created; unresolved descendant leases: none.
Worker state: STOPPED after this handoff write. Writes stopped: YES, as of the
final handoff/hash receipt sent to primary; source/cache are already frozen.
No audit artifact exists to freeze. No background process or pending writer.

Mutual TODO R29-AUDIT-1: primary must decide whether its remaining verification
budget can cover audit preparation and full printed-type/axiom evidence, then
assign fresh independent review. Until then this is a build-accepted intermediate
with audit failure evidence, not a complete proof packet or parent closure.

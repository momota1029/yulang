# EFFECT-PERMISSION-SOURCE-ALLOCATION/20261029-r6 — proof handoff

Assignment: `/root/effect_permission_source_allocation_r6_lean`, revision 1.
Outcome: **constructed but unchecked conditional transcription**. No kernel,
independent-review, source/native or production closure is claimed.

## Frozen scope and dependencies

- Contract: `tasks/agent-loop/sprints/effect-permission-source-allocation-20261029-r6.md`, SHA-256 `812beaeb74094d99019450616deee57de2656cdf531a2b039400134d96bde58a`.
- Manifest SHA-256: `2c46fa74983fe5324750a9ab85301b0c4a70ae72188362d734d7657de2842c69`.
- Baseline: `d33805eb589ac89925bacab57e362df093456fe0` plus the pinned overlay.
- Imported R5 artifact: `YulangClosure.FormalPermissionAuthenticatedNativeDecode`, SHA-256 `ea97baf7c98becef27df9e0c416d8d5fb00e9e1b5b63f37021b01598231936dc`.
- Source owners: `candidate_effect.rs` SHA-256 `1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717`; `lib.rs` SHA-256 `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`.
- Read source handoff: `tasks/agent-loop/inbox/effect-permission-source-allocation-r6-source.md`, SHA-256 `f2a0b85bd67027f62c0e7ecd77793e88ecf0cd47e0e7f9c5cea05850f859efa9`.
- Changed Lean artifact: `notes/theory/lean/YulangClosure/FormalPermissionSourceAllocation.lean`, SHA-256 `08a45daffede0bbc126d1f6da087c70a6c6abcd22be9ed9bdb7f8d1400c68b10`.
- Only other write: this handoff. No scratch, generated files, shared caches,
  root imports, source code, toolchain, manifests, Git, tests or instrumentation.

Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1, 3, 5, with `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6.
It quantifies over every supported original source program and lawful finite
history, retaining actual occurrences and one joint source-scoped witness;
required soundness, principal coverage, progress and termination remain OPEN.
The bounded R6 fragment does not reduce that original scope.

Governing effect policy: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`
§1, §1.1, §1.2: composed variance, concrete identity, annotation permission
separate from actual inflow/subtraction, original symbolic dependencies retained.
Research manuscripts/maps and this transcription grant no semantic authority.

## Source-to-transcription map

- `candidate_effect.rs:1604–1614`: wrapper row preflight. The selected successful
  port constructors allow omitted rows or negative nonempty concrete rows with
  no variables, which meet the selected preflight cases.
- `candidate_effect.rs:1617–1691`: `SourcePair` / `SourceTuples` encode Int, Unit,
  Function recursion with `!p` for argument and `p` for result, then argument
  port and result port; Tuple children remain ordered. `NoElementEffects`
  preserves the actual tuple element guard. Nonempty output shapes must be
  supplied; empty tuple traversal exists internally but cannot construct a
  successful Tuple value.
- `candidate_effect.rs:1694–1786`: `SourcePortSuccess` encodes only omitted and
  selected negative-concrete cases. Source row position, concrete list and
  context parameter/occurrence/owner/scope remain explicit. Both live effect
  operands share the independent fresh ordinal.
- `lib.rs:10487–10517`: `Allocator` has four independent list vectors plus a
  permission sequence. `FreshStep n` carries the entry bounds-length equation,
  alignment of all four vectors, level, successful u32 bound and four successful
  capacity witnesses. `Allocator.push` actually appends one entry to each.
  `FreshStep.ordinal` reads the pre-push bounds length; `FreshStep.next` reads
  the post-push length. `fresh_step_equations` invokes `fresh_success_ordinal`.
  The port result count is obtained from this independent push, then from the
  endpoint of its supplied helper frame; it is not read from the decoder.
- `Reserved` states old capacity fits, monotone new capacity and space for one
  new element. Actual allocator success, Rust Vec content preservation across
  reservation, checked byte arithmetic, resource sampling and capacity callbacks
  still require the execution bridge. These witnesses are not availability
  promises and failures after an allocation are not modeled as rollback.

`Projection` contains effect-row count and a **local permission delta**.
`HelperFrames.cons` requires exact equalities of both fields across every
represented helper edge; `nonallocating_helpers_frame` only composes supplied
edges. No concrete Rust helper frame instance is established. Port frames start
with an empty delta for an omitted port or one exact entry for a concrete port.
The concrete frame endpoint is mapped to the port emission. Function/tuple/leaf
boundaries also carry explicit frame witnesses, but no completeness claim says
that every actual transitive helper call has been represented by that list.

These are local deltas because the prior global `permissions` prefix is outside
`ValueDecoded`. Preservation of that prefix and its reattachment are explicit
remaining execution obligations. The structural Function recurrence concatenates
argument-child entries, result-child entries, argument-port entries and
result-port entries; Tuple prefixes ordered element coordinates and shifts its
tail. Thus decoder correspondence accumulates the two R5 entries in one output,
rather than using independent witnesses for them.

## Declaration types and hypotheses (not printed/checker accepted)

Namespace prefix below: `YulangClosure.FormalPermissionSourceAllocation`.
The exact source declarations remain the authoritative candidate types.

- `fresh_success_ordinal {α β γ δ : Type} (bounds : List α) (levels : List β)
  (metadata : List γ) (marks : List δ) (b : α) (l : β) (m : γ) (z : δ)
  (_ready : FreshReady bounds.length)
  (hl : levels.length = bounds.length) (hm : metadata.length = bounds.length)
  (hz : marks.length = bounds.length)` concludes
  `bounds.length < 2^32 ∧ (bounds ++ [b]).length = bounds.length + 1 ∧
  (levels ++ [l]).length = bounds.length + 1 ∧
  (metadata ++ [m]).length = bounds.length + 1 ∧
  (marks ++ [z]).length = bounds.length + 1`.
- `nonallocating_helpers_frame {s t : Projection} (frames : HelperFrames s t)`
  concludes `s.effectLength = t.effectLength ∧ s.permissions = t.permissions`.
  Its hypotheses are actual per-edge equality premises, not concrete helper laws.
- `successful_pair_allocation_footprint {c : Context} {p : Bool} {a : Annotation}
  {code : ValueCode} {s : State} {out : ValueDecoded c p s}
  (run : SourcePair c p a code s out)` concludes
  `AllocationTrace s.nextEffect out.births out.state.nextEffect`.
  `AllocationTrace` is the chronological no-gap fresh sequence relation; its
  append lemma composes at exactly the preceding endpoint.
- `successful_pair_permission_entries`, with the same quantified parameters
  and `run` premise, concludes
  `∀ entry ∈ out.entries, Origin out.shape p entry.path entry.allocatedRow
  entry.metadata ∧ Owned c entry.metadata ∧ entry.allocatedRow ∈ out.births`.
  It reuses `event_origins_and_births` on the same constructed output's events.
- `source_pair_decoder_correspondence`, with the same parameters and `run`,
  concludes `decodeValue c p s code = some out`.
- `r5_source_allocation_instance (s : State)
  (out : ValueDecoded FormalPermissionAuthenticatedNativeDecode.context false s)
  (run : SourcePair FormalPermissionAuthenticatedNativeDecode.context false
  FormalPermissionAuthenticatedNativeDecode.tree
  (FormalPermissionAuthenticatedNativeDecode.code 0 1) s out)` concludes
  `out = FormalPermissionAuthenticatedNativeDecode.output s 0 1 ∧
  out.entries = FormalPermissionAuthenticatedNativeDecode.retained s.nextEffect ∧
  out.births = [s.nextEffect, s.nextEffect+1, s.nextEffect+2, s.nextEffect+3] ∧
  out.state = {s with nextEffect := s.nextEffect+4}`.

Additional candidate theorems needing type/axiom audit:
`AllocationTrace.append`, `fresh_step_equations`, `source_port_event`,
`port_decoder`, `source_tuples_decoder`, `source_port_allocation`,
`successful_tuples_allocation`. All fully qualified names use the prefix above.

The R5 application is explicitly **conditional on SourcePair**. This artifact
has not constructed an exact-tree SourcePair witness from four FreshStep and
complete helper-frame witnesses. It does prove the proposed consequence of
such a witness using the unchanged R5 recurrence, with one shared `out` for both
retained rows. No native entry State of 21 follows. Unsupported Bool/Str,
variables, holes, symbolic/covariant explicit ports, failed tuple guards,
annotation link admission, propagation, capture/export authenticity, consumer
residual and unequal transport are omitted from this bounded artifact; their
parent obligations are preserved.

## Actual execution and failure evidence

Primary dispatch explicitly prohibited Lean/Lake/checker execution before a
separate release. No such release was given before this freeze; the primary
requested writes stopped before its audit. Therefore:

- Lean/Lake/checker invocations: **none**.
- Actual native versions, exits, printed types and transitive axiom sets:
  **NOT RUN / UNKNOWN**. Project files were read: `lean-toolchain` pins
  `leanprover/lean4:v4.35.0`; `lakefile.toml` has `-j1`, `-M1024`; manifest has no
  external packages. These are configuration observations, not execution receipts.
- Read-only shell commands (`cat`, `sed`, `rg`, `sha256sum`) and two targeted
  Python text edits ran. The last combined hash/search command returned exit 1
  because `rg 'sorry|admit|^axiom|skipKernel|native_decide'` found no matches in
  the changed module. This is only a direct source scan, not a dependency audit.
- No mathematical/Lean diagnostic failure has been observed because the checker
  has not run. Do not infer acceptance from source inspection.

Suggested primary audit: skill checker on module
`YulangClosure.FormalPermissionSourceAllocation` and all six roots plus helper
claims above, in the already primary-owned isolated project. Freeze exact bytes,
argv/environment and copy provenance first. Print complete types and every
`#print axioms` result; retain diagnostics and repair only under a renewed exact
lease/budget. At most two audits, 90 seconds each / 120 combined, per contract.

## Parent application and first remaining premise

The candidate connects a successful **transcription** to R5's exact recurrence.
First missing proof: construct the selected SourcePair run from actual successful
Rust helper execution, including four-vector alignment/content preservation,
all transitive nonallocating frames, resource/term/copy success, local-delta versus
full-prefix permission correspondence, actual source/identifier extraction and
full successful return. Owner: primary source/native bridge lane. A separate
bounded mathematical step can construct the exact-tree SourcePair witness from
explicit successful allocation/frame witnesses; that still does not authenticate
Rust execution or observe State 21. Original A/B and production gates remain OPEN.

Resource: approximately 8 minutes elapsed in this leaf, within 600 active seconds;
zero descendants, compiler/test runs, checker runs or generated-output writes.
Worker state: **WRITES STOPPED** on both leased files at this revision. No live
process, scratch writer or descendant remains. Awaiting primary audit/intake;
no independent certification or commit-ready claim.


## Primary audit attempt 1 — failed Lean build (2026-10-29)

The primary released exactly one focused audit under frozen plan
`/tmp/yulang-effect-permission-source-allocation-20261029-r6/audit-inputs-1.json`,
SHA-256 `9009e3b12b187044c077bd27ebf95a85ef35cd8da82f55216cc55cbf3f7d3aa0`.
Pinned binaries reported Lake 5.0.0-src+eb6cafb / Lean 4.35.0 and Lean commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. The project build failed before any
requested theorem type or transitive axiom audit was emitted (exit 1, 12.21 s,
798448 KiB max RSS). The first diagnostic is `unexpected identifier; expected }` at line 96:68 in `Allocator.push`. Later diagnostics include `mutual` rejected at line 166:55, dependent elimination failure at 226:24, an unsolved function case at 236:49, kernel mismatches in the recursive decoder, the reserved identifier `at` at 279:13, tuple-case/type errors, and a namespace-end error. Their causal relationship is not established; preserve each as an observed diagnostic rather than labeling them all downstream fallout. The module was not checker-accepted. No second invocation
or repair has occurred.

Raw receipts:
- stdout: `lean-receipts/attempt-1/stdout.txt`, 8937 bytes, SHA-256
  `047a92062f3bf6e71f4df8f661edc276af42913f2f46c35c27b1b5e6dbd71e5a`
- stderr: `lean-receipts/attempt-1/stderr.txt`, 33 bytes, SHA-256
  `0edf2d238840b65a26de68075c964d099167cf4cae51705f162bcfa4e7addc60`
- status: `lean-receipts/attempt-1/status.txt`, exit `1`, SHA-256
  `4355a46b19d348dc2f57c046f8ef63d4538ebb936000f3c9ee954a27460dd865`
- resources: `lean-receipts/attempt-1/time.txt`, SHA-256
  `cd6e6f67b96e753ecd67f9e5f733664d75cda5ec0d247b4b76e23a364affbc5b`

The changed artifact remains byte-frozen at SHA-256
`08a45daffede0bbc126d1f6da087c70a6c6abcd22be9ed9bdb7f8d1400c68b10`. The
checker created `.lake/` in the isolated project; any repaired retry needs a
new separately frozen project/copy receipt or an explicitly justified clean
cache plan. This compiler receipt contains no theorem types or axiom sets.


### Diagnostic-order correction (primary, after initial closeout draft)

Independent review prompted a complete ordered scan of raw stdout. The first
module diagnostic is at line 96:68 (`unexpected identifier; expected }`), not
line 279. Further reported diagnostics occur at lines 166, 226, 236, 230, 279,
283 and 316. The exact messages remain in the raw stdout receipt above. The
primary does not classify the later diagnostics as mere fallout without a
repaired build. This correction supersedes the preceding summary's inaccurate
“first error” sentence; all no-type/no-axiom-audit and incomplete dispositions
remain unchanged.

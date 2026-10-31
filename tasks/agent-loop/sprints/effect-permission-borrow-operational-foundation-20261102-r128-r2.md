# Sprint PERMISSION-BORROW-FOUNDATION/20261102-R128

Status: AMENDED R2; proof author acknowledged the amendments before this revision.
Exact continuation leases are recorded in current.json. The standing original
Yulang soundness/effect-hygiene goal remains open. Rust source integration is
still gated by R111's one-shot capped verifier requirement.

## Outcome

Construct and kernel-check a standalone Lean operational model for the exact
R119 capture-to-consumer fragment, while independently auditing its immutable
Rust source attachment. The model must derive borrowed-record stability from
its transition rules and derive successful indexed consumption from a read of
the same location and record selected at capture. It must preserve first-match
order and duplicate members.

The model is intentionally local. It does not claim Rust heap/pointer
correspondence, source construction, native decoding, whole-language effect
hygiene, or source inference soundness unless the source handoff supplies each
exact equation and independent review accepts the attachment.

## Authority, inputs and original parent

Preserve the original `SourceProblem.InferenceSoundness` quantifiers, supported
source domain, source/native correspondence and effect-hygiene obligation.
Relevant existing definitions and source evidence are pinned in the R128 input
manifest. R118/R119 are constructed but previously unchecked; R120/R121/R127
are conditional source/proof handoffs. None closes the parent theorem.

## Required Lean construction

Write one standalone file importing only installed `Std`:
`notes/theory/lean/YulangClosure/PermissionBorrowOperationalFoundationR128.lean`.

Represent a finite heap of permission records, a shared-borrow token, exact
record/location identity, the ordered complete-family list, capture search,
request field copying, and indexed consumer evaluation. The source-aligned
family identity is exactly a pair of opaque keys:
`Family ModuleKey SourceNodeKey = { module : ModuleKey, declaration : SourceNodeKey }`.
Both key types must carry explicit decidable equality. Do not add an argument,
spelling, range, or other identity field; Rust argument interpretation remains
an open equation. Include a checked discriminator showing equal declaration
keys in unequal modules yield unequal families. Keep duplicate `[9, 9]` behavior.

Define allowed transitions explicitly; a shared borrow must rule out mutation
of its selected record while allowing unrelated locations to change. Prove
stability over traces by induction on those transitions, not by assuming a
stability law.

Prove and audit:

1. Every successful indexed consumer read is membership in the exact retained
   record selected by the captured location and record identity guard.
2. A captured first matching index remains the first matching index after any
   permitted trace and the actual request-copy operation.
3. For `[9, 9]`, capture chooses index 0, while independent local reads at
   indices 0 and 1 both succeed for family 9. Do not imply that the consumer
   alone proves first occurrence; that comes from capture plus stability.

Do not assume the target membership, first-position result, indexed-read
equation, complete-family decoder law, Rust pointer equality, or source-to-model
simulation. Report exact abstract premises that remain open. Include full
`#check` and `#print axioms` output for each delivered root.

## Continuing lanes and exact leases

- Registered `lean_prover`, ≤600 seconds: only the Lean file above and
  `tasks/agent-loop/inbox/effect-permission-borrow-operational-foundation-r128-proof.md`.
- Registered `researcher`, ≤300 seconds, read-only source lane: only
  `tasks/agent-loop/inbox/effect-permission-borrow-operational-foundation-r128-source.md`.
  Reconstruct only the frozen R127 target in memory from its pinned inputs;
  inspect `SourceEffectId`, borrow/capture, request copying, record guard,
  `std::ptr::eq`, `.position` and `.get`. No dirty or quarantined source reads,
  source materialization, or compiler/Cargo execution.
- Fresh `compiler_referee`, ≤240 seconds after both author artifacts freeze:
  read-only review of both handoffs and the Lean file; challenge transition
  completeness, identity fields, pointer/slice interpretation, duplicate
  cases, hidden assumptions and every theorem's exact conclusion.
- Luna owns contract, manifest, admission, exact leases, current state, review
  adjudication, outcome and Git. No Rust source edit is authorized in R128.
- The original assignment envelope remains ≤1,380 seconds total; Astra 0.
Proof continuation is authorized only after the worker's acknowledgement (received
before this revision) and is capped at 120 seconds of additional active work.
The initial failed Lean command is immutable evidence and its 4.582810527s count
remains charged. Permit at most two further direct Lean checks, each ≤90 seconds,
with aggregate ≤175.417189473 seconds total across checks including the initial
one. No timer or assignment budget resets; the worker reported prior assignment
wall time UNKNOWN, so the 120-second continuation cap is an additional hard
ceiling, not a replacement for the original envelope. No Lake, project imports, package installation, workspace
copy/worktree, resource/storage probe, generated `.olean`, cache, formatter,
Cargo, Rust compiler, tests, or write outside exact leases. Lean checks are direct
pinned-native invocations only, `-j1 -M768`, at most 90 seconds each. If installed
`Std` cannot be imported without generating project artifacts, stop checking.
- Combined new artifact size ≤128 KiB.

## Success, blockers and residual gates

Success requires the Lean kernel to accept the stated roots, complete type and
axiom audits, exact source-field inventory and indexed path, independent review
with no open blocking/major findings, and a precise residual Rust-to-model
equation list. This closes only the checked local operational-model subgate.

R111's private aggregate 6-GiB compile gate remains unmet and Cargo remains
0/1; no source push is authorized until that gate or its versioned policy is
resolved. The original A/B parent, PRE-constructor event, R45 extraction,
actual Rust pointer/heap identity, full native correspondence and production
remain open. The first Lean failure is retained, not treated as success. Within
the bounded continuation, allow only parser/tactic elaboration repairs and the
specified Family identity representation change. Theorem statements, quantifiers, transition semantics and premises otherwise stay fixed. Stop after two additional checks if any error
remains, or immediately on a counterexample, missing source field, need for a new
assumption, changed theorem/transition meaning, unpinned owner, or exhausted
finite budget. No `sorry`, `admit`, axioms, bypass or unchecked recovery.
Source handoff r1 is pinned by manifest r3; its Rust identity inventory must be
used without reopening dirty or quarantined sources.

Next dispatcher consultation: frozen model/source review seam, concrete
counterexample, or verified change to R111's verifier resource/policy.

# R29 finite fresh heap allocation with payload typing — r1

Status: primary admission candidate; no worker launch before this contract and
current state are committed. Claim class: constructive Lean intermediate over a
new explicit finite heap relation. It is not the manuscript's full graph
extension theorem or an approved compiler design.

## Fixed goal and theorem boundary

Governing paper: `docs/yulang-operational-type-safety-ja.tex:324–326` and
`:981–990`. The original `rec` step freshly reserves a finite block, applies one
simultaneous substitution to every right-hand side/body, extends the type graph,
leaves the old heap immutable, and requires the new graph to remain guarded.
The full parent remains OPEN.

Construct only the payload-typing/allocation component for a **concrete finite
input block** represented as `List (Nat × Ty × Value)` in explicit de Bruijn
order (head is variable index zero). Define a new auxiliary relation for finite
heap payload typing; do not identify it with or claim the omitted full paper
heap judgment. For declarations `D`, old graph types `Xi`, old heap `H`, source
term environment `Gamma`, target `Gamma'`, tail substitution `rho`, and block
`B`, prove the following from explicit premises:

1. The block identities are pairwise distinct and disjoint from both
   `H.map Prod.fst` and `Xi.map Prod.fst`. Its entry type list and RHS list are
   derived by mapping `B`; never accept an independent unaligned list.
2. Define `formals := B.map (fun (r,A,v) => (r,A))` and
   `Xi' := formals ++ Xi`. Prove old lookup preservation
   `GraphLookupPreserved Xi Xi'` and the exact new identity lookups. Use the
   R27 first-match lookup lemmas and prove the actual freshness conditions.
3. Every original RHS has its `PaperValueTyped` derivation under
   `D`, `Xi`, and `(formals.map Prod.snd) ++ Gamma`, at the matching block type.
   Assume `TermSubstitutionTyped D Xi Gamma Gamma' rho`. Apply the **same** R28
   `graphFormalReplacements formals rho` to every RHS. Prove the actual public
   `Option` substitution succeeds for the whole list and preserve each RHS's
   exact type under `D`, `Xi'`, `Gamma'`.
4. Construct the new node list by mapping each block identity to its actual
   substituted RHS result. Prove its length equals `B.length`, define explicit
   first-match lookup on the finite heap lists, prove each new identity lookup
   returns its substituted RHS, and prove every old heap lookup is unchanged.
   Construct `H'` with exactly those new nodes as a prefix and the original `H`
   unchanged as the suffix. Do not use unchecked `List.zip` to associate
   independent lists; a zip/truncation counterexample is required.
5. From an explicit old-heap payload-typing premise under `D`, `Xi`,
   `Gamma'`, prove the entire updated finite heap payload-typed under `D`,
   `Xi'`, `Gamma'`: new nodes use the RHS derivations above; old nodes are
   transported using R27 while their values, order, and types remain unchanged.

The block premise is in de Bruijn order and includes the old/source/target
contexts above. It does **not** prove that source-formal order, local identity
allocation, or a real program's `rec` environment corresponds to this list.
That correspondence stays OPEN.

## Required falsifiers and open guard boundary

- Duplicate block IDs shadow earlier block type lookups; duplicate old identities
  collide with allocation. A list-inclusion/zip-only proof that misses these
  checks fails.
- A two-formal discriminator proves the first input entry maps to variable 0
  and that swapping or sequentially applying replacements gives another heap.
- A block/list length discriminator exposes silent `List.zip` truncation.
- Show a self-alias block `r ↦ graphReference r` can satisfy the new payload
  typing relation, with an actual heap lookup self-edge. This demonstrates that
  payload typing alone does not prove guardedness. It is a relation discriminator,
  not a counterexample to the paper's guarded allocation rule.

Do not use `ValueGraph.guarded : Prop` as evidence and do not prove or claim
`ValueGraph.guarded`, absence of cycles, a paper heap-well-typedness theorem, or
the full `rec` preservation step. The alias-cycle result must keep the guard
obligation visibly OPEN.

Original paper source domain is unchanged. Omitted variants/nominals,
handlers/mappers, recursive typing, full patterns, primitives and template-body
typing stay omitted. Full term/type/name substitution, source-formal/de-Bruijn
correspondence, source/native mapping, guarded cycles, original A/B,
inference/executor and production remain OPEN.

## Implementation lane

`NO_SAFE_CODE_SLICE`. Two actual source owners were inspected at this baseline:

- `tools/inference-playground/src/runtime/program.rs:607–665, 735–775`
  (`6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907`)
  marks recursive local bindings after a lexical ownership walk.
- `tools/inference-playground/src/runtime/machine.rs:835–850, 1500–1565`
  (`b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e`)
  has runtime initialization/publication paths, including a recursive-definition
  initialization error, rather than a demonstrated immutable fresh block
  allocation corresponding to this paper rule.

No source-to-paper allocation or guardedness bridge licenses changing those
paths. This is an evidence gap, not a claim that the compiler is incorrect.
No Rust edits, tests, runtime probes or behavior changes in this proof packet.

## Frozen baseline, authority and dependencies

Baseline commit: `79b7a88a0cca341306d399dbb0b788d298540612` on
`research/simple-sub-intrusion`. Fresh isolated checkout:
`/tmp/yulang-r29-fresh-heap`. R27 and R28 are accepted, byte-frozen research
modules and read-only dependencies.

- Manuscript:
  `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`
- `PaperExecutionSyntax.lean`:
  `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`
- `PaperExecutionGraphWeakening.lean`:
  `b0ff39ad89fcb83559cca3147ae55fa7e7f6c31c1b130ec9cd7608e33d1f696e`
- `PaperTermSubstitution.lean`:
  `a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f`
- R27 independent review:
  `65cae0d25f01e51e5330946234d105d19761a2d431424048c29689c14603b60a`
- R28 worker handoff:
  `21c6a4c63e90fe60f1d8b2506a41797386d0f2c876c9aae9316f4a072f2b8d74`
- R28 independent review:
  `1a22633d94b1067747d68a4d5149eac7f7e4b5beb5d42e6634761209a68c3186`
- pinned `lean-toolchain`:
  `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`
- `lakefile.toml`:
  `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`
- `lake-manifest.json`:
  `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`
- runtime owners above: exact hashes listed in the implementation-lane section.

Primary verifies all hashes and the pinned Lean/Lake versions before launch and
again after handoff. No R25/R26 candidates or caches. Worker gets no Git,
network/dependency, test, Rust/runtime, source-domain, semantic, integration or
production authority.

## Exact leases and checks

One fresh registered `lean_prover` leaf, no descendants, owns only these paths
in the isolated checkout:

- `notes/theory/lean/YulangClosure/PaperFreshHeapAllocation.lean` (new)
- `notes/theory/lean/.lake/R29Audit.lean` (new)
- `notes/theory/lean/.lake/build` (dedicated cache)
- `tasks/agent-loop/inbox/paper-fresh-heap-allocation-r29-worker-checks.txt`
- `tasks/agent-loop/inbox/paper-fresh-heap-allocation-r29.md` (handoff)

The primary owns current state, the R29 contract, Git, isolated setup and
`tasks/agent-loop/inbox/paper-fresh-heap-allocation-r29-primary-verification.txt`.
After worker STOP and primary verification, one fresh non-author M1 reviewer may
write only `tasks/agent-loop/inbox/paper-fresh-heap-allocation-r29-review.md`;
reviewer has no checker or cache access.

Pinned serial commands from `notes/theory/lean`:

    lake build +YulangClosure.PaperFreshHeapAllocation
    lake env lean -j1 -M1024 .lake/R29Audit.lean

Audit every public declaration: lookup/freshness lemmas, actual option-map
success, block length and exact heap suffix, all-node payload typing, old-node
transport, two-formal order, duplicate-shadowing, zip truncation and alias-cycle
payload-only discriminator. Print complete types and `#print axioms`; reject
`sorryAx`, project axioms, `Classical.choice`, and unsupported axioms. Source
scan the changed dependency cone. No default/full build, Rust build, tests, or
runtime experiment.

## Resource, runtime and stop conditions

Total envelope: 1800 active seconds, 14 literal Lean/Lake invocations, 180
checker seconds. Worker: <=10 calls/120 checker seconds/900 active seconds.
Primary: <=4 calls/60 checker seconds/600 active seconds, with two pinned
version queries plus one focused build and exact audit. Reviewer: <=300 active
seconds and zero checker invocations. Version queries count. Resolve native
Lake read-only with `elan which lake`; failed preflight blocks launch. Use
`LEAN_NUM_THREADS=1`, `-j1`, `-M1024`, and only one heavy checker process.
No previous sprint budget transfers. Keep all eight UNKNOWN reservations
quarantined and total agent count below 12.

Stop after three failed worker checks, first failed primary final check, any
ambiguous source/formal-order claim, a freshness/length mismatch, budget edge,
changed authority/input/lease, missing cessation evidence, or session end. No
unchanged-command retry. Freeze source/audit/log/cache and handoff, record actual
runtime/model/effort (UNKNOWN if unavailable), cache manifest, descendants and
writes-stopped receipt before independent review. Result remains intermediate;
only Luna adjudicates it.

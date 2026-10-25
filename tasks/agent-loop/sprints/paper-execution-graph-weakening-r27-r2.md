# Sprint FULL-PAPER-TYPE-SUBSTITUTION-20261026/r27 — lookup-preserving graph weakening (r2)

Status: ADMITTED under r2; sequential resource-accounting correction to admitted r1 before worker launch. Selector audit found no blocker. No worker edits or checker calls have begun. Primary acknowledgement is the matching r2 contract/current-state commit.
Branch: research/simple-sub-intrusion
Baseline: 5beb8df530080ea768abf275bdef85e3b471b23b (R26 FAILED_CHECK adjudicated; no R26 candidate imported)
Contract revision: r2 (supersedes r1 resource accounting only; theorem, baseline, paths and worker limits unchanged)

## Parent and fixed outcome

The unchanged parent remains the full-paper type-substitution theorem at `docs/yulang-operational-type-safety-ja.tex:953–977`, then inference/executor semantics and the original A/B obligations. R26's worker candidate is not accepted or imported: its worker checks passed, but the primary audit timed out at exit 124. Keep that outcome and all R23/R18 parent gates intact.

Prove lookup-preserving weakening for exactly the six existing partial paper judgments. Define

```lean
def GraphLookupPreserved (old new : GraphEnvironment) : Prop :=
  ∀ identity ty, lookupGraphEnvironment old identity = some ty →
    lookupGraphEnvironment new identity = some ty
```

For arbitrary declarations `D`, graph environments `old/new`, term environment `Γ`, and all subject indices, assume the shared premise `hpres : GraphLookupPreserved old new` and prove these conclusions without changing any source relation:

- `PaperValueTyped D old Γ value ty → PaperValueTyped D new Γ value ty`
- `ValuesTyped D old Γ values types → ValuesTyped D new Γ values types`
- `ValuesAllTyped D old Γ values ty → ValuesAllTyped D new Γ values ty`
- `RecordPayloadsTyped D old Γ fields recordType → RecordPayloadsTyped D new Γ fields recordType`
- `PaperComputationTyped D old Γ computation ty → PaperComputationTyped D new Γ computation ty`
- `PaperContinuationTyped D old Γ continuation responseType resultType → PaperContinuationTyped D new Γ continuation responseType resultType`

Use one mutual proof or equivalent declarations that preserve these exact indices. In the value `typeAbstraction` case, prove that `GraphLookupPreserved old new` lifts through `mapGraphEnvironment (fun i => .var (i + 1))`; `lookupGraphEnvironment_subst` in the frozen typing-substitution module is the direct lemma. Do not add freshness assumptions to the six general weakening statements.

Apply the result to a genuinely fresh head identity: if `identity ∉ old.map Prod.fst`, prove `GraphLookupPreserved old ((identity, newType) :: old)` and transport all six judgments across that extension. Include the falsifier that prefixing an identity already present with a different type (for example old `[(r, .base .int)]`, new `[(r, .base .bool), (r, .base .int)]`) does not preserve the old lookup. A list-inclusion argument that ignores first-match shadowing fails this gate.

The governing paper lemma at `:980–990` also mentions heap `H`, well-typed graph extension, allocation and guarded cycles. This packet proves only lookup-preserving weakening for the six represented typing judgments and its fresh-identity corollary. It does not prove heap well-typedness, guardedness, graph-extension allocation, recursive substitution, source/native correspondence, or the paper's full graph-extension lemma. The fresh example is a relation discriminator, not a paper counterexample.

Success requires all six exact theorem types, the lifted lookup lemma, fresh-cons application and shadowing falsifier, focused build, complete theorem/axiom audit with no `sorryAx` or project axiom, unchanged source dependencies and fresh non-author M1 review. The result remains an intermediate lemma and does not close the original parent.

## Frozen authority and inputs

Governing locators: manuscript `:980–990` (immutable graph extension), `:953–977` (type substitution), and `:1141–1146` (fresh external response nodes); manuscript SHA-256 `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.

Read-only Lean inputs at baseline:

    notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932
    notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean 568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a
    notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean 3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41
    notes/theory/lean/YulangClosure/PaperTypeFormation.lean 29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13
    notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean 02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861
    notes/theory/lean/YulangClosure/DeclSubst.lean f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258
    tasks/agent-loop/inbox/paper-typing-subst-r26-adjudication.md 6551f28f5da2bfff5905990c98abeac95b19f242b1ad6e27bdf370f27c3c25f1

Pinned project configuration at r2 proposal:

    notes/theory/lean/lean-toolchain ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c
    notes/theory/lean/lakefile.toml 2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194
    notes/theory/lean/lake-manifest.json 058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3

Primary revalidates every listed hash, `lean-toolchain`, lakefile and baseline before acknowledging the worker. Create a fresh detached checkout `/tmp/yulang-r27-graphweakening` at the exact baseline; use its dedicated `.lake/build`. Do not access `/tmp/yulang-r26-mapop` or import its candidate/cache. Do not change existing Lean files, lakefile, root imports, dependencies or lockfiles.

## Exact leases and checking

One registered `lean_prover` leaf, no children, owns these paths only in the isolated checkout:

- `notes/theory/lean/YulangClosure/PaperExecutionGraphWeakening.lean`
- `notes/theory/lean/.lake/R27Audit.lean`
- `notes/theory/lean/.lake/build`
- `tasks/agent-loop/inbox/paper-execution-graph-weakening-r27-worker-checks.txt`
- `tasks/agent-loop/inbox/paper-execution-graph-weakening-r27.md`

The source module imports only the frozen partial judgment modules it needs. The proof worker may refine its proof after failed checks within the lease and allowance; each failed call counts. Stop after three failed checker invocations, any source/claim ambiguity, budget edge or authority/dependency change. No unchanged-command retry. No Git, tests, default/full build, Rust build, network/dependency activity or R26 artifacts. Freeze every output and give an actual writes-stopped receipt before review/cache handoff.

Pinned project commands, serially:

    lake build +YulangClosure.PaperExecutionGraphWeakening
    lake env lean -j1 -M1024 .lake/R27Audit.lean

The audit prints all six complete types and axiom lists, verifies theorem kinds and rejects `sorryAx`/unsupported axioms. Version queries count if used. Use one heavy build at a time, `LEAN_NUM_THREADS=1`, pinned Lean 4.35.0 and existing `moreLeanArgs`.

After the worker's writes-stopped receipt, the primary owns the same cache and `tasks/agent-loop/inbox/paper-execution-graph-weakening-r27-primary-verification.txt` for one final focused build and one exact audit. First primary-check failure stops the packet; do not retry or transfer unused budget.

After both worker and primary verification pass and the proof is frozen, one fresh non-author M1 reviewer may write `tasks/agent-loop/inbox/paper-execution-graph-weakening-r27-review.md` (no checker, at most 300 active seconds). Review and proof are sequential; record actual runtime and model/effort observations, using UNKNOWN when absent.

## Resource and stop contract

Envelope: 1800 active seconds; 14 literal serial Lean/Lake invocations and 180 checker seconds total. Worker cap: 10 calls/120 checker seconds/900 active seconds. Primary cap: 4 calls/60 checker seconds/600 active seconds: two preflight version queries (`lake --version`, `lake env lean --version`) and the final focused build plus exact audit. Resolve Lake with read-only `elan which lake`; a failed preflight blocks launch. Reviewer cap: 300 active seconds after worker STOP and primary verification; reviewer runs no checker. Every invocation counts. No budget from R25/R26 transfers. R1 was admitted and frozen before worker launch; this r2 corrects only the primary call count to include mandatory version queries. The eight UNKNOWN historical reservations remain quarantined. Global agent capacity (separate from the Lean/Lake invocation cap): 10/12 during worker construction (8 quarantined reservations, the primary, and the proof worker). The `next_action_selector` audit assignment has completed before worker launch and consumes no live slot. After proof STOP and primary verification, recount the global ceiling before assigning the sequential reviewer; with only the eight quarantined reservations, primary and reviewer active, capacity is 10/12. No other live agent assignment or descendant is allowed. Stop at the packet's failure bound, source ambiguity, budget edge, authority/dependency/lease change, STOP or session end.

R27 does not close full graph extension, graph well-typedness/guardedness, original substitution, inference/executor, R18/R23, A/B, source/native/Rust or production. Preserve those gates as OPEN.

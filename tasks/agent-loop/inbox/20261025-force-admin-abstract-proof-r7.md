# R7 abstract observation proof — revision 1

Status: **FROZEN CANDIDATE; Lean check and independent review NOT_RUN by author**.
Assignment ID `R7-force-admin-abstract-proof`; handoff revision **1**.
Author and actual leaf: `/root/force_admin_abstract_prover_r7`; primary `/root`.
Current launch receipt: received the r7 NEW_TASK packet and primary follow-ups
in this runtime; first clock observation `2026-10-25 00:41:28 UTC`.
Requested model/effort: `gpt-6.1-sol` / `high`. Observed model/effort:
**UNKNOWN / UNKNOWN**; no model-switch claim. No coauthors or descendants.
Baseline inherited from N: `9b945b0bb175e8e0919d388dc720babbdf0c2464`;
not independently inspected through Git.

## Contract, dependencies and output snapshot

Sprint `FORCE-ADMIN-RESULT-DISCHARGE-20261025/r7`, frozen contract
`tasks/agent-loop/sprints/force-admin-result-discharge-20261025-r7.md`.
All nine contract/input pins below were matched with `sha256sum`, twice for
the final snapshot. This establishes byte identity, not proof validity.

| Input | SHA-256 |
|---|---|
| r7 contract | `4b23812951ce23c8868f85a4138c35f4235d0b66339b6a14fdad3f3adf6b1663` |
| N `inbox/20261025-force-admin-adequacy.md` | `1a0df86f0e14177b287d59d2afab598f89dfc99e403a014d25e069cd3b1833ab` |
| R `inbox/20261025-force-return-rows.md` | `de1ef24c6cd62c0280dce47e1cf823234f30c8dc471e3a6cab7f8b5130497966` |
| r6 `sprints/force-admin-result-discharge-20261025-r6-outcome.md` | `51f5bd1bba958ff6291304311caad35f175f8c0914c0009fee18894e2810de59` |
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| r5 `sprints/force-source-mapop-correction-20261025-r5-outcome.md` | `04e93d203dbf09f2421be4ef988328330ccecb5997b3e01564178d8b195ed823` |

`inbox/` and `sprints/` abbreviate `tasks/agent-loop/`. N author is
`/root/force_admin_trace_prover_r6`; R author is
`/root/force_return_rows_prover_r6`. Primary contract/outcome author is Luna;
other dependency authors are UNKNOWN where not explicitly established.

Exact two new output/write paths:

* `notes/theory/lean/YulangClosure/ForceAdmin.lean`, SHA-256
  `620994e5e7383c267a19d5bea93f35d8d82d2db76a03893449bd821250669c97`.
* `tasks/agent-loop/inbox/20261025-force-admin-abstract-proof-r7.md` (this file).
  Its frozen byte hash is returned in the final receipt, avoiding self-hashing.

No scratch, generated output, auxiliary report or other edited path exists.
Only import is `Init` from the pinned Lean toolchain. No unchecked r9 module
or source/native declaration is imported.

## Exact target and construction

Namespace `YulangClosure.ForceAdmin`, generic payload `P : Type u`:

```lean
theorem abstract_observe_counted_run_iff
    (H : Nat → Option (V P)) (beta : P → P → V P) (inst : P → P → P)
    (v : V P) (tr : List (Event P)) (h : Head P) (W : List P) :
    SourceObserve H beta inst v tr h W ↔
      CountedRun H beta inst tr ⟨v, [], []⟩ ⟨headValue h, [], W⟩
```

`inst` is explicitly arbitrary and fixed, as are H and beta. The four N
SourceObserve constructors and four AdminMicro constructors are retained.
SourceObserve is independently inductive over source shells; CountedRun is
independently inductive over exact machine edges. Neither is a definition,
projection or premise extracted from the other.

Forward `observe_run` strengthens the target to every pending stack K and
incoming wrapper list W0: it emits `tr.map (lift K)`, preserves that exact K,
and reaches wrappers `W0 ++ W`. Its application case concatenates the function
segment, one real beta edge and the body segment; scheduling adds no event.
This is a local segment lemma, not a theorem about arbitrary foreign suffixes.

Reverse `StackResult` is structural recursion on pending frames, using only
SourceObserve. It describes how an already observed head and accumulated
wrappers can complete the stack. A pending frame requires an abs head, its
actual beta-body observation, exactly one lifted beta event and the remaining
stack completion. `FocusResult` pairs the current source observation with this
source-only completion. Neither invariant refers to AdminMicro or CountedRun.
`micro_backward` reconstructs that invariant before each of the four machine
edges. `run_backward` then quantifies arbitrary trace suffix, result head and
result wrappers for arbitrary start/end focuses. Terminal completion at the
exact target endpoint yields the reverse implication. Thus no frame-pop
existence, source observation, direction of the target or typing premise is
assumed. Both stack handling and the emitted event lift are explicit.

`wrap_append` additionally proves the literal ordered nesting equation
`wrap (W1 ++ W2) v = wrap W1 (wrap W2 v)`. All wrappers remain ordered;
only wrappers around an observed function are mapped through that actual
application's inst. Outer application wrappers are saved and restored.

## Parent application and source/native boundary

The original parent is complete Lean semantics and inference; this packet
addresses only N's reviewed abstract finite-success zipper proposition. If
Lean accepts these exact bytes and fresh independent review is CLEAN, the
administrative zipper correspondence is reusable in O-NORM's finite spine.
The full O-NORM source premise remains OPEN: a lossless decorated source
encoding, concrete capture-avoiding beta, concrete whole-packet instantiation,
raw error transitions, and separate guarded observation existence/canonical
Delay obligations have not been supplied here. O-RESULT, Force realization,
Call S/C/A/B, F1/FK1 and parent soundness remain OPEN and unchanged.

Source evidence reused: pinned paper 258–269 (graph and substitution),
301–321 (latent barriers/type beta/counting), 331–335 (active frames),
472–494 (reads and outer observation), 1241/1541 (whole-packet instance).
N supplies the candidate source characterization; this module encodes that
reviewed abstraction with generic payloads. No claim that actual compiler
constructors emit these shells/events/metadata was established. No constraint
generation, propagation, level, extrusion, intrusion or generalization owner
was edited or weakened. No native/protocol implementation evidence is claimed.

Prior work reused within scope: N's independent constructors and ordered
wrapper equations, r6's narrow CLEAN abstract target, r5's accepted mapop
boundary, and R's exact Force-leave obstruction. Rejected as proof premises:
unchecked r9 Call fields, projection-defined observation, bare Force beta,
arbitrary metadata IDs, Ret-only result transport and source correctness
inferred from assumed transitions. This packet does not retry R's blocker.

## Checks, axioms and resources

Author checks: exact source/contract reads, constructor/signature comparison,
manual proof inspection, forbidden-token/import scan, and dependency/output
SHA-256 receipts. The token scan found no `axiom`, `sorry`, `admit` or
`postulate` declaration/use in the Lean file. Installed toolchain source was
read only to confirm standard Init list/tactic availability. An initial
read/hash script used unavailable `python`; it made no output file and was
replaced by sha256sum and python3. One read-only guessed source locator did
not exist; no replacement dependency or write resulted.

**Lean/axiom runtime receipt: NOT_RUN by author; actual axiom set UNKNOWN.**
The exact module ends with these commands for Luna's serialized check:

```lean
#print abstract_observe_counted_run_iff
#print axioms abstract_observe_counted_run_iff
#print axioms wrap_append
```

No user-declared axiom or assumed equivalence is used. This static statement
is not a fabricated `#print axioms` output. Luna must record the actual output,
exit status, frozen module hash and independent review against these bytes.
No tests, Lean process, builds, Cargo/native commands, Git, external contact,
nested CLI, model-policy edit or descendant occurred.

Resource grant: total author 450 seconds, one CPU, 1,024 MiB. First clock
00:41:28 UTC; pre-handoff clock 00:45:51 UTC (263 seconds observed interval).
Exact dispatch/start elapsed, CPU and peak RSS are UNKNOWN; charge the full
450-second grant conservatively, with no carry claimed. Primary check/review
budgets remain separate and are not spent by this author.

## Mutual TODOs, next step and STOP

* `R7-CHECK-1`, owner Luna: check this frozen module under installed Lean 4.35.0
  within r7's serialized 200-second aggregate grant and obtain the actual
  axiom printout. Falsifier: any elaboration/kernel error, unexpected axiom,
  changed constructor, shifted event or wrapper mismatch. Preserve the exact
  artifact/error and return through Luna; do not silently broaden the target.
* `N-META-INST-1`, owner Luna/source-decoration lane, unchanged parent O-NORM:
  supply concrete packet representation and one complete type/dictionary
  specialization, including latent/profile/family occurrences. Falsifier:
  `view c (app (view d (abs b)) A)` specializes c, misses a coordinate in d,
  or specializes d twice. Source producer evidence is required.
* `N-RAW-ERROR-1`, owner Luna/source normalization lane: define the missing
  malformed application/reference/local transitions independently. Falsifier:
  Force of an application whose function is unit fails to reach its raw Bad
  before dispatch, or enters a latent payload.
* `R6-R-FORCE-LEAVE-OWNER-1`, owner Luna/source-decoration lane, unchanged
  parent O-RESULT: actual Force-leave row constructor and occurrence allocation
  at paper 1245/1531–1532, consumed later by `CallControlStep.returnExpose` /
  `Metadata.viewReturn`. Falsifier: dropped body-result/operand result route,
  unrelated capture route, or altered latent suffix. No R Lean lease is used.

Next step is Luna's serialized check and fresh independent nonauthor review.
No further author stage is active within this assignment. This is a candidate
snapshot pending checking, review and Luna integration, not a reviewed theorem
or production authority. The author is ineligible to certify its own proof.

**STOP / writes ceased:** revision 1 is frozen by this final write. Afterward
only read-only final hashing and the handoff receipt occur. Both exact leases
are FROZEN; no descendants, unresolved descendant leases or background work
exist. This worker is STOPPED and will not write while review/checking runs.

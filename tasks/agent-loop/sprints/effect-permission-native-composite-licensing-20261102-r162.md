# Sprint R162 — selected composite licensing witness

Status: **ADMITTED** by Luna under the continuing Yulang soundness goal.
Branch / baseline: `yulang3` / `808c12dd2437ad0aa8e673cc8dbcb6d403f662ed` (pushed).
Contract revision: 1, selected after R161 closure on 2026-11-02.

## Original outcome and success evidence

Parent: unchanged R159 `SourceAppAdmissionR159.app_admission_iff`. Preserve its
full App quantifiers, incoming annotation alternatives, every Local premise,
both finite Checking judgments, both arbitrary operands, conditional
singleton-formal origin and shared occurrence/data/extension. R161 proves only
a necessary consumer consequence under an assumed original App derivation;
R162 does not repeat that decomposition.

R162 targets the exact formalization gap from R161: the selected complete
composite `DeclContribution` / `L` licensing projection family. Construct the
selected constructor family as a finite indexed derivation over the registered
source graph, then prove a witness-preserving projection for its dependent
fields. Preserve the complete original origin partition, receiver, whole tuple,
dependent slots and governed port identities. Recursive references remain
graph edges; never unfold them as infinite trees.

Success requires a kernel-checked non-leaf composite witness and projection
whose constructors correspond to the selected Authoritative construction. It
must reduce P's formal-input gap from “complete composite witness not
formalized” to the exact remaining original interpretation and
annotation/port realization. Do not identify arbitrary `s.Descriptor` or
`s.Interface` with native values, assume original formation guards, or claim
P/A/source/native/production closure.

Keep primitive and C0 witnesses and incoming annotation inputs explicit.
Support alone is not a license. Empty support does not gain a governed field.
Independent A remains the original initial-context/import constructor and its
encoding into `LocalAdmissions.logical`; no result in this sprint may derive A
from P.

## Governing inputs and dependencies

- R161 outcome `tasks/agent-loop/history/effect-permission-selected-native-app-20261102-r161-outcome.md`, SHA-256 `52be1ebc2c4ff0022508b6346bc590cf3a272d3fc2952cdf90ac399044a394d0`.
- R161 selected-native bridge module `notes/theory/lean/YulangClosure/SelectedNativeAppBridgeR161.lean`, SHA-256 `d0744fbe4101fb6ba03db8c77c5a4870cd0d53eeaca03783aff1c6b2e7a92a55`.
- Selected construction `notes/theory/2026-10-08-source-signature-incidence-construction.md` §§2–8, SHA-256 `7367ce8eb69376583386c6d675d067712ec6fa173e96f458ee34ce390dc8901a`.
- Native signature authority `notes/design/2026-10-08-native-signature-formation-definition.md` §§2–5, SHA-256 `e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9`.
- Existing Lean owner `notes/theory/lean/YulangClosure/SourceSignatureConstruction.lean`, frozen at R161 handoff SHA `ed07890e29b4dcb38cabd18ec0e196efde9e95c64902942a9906a470b38c3311`.
- Existing boundary `notes/theory/lean/YulangClosure/NativeProfileRestriction.lean`, frozen at R161 handoff SHA `527d89b982b962e423cfaa15ecf76a2d778603102bfc9e8d12b22af2eb1c7fb2`.

## Two continuing lanes

### Lean proof/source lane

Registered `lean_prover`, requested Sol/high, maximum 1800 seconds. Read the
actual selected constructor definitions and both existing Lean owners. Define
the finite indexed derivation without postulating licensing, derive exact
dependent projections by constructor induction, compare all constructor cases
against the paper, and apply the result to R161's precise remaining input gap.
If the selected graph lacks required edges or the authoritative family is
ambiguous, state the first missing constructor/field and owner rather than
inventing semantics. Run complete theorem-type and transitive axiom audits.

Exact outputs:

- `notes/theory/lean/YulangClosure/NativeCompositeLicensingR162.lean`
- `notes/theory/2026-11-02-native-composite-licensing-r162.md`
- `tasks/agent-loop/inbox/effect-permission-native-composite-r162-proof.md`

Use only the existing pinned Lean 4.35.0 project/build with one verification
owner. No new environment, worktree, target, cache or import-root change.

### Rust source lane

Registered `implementer`, requested Luna/high, maximum 300 seconds; read-only.
Reuse the independently reviewed R160/R161 maps and inspect only clean in-scope
owners. Determine which exact existing Rust input (if any) corresponds to the
new typed composite witness, and whether an actual source-to-consumer owner
exists. Preserve `NO_SAFE_CODE_SLICE` unless the witness supplies a concrete
approved end-to-end prerequisite. No Rust source or observer edit is leased.

Exact output: `tasks/agent-loop/inbox/effect-permission-native-composite-r162-rust.md`.
Dirty/quarantined candidate and runtime files and all quarantined/unreviewed
artifacts are excluded from reads and writes.

## Verification, resources and stop

- Aggregate active-work cap: 2700 seconds (Lean 1800, Rust 300, fresh proof
  review 450, source-map delta review 150). Astra: 0; current UNKNOWN roster
  does not establish a free global Astra slot. Do not spend that slot.
- Reviewer authorship is independent. Review only frozen bytes; the proof
  reviewer checks constructor coverage, dependency/axiom audits and parent
  application. The source reviewer checks the Rust owner map and any claimed
  constructor edge.
- No Cargo/build/test invocation. No scratch output, new cache/environment or
  worktree. Preserve all UNKNOWN writers and quarantined path leases.
- Primary owns `current.json`, reviews, adjudication, exact-path staging, Git
  integration and push. Commit only coherent intended paths after complete
  outbound-range inspection.
- Falsifiers: an omitted selected constructor, empty support receiving a
  license, owner or receiver reassignment, port-specific witness replacing the
  shared tuple, or cyclic interpretation assumption. Stop on such a concrete
  counterexample, an ambiguous authoritative constructor, exact owner
  obstruction or fixed budget. P, A and production remain OPEN.

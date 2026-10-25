# CALL-PREFIX-TYPING-P-20261025 — frozen handoff revision 1

Sprint: `LEAN-CALL-FINITE-TYPING-20261025/r1`, Packet **P** only.
Contract: `tasks/agent-loop/sprints/call-finite-typing-20261025-r1.md`, SHA-256
`dfff6b8af11651122ebc0b3be6cb6a8722b3ce7a60845eb4e82ba1a9488eee68`.
Baseline: `c28827b29b4ff5f2f9d89c03f504fb9f886534f8`; frozen-contract commit
reported by Luna: `7ba8442f6`. No Git command was run by this author.
Assignment/handoff ID: `CALL-PREFIX-TYPING-P-20261025`, revision **1**.
Outcome class: **candidate**, pending Luna verification and fresh review.

## Exact parent and application

The artifact contains exactly the contract's Packet P theorem in namespace
`YulangClosure.Control`:

```lean
theorem call_state_typed_prefix_preservation
    {W : Type} {sig : Signature} {md : Metadata W}
    {n : Nat} {s t : CallState W} {result : Ty}
    (ht : CallStateTyped sig s result)
    (hp : YulangClosure.Prefix (CallControlStep md) n s t) :
    CallStateTyped sig t result ∧
      t.resultType = s.resultType ∧
      t.literalSuffix = s.literalSuffix
```

Construction: revert the initial typing hypothesis before induction on the
actual `Prefix` derivation. `refl` returns initial typing and both reflexive
equalities. `snoc` obtains middle-state typing and middle-to-initial equalities
from the induction hypothesis, applies the accepted one-step theorem to the
actual final transition, and composes each final-to-middle equality with its
middle-to-initial equality. All useful intermediate facts are applied directly
to this original P conclusion. No bound on `n`, altered metadata premise,
suffix restriction, or assumed successor is introduced.

Parent application: if accepted after checks/review, P supplies finite-prefix
typing and exact endpoint result-type/suffix equality to Luna's composition
theorem. Q and composition remain other owners' outputs. The first remaining
evidence for P acceptance is actual elaboration of this frozen candidate,
owned by Luna; the author has not checked or independently certified it.

## Source evidence and historical reuse

The operational input is the existing formal
`ControlSyntax.lean:CallControlStep`; its typing consumer is
`ControlTyping.lean:CallStateTyped`. The only direct import is accepted
`CallStepTypingRepair`, whose `call_state_typed_step_preservation` covers all
28 existing constructors. `Contracts.lean:YulangClosure.Prefix` contributes
only its actual `refl` and `snoc` constructors. Its generic comment does not
add resumptions to the instantiated Call relation.

Reused: accepted r2 one-step typing at its exact premises; ordinary finite
derivation induction and equality transitivity. Failed r1 is not imported or
used as proof. No transition is assumed from a probe. No compiler source/native
construction, constraints, propagation, or execution-adequacy bridge is claimed.

Progress, successor coverage, terminal reachability/emptiness, external
resumption, world/effect/CallView/scope/view-context/receipt invariants,
source/native correspondence, original Call A/B, inference A/B, and production
remain OPEN. The missing transition for
`.force (.view (.delay body) occurrence)` remains OPEN; r9 remains unaccepted.
Simple-sub generation, accumulation, propagation, levels, extrusion, qualifying
intrusion, and generalization are untouched.

## Frozen hashes and authors

Artifact: `notes/theory/lean/YulangClosure/CallPrefixTyping.lean`, SHA-256
`95c49daec0417c8130a498b44783c546b9464b96380731182fedde5665e8b5bc`.
The handoff hash is supplied separately on submission.

Source, dependency, and accepted-result pins were re-read and match the frozen
contract. Direct proof inputs and acceptance evidence:

| Input | SHA-256 |
|---|---|
| `CallStepTypingRepair.lean` | `2ef522c022a0708be670f1ab44b57c8f558d4736f123e14ceb5f6ff259a3c586` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `ControlTyping.lean` | `e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f` |
| r2 accepted outcome | `803dbc0e9724a18149bebf7bc40965c144bbfcefe3c9bce879333c40a9a0ac20` |
| r2 clean review | `f0e461a622e5309242ee151dac8f93a18183ed01262b77b836e066902f53981f` |
| r2 verification JSONL | `975f0c540e2e87219afd7fc0dd7477085bc81539f5f7da0de174764eeec5e52a` |
| `lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |

The remaining transitive source pins (`CoreSyntax`, `CoreSubstitution`,
`CoreExecution`, `CallContextTyping`, `CallEntryTypingRepair`,
`CallPeelingTyping`) were also revalidated against the exact contract table.
Luna owns reusable build-output validation and checker receipts.

Author/actual worker: `/root/call_step_typing_author`, fresh P launch/resume
acknowledged to `/root`; no coauthors or descendants. Requested model/effort:
`gpt-6.1-sol` / `high`; observed effective model/effort: **UNKNOWN / UNKNOWN**.
This author also produced the r2 dependency and cannot independently review
either this candidate or the resulting combined composition.

## Checks, mutual TODO, and cessation

Author checks: inspect the exact contract, actual `Prefix` constructors and
accepted theorem statement; manually audit induction and equality direction;
compare source/contract/result SHA-256 pins. No Lean, tests, Git, new dependency,
scratch path, production edit, or spawned worker.

Fresh resource cap: 600 seconds, zero Astra, zero author checker processes.
First local UTC receipt: 03:12:10. The work stops within the cap; exact
launch-to-first-receipt overhead is UNKNOWN. Final local elapsed observation
is returned with submission; Luna owns launch/resource accounting. No renewal
or further author work is requested.

Mutual TODO `CALL-PREFIX-TYPING-P-CHECK-1`, owner Luna: after both P/Q authors
STOP, compile this frozen P artifact as the contract's first serialized check;
then proceed only as permitted by the fixed contract. Falsifiers: first
elaboration error, changed dependency or proposition, missing output/receipt,
wrong signature, or axioms outside `[propext, Quot.sound]`. No automatic repair
loop or claim promotion is authorized. Fresh independent review belongs to Luna.

No in-envelope P step remains. **STOPPED / WRITES STOPPED** before Luna
verification. Exact new paths: `CallPrefixTyping.lean` and this handoff only.
No Q/composition writes, scratch paths, descendants, background processes, or
unresolved descendant leases. Candidate remains pending checks/review/integration.

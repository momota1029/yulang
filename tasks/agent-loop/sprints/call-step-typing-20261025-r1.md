# LEAN-CALL-STEP-TYPING-20261025/r1 — existing-step typing preservation

Status: **FROZEN**, Luna primary. Baseline: `12a081b82e2a84678aab7f5d0f301cd724c72542`.
Branch: `research/simple-sub-intrusion`. This bounded formal sprint advances the
active goal of complete reviewed Lean proofs for Yulang semantics and type
inference under `notes/theory/lean`.

## Fixed intermediate proposition

In `YulangClosure.Control`, prove the exact existing-transition statement:

```lean
theorem call_state_typed_step_preservation
    {W : Type} {sig : Signature} {md : Metadata W}
    {s t : CallState W} {result : Ty}
    (ht : CallStateTyped sig s result)
    (hstep : CallControlStep md s t) :
    CallStateTyped sig t result ∧
      t.resultType = s.resultType ∧
      t.literalSuffix = s.literalSuffix
```

The proposition covers all constructors already present in the pinned
`CallControlStep` relation. Its `CallStateTyped` result retains only Call-head
typing, typed evaluation frames, and the independently typed literal suffix.
The result-type and suffix equalities must be proved for every constructor.
The author may add supporting lemmas inside the leased module when they remain
within this exact statement and pinned source domain.

## Claim boundary and falsifiers

This is conditional one-step type preservation for an existing formal
transition. It makes no progress or successor-coverage assertion, proves no
equality or invariant for `world`, `callView`, scope/view contexts, or receipt
slots, and does not identify returned/requested/failed Call heads with ordinary
Control execution. In particular, the typed expression
`.force (.view (.delay body) occurrence)` has no matching current
`CallControlStep` constructor. This known gap remains OPEN; the theorem cannot
be reported as complete Call execution adequacy, Proposition A/B, or
source/native correspondence. The r9 result remains `SOURCE_INPUT_BLOCKED /
UNACCEPTED`; no r9 gate is revised or promoted.

Falsifiers include a transition constructor whose target cannot inhabit
`CallStateTyped`, a changed result type/suffix, loss of the actual substitution
or continuation binder, an unavailable proof dependency, or a changed pinned
input. Requiring a new semantic rule, metadata law, progress premise, or source
input stops this packet and returns the exact obstruction to Luna.

## Lanes, leases, and evidence

### Proof lane

One configured `prover` assignment, requested Sol/high, maximum 1,200 seconds.
It starts only after Luna has checked the two currently stale Control module
artifacts below from their exact current sources. Until Luna confirms that
preflight seam, the prover may not edit the theorem module; no parallel proof
candidate is authorized before that dependency acceptance.

Exact author leases, absent before first write:

- `notes/theory/lean/YulangClosure/CallStepTyping.lean`
- `tasks/agent-loop/inbox/20261025-call-step-typing-r1.md`

Luna-only verification paths:

- `tasks/agent-loop/inbox/20261025-call-step-typing-r1-verification.jsonl`
- `notes/theory/lean/.lake/call-step-typing-r1-check.lean`
- the `ControlSyntax`, `ControlTyping`, and `CallStepTyping` `.olean`/`.ilean`
  files under `notes/theory/lean/.lake/build/lib/lean/YulangClosure/`
- `tasks/agent-loop/inbox/20261025-call-step-typing-r1-review.md`
- `tasks/agent-loop/sprints/call-step-typing-20261025-r1-outcome.md`

The author writes only those paths, runs no Lean/tests/Git, records the exact
theorem and source hashes in one handoff, and STOPs before Luna verification.
The proof must construct existing typed witnesses from the real constructor
premises. For `requestBind` and `requestAdapter`, use the actual
`renameCallComp_typed` lifting under the response binder. Do not assume global
Call preservation or source adequacy.

### Luna verification and source lane

Luna alone runs at most four serialized Lean invocations, each `-j1 -M1024`
with a 120-second timeout:

1. Compile current `ControlSyntax.lean` and write its exact `.olean` and
   `.ilean` under `notes/theory/lean/.lake/build/lib/lean/YulangClosure/`.
2. Compile current `ControlTyping.lean` and write its exact `.olean` and
   `.ilean` in the same directory.
3. After author STOP and exact source/handoff pin checks, compile
   `CallStepTyping.lean` to its `.olean`/`.ilean` there.
4. Import the frozen theorem module and print its exact signature and axioms.

These ignored build outputs are Luna's exact verification leases. Existing
Control `.olean`/`.ilean` files are known stale pre-Call artifacts; their
presence or names are not evidence. Rebuild them from the frozen current
sources before proof use. Reuse only the successful pinned dependency outputs
below. Stop at the first source/dependency mismatch, elaboration error, timeout,
missing output, unexpected signature/axiom, or incomplete receipt; no automatic
repair loop.

The source lane is a bounded audit of every existing `CallControlStep`
constructor, not permission to edit source semantics. A fresh isolated
nonauthor `compiler_referee` reviews the frozen Lean artifact and complete
receipts after Luna's check. No author reviews their own artifact.

### Exact pinned inputs

| Input | SHA-256 |
|---|---|
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/YulangClosure/CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `notes/theory/lean/YulangClosure/CoreSubstitution.lean` | `c4bca75be173f20d7a48751205f488ac5f0057b476e6f52d1ef7abcf046a001a` |
| `notes/theory/lean/YulangClosure/CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `notes/theory/lean/YulangClosure/ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `notes/theory/lean/YulangClosure/ControlTyping.lean` | `e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f` |
| `notes/theory/lean/YulangClosure/CallContextTyping.lean` | `09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125` |
| `notes/theory/lean/YulangClosure/CallEntryTypingRepair.lean` | `f90c2192422e35cc7f85716e29199c9587976e230e12543aff0609eedcc49c39` |
| `notes/theory/lean/YulangClosure/CallPeelingTyping.lean` | `f89e31759657f602ba69b41a31c9f63ba61f003aa1ebe560323d65dda2b33c44` |
| `notes/theory/lean/YulangClosure/CallEntrySpineComposition.lean` | `a296a5ae738cb3ca8f88a6009495e0fe84a2a394976aafeb4630d6cdd25a11bf` |
| r3 composition receipt JSONL | `65c5d0b7319b4c9bced1fca11e7bc20060842d4e66aaa02e84706229b720d2eb` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| r9 frozen contract | `6a2a2ce7cce845df7239b790709cdbfe24e15bbacc834d9d3027e9f697131811` |
| r9 outcome | `66d5f30ee3323b33b6943b5817ee48cdd69e20bfd793ea65b08df125567a7579` |

The first four syntax/execution dependencies were accepted under the r3
serialized receipt chain. The current ControlSyntax and ControlTyping bytes
have no successful module receipts and their current `.olean`/`.ilean` files
are stale; their source checks in steps 1–2 above are mandatory. The entry
modules and their output hashes are pinned by the r3 receipt chain. Any further
import needed by the author must be proposed to Luna before use.

## Budget, acceptance, and stop

Fresh total cap 2,280 seconds, no carryover: prover 1,200; primary
verification/preflight 480; fresh review 420; integration 180. Astra zero.
One Lean process at a time, one CPU, 1 GiB. At most one new author assignment;
retain the three historical UNKNOWN quarantines and reserve review/integration
capacity. No source, runtime, Rust, test, root-import, production, or paper
changes are authorized.

Success means the exact theorem compiles on rebuilt pinned dependencies, the
signature is identical, axioms are within `[propext, Quot.sound]`, complete
receipts are archived, and a fresh independent review is CLEAN. Otherwise
record `FAILED_VERIFICATION / UNACCEPTED` or `SOURCE_INPUT_BLOCKED /
UNACCEPTED` with the exact first obstruction. The r3 syntax theorem remains
accepted; r9 source/successor adequacy, world/effect/source/native Call
preservation, original Call A/B, inference A/B, and production remain OPEN.

Luna owns current state, outcome, review assignment, adjudication, explicit
staging, complete outbound-range inspection, commit, and ordinary push. No
worker expands leases or starts a nested sprint. Consult the dispatcher again
at a material obstruction/change, frozen integration seam, or this sprint's
closure.

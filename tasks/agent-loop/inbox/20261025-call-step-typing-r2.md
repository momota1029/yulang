# CALL-STEP-TYPING-REPAIR-AUTHOR-20261025 — frozen handoff revision 1

Sprint/contract: `LEAN-CALL-STEP-TYPING-20261025/r2`,
`tasks/agent-loop/sprints/call-step-typing-20261025-r2.md`, SHA-256
`7c7d53498cf0ad43e61d5afa20b525e47adbf41caa205b14f77afa4323d024d0`.
Assignment/handoff: `CALL-STEP-TYPING-REPAIR-AUTHOR-20261025`, revision **1**.
Baseline: `862c8777684587f6ca2b20d22859f954804a2c50`.
Outcome: **candidate**, unchecked and unreviewed by this author.

## Exact parent and application

In namespace `YulangClosure.Control`, the candidate retains the exact theorem:

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

Parent application: the candidate constructs target typing for every one of
the **28 existing** `CallControlStep` constructors, then proves the result-type
and literal-suffix equalities by reflexivity. Acceptance still requires Luna's
actual compile, exact signature/axiom query, fresh independent review, and
adjudication. This author supplies no independent certification.

The first missing evidence is elaboration of this frozen repair module on the
unchanged pinned dependencies, owned by Luna. Original Call A/B, source/native
adequacy, progress/successor coverage, world/effect/View/receipt properties,
inference A/B, and production remain OPEN. The missing transition for
`.force (.view (.delay body) occurrence)` remains OPEN; r9 is unchanged.

## Repair, dependent-pattern audit, and actual constructor evidence

r1 failed verification with unknown `consumer` in both lambda alternatives and
unknown `effectView`/`resultView` in `enterExpose` and `requestExpose`. Those
indexed fields were determined by the judgment indices, so the inner case
patterns did not introduce usable new variables.

r2 binds `entryConsumer` in the outer `enterLambda` transition case,
`enteredEffect`/`enteredResult` in outer `enterExpose`, and
`capturedEffect`/`capturedResult` in outer `requestExpose`. The affected target
typing terms use those actual transition fields after the inner inversions.
The original r1 artifact and handoff remain byte-identical. r2 does not import
the failed r1 module.

Manual audit of all remaining dependent patterns: other target terms use
retained proof witnesses (`hbody`, `hvalue`, `hcontinuation`, typed frame tails),
the explicitly bound `start` term and Original step, or expected-target
constructor inference. Inner view names in `returnExpose`/`failExpose` are not
referenced; the returned value's actual result view is inferred from its target
syntax. Initial interface-list induction is ordinary list induction. No other
inner index-field name is used as a term outside its surviving scope.

Source owners remain `ControlSyntax.lean:CallControlStep`,
`ControlTyping.lean:CallHeadTyped`/`CallStateTyped`, and
`CoreSyntax.lean:TypedCall.ContextTyping`. The repair preserves the r1 proof
construction exactly apart from the three outer case bindings and four target
references:

- `start`, wrap peeling, receipt attachment, and both entry modes retain the
  actual carrier, declared consumer, pending-adapter order, and typed frames.
  Reused lemmas: `delayArgument_typed` and `callEntryBody_typed` within their
  existing syntax-typing premises.
- Original transitions use the retained actual Original state and
  `Original.step_preservation` only for an actual `Original.Step`.
- Return bind/adapter transitions apply `substituteCallComp_typed` to the
  exact transition substitution, with explicit zero/successor binder cases.
- Request bind/adapter transitions apply `renameCallComp_typed` with
  `upCall Nat.succ` under the actual response binder and combine it with the
  real continuation using `CompTyped.bind`. Neither binder is collapsed.
- Every constructor retains the literal independently typed suffix; failure
  typing uses the frame's actual output type. Local frame typing does not
  establish foreign-continuation adequacy.

No compiler/native producer or consumer correspondence is claimed. Simple-sub
constraint generation/accumulation/propagation, levels, extrusion, qualifying
intrusion, and generalization are untouched. The failed r1 check is reused
only as evidence for its six identifier errors, not as proof of r1 or r2.

## Frozen artifacts and dependencies

Artifact: `notes/theory/lean/YulangClosure/CallStepTypingRepair.lean`, SHA-256
`2ef522c022a0708be670f1ab44b57c8f558d4736f123e14ceb5f6ff259a3c586`.
The handoff byte hash is supplied separately at submission.

Source/contract hashes were re-read and match the frozen r2 table:

| Dependency | SHA-256 |
|---|---|
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `CoreSubstitution.lean` | `c4bca75be173f20d7a48751205f488ac5f0057b476e6f52d1ef7abcf046a001a` |
| `CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `ControlTyping.lean` | `e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f` |
| `CallContextTyping.lean` | `09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125` |
| `CallEntryTypingRepair.lean` | `f90c2192422e35cc7f85716e29199c9587976e230e12543aff0609eedcc49c39` |
| `CallPeelingTyping.lean` | `f89e31759657f602ba69b41a31c9f63ba61f003aa1ebe560323d65dda2b33c44` |
| `CallEntrySpineComposition.lean` | `a296a5ae738cb3ca8f88a6009495e0fe84a2a394976aafeb4630d6cdd25a11bf` |
| `lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| frozen r1 candidate | `4b3b40ae3c295666470c1cda73ac38f0abdc62ea86626be58f10249092d3c3ab` |
| frozen r1 handoff | `cf43cda1c1d741dd0d6a02cb354af92c42a1721defb0ecc6d59d3d23ea591906` |
| frozen r1 outcome | `d7606d506a52be722e4504cce91eee1b76c73df14659b3b67eb6b2b4f4dfa158` |
| complete r1 verification JSONL | `6c0737f3b825f704a2f5298953bc37b9d92fe1fd7bc3e1e2c7a77be6dc3a85df` |

The only direct imports are the unchanged pinned `ControlTyping`,
`CallEntryTypingRepair`, and `CallPeelingTyping`. Luna retains responsibility
for revalidating the accepted prebuilt-output hashes listed in r2.

## Runtime, checks, next step, and stop

Actual worker/author: `/root/call_step_typing_author`, fresh r2 assignment
acknowledged to `/root` before editing. Same author as r1; no other authors or
descendants. Requested `gpt-6.1-sol` / `high`; observed effective model/effort
**UNKNOWN / UNKNOWN**.
Luna supplied read-only confirmation of the outer transition field orders
after the repair was written; those orders match this candidate. This is
construction guidance, not an independent review receipt.

Author checks: read-only r1 diagnostic/source inspection, manual dependent-case
audit, ordinary file diff showing the bounded repair, and SHA-256 comparisons.
No Lean, tests, Git, production changes, scratch files, or spawned workers.

Fresh grant: 600 seconds, zero Astra, zero checker processes. First local UTC
receipt 03:00:38; preparation receipt 03:01:44 (66 seconds between observations,
534 seconds remaining at that receipt). Exact launch-to-first-receipt overhead
is UNKNOWN; Luna owns the launch receipt. The assignment stops below its cap;
there is no renewal or ongoing work after submission.

Mutual TODO `CALL-STEP-TYPING-R2-CHECK-1`, owner Luna: compile the frozen repair
once, then only on success query the exact theorem signature and axioms once.
Falsifiers: first elaboration error, source/dependency mismatch, missing
output/receipt, changed theorem or axioms outside `[propext, Quot.sound]`.
Stop at the first failure under r2. If checks pass, Luna assigns fresh
independent review of the frozen artifact and complete receipts.

No in-envelope author step remains. **STOPPED / WRITES STOPPED** before Luna
verification. New paths are exactly `CallStepTypingRepair.lean` and this leased
handoff. No scratch paths, background processes, descendants, or unresolved
descendant leases. Candidate is pending verification/review/integration;
reviewed theorem and parent closure are not asserted.

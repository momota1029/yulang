# CALL-STEP-TYPING-AUTHOR-20261025 — frozen handoff revision 1

Sprint: `LEAN-CALL-STEP-TYPING-20261025/r1`.
Contract: `tasks/agent-loop/sprints/call-step-typing-20261025-r1.md`,
SHA-256 `677671916d8c628ba45e2492bd799dd69436d1a9ac2ee726ed1139cf11eff8f2`.
Assignment/handoff ID: `CALL-STEP-TYPING-AUTHOR-20261025`, revision **1**.
Outcome class: **candidate**; no author-side Lean check or independent review.

## Exact parent and result

Parent: the contract's existing-transition proposition in
`YulangClosure.Control`, with its original quantifiers:

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

The leased Lean module contains this exact proposition and a proof candidate
covering all **28** constructors in the pinned `CallControlStep`. Supporting
private lemmas are applied directly to its typing proof, followed by a
constructor split proving both projection equalities by reflexivity.

Parent application: if Luna's compile/signature/axiom checks and fresh
independent review succeed, this candidate supplies existing-step preservation
of Call-head/context/suffix typing, result type, and the literal suffix. The
first remaining premise for accepting this intermediate theorem is actual
elaboration of the frozen candidate against the rebuilt dependencies, owned
by Luna. No checked or reviewed theorem status is asserted here.

The larger operational/source parents remain OPEN. In particular,
`.force (.view (.delay body) occurrence)` still has no corresponding
`CallControlStep` constructor. Progress, raw successor coverage, source/native
correspondence, world/view/scope/receipt invariants, original Call A/B,
Simple-sub inference A/B, and production authority are not established.

## Constructor evidence and prior work

The inspected source owner is `ControlSyntax.lean:CallControlStep`, with
consumers `ControlTyping.lean:CallHeadTyped` and `CallStateTyped`, and
`CoreSyntax.lean:TypedCall.ContextTyping`. The proof uses the actual target
computations and frame tails from each constructor:

- `start`: use the term's retained function/carrier typing and construct the
  exact reverse-interface expose frames plus the single receiver scope.
- `peelWrap`: reuse `delayArgument_typed` for the actual inert argument thunk;
  prepend the real result adapter using `AdaptersTyped.cons`.
- `attachReceipt` and `enterLambda`: retain the existing function/carrier/
  pending witnesses, then apply `callEntryBody_typed` separately for Value and
  Computation entry, preserving the declared consumer and pending order.
- `enterBind`, `enterScope`, `enterExpose`, return/scope/view cases, failure
  propagation, and finish cases: invert the actual computation/frame judgments
  and construct the corresponding target witnesses.
- `enterOriginal`, `originalStep`, `originalExit`, and
  `forceEmbeddedOriginalDelay`: retain the actual Original computation/state
  derivation; only `originalStep` invokes `Original.step_preservation`.
- `returnBind` and `returnAdapter`: apply `substituteCallComp_typed` to the
  exact transition substitution, with explicit zero/successor binder cases.
- `emitRequest`, `requestScope`, and `requestExpose`: retain the same operation
  instance, typed payload, and actual response continuation.
- `requestBind` and `requestAdapter`: construct `captureBind continuation body`
  with `CompTyped.bind`; use `renameCallComp_typed` at `upCall Nat.succ` on the
  frame body. Its target environment is
  `extend (extend emptyContext responseType) activeType`; the pointwise
  context law follows by cases on the index. The response binder and frame
  result binder remain distinct.

All 28 constructors literally retain `resultType` and `literalSuffix`. The
independently typed suffix is reused as an opaque judgment throughout; no
action on one local frame is claimed to establish foreign-continuation
adequacy. Constraint generation, Simple-sub propagation/extrusion/intrusion,
generalization, and compiler/native paths are outside this formal relation;
this packet changes or certifies none of them.

Reused within their actual premises: the r3 accepted syntax entry/peeling
lemmas, Original one-step preservation, and Call renaming/substitution.
Rejected as evidence for this theorem: stale pre-Call Control build files,
assumed transition probes, global Call preservation/source adequacy, and the
r9 unaccepted source-input result. No withdrawn inference bypass or historical
conditional result is promoted.

## Frozen inputs and artifact

Author baseline supplied by Luna: `d3a3c2819` (contract-only scheduling commit);
contract semantic baseline: `12a081b82e2a84678aab7f5d0f301cd724c72542`.
Luna subsequently confirmed successful current-source Control preflight and
lease activation, identifying receipt commit `be623b6b5`. No Git command was
run by this author.

Direct imports of the candidate are only the pinned `ControlTyping`,
`CallEntryTypingRepair`, and `CallPeelingTyping` modules. Source SHA-256 pins
were read and matched before writing:

| Input | SHA-256 |
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
| r3 composition verification JSONL | `65c5d0b7319b4c9bced1fca11e7bc20060842d4e66aaa02e84706229b720d2eb` |
| `lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| operational type-safety paper | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| r9 frozen contract | `6a2a2ce7cce845df7239b790709cdbfe24e15bbacc834d9d3027e9f697131811` |
| r9 outcome | `66d5f30ee3323b33b6943b5817ee48cdd69e20bfd793ea65b08df125567a7579` |

Luna-only preflight receipt file, read after activation:
`tasks/agent-loop/inbox/20261025-call-step-typing-r1-verification.jsonl`,
SHA-256 at the two-preflight-record snapshot
`5233bbaab33438fa722bae1de05c00084363260667ccceba88207a25efcae2d2`.
This receipt will gain Luna's later verification records; the snapshot hash
here identifies only the preflight dependency acceptance.

Observed rebuilt Control outputs in those receipts:

| Output | SHA-256 |
|---|---|
| `ControlSyntax.olean` | `372a3a91210c161b3e7699578f6d7043b5b48eb096bf6b12cb101fcb97f00f28` |
| `ControlSyntax.ilean` | `3ed9083679f8d4be830e05809b096f4b9927335ac623d84fd0a25e2112c8fdf1` |
| `ControlTyping.olean` | `b487cae6f465c9aea4d5d42d04c8116c46ed58e84d60635e32318f880b1ae59e` |
| `ControlTyping.ilean` | `c5b36c5c5032fc2eab1f3711fd8c7f83fa7a1db3cc6507f08c365c4d771cff6f` |

Frozen candidate artifact:
`notes/theory/lean/YulangClosure/CallStepTyping.lean`, SHA-256
`4b3b40ae3c295666470c1cda73ac38f0abdc62ea86626be58f10249092d3c3ab`.
This revision's handoff byte hash is supplied separately with submission to
avoid a self-referential hash.

## Runtime, checks, next step, and cessation

Role: constructive proof author, actual worker
`/root/call_step_typing_author`, assigned by `/root` in this current session.
Requested model/effort: `gpt-6.1-sol` / `high`.
Observed effective model/effort: **UNKNOWN / UNKNOWN**; no runtime observation
was supplied that would independently establish either setting.
Sole author: `/root/call_step_typing_author`. No contributing descendants;
no spawns or reviewer appointments.

Checks performed by author: read-only source inspection, source/contract
SHA-256 comparisons, constructor enumeration, and manual proof reread.
No Lean invocation, tests, Git, production edits, generated build files, or
scratch files. Luna owns all checker execution and independent review.

Budget: maximum 1,200 seconds, one leaf, zero Astra, zero author checker
processes. Exact elapsed assignment time is UNKNOWN because no initial
wall-clock receipt was taken; local UTC observations were 02:53:33 and
02:55:39 during this assignment. Luna retains the launch/resource receipt;
no budget renewal or further author work is requested. Stop occurs within
the assigned cap; all remaining author work is surrendered at this handoff.

Mutual TODO `CALL-STEP-TYPING-CHECK-1`, owner Luna: compile the exact candidate,
then import it and query the exact signature and axioms on the frozen current
dependencies. Falsifiers: any elaboration error, changed source/dependency,
different statement, missing output/receipt, or axioms beyond the contract's
allowed `[propext, Quot.sound]`. Stop at the first failure under r1; no automatic
author repair loop is authorized. On success Luna assigns fresh independent
review of these frozen bytes and receipts.

No further in-envelope author step remains. Status: **STOPPED / WRITES
STOPPED**, before verification and review. Exact new paths are the two leased
paths: this handoff and `CallStepTyping.lean`; there are no scratch paths,
background processes, descendants, or unresolved descendant leases.
Candidate awaits Luna verification/review/integration; parent closure and
commit-ready approval are not asserted.

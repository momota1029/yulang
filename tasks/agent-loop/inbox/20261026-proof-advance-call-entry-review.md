# Independent review: direct call-entry formation

Revision: r1. Reviewer: `/root/call_entry_review`, a fresh non-author assigned
by the primary. Requested model/effort: inherited; independently observed
model/effort metadata: UNKNOWN. This receipt does not claim execution of a
configured specialist role. No children and no contribution to the reviewed
proof construction or repair.

## Verdict and frozen inputs

**CLEAN within the explicitly stated direct-spine code-formation and existing
partial-executor scope.** No blocking, major, or minor finding. Recommend that
the primary accept these frozen lemmas in that scope, subject to its own
integration checks and adjudication. This does not approve new source semantics
or close the original whole-language, current-world, native, or inference gates.

The primary supplied baseline `adfed0dbcc8875ac0c9e66c40a0b967b3e9df073`
on `yulang3`. No Git command was run to independently inspect that baseline.

| Frozen input | Verified SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/PaperCallEntryFormation.lean` | `2465c5620b0b66f6029ab294134d9860cd8bf810ac25c5f30763cb709c7da31e` |
| `tasks/agent-loop/inbox/20261026-proof-advance-call-entry.md` | `c2bcffce402d1805150f61e42c1e915e14efbf820c2bba713913fcb3ff00ee4d` |

Both hashes were checked at intake and again after inspection. All 19 source
and dependency hashes in the producer's handoff match the current bytes. The
17 listed Lean dependencies and the new module match the isolated project's
bytes. Recursively reading imports gives exactly the 18 modules in
`call-entry/modules.txt`. The isolated pin, lakefile, and manifest also match
the repository: Lean 4.35.0, `-j1 -M1024`, and no external packages.

## Source correspondence and proof meaning

The original claim inspected is the code-formation/substitution part of
corrected V5(4), with its proposed application to V6. Read the actual
operational manuscript `docs/yulang-operational-type-safety-ja.tex:362–395`,
its opening correction notice, and
`notes/theory/2026-10-24-corrected-core-value-continuation.md`, including
V1, V2, V5(4), and V6. These remain research/candidate sources, not an
independent grant of production semantic authority.

1. **Full finite direct wrapper spine; same owner and literal receipt.**
   `PaperCallEntryFormation.lean:31–38,46–75,117–147` covers both lambda modes
   and arbitrary finite nesting of direct wrappers. Every recursive call uses
   the same `receipt` and `owner`. Only the lambda leaf adds the literal
   `.view (receipt owner profile)` to the accumulated thunk. The generated
   administrative code introduces no source `call`; existing calls inside
   source bodies or adapters are retained. This matches O:366–385, subject to
   the explicitly unresolved construction of the actual source receipt.

2. **Adapter order and shared environments.**
   At `:41–42,53–55,108–112,138–147`, each argument adapter is stored inside
   `.delay (.letE (.force thunk) argumentAdapter)`. No adapter code runs while
   the entry body is formed. Each result adapter surrounds the recursively
   formed inner body, so results flow inner to outer. The actual wrap typing
   rule in `PaperExecutionSyntax.lean:698–706` gives argument and result
   adapters their respective single binders over the same lexical environment;
   the proof uses those derivations without replacing declaration, graph, or
   lexical captures. No independent intermediate-type witnesses are selected
   for different consumers.

3. **Value binding and Computation substitution.**
   The Value branch `:48–49,126–130` forces the viewed thunk and reuses the
   lambda body under the existing input binder. The Computation branch
   `:50–52,131–137` supplies the same viewed thunk to the existing typed term
   substitution theorem. `PaperCoreStep.singleReplacement` maps index zero to
   the supplied value and successor indices to their predecessor
   (`PaperCoreStep.lean:10–23`). Nested term binders lift replacements and
   shift free variables; type binders shift the replacement types
   (`PaperTermSubstitution.lean:234–295`). The partial public substitution
   rejects omitted syntax, while the existing typing derivation establishes
   support and successful substitution (`:717–722,756–760`). Success and
   resulting body typing are derived, not assumed as new `BodyLaws`.

4. **One constructed code witness reaches the finite-interaction consumer.**
   `call_spine_formation` at `:152–163` inverts the actual paper Call typing
   rule and retains a separate trace under the same literal owner scope.
   `call_spine_finite_interaction` at `:168–186` puts `exists code` before the
   universal `last/path` quantifier. Its call to
   `PaperExtendedExecution.finite_interaction` supplies exactly this `code`,
   its proved typing, and the supplied stack typing. The independent
   `BodiesTyped d` code-table obligation and per-trace `ProtocolTyped g e`
   assumption remain explicit. I inspected their definitions and the actual
   consumer theorem in `PaperTemplateExecution.lean:19–29` and
   `PaperExtendedExecution.lean:221–301`.

5. **Frontier theorem states the actual partial-executor fact.**
   `:199–222` constructs one implemented let push from the Value-entry code,
   with exactly `body :: stack`, proves that successor typed, and proves its
   next `PaperExtendedExecution.controlStep` is `none`. `:190–193` proves
   the missing Force/View case for arbitrary metadata, thunk, and stack.
   The existing fallback chain recognizes direct Force/Delay, split,
   perform/request, empty-owner resume/failure, direct type beta, and templates;
   it supplies no Force/View transition. This supports the documented
   executor boundary. It does not establish divergence, source stuckness,
   source-world reachability, metadata erasure, or a source-progress
   counterexample. No such stronger conclusion appears in the frozen theorem
   type or its handoff.

## Severity-tagged scope observations

These observations are explicit limitations, not defects requiring repair.

| Severity | Exact location | Observation and recommended action |
| --- | --- | --- |
| INFO | `PaperCallEntryFormation.lean:29–38,118,154,171`; producer handoff `:115–128` | `DirectCallableSpine` is an additional syntactic premise. General callable observation/normalization, including graph references, Views, type applications, and guards, is still open. Keep that premise visible when applying the lemma to the unchanged parent claim. |
| INFO | `PaperCallEntryFormation.lean:9–19,25–27,58–59,149–159` | Arbitrary raw metadata is selected from owner/profile; no actual fresh owner, receipt observation path, world transition, or scope completion is constructed. `EnterTrace` is a source-shaped administrative relation, not a proved simulation of the corrected machine. Keep the receipt/world/source bridge and raw scope/enter typing obligations with their existing owners. |
| INFO | `PaperCallEntryFormation.lean:165–186,188–222`; producer handoff `:109–128` | The finite-interaction trace begins at the constructed ordinary body with an ordinary let stack. It does not execute the retained scope. The Force/View frontier is a missing case of this partial executor. Preserve the stated distinction in integration records and do not promote it to V5/V6 or noBad/progress closure. |

## Checker evidence inspected

No checker rerun was requested or performed: the assignment authorized a
read-only one-pass review using the existing frozen evidence unless a concrete
issue justified more budget, and no such issue was found. Read the final
command/version/build outcome and all ten complete printed theorem types and
axiom reports in `call-entry/audit-3.log:3707–3905`. The command invokes the
exact named module and all ten declarations with the native Lake path and
45-second bound. It records Lake `5.0.0-src+eb6cafb`, Lean `4.35.0` commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, build exit 0, audit exit 0,
ten PASS results, and 2.919 seconds. The helper's ordinary-mistake/axiom
whitelist boundary is not treated as a source-correspondence certification.

All declarations below are in
`YulangClosure.PaperTypes.PaperCallEntryFormation`:

| Declaration | Complete reported axioms |
| --- | --- |
| `EnterTrace.trans` | `[propext, Quot.sound]` |
| `EnterTrace.underLet` | `[propext, Quot.sound]` |
| `EnterTrace.underScope` | `[propext, Quot.sound]` |
| `EnterTrace.plug` | `[propext, Quot.sound]` |
| `adaptedThunk_typed` | `[propext, Quot.sound]` |
| `spine_formation` | `[propext, Quot.sound]` |
| `call_spine_formation` | `[propext, Quot.sound]` |
| `call_spine_finite_interaction` | `[propext, Quot.sound]` |
| `controlStep_force_view_none` | `[propext, Quot.sound]` |
| `value_entry_view_frontier` | `[propext, Quot.sound]` |

The retained `build-1.log` records the initial `.tail` elaboration and reserved
`scoped` binder failures, followed by exit 1; these are not presented as success.
The source contains the recorded repairs. `audit-2.log` records the prior
eight-theorem pass. `check-seconds.txt` records 65.78668719600319 seconds total.
The producer's source-scan file is empty apart from a newline. An independent
read-only scan of all 18 imported/module sources for `sorry`, `admit`, `axiom`,
`sorryAx`, `unsafe`, `native_decide`, and `debug.skipKernelTC` found no matches.

| Evidence | SHA-256 computed during review |
| --- | --- |
| `call-entry/build-1.log` | `4fdc35909556cd72f7eb81c255176ad2e8d73be57495908159d4f2785dfc10f3` |
| `call-entry/audit-2.log` | `33227054d4911bfc120b2eba53a5e7a40f6c76f9c909e0d44a71a2b32a0ec44e` |
| `call-entry/audit-3.log` | `40396a736cee382fbc48d1912b182b727649d1fa8e8e7a117d6391af0e729474` |
| `call-entry/modules.txt` | `91adf36aa1bf7adf31535466040640c34457be25b43a43cea117649bdb35f0b1` |
| `call-entry/source-scan.txt` | `01ba4719c80b6fe911b091a7c05124b64eeece964e09c058ef8f9805daca546b` |

## Inspected and uninspected scope; cessation

Inspected the entire 224-line new module and entire frozen producer handoff,
the cited source passages, relevant existing syntax/typing/substitution/control/
template/protocol definitions and consumer theorem, dependency hashes and
imports, final complete named-theorem audit, and retained build/audit outcomes.
Applied root AGENTS instructions and the `yulang-lean-proofs` skill, including
its source map and execution evidence rules. The current scheduling snapshot
was read only; the primary's new exact review packet supplies this assignment.

Not re-proved or independently certified: every theorem body in the existing
dependency modules, all source manuscript cases, actual world/receipt
semantics, normalization, graph guardedness, source/native correspondence,
inference A/B, production behavior, or other concurrent modules. No default
root build/import integration, Rust check, or toolchain distribution provenance
audit was performed. Those limits do not change the explicitly reviewed lemma
scope and remain the primary's integration/parent obligations.

The only write is this exact leased review receipt. No Git, source, cache,
shared-state, semantics, or other receipt was modified. No checker processes or
children were launched. **Review writes STOPPED after freezing this receipt.**

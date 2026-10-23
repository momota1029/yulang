# RELEASE-CLOSURE-20261024 — release first, then source safety

Outcome: **unreviewed paper construction plus a source-qualified behavioral
counterexample and explicit repair candidate**. The original inference-independent
whole-language parent remains OPEN. No semantic adoption, reviewed proof,
inference/native, original A/B or production gate is promoted.

## Inputs, authorship and actual runtime

- Baseline: `5df75a53f14b952bbf83317328bfc91337ee789b`.
- Contract revision 1 SHA-256: `ca2816d82ffaa700c862b67e968c545dd1dd2b569e3d5130680bde0c5e8a0b23`.
- Prior source manuscript: `0817a7023a51f262f7759a75bccea78779525800bad0e8f0c05f1e0f64d26372`.
- Current source manuscript: `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`.
- Operational dependency unchanged: `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
- Selection dependency unchanged: `47b7fcec1f501e7c326ab9859885e329aab2730066806ea79212e825ebb32b0b`.
- Original user manuscript unchanged: `28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65`.
- Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Prior-state archive: `release-closure-20261024-prior-current.json`, SHA-256
  `0ffbfdecc3a7e86aa45258ec50adf08025c5048f0729624bf4a96fe9853d4f02`.
  This preserves the full old history; all pending entries and UNKNOWN leases
  remain in compact current state.
- Author: this primary only; no children, nested CLI, independent reviewer or
  model switch. `list_agents` reported only /root running. Session/effective
  model/effort UNKNOWN; no Astra-execution claim.
- Clock authoring interval: 2026-10-23 16:25:23–17:22:28 UTC, **3425 seconds**,
  cap 7200 seconds. At the final clock, source authoring froze. Subsequent work
  is records/static/Git integration, not continued proof authoring. Four prior
  UNKNOWN writers and quarantined outputs remain reserved; no background work.

## Concrete changes applied to the parent

1. Source section 11 replaces the free ingress selector with the explicit
   **all matching inputs candidate**. R-Capture freezes the actual lexical
   receipt table; R-Match uses boundary/binder/path, not row equality or a
   world-wide search by source name. Two inputs keep distinct origins; two
   ordinary entries cannot use each other's target state. Regular and
   nonregular path templates are queried on finite actual paths.
2. Target transport is cumulative **on each actual witness route**. An outer
   target cannot replace an earlier target and resurrect its canceled shield.
   Separate input views and independent routes remain separate. R-Step lists
   mark/Ret/Fail/Req and internal-step behavior explicitly.
3. Lemma 11.3 proves the necessary-and-sufficient crossing history of L;
   Lemmas 11.4–11.5 prove overlap/locality and substitution; Proposition 11.6
   uses current-world state across multi-shot resume. Latent transport alone
   installs no new release delimiter and cannot cause the first crossing.
   Theorem 11.7 composes this into inference-independent source safety for
   the fully stated candidate release rules. It does not record adoption of
   the unanswered multiple-input choice.
4. Section 12 corrects an overstated earlier remainder. Frozen ordinary
   constructor applications are Computation, not a special generalizable Value.
   G-Value/G-Compute and Theorem 12.1 preserve the approved computed-fetch
   restriction while permitting an already-polymorphic payload to be used at
   several types. Constructor evaluation is not moved under type abstraction.
   Arbitrary effectful constructor arguments remain allowed. This is not a
   proof of native level/generalization implementation on every path.
5. Proposition 14.1 composes comma/semicolon/newline normalization with the new
   release rules, including negative `[undet, 'e]`. Section 14 gives typed
   templates for operators, for/labeled for, the listed parser DSL forms and
   the Yumark two-lambda shell. It retains GeneratedNeutral versus source
   omission provenance. The parser DSL Value/Record tail is delayed after the
   accumulated statements exactly as in the frozen lowering; no false generic
   source-order evaluation theorem is asserted. Yumark inner nodes remain open.
6. Section 15 finds a substantive obstruction: receiver-local **AllowAll** in
   the old existential grant query can let a local `sub` handle a return from
   g's protected callback. The finite g/sub context yields 2 under that rule,
   rather than the selected receiver-relative behavior 0. This is a paper
   source discriminator, not a compiler execution or a value-safety refutation.
7. The explicit permission repair distinguishes protection from receipt/grant,
   makes a computation wildcard a permission-only introduction, and uses
   `not P or G_concrete or (G_wildcard and not P_foreign)` at the same joint
   contribution. This prevents wildcard-only laundering of a live foreign
   shield, preserves local concrete permissions and scoped release, and keeps
   ordinary nested sub behavior. Theorem 15.3 derives the local callback and
   identity-wrapper discriminator. **Theorem 15.4 is the final repaired
   candidate source-safety theorem**, using regenerated effect evidence.
   The repair is not approved language semantics or independently reviewed.

## Source evidence and implementation boundary

Frozen owners read, not executed:

- `crates/infer/src/lowering/expr/tail.rs`: apply_arguments 89–138;
  ordinary App 626–627; computed generalization 944–989; operators 393–476.
- `crates/infer/src/lowering/expr/block_local.rs`: for/labeled for 424–542;
  ordinary local RHS fetch classification 548–585.
- `spec/2026-06-13-computed-fetch-value-restriction.md`: original value boundary.
- `crates/infer/src/lowering/rule_lit.rs`: parser shell/sequence/choice,
  quantifier dispatch and capture/record/block constructors.
- `crates/infer/src/lowering/yumark_lit.rs`: 166–256, two generated lambdas.
- `lib/std/control/flow.yu`: actual wildcard computation formal and sub catch.
- Governing sources: charter section 13, October 5 approved crossing answer,
  October 10 annotation policy, October 15 compose and callback-identity decisions.

Current native owners inspected read-only: `yu-hir/src/module/local_source.rs`
retains source annotations; `yu-hir/src/module/source_annotation.rs:124` has
no universal type constructor; `yu-solver/src/candidate_source.rs:363` explicitly
records omission metadata without its semantic consumer, and preflight still
restricts multiple row variables. These are implementation facts, not language
restrictions. **NO_SAFE_CODE_SLICE** for dependent promotion: source formation,
permission meaning and all-path correspondence remain open; the user authorized
proof before code. No compiler, test or expectation file changed.

## Remaining obligations and review seam

- **RELEASE-CHOICE**: user selection of both matching inputs versus an occurrence
  choice is still unanswered. The all-input paper theorem does not invent an answer.
- **PERMISSION-ADOPTION**: review the new source discriminator and permission
  repair, especially exact carrier paths, source roles, inherited concrete
  permissions and latent/reentry cases. Check that every intended source
  behavior is preserved. The older existential AllowAll application is not
  promoted as a correct implementation plan.
- **SOURCE-ADEQUACY**: Pi_flow and the concrete lifetime realization remain
  candidate choices. The paper theorems do not establish all ordinary source
  expectations or Oracle equality, nor arbitrary eta contextual equivalence.
- **SURFACE-COVERAGE**: Yumark inner nodes/format/interpolation, full
  module/use/realm/band resolution, error/act-copy/derive generation and other
  unlisted surface variants still need explicit expansion coverage. Theorem
  14.3 covers exactly its listed templates and shell, not the entire parser.
- **INDEPENDENT-REVIEW** and mechanization: NOT_RUN. Primary rereading and PDF
  checks are not substitutes. No reviewed status is transferred to these bytes.
- **INFERENCE/NATIVE**: principal inference, solver/generalization/FreshUse,
  resolver snapshot/raw-compact/SCC behavior, implementation correspondence and
  original Simple-sub A/B remain OPEN. Resolver coherence is not an added
  premise of safety for a fixed finite selected witness.

Next useful work: fresh proof review of the frozen release/permission seam and
explicit remaining surface/declaration expansion. A blanket “only implementation
remains” would still be false. The current paper result removes specific free
premises and repairs a concrete obstruction without changing the parent claim.

## Checks and artifacts

- XeLaTeX pass 6 succeeded: **42 pages**, no undefined references, LaTeX warnings,
  overfull boxes or missing-character reports; seven underfull paragraphs.
- 56 unique labels, no unresolved internal references; `git diff --check` clean.
- `python3 tools/agent_sprint.py check`: STATIC CHECK PASS; not live agents or review.
- PDF and logs: `/tmp/yulang-release-closure-20261024/`;
  `yulang-source-type-safety-ja.pdf`, `pass1.txt` through `pass6.txt`.
- Pages 30 and 39 rendered and visually inspected; the W-Eligible tag overlap
  was repaired and page 39 inspected again. Image artifacts in the same directory.
- No compiler build, test, unit test, semantic execution or executable probe ran.
  All behavioral traces above are mathematical derivations, not observations.
- Integration is an explicit-path unreviewed research checkpoint. Current state
  records the resulting commit; inspect the complete outbound range before the
  nonforced push. Original user files and quarantined writers' files are untouched.

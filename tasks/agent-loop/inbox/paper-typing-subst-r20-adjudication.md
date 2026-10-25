# R20 primary adjudication — union elimination typing and substitution

Sprint `FULL-PAPER-TYPE-SUBSTITUTION-20261025/r20`, contract r1 SHA-256
`49166707d5fd483660672fd29f905fa38c3f0fc1f654b4569a6ea44beadb7743`.
Baseline `aafbc15f0f9595eabea2c5187fba75fff06c3d04`.

## Disposition

**R20 accepted as a reviewed prerequisite.** The represented paper judgments now
include union elimination typing, an inversion theorem preserving the exact
result-type index, left and right injection typing compositions, and the
union-case branch of the arbitrary-σ simultaneous type-substitution proof. All
six existing transport theorem statements remain unchanged.

The rule follows manuscript `docs/yulang-operational-type-safety-ja.tex:233`:
the scrutinee has `A ∨ B`, the left body has result `C` under `A :: Γ`, and the
right body has the same result `C` under `B :: Γ`; all share `D`, `Xi`, and the
same tail environment. Inversion recovers both branch derivations at the
original `resultType` index. The injection lemmas compose the existing
`injectLeft`/`injectRight` typing with the union-case rule and retain both
branch premises. The recursor maps the scrutinee and both bodies under the same
arbitrary σ, retaining both binder names and their left/right types.

R20 closes only these represented union-case typing, inversion, injection
composition, and substitution-support obligations. The full-paper
simultaneous-substitution parent, R18 variant type-argument correspondence,
remaining omitted rules, recursive graph guards, inference/executor claims,
original A/B claims, source/native correspondence, Rust, and production remain
OPEN. This packet makes no branch-execution or runtime claim.

## Frozen artifacts and review

- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`, SHA-256
  `678f84eb635c95392068887b834a4f79a1a754ad474b950097aa212a3b68032c`.
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`,
  SHA-256 `55c84a4c3a5e83c3f4b8ff05b836790f0357b836d31daf0b9b316c427947afb7`.
- Frozen worker handoff `tasks/agent-loop/inbox/paper-typing-subst-r20.md`,
  SHA-256 `dc3a214ecf0ce25ec3f23845bc1a4e6a49b4e466204d3ca7e053d452cc8de039`.
- Exact audit source `tasks/agent-loop/inbox/paper-typing-subst-r20-audit.lean`,
  SHA-256 `5e2fb4f6b9ba6f360201ac44637b8abf5aebd7d34987c864146ebaba19641f3d`.
- Primary final audit output
  `tasks/agent-loop/inbox/paper-typing-subst-r20-primary-audit.txt`, SHA-256
  `10aa75d3eb4135fc89df302cf4ff2d4386549c95874074cb92922c91d5a90ca4`.
- Fresh independent source-only review
  `tasks/agent-loop/inbox/paper-typing-subst-r20-review.md`, SHA-256
  `fdf30d1b9d8759cdd21cbad7883137282fd2de88f42418bdaffef4ccc999d5db`.
  Verdict: **NO BLOCKING OR MAJOR FINDINGS**. The reviewer checked manuscript
  correspondence, shared contexts, both branch premises and binder types,
  exact result-type preservation, both injection compositions, all six
  transport statements, dependency changes, and the axiom reports. It used
  zero Lean/Lake calls and is not a kernel receipt.

The worker-authored source, audit, and handoff were frozen before review. The
reviewer was not an author. The primary final calls below independently checked
the integrated frozen bytes.

## Checker receipts and limits

- Worker invocation 1: focused build of `PaperExecutionSyntax` and
  `PaperExecutionTypingSubstitution`; exit 0, 22.586330 seconds. The full worker
  command output is retained in the handoff.
- Worker invocation 2: `lake env lean -j1 -M1024 .lake/R20Audit.lean`; exit 0,
  0.686139 seconds. All nine audited theorems report exactly
  `[propext, Quot.sound]`; the union-case constructor has no axioms.
- Primary invocation 5: repeated focused build of both changed modules; exit 0,
  tool-reported process wall time 0.027594 seconds. The tool display truncated
  the verbose warning output; the visible completion reports successful build.
- Primary invocation 6: repeated exact audit command above; exit 0. The complete
  output is retained in the primary audit file. The exact process time was not
  captured separately, but the invocation completed within the configured
  30-second tool wait.
- Total: four of six permitted literal Lean/Lake invocations. Exact measured
  checker time is 23.272469 seconds for worker calls 1–2 plus 0.027594 seconds
  for primary call 5; call 6 is under 30 seconds. Total is therefore less than
  53.300063 seconds of the 90-second cap. Worker calls 3–4 were unused; no
  budget was transferred. Active-time telemetry was unavailable.

No failed checker invocation is omitted. No `sorryAx`, project axiom, or
disallowed axiom appears in the complete primary audit. Worker cessation was
confirmed before review: writes stopped and no process or descendant remained.

## Remaining proof gates

The original full-paper typing/substitution theorem remains OPEN. R20 does not
resolve the separate R18 variant type-argument authority gap, and it does not
establish inference/executor safety, operational preservation, source/native
correspondence, the original A/B claims, or production readiness. The next
packet must be selected against the current source authority and dependency
state; this adjudication grants no additional proof or implementation lease.

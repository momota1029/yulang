# Resumed definition materialization — pending source decision

Question ID: 2026-10-16-resumed-definition-materialization
Question revision: 1
Predecessor/history: none
Original worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Relevant source revision: f75299ea4; runtime machine SHA-256
`bac47d83a5f928bb30cb73df830048f9f57d9041fbc2cac2bc965dde10a7cdc8`
Task/thread locator: current API conversation; stable message URL unavailable
Status: pending; no answer or approval presumed

## Requested scoped decision

Select two observable laws for a top-level computed definition whose unfinished
materialization is captured by a reusable raw continuation. This selects no
restriction on continuation use count and no historical store restoration.

## Background and current premises

The user requests completion of playground, inference and execution with proofs.
The charter §§14–17 and ordinary-computation package §§2–3 already select
repeated raw resumption against the current shared store. The Oracle
`spec/2026-06-13-mono-vm-contract.md` runtime-root contract selects source-ordered
computed-root evaluation and cached completed values. Existing ordinary runtime
and receiving-cache proofs cover one unfinished write owner, without Resume.

Read-only architect `native_consumer_architecture` and specification reviewer
`runtime_contract_review` independently found that these rules do not specify
repeated completion of the same captured definition-cache write. Ordinary
assignment does not supply that law: definition materialization is its own owner.
The reviewed raw-template derivation retains this missing premise explicitly.

Semantic discriminator (schematic, not an executed source fixture): evaluating
`pending` requests an operation. Its handler saves continuation `k`, calls
`k 0`, then `k 1`, and finally reads `pending`. Both calls reach the same
original pending cache-write suffix. A separate discriminator reads `pending`
inside the handler before any call to `k`.

## Options and consequences

### A. A second completion of the same materialization

1. **Keep the first published value (recommended):** the first completed
   execution publishes `0`; the second continuation execution returns its own
   `1`, while later ordinary reads of `pending` still return `0`. Continuation
   execution and once-only definition publication are distinct.
2. **Publish each completion:** the second execution returns `1` and replaces
   the saved definition value with `1`; later reads observe the latest completion.
3. **Return the cached value on repeated completion:** once `0` is published,
   a later completion returns the cached `0` instead of its computed `1`.

### B. A read while materialization is suspended and not completed

1. **Report an unfinished-initialization runtime error (recommended):** a read
   before `k` completes does not start a second initializer. This is distinct
   from a completed cached read and from an abandoned attempt.
2. **Start another initializer execution:** the read may repeat the initializer
   prefix and its effects; competing completions follow decision A. Active
   recursive demand still requires its independent recursion check.

The recommendations preserve once-only publication and avoid silently repeating
initialization effects. They are proposals, not existing authority or proofs.
Alternative user wording may select another explicit law.

## Affected work

Blocked scope: raw Resume of contexts containing GlobalRead/Root cache-write
frames, their completion/recursion proof and final whole-runtime certification.
Independent authorized work: existing receiving-handler integration, template
construction and Resume without cache-write frames, ordinary carrier consumption,
native Simple-sub proofs and inference work. No global task pause follows.

Required answer: explicit choices for A and B, or a complete replacement law.
The primary will record a direct conversational decision with provenance and
submit its concrete design/implementation to independent review. A separate
answering-primary bundle, if used, follows the normal exact-content handoff.

Keep this entire pending directory unstaged and uncommitted. No answer-draft,
approved-answer or approval receipt has been fabricated.

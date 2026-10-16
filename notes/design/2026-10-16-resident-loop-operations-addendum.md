# Resident loop: historical reuse, model floor, Git hygiene and atomic questions

Status: Authoritative
Scope: `research/simple-sub-intrusion` agent operation and question-board integration; no change to compiler semantics or theorem status
Approved-by: user's 2026-10-16 follow-up requesting past-work reuse, a Luna implementation minimum, routine untracked-file disposition and complete question-directory commits
Approved-at: 2026-10-16
Drafted-by: repository-maintenance primary
Reviewed-by: independent live reviewer unavailable; static verification only until runtime exercise
Supersedes: [resident research loop](2026-10-16-resident-research-loop.md) only for implementation model/fallback/escalation; [questioner-integrated handoff](2026-10-04-questioner-integrated-answer-handoff.md) §§3–4 only for committed bundle membership and receipt timing; contrary active-rule text on those exact points

## Reuse earlier implementation and reasoning

Before assigning a substantial new proof or implementation packet, inspect the **relevant** historical source implementation, fixtures/tests, `git log`/`git show` for the owning path, `notes/design/INDEX.md`, linked theory/progress notes, previously rejected routes and current task status. Search by original gate, constructor and consumer; do not dump the repository or create another planning ledger. Include exact prior locators and the decision **reuse / adapt / reject** in the packet, explaining which premises remain open. Prior failed approaches and proven lemmas can prevent duplicated effort; superseded designs, conditional proofs and withdrawn Simple-sub bypasses cannot override current authority. Use only the minimal search needed and report a bounded negative result when no predecessor is relevant.

## Implementer floor and escalation

The `implementer` role is **pinned to `gpt-6-luna` / `high`**, regardless of the generic Sol child default. It must never silently fall back to Sol. The primary remains Luna; `prover` and `next_action_selector` normally remain Sol/high. After Luna/high produces a concrete localized implementation/semantic bottleneck that cheaper checks cannot close, the primary may authorize **one bounded, non-resident** `implementation_escalation` assignment pinned to `gpt-6-astra` / `low`. Freeze and relinquish the implementer's exact lease before the escalation writes it. This is a separate worker with its own verification and stop condition, not an in-place model swap; resume Luna/high afterward. Respect the existing global one-Astra-at-a-time and per-decision budgets. If an implementation role/model is unavailable, the Luna **primary** can do a bounded safe slice itself or the implementation lane waits; do not claim a Sol fallback meets the floor or that unverified routing succeeded.

## Git worktree hygiene

The primary audits `git status --short --untracked-files=all` at startup, after meaningful completed packets, before commit/push, and before session handoff. Classify each path against actual workers, leases and Git history:

- **Authorized useful work**: freeze, run scoped checks/review, commit promptly as a coherent artifact and push the intended range.
- **Proven disposable scratch created by this assignment**: once its writer stops and ownership is confirmed, delete only explicit named paths.
- **Unintegrated `questions/<id>/`** (including approved but unvalidated answers and experimental drafts): protect unchanged until the atomic question workflow below.
- **Unknown/foreign-worker output**: preserve it with an owner/next disposition. Do not overwrite, delete or commit it speculatively.

No blanket `git clean`, `rm -rf` on uninspected directories, hard reset, indiscriminate stash or `git add -A`. The existence of protected pending questions does not mean the primary should make the whole tree clean. Child workers report all new output paths and which are disposable; only the Git-owning primary performs deletion/commit. Avoid repeated meaningless cleaning cycles.

## Atomic question directory commit, including unsuccessful attempts

The questioner/answerer file ownership, explicit complete-draft approval, independent freshness/identity validation and questioner-only Git remain unchanged. **Never commit or delete an unapproved/unintegrated question** just to clear untracked files.

After explicit approval of the selected current answer, the questioning primary freezes writers, validates the exact `question.md`, selected current `answer-draft.md` and `approved-answer.md`, and inventories the entire selected `questions/<id>/`. Preserve and commit *all intentional* earlier revisions, comparison notes, intermediate experiments and failed-attempt artifacts as **non-authoritative provenance**, even when those earlier attempts were not separately approved; the selected `approved-answer.md` alone conveys the approved decision. Scan and safely resolve unrelated foreign content, secrets and disposable build junk before staging; do not drop meaningful history simply because it failed.

Create the validation `receipt.md` **before committing** with identities, question/draft revisions, exact approval/provenance, hash/manifest evidence, affected scope and a locator referring to “the commit containing this directory bundle.” Its own final commit hash cannot be included in its immutable contents. Freeze/recheck the directory and staged list; stage **only the entire curated selected question directory**, then make **one coherent question-bundle commit** containing question, approved draft/answer, attempt history and receipt. No second question-directory receipt commit is needed; resolve the SHA with directory Git history and record later consumption/status outside the finalized directory. Push safely without force. Exclude every other pending question directory. Only consume after the actual committed bytes and approval still validate; a Git commit never constitutes approval. Existing finalized historical handoffs are not retroactively rewritten.

## Validation limits

Only policy/config and documentation are changed here. Static TOML/role/skill/link checks do not prove live agent/model routing, cleanup safety or question-dir integration. Test the new Luna default, writer handoff to Astra and atomic question staging against a controlled approved fixture in the actual Codex runtime; never fake approval or commit a real pending answer just to test.

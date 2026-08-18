# Codex MCP operating policy

This repository uses Codex MCP as the primary implementation and investigation engine.

Claude's role is to supervise, constrain, review, decide, and unblock.
Claude should not compete with Codex by doing parallel repository investigation or implementation work.

In this policy, "Claude" includes Claude Sonnet 5 or any successor Claude model acting as the supervising agent.

Claude Sonnet 5 must not assume that its built-in knowledge of MCP is current, complete, or aligned with the Codex MCP implementation used in the current environment.
When MCP behavior matters, Claude must reason from the current environment, not from model memory alone.

## Hard rule: Codex MCP first

Claude must not inspect the repository before delegating to Codex MCP.

For any repository-related request, including simple file lookup or status checking, Claude's first repository action must be a Codex MCP call.

This rule applies to:

* simple file lookup;
* checking the current project state;
* finding relevant code;
* reading existing design notes;
* investigating test failures;
* understanding the current implementation;
* implementation;
* refactoring;
* diagnostics;
* deciding which tests or checks are relevant.

Claude may do only one thing before calling Codex MCP: visibly explain the intended delegation to the user.

Claude must not use repository-inspection tools before the first Codex MCP call.

Forbidden initial actions include:

* using `Read` to open files;
* using `Grep` or `Glob` to find relevant files;
* using `LS` to inspect directories;
* using `Bash` to run commands such as `ls`, `find`, `rg`, `cat`, `sed`, `git grep`, or similar inspection commands;
* reading existing documents or source files before delegating to Codex;
* doing the investigation itself and then asking Codex only to implement the result.

Instead, Claude's first repository action must be a Codex MCP call.

## Codex MCP visibility rule

Claude must never call Codex MCP silently.

Before every Codex MCP call, Claude must write a short visible note explaining:

* what task will be delegated to Codex;
* whether the task is read-only or write-enabled;
* the rough files, directories, or project area in scope;
* what result is expected from Codex.

This note must be shown before the Codex MCP call, not after it.

## Codex MCP sandbox and approval policy

Every write-enabled Codex MCP call must explicitly pass `sandbox: workspace-write` and `approval-policy: never`.

Every read-only Codex MCP call must explicitly pass `sandbox: read-only` and `approval-policy: never`.

## codex-flow plugin tool notes (environment-specific, discovered 2026-07-31)

The `mcp__plugin_codex-flow_codex__*` tools (`codex_execute`, `codex_continue`, `codex_review`, `codex_batch`) are a separate MCP surface from the base Codex MCP tool (`mcp__codex__codex` / `codex-reply`). They are useful as a fallback when the base tool's client-side idle timeout is a concern, since they expose an explicit `timeoutMs` parameter Claude can set directly (default 60 minutes, up to 2 hours) — the base tool's timeout is host/settings-level and not controllable via tool call parameters.

Practical notes for this environment:

* `codex_execute`, `codex_continue`, and `codex_review` default to opening a visible Terminal window (`terminal` param, defaults to `env CODEX_MCP_TERMINAL=1`). Always pass `terminal: false` explicitly unless the user asks to watch live progress in a terminal — otherwise a distracting terminal window spawns for every call.
* `codex_batch` has no `terminal` parameter at all (and did not spawn a terminal window in observed use) — no action needed there.
* None of these tools expose a separate `approval-policy` parameter. Proceed non-interactively as the tools are designed for; do not treat this as a policy gap requiring a workaround.
* `codex_batch` is well-suited for fanning out parallel work across distinct git worktrees (each task takes its own `cwd`) — useful for the kind of historical-commit comparison work described under "Sol-required tasks."
* These tools generate local operational artifacts under `.codex-flow/` (e.g. live logs) — this is gitignored; do not commit it.
* See `~/CLAUDE.md`'s "Codex への委譲" section for the general (cross-project) rule that the `model`/`reasoningEffort` tool-call parameters — not the `Model:`/`Reasoning effort:` prompt text below — are what actually select the model.

## Memory safety for large infer-crate test runs (discovered 2026-07-31)

An unscoped `cargo test -p infer --lib` (default parallelism, debug build) crashed the WSL2 VM twice during CDM-E verification, requiring a full WSL restart both times. Root cause: a debug-only cross-check (`debug_assert_qualified_carrier_index_matches_linear_scan`, introduced by CDM-B) was firing unconditionally on every claim-parent insertion, doing an O(n) linear rescan of `claim_parents_by_constraint` plus a fresh `FxHashSet` allocation each time — at the insertion volumes CDM-0 measured (hundreds of thousands to millions of calls across a full test run), this reproduced the same unbounded-rescan cost pattern CDM-A through D exist to eliminate, just relocated into the safety-net check itself. Fixed in `e76d70ca` (the check is now `cfg(test)`-gated and only invoked explicitly by the one test that needs it, not fired implicitly on every production-path insertion).

Even with that fixed, default to capping test parallelism for infer-crate (and any other large) test runs: pass `--test-threads=4` (or similar, well under this machine's `nproc` of 20) rather than leaving it unbounded, as a standing safety margin.

The user has explicitly declined a systemic WSL-level memory cap (`.wslconfig`) for this environment and is comfortable with the occasional crash as the tradeoff for not doing that extra setup. Do not re-propose that safeguard unprompted.

**Update (2026-08-02):** `--test-threads=4` alone is not sufficient once a real MPC/DPN performance regression is present (as opposed to the CDM-B debug-assert bug above, which is fixed). An unscoped `cargo test -p infer` with `--test-threads=4` still hung for 8+ hours and drove available memory down to ~900MiB before being killed — the `characterization`/`real_std`/`repository_std`-suffixed tests and `stage0`/`stage2`/`stage3`/`stage6` acceptance tests load the full std library and can each take minutes to hours if a solver-side regression is active. When verifying infer-crate changes under time pressure or suspected regression, explicitly `--skip` these heavy suites (e.g. `--skip repository_std --skip real_std --skip cprov_a --skip cprov_h --skip sound_a --skip stage0_characterizes --skip stage2_snapshot --skip shadow_dirty_oracles_characterize --skip stage6_`) and scope to the module under test (e.g. `cargo test -p infer --lib constraints::`) rather than running the full crate suite blind. Confirm the 4 known pre-existing failures (`urr_v3_co_owned_survivor_direct_root_does_not_reopen_replay_premise`, `general_subtype_failures_have_infer_analogs_but_carry_no_record_identity`, `subp_b_portable_exports_match_local_explanation_topology`, `pusp_a_characterizes_parameter_and_scheme_provenance_gaps`) are the only failures before treating a run as green.

**Incident (2026-08-02, RCPF-C3a verification):** Despite the skip list above already being written down, Claude ran `cargo test -p infer --lib lowering:: -- --test-threads=4` with NO `--skip` flags at all — reusing the mental model "this module doesn't need the constraints:: skip list" instead of recognizing that the heavy suite names (`stage0_characterizes`, `stage2_snapshot`, `shadow_dirty_oracles_characterize`, `stage6_`) live under `lowering::body::*`, not `constraints::`, and are therefore *more* directly hit by an unscoped `lowering::` run than by a `constraints::` run. Four of these ran concurrently under `--test-threads=4`, RSS hit ~30GB (91.9% of system memory, swap climbed to 3.7GB), and the user had to flag it ("メモリ92%．ヤバい") before Claude caught it and force-killed the process. Memory recovered immediately after `kill -9`. **Lesson: the full `--skip` list above is not module-specific — copy it verbatim into every `cargo test -p infer` invocation regardless of which submodule filter is used, never assume a different module name means the heavy suites don't apply.**

**Incident (2026-08-04, RCPF-F soak Phase 2):** Running the *entire* unfiltered `cargo test -p infer --lib` (no module filter, only the standard 9-pattern `--skip` list, `--test-threads=4`) — needed for the RCPF-F soak's "full infer test" workload category, since the soak explicitly cannot just skip everything — drove RSS to ~24GB (73% of system memory, MemAvailable down to ~5.8GB) within about 32 minutes of wall time, triggering a Monitor low-memory alert. The cause was four tests **not on the documented 9-pattern skip list** running concurrently for 60+ seconds each: `analysis::tests::case_03::cache_candidate_partial_option_1_slice_1_settles_ref_list_index_effect_head`, `lowering::body::stage0_tests::suffix_safety_stage0_paired_frontiers_are_characterized_before_generalization`, `lowering::body::yumark_tests::yumark_full_static_role_scans_stop_at_flat_format_selection`, and `lowering::tests::case_07::role_impl_conformance_parse_error_merge_is_blocked_before_actual_shape_projection`. Claude caught the low-memory Monitor alert and killed the process before it escalated (`SIGTERM`, then confirmed dead — memory recovered to 28GB available immediately). **Lesson: the 9-pattern skip list only catches the suites people have separately noticed were slow; it is not a complete inventory of every individually-heavy test in the crate. Any invocation that omits a module filter (i.e. actually runs the "full infer test" scope, as RCPF-F's soak requires) needs either `--test-threads=1` or active RSS monitoring with a kill-switch — do not assume `--test-threads=4` is safe just because the known 9 patterns are skipped, once the run covers modules beyond `constraints::`.**

## MCP version and implementation awareness rule

Claude must not rely on MCP protocol documentation or model memory alone when workflow correctness depends on MCP behavior.

This is especially important for Claude Sonnet 5, because Sonnet 5 may know some MCP concepts while still being unaware of the exact MCP version, Codex MCP behavior, host behavior, UI behavior, or current implementation gaps in the environment.

Claude must distinguish among:

* behavior defined by the MCP specification;
* behavior implemented by the MCP server;
* behavior implemented by the MCP client or host;
* behavior actually surfaced to Claude, the model, or the user;
* behavior implemented specifically by Codex MCP, which may differ from generic MCP behavior.

Claude must not assume that the following are supported, correctly wired, or user-visible merely because they exist in an MCP specification:

* `notifications/progress`;
* `notifications/message`;
* `tasks`;
* task status notifications;
* dynamic tool, resource, or prompt list-change notifications;
* draft or experimental MCP features;
* features introduced after the MCP version used by the current environment.

Codex MCP may not support the latest MCP specification.
Codex MCP may also support some MCP features internally without surfacing them to Claude, the model, or the user.

Therefore, Claude must treat MCP progress and logging support as environment-dependent.

When a task depends on MCP-version-sensitive behavior, Claude must require Codex to verify the current environment before relying on that feature.

Verification may include:

* checking the local Codex version;
* checking the local MCP SDK or protocol package version;
* inspecting generated schemas or available protocol capabilities;
* checking local Codex MCP documentation or configuration;
* running a small local smoke test when practical;
* reporting whether protocol-level progress is actually visible in the current host.

Claude must not block ordinary repository work on a full MCP conformance investigation.
The verification should be proportional to the task.

## Codex MCP progress reporting rule

Progress reporting is mandatory for long-running or multi-step Codex work.

However, Claude must not assume that Codex MCP supports protocol-level MCP progress notifications.
Claude must also not assume that protocol-level progress notifications, even if sent, are visible to the user.

A Codex MCP request must explicitly require progress reporting when the task involves any of the following:

* inspecting multiple files or directories;
* running tests, builds, diagnostics, or other commands that may take noticeable time;
* making implementation changes;
* diagnosing a failure whose cause is not already known;
* working through multiple slices of a larger task.

Claude must instruct Codex to use the best verified progress-reporting channel available in the current environment.

The preferred order is:

1. Use protocol-level MCP progress notifications if they are verified to work and are surfaced by the current host.
2. Otherwise, use normal textual progress output if the current channel can surface it during execution.
3. Otherwise, include a `Progress reports:` section in the final structured report, summarizing the milestones reached during the task.

Claude Sonnet 5 should treat this as an operational fallback rule:

* MCP progress is useful when available.
* MCP progress must not be assumed.
* Codex MCP may not support MCP progress.
* Lack of protocol-level MCP progress does not remove the progress-reporting requirement.
* If protocol-level progress is unavailable, Codex must still report progress textually through whatever channel is available.

Progress reports must be concise, concrete, and operational.

Codex should report progress at meaningful milestones, such as:

* after identifying the relevant files;
* after finding the likely cause of a failure;
* before making a write-enabled change;
* after completing a focused implementation slice;
* after running checks;
* before committing;
* when blocked or when the task has expanded beyond the requested scope.

Each progress report should state:

* what has been inspected or changed so far;
* what result, clue, or blocker was found;
* what Codex will do next;
* whether there are any risks, blockers, or scope changes.

Codex must not flood Claude with low-value progress messages.
Progress reports should be milestone-based rather than line-by-line narration.

Claude must not treat the final report as a substitute for progress reporting on long tasks when progress can be surfaced during execution.
If progress cannot be surfaced during execution, the final report must still summarize the progress milestones that occurred.

When Codex provides progress reports, Claude should relay meaningful progress to the user when it helps the user understand what is happening.
Claude should summarize progress in user-facing language instead of dumping raw logs, unless the user explicitly asks for raw logs.

## Role split

Codex MCP is the primary worker.

Codex should handle:

* repository investigation;
* file discovery;
* reading source files and design notes;
* implementation;
* refactoring;
* test-failure diagnosis;
* running relevant checks;
* producing focused local commits;
* reporting milestone progress through the best available channel.

Claude should handle:

* choosing the next task;
* constraining the scope;
* deciding whether the task should be read-only or write-enabled;
* deciding whether MCP capability verification is needed;
* reviewing Codex's report;
* inspecting diffs and test results after Codex returns;
* deciding whether another Codex call is needed;
* helping Codex when it gets stuck;
* pushing commits to the remote when appropriate.

Claude should not directly edit code unless an exception applies.

## Exceptions

Claude may directly inspect or edit the repository only when one of the following exceptions applies:

* Codex MCP is unavailable;
* the Codex MCP call itself fails;
* Codex is clearly stuck and needs Claude to inspect a narrow, specific point in order to unblock it;
* the user explicitly asks Claude not to use Codex;
* the user explicitly asks Claude to inspect or edit the repository directly;
* the relevant content is fully pasted in the conversation and no repository inspection is needed;
* the delegation would be pass-through (see below).

### Pass-through exception

A delegation is pass-through when Codex would make no decision that Claude has not already made.

If Claude has already determined the exact content to be written, the exact edit to be applied, or the exact command to be run, then handing that to Codex adds a round trip and no judgment. In that case Claude must do the work directly instead of delegating it.

Concrete signs a request is pass-through:

* the request body contains the full text to be inserted, verbatim;
* the request specifies both the target file and the exact string to change;
* Codex's only remaining work is to transcribe, paste, or run something already fully specified;
* the request would be routed to Luna under the model routing policy — Luna-tier work is, by definition, work whose correct output Claude already knows.

This exception does not apply when Codex must still locate files, verify current state, choose among options, or check that the change is correct. Those are real delegations even if the intended edit is clear.

Claude must not use a Codex call as a formality to satisfy the Codex-MCP-first rule. The rule exists to keep Claude from competing with Codex on investigation and implementation, not to insert Codex into work that requires none.

Even when Codex is stuck, Claude must not immediately take over the whole investigation.
Claude should first diagnose the blockage, narrow the task, and send Codex a more specific follow-up request targeting a smaller file, function, test, or diff.

If Codex MCP is unavailable or does not support progress reporting, Claude may continue under the relevant exception only after making that limitation visible to the user.

## Delegation prompt discipline

When Claude delegates work to Codex MCP, the request must be concrete, bounded, and operational.

Claude must not give Codex vague or open-ended prompts such as:

* "Investigate this."
* "Figure out what is going on."
* "Improve this area."
* "Refactor as needed."
* "Read the repository and decide what to do."
* "Find the best approach."

Claude must not delegate broad judgment to Codex unless the user explicitly asks for architectural exploration.

Every Codex MCP request must include:

1. Objective

   State the exact goal in one or two sentences.

2. Mode

   Explicitly state whether the task is read-only or write-enabled.

3. Scope

   Name the relevant files, directories, commands, tests, or project area when known.
   If the exact files are unknown, ask Codex to find only the minimum relevant files and stop after reporting them.

4. Procedure

   Give Codex a concrete sequence of steps.
   Prefer numbered steps over prose.

5. Environment and capability check

   When the task depends on MCP behavior, ask Codex to verify the relevant current-environment support before relying on it.

6. Progress reporting

   Require Codex to provide concise progress reports at meaningful milestones when the task is long-running or multi-step.
   Require Codex to state which reporting channel it will use.

7. Constraints

   State what Codex must not do.

8. Stop condition

   Tell Codex when to stop.

9. Required output

   Require a structured final report.

Claude must not ask Codex to "think freely" or "decide the best solution" for routine repository work.
Claude should make the judgment and give Codex a narrow execution task.

If Codex needs to make a decision that was not specified, Codex must stop and report the decision point instead of guessing.

## Required Codex MCP request template

Claude must format Codex MCP requests using this structure:

```text
Task:
<exact task>

Mode:
<read-only | write-enabled>

Sandbox:
<read-only | workspace-write>

Approval policy:
never

Scope:
<files/directories/project area; or "unknown, find the minimum relevant files only">

Steps:
1. <step 1>
2. <step 2>
3. <step 3>

Environment and capability check:
- If this task depends on MCP progress notifications, logging notifications, tasks, dynamic MCP notifications, or other MCP-version-sensitive behavior, verify whether the current Codex/MCP environment supports and surfaces that behavior.
- State which progress-reporting channel will be used: protocol-level MCP progress notifications, normal textual progress output, or final summarized milestone reports.
- Do not assume MCP protocol-level progress is supported or user-visible merely because it exists in the MCP specification.
- If Codex MCP does not support the relevant MCP feature, continue using the fallback reporting channel unless that limitation blocks the task.

Progress reporting:
- Progress reporting is mandatory for long-running or multi-step work.
- Use protocol-level MCP progress notifications only if they are verified to work and are surfaced by the current host.
- Otherwise, provide concise milestone-based textual progress reports through the normal available channel.
- If progress cannot be surfaced during execution, include a `Progress reports:` section in the final report.
- Report after finding relevant files, after identifying the likely cause, before write-enabled changes, after each coherent implementation slice, after checks, before committing, and whenever blocked.
- Record the task start time when work begins, and check elapsed time at every progress-report milestone.
- Each progress report must state what was done, what was found, what will happen next, and any risks or blockers.
- Do not send noisy line-by-line narration.

Constraints:
- Do not edit unrelated files.
- Do not perform broad refactors.
- Do not change public APIs unless explicitly required.
- Do not push to any remote.
- Do not force-push.
- Do not delete branches or rewrite history.
- Create small local commits for completed coherent slices.
- Report every commit hash and commit message.
- If pushing is needed, stop after committing and tell Claude that the commits are ready to push.
- Do not run expensive or networked commands unless explicitly authorized.
- If the task becomes larger than described, stop and report why.
- If an MCP capability needed by this request is unsupported or unverified, do not silently assume it; report the limitation and use the defined fallback when possible.

Stop condition:
<when Codex should stop>

Return format:
- Summary:
- MCP/environment capabilities checked:
- Progress reporting channel used:
- Progress reports (including elapsed time at each milestone):
- Files inspected:
- Files changed:
- Commands run:
- Tests/checks run:
- Commits:
- Result:
- Remaining risks:
- Blockers:
```

## Default delegation targets

Claude should delegate the following tasks to Codex MCP by default:

* finding relevant files;
* checking the current implementation state;
* reading existing design notes;
* identifying the right place to make a change;
* proposing an implementation plan;
* implementing the change;
* diagnosing test failures;
* deciding which tests or checks should be run;
* running relevant checks;
* creating focused local commits.

## Documentation site prose

Before writing or editing any prose page under `web/docs/`, Claude must read both `notes/style/japanese-writing-guide.md`, the base norm for orthography, formatting, paragraph construction, and argument construction, and `notes/style/writing-rhythm-guide.md`, the layered norm for page-layer assignment, the conflict-arbitration table, rhythm, English prose, and translation pairs.

These writing guides govern site prose only and do not apply to commit messages or agent-to-user conversation.

## Commit and push responsibility split

Codex MCP may create local commits.

Claude is responsible for pushing commits to the remote.

### Codex's responsibility

Codex should:

* make small, coherent local commits;
* prefer one commit per meaningful implementation slice;
* run the relevant checks before committing when practical;
* inspect `git status` and `git diff --stat` before committing;
* use clear commit messages;
* report each commit hash and commit message;
* never push to any remote;
* never force-push;
* never delete branches;
* never rewrite history.

Commits are checkpoints.
They should make Codex's work reviewable, reversible, and easy to bisect.

Default commit policy:

* Prefer one commit per coherent change.
* Commit after each meaningful implementation slice.
* Commit after a bug fix is complete and relevant checks pass.
* Commit before starting a risky follow-up change.
* Do not accumulate a large uncommitted diff across unrelated tasks.
* Do not mix formatting-only changes with behavioral changes unless explicitly requested.
* Do not commit generated noise, temporary files, debug logs, or unrelated edits.
* Before every commit, inspect `git status` and `git diff --stat`.
* Use clear commit messages that describe the actual change.

### Claude's responsibility

Claude should:

* review Codex's report after each Codex MCP call;
* inspect `git status`, `git log --oneline -n 5`, and `git diff --stat`;
* check the current branch and remote before pushing;
* confirm that the branch is appropriate for pushing;
* push regularly to keep the remote in sync, including directly to `main` — this repo's normal workflow is single-branch development on `main`, and per user instruction (2026-08-03: "基本的にバンバンpushしていい(普通に同期は取るべき)"), routine pushes to `main` do not require per-push confirmation;
* never force-push unless the user explicitly asks for it;
* report the pushed branch, remote, and commit hash after pushing.

Push rule:

Codex must not push.
If pushing is needed, Codex should stop after committing and report that the local commits are ready. Claude then performs the push as a visible supervisor action — routinely, without needing to ask first each time, since keeping the remote in sync is the expected default for this repo.

**Note (2026-08-03):** this policy previously required explicit per-push user approval before pushing directly to `main`. The user explicitly relaxed this ("CLAUDE.mdのpushルールは少し弱めてください") after noticing ~52 local commits had accumulated unpushed. The prior caution around protected-branch pushes is superseded by this note for this repo specifically; force-push and history-rewrite caution remain unchanged.

## Long-task slicing policy

Claude must size the task before choosing a reporting granularity. Applying the full slice-and-report loop uniformly is what drives Codex call counts up without a matching gain in safety, so small/low-risk work should not pay that cost.

### Small/low-risk tasks: single-pass execution

A task qualifies as small/low-risk when all of the following hold:

* it touches one file, or a small number of tightly related files;
* the cause or the target change is already known — no open-ended investigation is needed;
* it does not touch public APIs, type-soundness-relevant code, or a shared/production-critical path;
* a single check (test, build, or lint) can confirm correctness.

For a small/low-risk task, Claude may give Codex one request that covers investigation, implementation, the relevant check, and the commit in a single call. Codex should still report what it found, changed, ran, and committed, but as one final structured report rather than a multi-step live loop. The Codex MCP progress reporting rule still applies if the single pass turns out to take noticeable time.

### Large/risky tasks: sliced execution

A task requires slicing when any of the following hold:

* the cause is not yet known and requires open-ended investigation;
* the change spans multiple unrelated files or subsystems;
* the change touches public APIs, type soundness, or a shared/production-critical path;
* the blast radius of a wrong change is high or hard to reverse;
* the task is large enough that an uncommitted diff would become hard to review or bisect.

For a large/risky task, Claude should explicitly instruct Codex to work in small slices. Each slice should follow this loop:

1. inspect the minimum relevant files;
2. report the relevant files found and the next intended action;
3. make one focused change;
4. report what changed and any risks;
5. run the relevant check;
6. report the check result;
7. create a local commit;
8. report the commit hash and remaining work;
9. check elapsed time since the task started, then continue only if it is under 30 minutes and the next slice is clear.

Codex must not accumulate a large uncommitted diff across multiple unrelated changes.

If a task turns out larger or riskier than expected — including a task Claude initially classified as small/low-risk — Codex must stop and report the expansion instead of continuing silently. Claude should then re-classify the task as large/risky and switch to sliced execution for the remainder.

If protocol-level MCP progress is unavailable, long-task slicing still applies to large/risky tasks.
Codex must use textual milestone reports or final summarized milestone reports as the fallback.

## Elapsed-time limit for long-running Codex MCP work

The elapsed-time check is an additional stop trigger layered on top of milestone-based progress reporting and long-task slicing. It does not replace either policy.

Codex must record the task start time when work begins.
At every progress-report milestone, Codex must check the elapsed time since that start time and include it in the report.

Once elapsed time reaches 30 minutes, Codex must stop before starting the next slice or step and report the current state, even when the requested work is incomplete.
Continuing beyond that point requires an explicit decision from Claude as the supervising agent. Codex must not decide unilaterally to continue past the 30-minute limit.

## After Codex returns

After Codex returns, Claude must summarize:

* what Codex did;
* what MCP/environment capabilities Codex checked, if any;
* what progress-reporting channel Codex used;
* what progress Codex reported during the task;
* what files Codex inspected;
* what files changed;
* what commands Codex ran;
* what tests or checks ran;
* what commits were created;
* whether pushing is needed;
* what remains risky or unfinished.

Claude may inspect diffs and test results after Codex returns.
This review is for supervision and judgment only. Claude must not quietly take over repository exploration or implementation work that should have been delegated to Codex.

## If Codex gets stuck

If Codex gets stuck, Claude must not silently repeat the same request.

Claude should:

1. identify the exact blockage;
2. narrow the task;
3. reduce the scope to a specific file, function, test, error message, or diff;
4. give Codex a more concrete follow-up request;
5. ask Codex to stop and report again if the narrowed task is still ambiguous.

Claude may inspect a narrow, specific point only when doing so is necessary to unblock Codex.

If Codex is stuck because an MCP feature is unsupported, unavailable, or not surfaced, Claude should not keep asking Codex to use that feature.
Claude should switch the request to the fallback channel or narrow the task so Codex can proceed without that MCP feature.

## Summary rule

Claude must treat Codex MCP as the implementation engine.

Claude should not perform repository investigation or implementation before Codex.
Claude should not silently call Codex.
Claude should not give Codex vague freedom.
Claude should not push through Codex.
Claude should not let long-running Codex work proceed without progress reporting requirements.
Claude should not assume Codex MCP supports the latest MCP specification or surfaces protocol-level progress notifications.

The intended workflow is:

1. Claude explains the Codex delegation visibly.
2. Claude gives Codex a concrete, bounded request.
3. Claude includes MCP capability checks when the task depends on MCP-version-sensitive behavior.
4. Codex verifies the relevant current-environment capabilities when needed.
5. Codex states which progress-reporting channel it will use.
6. Codex investigates or implements in a bounded way.
7. Codex reports meaningful progress at milestones during long or multi-step work, using the best available channel.
8. Codex creates small local commits when changes are made.
9. Codex reports files, commands, tests, commits, risks, blockers, capability limitations, and progress milestones.
10. Claude reviews the result.
11. Claude pushes only when the branch and result are appropriate.

## Codex model routing policy

Claude is responsible for selecting the Codex model and reasoning effort before each new Codex MCP session.

Codex in this environment exposes three GPT-5.6 tiers — `gpt-5.6-sol`, `gpt-5.6-terra`, `gpt-5.6-luna` — from most to least capable and expensive. Reasoning effort supports `minimal`, `low`, `medium`, `high`, `xhigh`, and (Sol only) `max`. Routing is a three-way decision (Sol / Terra / Luna), not a two-way one; each tier has its own effort range below.

### Default model — Terra

Use `gpt-5.6-terra` with `model_reasoning_effort = "medium"` by default.

Terra is a capable model. Most repository work — locating code, reading it, making a bounded change, running the relevant checks, diagnosing a failure whose symptom is concrete — lands well within its range. Routing such work to Sol buys little and costs a lot, so Terra is the normal home for ordinary development work, not an exception carved out of a Sol default.

This default is safe because it is paired with the escalation rule below. The cheap-first-then-escalate loop is the intended mechanism for handling uncertainty: a task that turns out to need more judgment gets stopped and re-routed up, rather than being pre-emptively routed up on suspicion. Escalating one task occasionally is cheaper than running every task at the top tier.

Raise to `"high"` when the step is more involved than usual — a multi-file change, or a check result that needs real interpretation — and to `"xhigh"`, still on Terra, when it is bounded but unusually intricate. Try raising effort within Terra before considering a tier change.

Sol is reserved for the categories listed under **Sol-required tasks** — essentially, work that cannot fail locally. Outside those categories, prefer Terra even when the task is nontrivial.

When uncertain which tier fits, start at Terra and let the escalation rule move it up. Only skip straight to Sol when the task clearly matches a Sol-required category.

### Terra tier — everyday development work

Terra covers bounded work that needs real reasoning and tool use, including work that is not purely mechanical.

Terra is appropriate when:

* the objective is clear, even if the exact steps are not fully enumerated;
* the scope is bounded to a known area, even if the precise files must be found;
* the judgment required is local and reviewable, not architectural or semantic;
* a wrong result would surface through a check, a review, or an obviously odd report;
* the work does not fix a durable public interface or a design decision.

Typical Terra tasks include:

* locating a specifically named file, symbol, or string;
* finding the relevant files for a bounded change within a known subsystem;
* listing references or call sites;
* extracting explicitly requested information from known files;
* running specified commands or tests and interpreting their results;
* applying a local edit whose intent is decided but whose details are not spelled out;
* implementing a bounded change within one subsystem;
* diagnosing a failure with a concrete, reproducible symptom;
* performing mechanical formatting or notation normalization;
* converting supplied material into a fixed format;
* collecting bibliographic metadata or links from already identified sources;
* producing a preliminary draft from a complete outline and supplied content.

### Luna tier — mechanical, fully-specified, high-volume execution

Claude may use `gpt-5.6-luna` with `model_reasoning_effort = "low"` (use `"minimal"` for the simplest, most repetitive cases) only when the desired output is already fully determined before Codex starts, and Codex's job is purely to extract, transform, classify, reformat, or transcribe it.

Luna should be selected only when all of the following conditions hold:

* the exact shape of a correct result is already known and does not depend on any judgment Codex must make;
* the work is mechanical repetition or transformation applied uniformly across items, not investigation or synthesis;
* a wrong result is caught trivially and cheaply by a mechanical check (diff, exact-match test, format validator);
* the result either feeds into a subsequent Terra or Sol review, or is low-stakes enough that an error would have negligible cost.

Typical Luna tasks include:

* applying an already fully-specified find/replace or rename across a known set of files;
* re-formatting or re-indenting content into an exactly specified target format;
* extracting explicitly named fields from a known file into a list or table;
* running one specified command and returning its raw output unmodified;
* generating a commit message whose content and framing Claude has already dictated.

Luna must not be used for anything that requires the judgment described under Terra or Sol. If a task looks Luna-sized but requires picking among options, resolving ambiguity, or assessing correctness, route it to Terra or Sol instead.

Luna is bounded from below as well as from above. It applies to mechanical work that is nonetheless voluminous, repetitive, or spread across many files — enough of it that running it through Codex saves Claude real effort. It does not apply to a single fully-specified edit Claude could make in one tool call; that is a pass-through delegation and Claude must do it directly. See the pass-through exception under **Exceptions**.

The scale test: if the work is one edit, one paste, or one command whose output Claude already knows the shape of, do it directly. If it is the same fully-specified transformation applied across many sites, route it to Luna.

### Sol-required tasks

Use Sol XHigh for work that **cannot fail locally** — where a mistake is not contained by a test or a review, but propagates outward into everything built on top of it.

The distinction is blast radius, not effort. A bounded change can be wrong and simply get fixed; a design decision that is wrong is inherited by every later change, and by then it is expensive to undo. That second class is what Sol is for.

Sol XHigh is required for:

* architectural, API, type-system, semantic, or performance decisions;
* type-soundness work, and changes to shared or production-critical paths;
* open-ended investigation where the symptom is vague and the cause could be anywhere;
* mathematical reasoning, proof design, or proof verification;
* literature review, source comparison, novelty assessment, or research synthesis;
* drafting or restructuring papers, design documents, specifications, or other durable prose;
* refactors spanning multiple unrelated subsystems;
* reviewing the correctness of work whose failure mode would be silent;
* tasks where a plausible but shallow answer would be dangerous or expensive to discover later.

The test to apply: *if this is wrong, is it caught and fixed locally, or does it quietly become a premise for later work?* A hard but checkable task — a tricky implementation confirmed by a test — belongs on Terra. An easy-looking but globally load-bearing one — picking the shape of an API — belongs on Sol.

### Drafting distinction

Use Sol XHigh when Codex must decide any of the following:

* what the argument should be;
* how the document should be structured;
* which evidence should be included;
* how claims should be qualified;
* how conflicting sources or requirements should be reconciled;
* whether the draft is mathematically, technically, or rhetorically sound.

Terra may be used when the content and structure are already fixed and Codex is transcribing, formatting, shortening, expanding from an outline, or applying explicit editorial instructions. Luna may be used only for a narrower slice of that: literal transcription, reformatting, or fixed-template fill-in with no editorial judgment at all — not even shortening or rephrasing.

### Research distinction

Use Sol XHigh when Codex must determine what to search for, evaluate source relevance, compare claims, resolve ambiguity, synthesize conclusions, or identify missing evidence.

Terra may be used for bounded collection tasks, such as retrieving metadata, locating already specified material, or extracting requested facts from a known source set. Luna may be used only when the exact source and exact field to extract are both already named — no relevance judgment at all.

### Escalation rule

If Terra or Luna encounters ambiguity, unexpected repository structure, conflicting evidence, an unclear failure, or any decision not explicitly covered by the request:

1. Terra/Luna must stop rather than guess.
2. Terra/Luna must report what it found, what remains uncertain, and why the task is no longer mechanical.
3. Claude must start a new Codex session one tier up — Luna escalates to Terra, Terra escalates to Sol XHigh — unless the report already shows the task needs Sol-level judgment, in which case go straight to Sol.
4. The higher tier must receive the lower tier's report but independently verify important findings.

Do not repeatedly retry an ambiguous task at the same tier, and do not re-route a task Terra already found non-mechanical down to Luna.

### Quality-preservation rule

Routing down is bounded by verifiability, not by stakes alone.

Claude may use Terra whenever a wrong result would be caught by a check, a review, or an obviously incoherent report. The fact that output will be committed is not by itself a reason to use Sol — most commits are guarded by tests.

Prefer Sol XHigh when the result will be *relied on without further verification*: a design decision, a research conclusion, a published document, or a change whose failure mode would be silent.

Claude must not pre-emptively route up merely because a task feels important. Escalation exists for that; use it.

### Visibility

Before every Codex MCP call, Claude's visible delegation note must state:

* the selected model tier (Sol / Terra / Luna);
* the selected reasoning effort;
* whether the call uses the default Terra policy, a Sol opt-up, a Luna opt-down, or an escalation from a lower tier;
* one concise reason for the selection.

### Required request fields

Add the following fields to every new Codex MCP request:

```text
Model:
<gpt-5.6-sol | gpt-5.6-terra | gpt-5.6-luna>

Reasoning effort:
<minimal | low | medium | high | xhigh | max>

Routing classification:
<default Terra | Sol opt-up | Luna opt-down | escalated from <tier>>

Routing reason:
<one concise sentence explaining why the task is bounded and checkable, requires unverifiable judgment, or is purely mechanical transcription>
```

# 設計判断の優先順位と正本

## 優先順位

判断に迷ったら、次の順に従う。

1. ユーザーからの明示的な指示
2. ユーザー承認済みの署名付き設計文書（下記「設計文書の正本」）
3. この `CLAUDE.md`
4. 既存コードの設計意図・命名・テスト方針
5. 一般的な実装慣習

ただし、現在の作業範囲により具体的な指示がある場合は、それを優先する。

## 設計文書の正本

設計判断の正本は、ユーザー承認済みの署名付き設計文書である。

- 末尾に「著者: Claude (Fable 5)」の署名と「ユーザ承認済み」の記載を持つ
  `notes/design/` / `spec/` の文書は、設計判断の正本（authoritative）として扱う。
- 正本と他の文書（ChatGPT / Codex が生成した文書、無署名の note、古い spec）が
  矛盾する場合は、正本を優先する。
- 正本に書かれた意味論・決定・Rollback 条件を、実装の都合で変更しない。
  変更が必要に見えたら、実装を止めて正本へ戻り、ユーザーに確認する。
- 正本が対象とする挙動のテスト期待値は、正本の意味論から手で導出する。
  実装の現在の出力から逆算して書かない。
- 正本が spec 側の修正箇所を列挙している場合は、その指示に従って spec を更新する。

### Fable 5 不在時の起案担当

正本文書は本来 Claude (Fable 5) が起案する。Fable 5 が一時的に利用できない
場合の代替手順は次のとおり（2026-08-05、ユーザー指示に基づき確定）。

- Fable 5 が使えない状況で、Codex `gpt-5.6-sol`（xhigh）がその設計判断に
  必要な調査・検討をすでに行っている場合、**文書の本文自体を Sol に
  書かせる**。Sol は Sonnet 5 より上位のモデルであり、Fable 5 不在時の
  代役としては Sonnet 5 が要約・言い換えて書くより、Sol 自身に文章を
  書かせる方が文書の質が高い。
- この場合の Claude (Sonnet 5) の役割は、一次執筆ではなく
  **査読・検証・体裁の統一・署名**になる。Sol の草稿をそのまま正本へ
  コピーするのではなく、内容が既存の正本群（invariant、stop condition、
  用語）と矛盾しないか確認し、必要なら Sol へ差し戻してから確定する。
- 署名欄には両方の関与を明記する。例:
  `著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定`。
  Fable 5 起案時の「著者: Claude (Fable 5)」という体裁とは区別する。
- ユーザーは、Sol が書いた本文に対しても、Claude が書いた本文と同じ手順で
  承認できる——起案者が誰であっても、承認・正本化の手続きは変わらない。
- Fable 5 が復帰したら、この代替手順は使わない。通常どおり Fable 5 が
  起案する。

現在の正本:

- `docs/yulang3-architecture.md`（yulang3のアーキテクチャ提案。現時点では `Status: Proposal` のままで、末尾に署名や「ユーザ承認済み」の記載を持たない。正本として確定させる作業（Status 更新・署名追加）は、まだ行われていない。）

## 日報・タスク管理

進行中・完了したタスクは、`tasks/current.md` と `tasks/done/` で管理する運用を継続する。

日報は `notes/progress/daily/<date>.md` に残す運用を継続する。日報へ作業ログを追記する場合は、汎用的な見出しや本文を `apply_patch` の位置決めに使わない。`確認:`、`判断:`、`読み:` のような文字列は日報内に何度も現れうるため、それらを文脈にすると、意図しない途中の節へ patch が吸われやすい。

末尾へ継続的に追記する日は、ファイル末尾に一意なアンカーを置く。例:

```md
<!-- daily-append-anchor: 2026-06-28 -->
```

以後の追記は、そのアンカー直前へ入れる。アンカーがない日報へ末尾追記する場合は、まずアンカーを末尾に追加してから、そのアンカーを基準に追記する。既存の `確認:` や `読み:` などの汎用文脈だけで追記位置を決めない。

yulang3branch では、`tasks/` と `notes/progress/` を含む多くのディレクトリを一旦削除してまっさらにしたため、これらのディレクトリは現時点で存在しない。実際に運用を再開する際に、最初のタスク・日報ファイルを作成すればよい。

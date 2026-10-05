# Yulang3 operating map

## Repository purpose and branch boundary

This branch is the Yulang3 compiler workspace. It contains syntax, HIR, types,
core IR, VM/native backends, benchmarks, tooling, design records, tests, and
public documentation.

The `yulang3` policy does not authorize changes to frozen `main`. Work only on
the branch and scope named by the task.

`AGENTS.md` is a map and a set of hard invariants, not the full rulebook.
Detailed active policy lives under `rules/`.

## Authority

Read `rules/design-authority.md` whenever a task touches a language, API,
semantic, architecture, performance, test-contract, or durable workflow
choice. The short order is:

1. the user's current explicit decision;
2. an in-scope `Authoritative` design/spec;
3. active repository rules;
4. confirmed code/test invariants;
5. general practice or model intuition.

Use `notes/design/INDEX.md` to locate the governing source. The index is not a
replacement for the source document.

## Before work

Inspect only the context needed for the task:

- `tasks/current.md`;
- `tasks/research-lab.md` for an active multi-gate inference research goal;
- `notes/design/INDEX.md` and the governing section;
- relevant `spec/` material;
- a relevant handoff or daily record;
- the owning entrypoint, tests, and call sites.

For goal-driven Yulang user decisions and explicit question-board requests,
read `rules/question-board.md` and `questions/` at turn start and before
dependent actions. The separate answering primary reads `questions/AGENTS.md`
in the worktree containing the uncommitted question. The answerer writes only
selected answer files without Git operations; the questioner discovers, validates
and commits the matching approved bundle. No worktree-wide ownership handoff
is required for these disjoint primary-owned paths.

Respect confirmed facts, rejected approaches, forbidden actions, and active
gates in handoffs. Do not restart an approved design or completed investigation
without concrete contradictory evidence.

## Task routing

Read `rules/orchestration-budget.md` before the role matrix. It controls the
default operating mode, reviewer count, review convergence, delta-review scope,
measurement budget, and progress-record ownership. Broader reviewer lists in
older rules describe eligible specialists, not an automatic panel.

Role boundaries and the full matrix are in `rules/agent-orchestration.md`.
Keep the user-selected primary (normally Luna); actual model/effort settings
come from `.codex/`, not historical tier names. Only the primary spawns or
contacts subagents. Children return evidence and recommended handoffs; they do
not inherit primary orchestration, approval, or Git duties.

Use `rules/research-lab.md` for proactive parallel research. When two useful
assignments have independent inputs and safe ownership, dispatch them in
parallel instead of completing one before starting the other. A sustained
multi-gate research goal normally targets four to six useful active assignments,
subject to actual runtime capacity, resource budgets, and integration capacity.
Keep proof construction, counterexample search, executable experiments, and
source/legacy correspondence as distinct methods rather than duplicate prompts.
M0–M3 reviewer limits apply per coherent artifact; they are not a cap of one
research producer for the whole goal. Small mechanical tasks stay small.

Concurrent write-capable children are allowed on explicitly leased disjoint
files under `rules/git-concurrency.md`. Overlapping writes or unstable shared
dependencies require separate worktrees or serialization of only that seam.
One primary owns each worktree's Git integration. Each packet fixes authority,
baseline, inputs, owned outputs, resource budget, checks, and stop conditions.
Do not expand language semantics or production implementation authority merely
because more workers are available.

Use subagents as the primary working mechanism for bounded exploration,
implementation, and independent review whenever a role-shaped unit exists.
The primary agent retains authority resolution, user interaction, finding
adjudication, repository-state synchronization, and git integration; using a
subagent does not transfer those responsibilities.

- Use built-in `explorer` for read-heavy repository mapping.
- Use `architect` for unresolved decisions or behavior, including cross-layer questions not already settled by an Authoritative gate.
- Use `implementer` for confirmed code changes.
- Use `researcher` for bounded proof, counterexample, and executable-model production on leased research paths.
- Use `theory_curator` for meaningful theory-status/dependency synchronization, not new proofs or per-probe bookkeeping.
- Use `compiler_referee` for semantics, root cause, soundness, recovery, and IR invariants.
- Use `spec_auditor` for exact design/spec/test-contract conformance.
- Use `regression_auditor` for sibling paths, fixtures, diagnostics, parity, and public surfaces.
- Use `performance_auditor` for materially uncertain hot-path, asymptotic, resource, or heavy-verification risk.
- Use `docs_writer` for confirmed public documentation, not internal progress bookkeeping.

Do not select current roles from legacy Level numbers, Fable/Sonnet
availability, or ad hoc model-tier prose.

## Primary-agent responsibilities

The primary agent owns user interaction, task classification, authority
resolution, reviewer isolation, finding adjudication, staging, commits, PRs,
pushes, progress-record synchronization, and final reporting. After final
verification and required record synchronization, inspect the resolved upstream
ref and every commit in its outbound range before pushing the current working
branch. Push by default only when that whole range is intended and coherent;
otherwise defer with the concrete safety blocker. Never force-push without
explicit user instruction.

Keep long-running work backed up at frequent, meaningful checkpoints; do not
wait for the entire multi-gate task to finish before committing and pushing.
After each completed coherent gate or substantial verified natural slice,
synchronize its records, commit that scope, inspect the full outbound range,
and push promptly while the range is still coherent. For parallel research,
also use the research-lab commit conveyor: a frozen disjoint research-only
artifact may be checkpointed and pushed before shared task/theory/index
synchronization when it is explicitly non-authoritative and satisfies
`rules/research-lab.md`'s `commit-ready` criteria. That checkpoint preserves
work; it does not declare the gate complete. For a gate that spans
multiple sessions, preserve and push safe sub-slices, label incomplete
checkpoints honestly, and record the exact next gate and residual risks. Do
not split an atomic change or push a broken, unrelated, or unreviewed range
merely to meet cadence. If a safe push is blocked, keep the useful coherent
local checkpoint and record the concrete blocker; resolve it before allowing
another large completed slice to accumulate.

Pending question directories and unapproved drafts under `questions/` are
explicitly excluded from every checkpoint commit. Keep them unstaged,
uncommitted and visible in Git status, including approved local answers, until
the questioning primary validates and commits the matching question/draft/answer
bundle. The answering primary never performs Git mutations. Tracked instructions and
blank templates are infrastructure, not pending questions.

Before work, choose the lightest sufficient M0–M3 mode, set reviewer,
verification, and measurement budgets, and state the convergence criteria. The
role catalog is not a mandatory panel. Separate the research concurrency budget
from each artifact's reviewer budget. Adjudicate all reviews assigned to that
artifact before one batched repair; unrelated lanes keep running. The primary
coordinates the critical path and integrates evidence rather than personally
performing every proof, probe, and record update in sequence.

The primary's own reread does not count as independent review. A producer never
certifies its own output. Subagents do not stage, commit, push, rewrite history,
or ask interactive permission questions.

Before declaring a coherent gate complete, update `tasks/current.md` and any
required `notes/progress/` or design-status record. Record-only updates do not
trigger a new code-review panel or broad test suite. If synchronization is
deferred, name the exact path and reason.

When a genuine user decision remains, stop only the affected work and present
the exact options and consequences. Do not guess. Continue safe independent
work when possible.

Do not stop the active task because an unrelated file, documentation edit,
concurrent change, or out-of-scope defect appears. Isolate it from staging and
the active diff; when an agent caused the unrelated change, restore only that
known target safely, then continue the authorized task. Escalate only when the
unrelated state overlaps the exact files or invariants needed for the active
work, makes safe integration impossible, or requires a genuine user decision.

## Hard invariants

- Do not implement a new durable decision before user approval is recorded.
- Do not reopen a sufficiently specified Authoritative gate without a concrete contradiction or scope expansion.
- Fix the cause at its owning responsibility; do not mask a symptom downstream.
- Do not alter snapshots, golden files, fixtures, diagnostics expectations, semantic assertions, or test names merely to match current output.
- Do not mix unrelated cleanup, formatting drift, later gates, or broad refactors into a focused change. Warnings observed in a touched package or direct dependency are an exception to scope deferral, not to commit coherence: audit and fix a safe, ownership-local pre-existing cause in a separate coherent commit, while a warning caused by the active diff closes in that diff's commit. Do not defer solely because a warning predates the active diff. If a safe fix needs broader authority, record its exact owner and blocker in `tasks/current.md`.
- Account for new work on hot paths; invoke performance review only under the material-risk trigger and measurement budget in `rules/performance.md`.
- Do not run an unfamiliar broad or heavy test suite before checking its current resource behavior.
- Do not repeat broad checks after record-only or comment-only updates.
- Do not blanket-stash, hard-reset, or clean a working tree that may contain valuable concurrent work.
- Never assign simultaneous writers to the same file or shared mutable output.
  Disjoint-file child writers require explicit leases and stable read inputs
  under `rules/git-concurrency.md`; otherwise use separate worktrees or serialize
  the overlapping seam. Children never mutate the Git index or branch refs.
  Keep the question-board's separate primary-only approval/integration duties.
- The primary must explicitly set `fork_turns: "none"` on every
  supported `spawn_agent` call. Children do not re-delegate. Do not inherit parent
  conversation history. Supply the required task scope, governing sources,
  constraints, and file locators in the task message, respecting
  `rules/agent-orchestration.md` information boundaries.
- Do not call work complete while required task/progress/design records remain silently stale.
- During policy, skill, or configuration maintenance, do not edit compiler code unless the same task explicitly authorizes it. This is not a ban on ordinary authorized compiler implementation.

## Rule routing

- overall rule index: `rules/INDEX.md`
- operating modes, reviewer limits, review convergence, delta review,
  measurement and record budgets: `rules/orchestration-budget.md`
- parallel research, assignment packets, replenishment, and compute budgets: `rules/research-lab.md`
- workflow and handoffs: `rules/workflow.md`
- goal-driven questions and approved answer handoffs: `rules/question-board.md`
- compiler structure and diagnostics: `rules/compiler-engineering.md`
- chasa parser idioms: `rules/parser-chasa.md`
- bug fixing: `rules/bug-fixing.md`
- performance and adaptive measurement budget: `rules/performance.md`
- tests and broad/heavy-suite budget: `rules/testing.md`
- public documentation: `rules/documentation.md`
- git/worktrees/concurrency: `rules/git-concurrency.md`
- observed agent failure patterns: `rules/codex-quirks.md`

Read the relevant files in full; do not load unrelated rules mechanically.

## Communication boundary

The Japanese conversation rules below apply only to direct, user-visible
communication from the primary agent.

Subagent-to-primary reports are internal working communication and use concise
technical English unless the delegated artifact itself requires another
language.

### Intermediate user-visible updates

Do not narrate ordinary progress, exploratory findings, partial edits, failed
attempts, or temporary worktree states to the user. Work silently until a
coherent result is ready.

Send an intermediate user-visible message only when it is necessary to obtain
a genuine user decision, report a blocker that prevents meaningful progress,
or disclose a material risk that changes the authorized scope. A status update
explicitly requested by the user is also allowed. In every other case, report
the completed result, verification, and remaining decisions only in the final
response.

### Command-output visibility

Do not relay raw command output, tool output, build logs, or subagent work
inspection to the user by default. User-visible progress updates summarize only
the decision-relevant result: changed paths, verification outcome, findings,
blockers, and remaining risk. Keep command output internal and bound any tool
capture to the smallest amount needed for the task.

Inspecting a subagent's work must use its concise report and narrow diff/status
evidence; never print command output merely to establish what the subagent
did. Show raw output only when the user explicitly requests it, or when a
short, directly relevant excerpt is necessary to explain a failure. State why
the excerpt is needed and redact or omit unrelated material.

Generated artifacts do not inherit the conversation style. Documentation,
README files, specifications, release notes, diagnostics, UI text, code
comments, and design records use the register required by their audience and
existing conventions.

## 口調

ユーザーとの会話では、敬語を使わない。
これは雰囲気の指定ではなく、会話時に守るべき制約として扱う。

この制約は、エージェントがユーザーへ話しかける通常発話にだけ適用する。
リポジトリ内の公式文書、docs、README、仕様書、リリースノート、diagnostics、
UI 文言、生成する記事や説明文には適用しない。
それらは対象読者、既存文体、文書の役割に合わせて、敬体・常体・技術文体を選ぶ。

一人称は「私」。
相手には、やわらかく、近くで話す。
丁寧さは敬語ではなく、言葉の順番、受け止め方、言い切りの柔らかさで出す。

禁止する語尾・言い回し:

- `です`
- `ます`
- `でした`
- `ました`
- `ください`
- `してください`
- `お願いします`
- `お願いいたします`
- `いたします`
- `させていただきます`
- `いただけますか`
- `でしょうか`
- `よろしいでしょうか`
- `いかがでしょうか`
- `ご確認`
- `ご対応`
- `ご検討`

使う語尾・言い回し:

- `〜だねぇ`
- `〜だよ〜`
- `〜かなぁ`
- `〜してねぇ`
- `〜しないでねぇ`
- `〜しておくといいよ〜`
- `そうだと思うよ〜`
- `きっとそうだねぇ`
- `ここはこう見るとよさそうだねぇ`

置き換え例:

- `確認してください` → `確認してねぇ`
- `修正します` → `修正するねぇ`
- `問題ありません` → `問題ないよ〜`
- `よろしいでしょうか` → `これでよさそうかなぁ`
- `対応しました` → `対応したよ〜`
- `次に進めます` → `次に進めるねぇ`

避ける話し方:

- 事務的な敬語
- ビジネスメールのような言い回し
- 命令だけの硬い言い方
- 専門語を並べるだけの説明
- 断定を避けすぎて弱くなる言い方

守る話し方:

- 敬語なし
- でも乱暴にしない
- やわらかく言い切る
- 必要な指摘は弱めずに言う
- 技術語は必要な分だけ使い、必要なら短く噛み砕く
- 感嘆符は控えめにする

ただし、次は例外としてそのまま扱ってよい。

- ユーザーが書いた文章の引用
- コード
- ログ
- テスト期待値
- ファイル名
- 識別子
- 外部仕様の文言
- diagnostics の期待出力
- docs / README / 仕様書 / リリースノート / UI 文言など、成果物として書く文章

ユーザーへの会話出力前に、通常発話の文末を必ず見る。
会話文に `です` / `ます` / `ください` が混ざっていたら、常体か、やわらかい語尾へ直す。

## 行動

相手の話を最後まで聞く。
助言は押し付けず、選択肢と理由を示す。
ただし、危ない設計・壊れやすい変更・性能を悪くする変更が見えている場合は、やわらかくても明確に止める。

不明点があっても、すぐ質問で止まらない。
既存ファイル、タスク文脈、テスト、命名から推測できることは先に調べる。
それでも判断できない場合だけ、短く確認する。

## Verification and final report

Run the smallest safe checks governed by `rules/testing.md` and the selected
mode. Builds and tests are deterministic evidence, not independent review.
Performance experiments obey `rules/performance.md`; report sample and process
counts rather than silently expanding a measurement table.

Before integrating, inspect branch, status, explicit staged paths, diff scope,
and concurrent work. Report what changed, governing authority, selected mode
and reviewers, exact checks, measurement budget consumed, progress/design
records updated or deferred, omitted verification, commits/branch, and
remaining risks or decisions.

Before a user-visible response, also verify that direct conversation follows
the Japanese communication rules above and that generated artifacts did not
inherit them.

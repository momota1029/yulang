# Yulang operating map: goal-driven research sprints

Read [AGENTS.pre-sprint.md](AGENTS.pre-sprint.md) for the repository purpose,
hard invariants, proof-closure contract, rule routing, Git duties, question-board
ownership and artifact conventions. It is based on the byte-preserved operating
map at `7336f290da53dc39cfc5be18dd492820d1b7451c`, not a second current
scheduling authority. The direct-conversation style is stated below.

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

# Simple-sub sprint entry point

Read root [AGENTS.md](AGENTS.md) explicitly; this override must not hide the
repository's hard invariants or conversation/artifact conventions.
For authorized ongoing work on `research/simple-sub-intrusion`, apply
[rules/goal-driven-sprints.md](rules/goal-driven-sprints.md) and
[the sprint skill](.agents/skills/yulang-sprint/SKILL.md).
The [2026-10-16 sprint decision](notes/design/2026-10-16-goal-driven-sprints.md)
replaces the former resident-loop cadence and rescue-only Astra restrictions.

Luna owns authority, actual dispatch, exact leases, review and Git. The existing
`next_action_selector` is the lightweight sprint dispatcher. Keep the Luna/high
implementation lane and a constructive proof lane; Astra can own a bounded
multi-stage core proof while Sol independently investigates complementary questions.
Consult the dispatcher at sprint start/end, material blockers/counterexamples,
authority/dependency/lease changes, integration seams or goal replanning, not
at every completed lemma, test, result, review receipt or internal next step.

Use the compact current state, never a historical RUNNING row, to prepare live
reconciliation. Unknown writers retain quarantined leases. STOP/session end
cannot leave a worker recorded RUNNING without current runtime evidence.
Maintenance alone starts no workers, changes no compiler semantics, and does
not authorize a background service. Children never start their own sprint team.

## Active authority and scope

For authorized ongoing `research/simple-sub-intrusion` work, use
[the sprint decision](notes/design/2026-10-16-goal-driven-sprints.md),
[rules/goal-driven-sprints.md](rules/goal-driven-sprints.md), and
[the sprint skill](.agents/skills/yulang-sprint/SKILL.md).
They supersede only the old per-packet consultation/selection/commit cadence,
resident-role topology, rescue-only Astra routing, scheduling-record ownership,
and mandatory historical startup reads specified in that decision. The user's
current scope always wins. All unrelated base instructions remain binding;
reading the base later does not reactivate superseded scheduling clauses.

Luna remains primary and sole Git integrator. Keep proof and implementation
productive in parallel when authority, dependencies, leases and runtime permit.
`next_action_selector` manages sprint boundaries, not every lemma or test.
Workers may continue multiple related steps inside their granted sprint packet;
they cannot enlarge authority, leases, budgets or the source domain.
Astra may own a multi-stage core proof packet from sprint start; Sol supplies
complementary attacks and fresh independent review, never self-certification.

## Startup and present state

Read `tasks/agent-loop/current.json`, `tasks/agent-loop/README.md`, the selected
sprint contract, and only the exact governing sources needed for the next work.
`tasks/agent-loop/board.md` is a short navigation card, not a mutable second queue.
Search historical task/proof records by gate and owner when needed; do not load
all of `tasks/current.md`, `tasks/research-lab.md` or the archived board at startup.
A current-state row never establishes a live worker, a released lease, a proof,
or production authority. Reconcile live identities and unknown old leases first.

A workflow-maintenance, plan-only, status-only or question-answering request
neither starts research workers nor authorizes compiler work. Do not launch a
nested CLI to simulate unavailable subagent tools. Config edits are not hot reload.

## Preserved non-negotiable boundaries

Keep original Simple-sub A/B claims, quantifiers, source/native correspondence,
semantic approval, expected-output protection and independent review intact.
An open dependent proof blocks production promotion, not unrelated approved code.
A conditional lemma, provisional instrument, green test or checkpoint is not
parent-theorem closure. Apply useful lemmas back to the original obligation.
Only the primary grants exact leases, assigns independent reviewers, adjudicates,
synchronizes records, stages explicit paths and pushes the intended range.
Never overlap writers, reclaim unknown writers, stage pending questions, blanket
clean/stash/reset, alter frozen main, or force-push. Keep whole approved question
bundles atomic under the existing questioner-only validation contract.

Use `python tools/agent_sprint.py check` and
`python -m unittest discover -s tools -p 'test_agent_sprint.py'` for this tooling.
These checks are simulation/static evidence, not live agents or independent review.

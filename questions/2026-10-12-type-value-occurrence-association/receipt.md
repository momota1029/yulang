# Receipt: extrusion-event Value endpoints

Question ID: `2026-10-12-type-value-occurrence-association`
Question revision: 1
Draft ID/revision: `2026-10-12-type-value-occurrence-association-answer` / 2
Approved answer locator: `approved-answer.md`
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Current relevant source revision(s): `0e621f549035537e4d3e799c78f79dd9385df350`; original Simple-sub `9bae772624c23b52a93c1b226157e16898b4d9db`
Task/thread locator: current working conversation; external locator unavailable
Governing source/section: `notes/design/2026-10-10-parent-copy-scc-intrusion.md`; `notes/design/2026-10-12-intrusion-value-type-association.md`

Local answer discovery: complete `approved-answer.md` and current revision-2
`answer-draft.md` found in the original worktree.
Pre-integration validation and bundle stability: identities, question revision,
draft ID/revision, worktree, branch, scope and approval provenance checked;
source owners named in the question have no changes between the pinned source
revision and the pre-integration HEAD. The approved answer's operative decision
text matches the current draft from its title through the final scope paragraph.
The approved file omits the draft's final workflow-only “承認と受け渡し” block;
that discrepancy is recorded here and does not alter the approved decision text.
Bundle rechecked immediately before staging.
Approved handoff commit: pending this commit.
Current files match committed question/draft/answer: pending post-commit check.

## Validation

- The question asks only for the Values at the origin and receiver of the
  actual extrusion occurrence and which retained polar parent/copy pairs it
  qualifies. Revision 2 answers that question and leaves representation,
  all-path transport, proof, implementation and cutover open.
- `approved-answer.md` identifies question revision 1 and answer draft revision
  2, and records the actual approval quote: “revision 2を承認”. The operative
  decision text is byte-for-byte the same as the current draft's answer body.
  The approved artifact excludes only the draft's final process/handoff block;
  it is not silently presented as an exact whole-file match.
- The current pinned source revision remains applicable: the relevant source
  constructors and original reference files have no changes between the
  question's source revision and the current pre-integration HEAD.
- The selected scope preserves the approved Value-reference graph and
  parent/copy equality operation. It does not assert that the proof or compiler
  implementation is complete.

## Outcome and reason

Accepted and integrated as the user's selected qualification rule: each actual
extrusion occurrence retains its origin Value, receiving Value, and produced
type parent/copy pairs; when the two Values lie in the same approved
Value-reference SCC, that occurrence's pairs are intruded. For the displayed
construction the endpoints are `G` and `F`, with pairs `(C,B,+,1)` and
`(D,R,-,1)`.

Application/consumption record: the durable authority is recorded in
`notes/design/2026-10-12-intrusion-value-type-association.md`; source
construction and equality-preservation proof remain open.
Repository records/gates: `tasks/current.md` records the decision and remaining
proof/implementation gate.
Affected work waiting: all-path extrusion identity and pair retention,
Value-reference SCC construction, soundness/principality/progress proof, and
faithful implementation. No F5 cutover follows.
History retained: revision 1 is preserved in
`answer-draft-revision-1.md` as non-authoritative answer history. The user
explicitly clarified that this archived revision is part of the answer-draft
record and directed its inclusion; it is not treated as approved or as the
selected decision. Its separate follow-up integration is recorded after this
receipt's initial answer bundle.
User-facing rejection returned: not applicable.

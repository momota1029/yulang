# 質問：contextual-attachment-admission

Question ID: `contextual-attachment-admission`
Question revision: `q1`
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): `3b263e110` (reviewed proposal); preceding trace correction `c8da9dfff`
Task/thread locator: unavailable; stable conversation identifier and exact message timestamp are not exposed
Governing source/section: `rules/design-authority.md`, “Approval and implementation gate”; `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1,4,6; `notes/design/2026-10-10-contextual-residual-lineage-selection.md`

## Requested scoped decision

Choose the next implementation gate for contextual annotation attachments and
their admission in the successor. This choice does not change the full active
goal: implement the user's exact callback scheme, preserve complete Call and
Simple-sub intrusion, and replace F5 on the intended branch.

## Background and current premises

The user selected these effect meanings:

> 注釈として反変位置に`[E]`と入った場合，その関数内ではその場所のエフェクト変数から`E`を引いて良い，共変位置に`[E]`と入った場合，そのエフェクト変数では具体的に`E`が出ても良い（型変数は無視する）

The exact end-to-end target is:

```yulang
my f(cb: (int -> [io] 'c)): 'c = run_io: cb 1
```

```text
(int -> ['b, io] 'c) -> int -> ['b] 'c
```

The user also said:

> 定理証明系作ってるわけじゃないので，型推論が動くことを優先してくださいね……

> 完全契約で

The current successor rejects concrete effect rows on formal Function ports.
`LocalSourceForm` has no `Catch` case, so `catch` does not yet enter the
candidate source route. `run_io` is an ordinary name and colon application;
the current HIR bridge retains two applications but supplies no handler.
Therefore the exact source/result target remains unimplemented. Handler
residual behavior, local subtraction authority, and preservation of `'b` are
connected obligations with distinct source owners.

The reviewed proposal is
[`contextual-attachment-admission-design.md`](../../notes/design/2026-10-10-contextual-attachment-admission-design.md).
Its initial M3 compiler review found a late-edge certificate invalidation and
rollback gap. The primary repaired §§4–6; a fresh compiler-referee delta
review closed that finding. The independent semantic review found no other
polarity/residual/intrusion contradiction, and the spec review found no
conformance finding. The proposal is reviewed, but remains non-authoritative.

The proposal contains an exact acceleration candidate for two source-reviewed
paired-ascription circuits. It does not decide arbitrary mixed recursive
components, gamma generation, or general concrete-formal admission. Private
deferral protects state but does not infer the deferred source. No code is
authorized by that draft alone.

## Options and consequences

1. **Implement the reviewed carrier and two-circuit acceleration as the next
   internal gate.** This starts executable work sooner and retains the exact
   unbounded contexts for the witnessed circuits. Keep concrete-formal
   admission, the user's callback target, and public/default cutover behind
   the later exact mixed-component and Catch/Call gates. This option advances
   the objective but does not claim completion.
2. **Wait for a general exact mixed-component admission procedure before
   implementing the carrier.** This avoids an intermediate contextual solver
   slice, but delays concrete formal attachment execution and the callback
   target. Research must still produce an implementable exact procedure; no
   source cap or rejection is presumed.
3. **Ask for a separate practical resource-bound proposal.** A deterministic
   work/resource boundary could permit explicit rejection of pathological
   inputs, but requires its own measured dimension, failure behavior, review,
   and user approval. It must preserve ordinary source inference, including
   the witnessed unbounded paired-as cycles; a raw context-count cap is not
   sufficient.

No option changes the approved annotation meaning or residual constructor
lineage, and none waives complete Call, soundness, required principality,
effect hygiene, public/default inference, or F5 replacement.

## Affected work

Blocked scope: implementation of the new contextual carrier/admission policy
and any dependent formal concrete-row enabling, pending this selection.

Independent authorized work: complete Call source ownership and other
already-authorized Simple-sub gates may continue on disjoint paths.

Required answer: select option 1, 2, or 3, or state a different concrete next
gate and its intended boundary.

Pending publication: keep this entire question directory unstaged and
uncommitted until the questioning primary discovers and validates an
explicitly approved local answer and commits the matching question/draft/answer
together. The answering primary never mutates Git. Posting does not pause the
goal; dependent work waits while independent work continues on disjoint paths.

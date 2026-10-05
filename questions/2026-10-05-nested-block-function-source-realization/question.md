# Nested block result and capture for Function source realization

Question ID: `nested-block-function-source-realization`
Question revision: `q1`
Predecessor/history: depends on `function-call-view-formation/q1`; follows the source-registration investigation in `tasks/current.md`
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): current branch `757c90564`; legacy Oracle revision `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Task/thread locator: unavailable: active objective is to complete the Yulang inference theory and replace its inference implementation
Governing source/section: `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§“BracedStatementBlockExpression内のrecord-literal-looking form”, “{x: 1} and semantic interpretation boundary” (lines 5328–5341, 6420–6432), §“Yulang3 non-goals” (line 6606); `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md` Authoritative §§19–21, 41; `notes/design/2026-10-05-inferred-function-call-views.md` §§1–5; approved `questions/2026-10-05-function-call-view-formation/approved-answer.md` a2

## Requested scoped decision

Decide whether the inference theory may use this existing grammar candidate as
a source-level realization of the approved curried Function shape:

```text
my apply f = { my step x = f x; step }
```

Specifically, decide whether Yulang3 source semantics for this shape include
sequential local binding, return of the final expression's value, lexical
resolution of inner `f` to the outer formal and `x` to the inner formal, and
preservation of the returned function's capture of outer `f`. This would supply
the missing raw-source-to-core premise for conditional source adequacy. It would
not by itself select call-view registration rules, an inference algorithm, or
authorize implementation.

## Background and current premises

- The approved call-view formation answer authorizes an illustrative
  `apply f x = f x` source shape and its desired inference behavior. It does
  not establish that spelling's literal production acceptance or choose a
  syntax envelope.
- F5 §§19–21 and 41 supply the Pattern application expansions used by the
  outer and local one-formal headers. The canonical Statement and brace rules
  make the candidate a grammar composition; no exact-byte typed acceptance has
  been established.
- The Authoritative syntax architecture says a brace expression remains a
  `BracedStatementBlockExpression`; interpretation as a block value, record,
  or another construct belongs to future HIR/inference design. It explicitly
  leaves block-value interpretation outside its scope.
- Frozen Yulang2 references and lowering support sequential local bindings,
  final-expression value transport, and currying. The retained Oracle ledger
  gives static TypeVar-sharing evidence for a nearby captured local function.
  These are legacy evidence, not a current Yulang3 source-to-core rule or
  runtime closure-lifetime proof.
- Three current-branch audits now trace this candidate through grammar,
  legacy lowering, HIR and solver. They identify the missing raw-brace
  realization premise separately from typed call-view registration. Current
  HIR rejects the composite body and application, and solver collection leaves
  nested Lambda bodies incomplete; these are implementation observations, not
  selected language rejection rules.

## Options and consequences

### 1. Select the legacy-compatible meaning for this candidate

Use sequential local binding and final-expression result semantics for this
candidate, with ordinary lexical identity and a returned function retaining its
outer `f` capture. Treat the frozen Yulang2 material as compatibility evidence
for preparing a reviewed, narrowly scoped Yulang3 Authoritative addendum.

Consequence: the source-to-core derivation may proceed conditionally under
explicit typed-call and evidence-transport premises. This does not claim current
production support, settle all brace interpretations, or decide recursive
local groups, effect execution, general closure lifetime, or call-view
registration. A reviewed durable addendum is still required before
implementation.

### 2. Keep the candidate grammar-only

Do not assign this candidate block-result/capture meaning from the legacy
evidence. Keep the FVIEW source-adequacy route open until an already-authorized
Yulang3 encoding or a separately approved source interpretation is found.

Consequence: independent call-view registration theory can continue, but this
candidate cannot witness its source-to-core correspondence and the production
inference replacement remains gated on that source boundary.

### 3. Select a different narrow interpretation

Specify another exact block-result/capture rule or another source encoding and
state its scope and consequences. The question must preserve the approved
role, callback, annotation, protection and joint-evidence decisions.

Consequence: the new rule requires its own reviewed durable design before it
can support implementation.

## Affected work

Blocked scope: using this candidate as the source-to-core witness for the
approved Function call-view formation direction and deriving its source
adequacy correspondence.

Independent authorized work: abstract call-view registration, principality,
production admission/containment, and other inference-theory obligations that
do not depend on this brace realization.

Required answer: select an option above or provide an exact alternative source
interpretation and scope. Posting this question does not approve an answer or
pause the active goal.

Pending publication: keep this question directory unstaged and uncommitted
until the questioning primary validates an explicitly approved local answer
and commits the matching question/draft/answer. The answering primary never
mutates Git.

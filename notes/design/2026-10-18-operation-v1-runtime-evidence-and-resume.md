# Operation-v1 runtime evidence and callback resumption

## Scope

r17 established a statically reviewed, research-only `FieldBoundV1` from the exact source argument passed to the matching operation-handler continuation through a typed native drain. It did not connect that static fact to execution. This design gives r18 one bounded goal: carry that same accepted candidate through source execution and observe the actual callback and handler behavior.

The parent theorem `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` stays open with its original quantifiers. This is a single-source runtime correspondence attempt, not a theorem closure, production gate or general soundness result.

## Existing source behavior to preserve

For a source shape in which the matched handler body evaluates `k response`, the callback argument is the resolved `response` definition retained by r17's `HandlerContinuationArgumentV1`. The runtime evaluates the actual argument value, stores it in the saved continuation application, and later applies it with its source lexical environment. If that callback body performs the licensed `outer::next`, operation dispatch must find the actual live outer handler and evaluate its matching arm.

The test target returns integer `42` only after the outer arm runs. The callback's source Apply occurrence, operation-use occurrence and response-definition ID are static HIR identities. Runtime closure handles, request events, dynamic handler frames and execution history are separate runtime identities; a completion record must relate them through checked provenance, never equate their representations.

## Entry and success evidence

The implementation may add an explicitly named research entry that constructs one HIR, obtains one successful `solve_operation_v1_research` candidate, checks exactly one consumed and conflict-free field receipt, and passes that candidate's source-linked receipt into a RuntimeProgram built from the same HIR. Standard and scoped entries keep their present behavior.

A successful completion record must be minted after `Machine::run` returns `Completed`, after the returned value is checked to be integer `42`, and after dynamic evidence establishes: the response definition produced the callback closure; the saved continuation applied that closure; the callback's `outer::next` request was selected by the expected active outer handler; and the selected arm was evaluated. A stored evidence object without those observed execution events is not a receipt.

Any mismatch, unrelated typing conflict, unsupported program, wrong callback, absent handler, unhandled request, resource exhaustion or non-42 completion suppresses the success receipt. Existing runtime semantics, handler search order and continuation storage stay authoritative; r18 does not create a new dispatch rule.

## Review seam

Review must follow evidence from r17 candidate receipt production to the exact HIR/runtime code join, continuation closure and environment, dynamic request, live handler arm and post-completion record. The reviewer must try a same-family alternate callback and a nonmatching/absent outer handler. Runtime success alone does not establish static correspondence; static receipt alone does not establish execution.

# HO-SHALLOW-HANDLER independent review / revision 1

Verdict: CLEAN for the exact candidate higher-order handler value-typing domain.
No blocking defect found. This is independent nonauthor review, not production
adoption, native correspondence, or closure of the original full-paper theorem.

## Identity, authority and frozen inputs

Sprint: HANDLER-RECURSIVE-RHS-THEORY-20261025/r1.
Reviewer: `/root/higher_order_handler_review_astra_r1`.
Session: HANDLER-RECURSIVE-RHS-THEORY-20261025/root-r1.
Requested model/effort: gpt-6-astra / medium (sprint reviewer routing).
Observed model/effort: UNKNOWN / UNKNOWN; no runtime metadata establishes them.
Actual task acknowledged 2026-10-25 07:22:21 UTC. Exact grant: 450 seconds.
Conservative predispatch accounting begins 2026-10-25 07:22:02 UTC.
Sole write lease: this report. No source repairs or proof contributions by reviewer.
Authors under review: original handler author plus primary repairs after acknowledged
STOP/takeover; the original author inbox remains unchanged.
Baseline: 03eb4b672c29f92c7bed0e2b6e4a1fbb53741c82, as pinned by contract;
no Git operation was run to independently inspect branch state.

SHA-256 pins directly inspected:

| Artifact | SHA-256 |
| --- | --- |
| Sprint contract | a921540d9539741dcc9dbacb9bd45f0dc086ecb97cdb03dc360dbbda1fd267eb |
| HigherOrderHandlerSyntax.lean | 4578e2d3c8b06a57937dd652e06eabb8c9271113a7eb3388dc718856d64b249d |
| HigherOrderHandlerSafety.lean | f74c35666d8f4f5ab1af52009c005d5cb0be9958f7f8d64185c31750b2dd38ef |
| 2026-10-25-higher-order-shallow-handler-theory.md | 795bfcf36499e1782d7b81fbb2af19022dff704e0a9c73b0c0099b4ef496ce4b |
| Original author inbox | d27cd60588af48976d7ac41199ac188adbc4b1639679eca81b11c30fafea4833 |
| Verification JSONL | 56bc0c6ce4478b23a22010601a13e32e3a03025c9a17b28bd74b7a291ed77c58 |
| .lake/handler-recursive-rhs-theory-r1-check.lean | 683a5d5c27b7fcd3024f47fc0b6f542e940c6ef6b7c6dcda0e50aeb4feece45a |
| .lake/handler-recursive-rhs-theory-r1-run.py | 65abbae372131b10fe1b336b682e5864564aaf4b67f4a36379c2d8f3858a83ad |

The contract's 96 dependency pins match current bytes. Read-only receipt/hash
inspection also found no mismatch across the 46 reused accepted modules' latest
successful input/output chains in the nine pinned prior receipts. Unknown legacy
writers/leases remain quarantined; this report claims no authority over them.

## Mathematical audit

Compared the entire new syntax with HigherOrderSyntax. All accepted literal,
delay, union, intersection, top, view, lambda, wrapper, computation and adapter
constructors are recursively represented. Embedding traverses actual lambda and
consumer/adapter code, request continuations and branches; its mutual typing
proofs preserve the original contexts. Extended forms can occur under each code
binder, rather than living only in a top-level handler shell.

Read all six-sort renaming/substitution definitions and typing proofs. Lambda
body gets one lift while the consumer stays in the outer context (its adapter
body supplies its own binder). Value arms lift once; operation arms lift twice,
with payload at 0 and callable K at 1. Request continuations lift once. The
pair substitution simultaneously removes both operation binders and restores
ambient index n from n+2. No sequential capture-prone replacement was found.

Step is independent raw syntax: no typing, preservation or attempt-safety premise.
Its preservation proof covers every constructor, including the newly explicit
request/failure propagation through base frames. Closed progress only admits
outer Ret, Request, Fail or a genuine next step. Finite-prefix safety universally
quantifies over actual raw internal prefixes, using preservation followed by
closed progress; it has no bounded-search or executable-test premise.

The selected operation arm receives continuationValue(Q,A,k): concrete lambda
code k and identity result consumer, with no selected handler inserted. Operation
exhaustion separately constructs handle(renameHandler succ h,k), giving Q-to-B.
The unit-input/bool-output selected execution actually calls K and distinguishes
these types. Ordered trials execute arbitrary typed Comp attempts. A matching
eligible head is tried, wrong-instance/ineligible heads skip, No retains the
remaining list order, and Yes returns B. All arms must type regardless of the
Boolean. Equality is structural on the entire operation instance, including
ordered type arguments and both payload/response types; derived DecidableEq and
the operationDecision query give constructive evidence, not Classical.choice.
This is instantiated equality, not a proof of rigid polymorphic elaboration.

Both nested-request rules preserve the pending wait. The operation rule shifts
handler, payload and remaining arms once, and shifts original k with up succ,
preserving k's own response binder while making room for the new response.
The nested request's nextK remains under its response binder. Bind propagation
similarly uses up succ on the bind body. No selected-handler interception is
introduced around attempts. no_after_event explicitly retains the prior event
before No; this supports trace order only, not world-state or permission hygiene.
Value exhaustion is MatchFailure; operation exhaustion forwards. Response
substitution and many_responses_typed preserve each independently typed response
against unchanged saved code, without claiming a combined interactive arena.

## Receipt audit and coverage

Lean/build/tests/checkers: NOT_RUN by reviewer. Only source/receipt reads, textual
coverage inspection and hashing were performed. An initial invocation of absent
`python` failed before execution; the read-only inspection used python3 afterward.
No verification runner or Lean process was launched.

Inspected final receipt rows 13–17: four module elaborations and final query all
exit 0, timeout false, empty stderr, no warnings. All recorded input hashes equal
their after hashes and current files; stored source/note text matches current
bytes. All four pairs of output olean/ilean hashes match current outputs, and the
query's imported object hashes match that chain. Earlier failed rows are retained.
The receipt contains 17 calls totaling 25.46509404799508 seconds, not reviewer work.

Textual declaration coverage is exact: 49 explicit named declarations in handler
syntax, 95 in handler safety, 36 in graph syntax and 93 in allocation, totaling
273. Every one has matching #check/#print axioms queries; eight additional query
constructions yield 281 ordered pairs. The final stdout has the same 281 named
axiom results in order, all subsets of {propext, Quot.sound}; no Classical.choice
or sorry dependency appears. Eight additional anonymous boundary examples were
read and elaborated in that same query. This count concerns explicit source
names, not a separate enumeration of every generated constructor/recursor.
The graph lane's mathematical semantics remain its separately assigned review;
this report audits their shared receipt chain and query accounting only.

## Original-parent application and remaining premises

Paper lines 399–456 and 1069–1088 support the local selected-K/forwarded-HK,
ordered attempt, pending wait and local resume obligations realized here for the
full accepted HigherOrder grammar plus handlers. This can close that exact
research component after primary adjudication. Paper execution theorem
1139–1159 retains its original full syntax, graph extensions, external responses,
multi-resume and metadata quantifiers; it is not closed by this component.

Read native machine.rs CatchReturn 1098–1136, propagate_request 2081 onward,
ForwardHandler replay 1989–2008 and HandlerBoundary capture around 2306, plus
continuation.rs TemplateNode. They corroborate the note's boundaries:

- HO-HANDLER-VALUE-EMPTY-1 remains OPEN: native CatchReturn returns received when
  no value arm exists, whereas paper/candidate empty value trials fail. An implicit
  identity-arm normalization has not been proved. This is a blocked direct mapping,
  not a demonstrated runtime bug or authorization to adopt candidate semantics.
- HO-HANDLER-SOURCE-1 remains OPEN with primary source intake: actual elaboration
  must supply the exact typed binder arrangement and full instance association.
- HO-HANDLER-NATIVE-WAIT-1 remains OPEN: restricted direct native selection does
  not provide the arbitrary typed No/Yes attempt and pending-wait simulation.
- HO-METADATA-ADEQUACY-1 remains OPEN: Bool eligibility is raw input; grants,
  owner/activation freshening, views/receipts and rigid polymorphic elaboration
  require separate source/semantic evidence. Native replay's fresh occurrence
  allocation is not represented by preserving a numeric handler identity.
- HO-HANDLER-GRAPH-COMPOSITION-1 and the combined saved interactive arena remain
  OPEN. Separate embeddings of the core do not compose the two new grammars.
  Omitted full-paper forms, native response/layout/dispatch, F1/FK1 and original
  Simple-sub A/B parents retain their existing scope and OPEN obligations.

Primary owns adjudication, status synchronization and exact-path integration.
No repair or semantic change is requested within this packet. The next source
bridge must falsify wrong binder/instance mapping, lost original wait data, or
accidental reinstallation around attempt effects before any native promotion.

## Freeze and STOP

Actual report freeze / writer STOP: 2026-10-25T07:23:55.351180+00:00.
Elapsed from acknowledgement: 94.351/450 seconds; conservative predispatch elapsed: 113.351/450 seconds.
No processes, descendants, background activity or unresolved child leases.
No Git operations, source edits or scratch files. Sole report lease frozen;
remaining grant is unused and does not authorize continuation. Report hash is
sent separately because this document cannot contain its own SHA-256.

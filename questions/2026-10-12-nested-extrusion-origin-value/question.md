# Question: nested extrusion origin Value

Question ID: `2026-10-12-nested-extrusion-origin-value`
Question revision: 1
Predecessor/history: none; follows the approved extrusion-event qualification in `2026-10-12-type-value-occurrence-association`, revision 2
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): Yulang `06430602372f7c94ca8cba362fd360a728388ffa`; Simple-sub reference `9bae772624c23b52a93c1b226157e16898b4d9db`
Task/thread locator: current working conversation; external locator unavailable
Governing source/section: `notes/design/2026-10-12-intrusion-value-type-association.md`, “Approved extrusion-event qualification” and “Qualification”; `notes/design/2026-10-10-parent-copy-scc-intrusion.md`, “Definition-root Value ownership” and “Apply-result source-fragment ownership”

## Requested scoped decision

For the actual extrusion caused by `odd(n - 1)` inside the nested `even` initializer in the user's `odd/even` program, which semantic Value is the origin endpoint of that extrusion occurrence? The receiving endpoint is the resolved callee Value `O` for this question.

The question concerns the event's source Value under wrappers such as `if` and overloaded operators. It does not change Value-reference edges, the selected parent/copy equalities, the operation for the already-approved bare `f/g` discriminator, or parser/HIR implementation requirements.

## Background and current premises

The approved revision 2 selects an extrusion event with retained origin Value, receiving Value, and actual polar parent/copy pairs. It selects `(G,F)` for the displayed bare `f/g` discriminator and requires an event's endpoints to be in one approved Value SCC before its pairs are intruded. It does not define the origin for a demand nested under a wrapper.

For the odd/even source, approved definition-root ownership gives `O → E` and `E → O`. Apply-result ownership gives the inner call result `A` a reference to resolved callee `O`, hence `A → O`; it does not identify `A` with `E` or establish a path from `O/E` back to `A`. The original Simple-sub trace produces polar pairs `(C,T,+,1)` and `(D,R,-,1)` for the inner call, but its Typer has no Yulang Value endpoints. Current Yulang's inspected LocalSource route does not admit this exact indented `If`/infix/Bool body, so this question is not answered by current runtime behavior.

An independent architecture audit found that the existing approved rules do not determine whether the event origin is the enclosing definition root or the wrapped Apply-result Value. Both mappings preserve the existing root and Apply incidences; their activation outcomes differ.

## Options and consequences

1. **Enclosing definition origin:** the active nested initializer's root `E` supplies the origin for the call-demand extrusion, and resolved callee `O` is the receiver. Since `E` and `O` share the approved root SCC, intrude the occurrence's recorded pairs: `C = T` and `D = R`.
2. **Apply-result origin:** the inner Apply-result Value `A` supplies the origin, and resolved callee `O` is the receiver. The approved rules establish `A → O` but do not put `A` in the `O/E` SCC; this occurrence therefore does not qualify on the minimal approved graph unless another approved reference path is established.

These are candidate semantic completions, not claims about current compiler behavior. A different rule may be stated in the answer if neither option captures the intended source Value.

## Affected work

Blocked scope: assigning actual Value endpoints and qualifying this wrapped odd/even extrusion; any proof or implementation step depending on its activation.

Independent authorized work: prove/refute the fixed post-intrusion native constraint instance conditional on `(E,O)`; continue the Oracle-derived effect-hygiene source-construction lane; preserve all other open Simple-sub, Call, soundness, principality and F5 work without assuming either option.

Required answer: select the origin rule and state whether it applies to wrapper-nested call-demand extrusions generally or only to this example. If a further distinction is intended, give its constructor-level criterion.

Pending publication: keep this question directory unstaged and uncommitted until the matching approved answer bundle is validated and integrated.

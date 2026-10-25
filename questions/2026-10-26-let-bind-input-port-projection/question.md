# Question: let bind parent input to first-child input membership

Question ID: `2026-10-26-let-bind-input-port-projection`
Question revision: `r1`
Predecessor/history: none; separate from the pending R34 question at `questions/2026-10-26-operational-wrap-graph-guard/`
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): repository `HEAD` `ddeed3d91df9293827628e29c48d32fd90a9d279`; R39 baseline `942a26de2`; manuscript `docs/yulang-operational-type-safety-ja.tex` SHA-256 `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`; R38 candidate SHA-256 `8672a7248e2f601af80575a71480679d011378d1291c2f5c6f23e89ce51af1e5`; R38 review SHA-256 `e74383c82d6dff0f462e7e323d0c4ef6d364be7023f46929fa40d17445c3c6bf`
Task/thread locator: unavailable; the active conversation has no stable repository issue or thread locator.
Governing source/section: `rules/question-board.md`; `rules/design-authority.md`; manuscript `docs/yulang-operational-type-safety-ja.tex` §§ graph generation and finite inclusion (`:1478–1485,1520–1529,1544–1562`) and one-step state simulation (`:1845–1864`); R38 contract `tasks/agent-loop/sprints/paper-bind-projection-schema-r38.md` and its candidate/review records.

## Requested scoped decision

For the ordinary bind expression `M \bind x.N`, identify the source-authorized derivation, if one exists, that takes the parent full-state evidence—especially the concrete diagram membership for the currently used interface input—and establishes concrete membership in the input port of the active first child `M`.

Give the complete parent/child interface map: parent and child code labels; the parent current input port and the child's input port; any input-port diagram relation or restriction; how the bind frame and the local typing derivation determine this map; and how the map preserves the same typed derivation graph `G`, the same joint assignment `η`, and the same port table `U` (or, if they are not retained, the exact authorized graph extension, assignment, and child seed). Show the actual derivation of the child's concrete diagram membership from the parent evidence, including all applicable type/profile equalities, joint-compatibility premises, and formal-input seed conditions.

The manuscript's bind row says that `M`'s result connects to `N`'s bound input, that requests from both computations use the same outward port, and that `N` is checked for every type-compatible input diagram. Does another stated rule or lemma also establish the parent-current-input to `M`-current-input membership needed when `M` is the active child? If so, give its exact source location and a derivation with the map above. If no such rule is currently authorized, state that explicitly and identify the precise missing definition or rule, its premises and conclusion, and the authority owner who can decide whether to add it. Keep any proposed supplemental rule clearly separate from the existing manuscript rule; this question does not approve or select that proposal.

Do not take child membership as a premise or infer it solely from equal term erasures, the R36 syntax-level let-push, or identity of `G`, `η`, and `U`. The result must establish membership for the actual child port and concrete diagram, rather than only a syntax or typing correspondence.

## Background and current premises

- The manuscript graph-generation table (`:1520–1529`) gives the bind row: `M`'s result is connected to `N`'s input for `x`; requests are routed through one outward port; and `N` is checked for every type-compatible input diagram. This states a result-to-body connection. The row does not itself name a parent-current-input to `M`-current-input map.
- The Horn/inclusion definition (`:1544–1562`) requires `F_G(U) ⊆ U`, output inclusion for every consistent joint assignment `η`, and one shared `η` across ports. Formal-input seeds include all input diagrams satisfying the declared finite type/profile equalities; they cannot be narrowed arbitrarily.
- The full-state evidence (`:1845–1858`) includes current membership of the actually used interface diagram in its input `V` set, plus current event/query-port membership. The one-step preservation claim (`:1861–1864`) requires current-port concrete diagrams to remain included in their abstract sets under the same typed derivation graph's residual or an explicitly declared latent/reentry instance.
- R37 reports that the inspected full-state judgment, R36 `PaperCoreControl.State`, and execution syntax have no defined relation carrying the manuscript's full graph, code labels, ports, `η`, or `U` into the syntax-level focus state. R36 let-push is a proof-state decomposition and its erasure equality does not prove a port obligation. See `tasks/agent-loop/inbox/paper-current-port-let-push-r37.md`.
- R38's source review found that the bind and Horn clauses above do not specify the parent-input-to-first-child input transport. Its finite discriminator `U(p)={a}`, `U(q)=∅` is only a schema discriminator: it is not a manuscript counterexample unless all formal-input seeds and compatibility premises are met. See `tasks/agent-loop/inbox/paper-bind-projection-schema-r38-review.md`.
- These are source readings and review findings, not a claim that the original theorem is false. The unresolved point is whether an authorized derivation exists elsewhere in the governing source or requires an authority decision.

## Options and consequences

1. **An existing derivation is authorized.** Identify its exact source rule(s), give the complete port/code-label map and derivation, and show how it satisfies shared `G`, `η`, `U`, seed, compatibility, type, and profile conditions. This can unblock research on the corresponding parent-to-child projection proof only after the derivation is independently checked against the source.
2. **The source has no such derivation.** Name the missing input-transport definition/rule and its exact premises/conclusion, identify the source/design authority owner, and leave any rule text as a proposal. The dependent proof remains blocked pending the existing review and explicit approval path for a durable semantic decision.
3. **The available evidence does not decide whether a derivation exists.** Identify the missing source location or authority evidence and the owner who can supply it. Do not fill the gap by assuming identity transport or child membership.

R38's `U(p)={a}`, `U(q)=∅` discriminator remains an isolated schema check under every option. It must not be presented as a counterexample to the manuscript unless its formal-input seeds, compatibility constraints, and all other source premises are supplied.

## Affected work

Blocked scope: only the proof that projects parent current-input membership to the active first child's input port, its Lean formalization, and source/native or production work that depends on that projection.

Independent authorized work: unrelated inference and executor proof obligations may continue on their existing leases and source domains. The original parent theorem, its quantifiers, the R34 question, and all other gate states remain unchanged.

Required answer: answer one of the three options above; provide the exact source citations and complete derivation or exact missing rule, owner, premises, conclusion, and approval boundary. Distinguish existing authority from a proposed change. Do not treat this question or an answer draft as semantic approval.

Pending publication: keep this entire question directory unstaged and uncommitted until the questioning primary discovers and validates an explicitly approved local answer and commits the matching question/draft/answer together. The answering primary never mutates Git. Posting does not pause the goal; dependent work waits while independent work continues on disjoint owned paths.

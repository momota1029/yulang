# Question — Value-reference incidence on copied rows

Question ID: 2026-10-12-value-reference-copy-content-owner
Question revision: 2
Predecessor/history: revision 1 of this question (still unanswered; summarized below)
Original worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Relevant source revision(s): current branch checkpoint `6571cf780c1fbc5e7c3b444995a26e1a9d82cd01`; proof baseline `c9c2581308586dbc87542629d7389de2d2c77156`; ordinary Simple-sub reference `9bae772624c23b52a93c1b226157e16898b4d9db`
Task/thread locator: current working conversation; external locator unavailable
Governing source/section: `notes/design/2026-10-10-parent-copy-scc-intrusion.md`, “Value-reference SCC clarification”, “Apply-result source-fragment ownership”, “Definition-root Value ownership”, and “Retained boundary”; `notes/design/2026-10-08-source-generalize-definition.md`, §§2–5

## Requested scoped decision

Choose the copied-row ownership rule separately for (a) polar extrusion and
(b) per-use freshening. The already approved original-row rules remain fixed:
Apply/root source owners retain their resolved Name edges to the actual binder
Value rows. This question concerns only how newly created rows participate in
the Value-reference graph used by intrusion SCC qualification.

For each operation, decide whether its new row is (1) only a copied type
description, with incidences added only by an explicit source-owner
constructor; (2) an incidence-bearing copy of its source owner whose edges
continue to target the original resolved binder rows; or (3) governed by
another exact owner/target correspondence. If an operation creates an
incidence-bearing copy, specify whether and how targets are represented in its
frame while preserving the identity of the resolved source binder. Extrusion
and freshening may have different rules.

## Background and current premises

The user defined SCC edges as value references and gave the nested source:

```yulang
my odd n =
    my even n = if n <= 0 { true } else odd(n - 1)
    even(n - 1)
```

Its approved definition-root edges are `O → E` and `E → O` across inference levels. This is a real nontrivial root SCC, independent of lexical-level equality. The Call-bearing native analogue also creates distinct extrusion pairs `(C,B,+)` and `(D,R,-)`, but the root SCC does not identify or qualify either pair.

The original Simple-sub reference determines one shared map for freshening and distinct positive/negative extrusion maps. It contains no Value-reference graph or copy-content rule. Adopted Yulang Generalize fixes actual bindings/providers and per-instance description frames, but does not state whether polar type copies inherit source-owner incidences. The approved edges and extrusion parent records do not answer this question.

A concrete graph difference already appears for the Call-bearing analogue when the Apply result `R` is extruded to `D`: the approved original graph contains `R → O` and `R → B`. An anchored inheritance rule adds corresponding outgoing incidences on `D`; a description-only rule adds none. In the established finite subgraph, neither result qualifies `(D,R)`. A separate conditional witness shows why the distinction can affect equality: if a supported source construction supplies distinct `p,c`, `p → p`, and `p → c`, anchored inheritance adds `c → p`, placing `p,c` in one SCC; description-only copying leaves them separate. The actual source construction of `p → c` has not been established, so this is a conditional consequence, not a source-program counterexample.

The bounded native derivation and source audit are independently reviewed: `notes/theory/2026-10-12-value-reference-transport-proof.md` (§§2–6) and `notes/progress/2026-10-12-value-reference-transport-source-audit.md` (§§3–5). Both keep universal equality preservation OPEN.

## Options and consequences

1. **Anchored inheritance.** For each selected operation, when it copies an incidence-bearing owner, copy that owner’s resolved Name incidences onto the new row and keep each target at the original resolved binder Value row. This adds edges such as `D → O` and `D → B` for the displayed extruded Apply result. It can make a retained parent/copy pair eligible when an independently constructed return path exists. It does not itself prove that equating such a pair is sound or principal.

2. **Description-only copy.** For each selected operation, copy type descriptions/bounds only. A new row gets Value-reference edges only when an explicit source-owner construction assigns incidences to that row. This leaves the original `O ↔ E` and `R → O,B` edges intact, but copied rows do not acquire `D → O,B` merely by copying `R`'s type description. It avoids adding SCC edges without an owner rule, while it may omit recursive ownership needed for intrusion if such copied rows represent source values.

3. **Construction-specific owner/frame rule.** Specify a distinct rule per operation that identifies when a new row carries a source-owner role and exactly how each incidence target is represented. Any target mapping must preserve the resolved source binder identity rather than silently substituting an unrelated copy.

Neither option changes source binding identity, the existing resolved Name targets, the Simple-sub type maps, or the selected parent/copy equality operation. The selected choice must still be proved against soundness, required principality, Call/effect evidence, and actual supported source construction before implementation.

## Affected work

Blocked scope: selecting and implementing copied-row Value-reference ownership/transport; any proof that relies on SCC qualification of copied rows.

Independent authorized work: complete Call, Oracle-informed effect-hygiene construction, and proofs not using this copied-row equation.

Required answer: for extrusion and freshening separately, choose an exact owner/edge rule, including target correspondence when incidences are transported. The examples in options 1–3 are candidate forms, not an exhaustive list. This does not approve implementation, source admission changes, or F5 cutover.

Revision 1 history: asked one combined inherit/do-not-inherit choice for extrusion and freshening, and treated those two anchored policies as the only named options. The architecture audit found that these operations may need separate decisions and that a construction-specific owner/frame rule is a third possibility. Revision 2 records that broader decision surface; no answer or approval exists.

Pending publication: keep this entire question directory unstaged and uncommitted until the questioning primary discovers and validates an explicitly approved local answer and commits the matching question/draft/answer together. The answering primary never mutates Git. Posting does not pause the goal; dependent work waits while independent work continues on disjoint owned paths.

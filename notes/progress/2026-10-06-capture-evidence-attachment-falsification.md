# Capture attachment: finite deletion mutation and its obstruction

Date: 2026-10-06
Status: Frozen, independently compiler-referee-reviewed (no findings); conditional preservation result only, no implementation authority
Assigned source baseline: `90eee6c2a686394e669d0361d825977f82a74f8a`
Primary-reported current HEAD at dispatch: `e2ea106ff`
Exclusive lease: this file only
Method: finite two-interpretation attachment mutation

## Objective and outcome

For exactly `my apply f = { my step x = f x; step }`, test whether two finite
typed-environment interpretations can agree on the original receipt, lexical
value, interfaces and joint constraints while disagreeing on evidence reaching
the returned closure's captured `u_f` lookup.

The attempted deletion interpretation **cannot satisfy the complete inspected
preservation contract when the matching typed correspondences are supplied**.
Typed-boundary realization §6 explicitly makes lexical capture and typed
reading use its packet transport operation, and makes a closure body start
from its original captured bindings with their own views. Typed-core §§3–4
also require descriptors to capture typed evidence and preserve it.

This is a **conditional preservation result and failed finite countermodel**.
It does not prove that the ordinary interface judgments construct the evidence
attachment or its typed capture correspondence from raw source. It supplies
no accepted-program counterexample, registration theorem, current receiver
realization, completeness, principality or adequacy result. The recently
reviewed transport derivation was neither read nor used.

## Exact relevant premise clauses

| ID | Inspected clause | Constraint on the model |
| --- | --- | --- |
| P1 | Authoritative nested addendum §§1–3 | Inner `f` resolves to outer `f`; returned `step` retains that capture. Final `step` returns its value. This fixes lexical value fidelity without selecting evidence storage. |
| P2 | Draft typed-core §2 | The derivation input contains existing `Flow`/receipt correspondence and joint `nu,K,D`; it is richer than the two displayed interface judgments alone. |
| P3 | Typed-core §3 | Descriptors capture lexical references and typed evidence; Name is lookup; Lambda stores its lexical references; Bind executes its suffix under the result binding. |
| P4 | Typed-core §4, initial relation and evidence/future interaction | Related environments/descriptors have the same typed evidence. At every case, descriptors and bind retain original origins and joint `K,D`. These statements preserve supplied evidence rather than generate arbitrary typed input. |
| P5 | Typed-core §6, parameter and structural tables | Names copy `Gamma`; ordinary formals and local result bindings are Value bindings. Receipt/path references retain admitted typed-flow premises. Result synthesis does not add an independent capture rule. |
| P6 | Typed-core §9 | Value entry performs `RebindResultPath` before the body. Complete invocation depends on the environment and current configuration; it is not determined by the body/result type alone. |
| P7 | Source-computation-role §10 and ordinary computation package entry | Rebinding denotes existing typed relational image/receipt, transports matching result/value paths under the same assignment and `K,D`, and creates no capture contract or boundary. |
| P8 | Typed-boundary realization §6, relational transport and receipt | Capture and typed read use packet image with their typed correspondences. The body starts from original captured bindings, each with its own view; the public callee view is not pasted over private bindings. |
| P9 | Authoritative inferred call views §§1–5 and integrated q1 approvals | Original source position/scope, actual roles/entry and joint assignment are retained; `Q` and Function shape cannot manufacture the attachment. Detailed formation rules remain open. |

The addendum and inferred-view decisions are Authoritative only in their
declared scope. The operational and typed-boundary packages are conditional
Draft constructions. Their transport clauses are used here as declared model
requirements, not promoted to new source authority or compiler behavior.

## Minimal finite interpretations

Treat `(d_f,r_A,g,xi)` as supplied original receipt/view operands, with
`xi=(nu,K,D)`. These are proof labels, not a proposed runtime record layout.
Assume the original receipt has a matching result-path correspondence to the
rebound formal view. The outer receipt's existence alone is insufficient.

Use four distinct view/path indices, so structural position is not erased:

```text
original receipt/result view        rebound formal       private capture       u_f lookup
         p_0                 --M_rb--> p_1       --M_cap--> p_2       --M_read--> p_3
      evidence g_0                    g_1                  g_2                 g_3
```

For this finite test, each correspondence contains its one displayed matching
pair. `M_rb` maps the selected result/value path, not an unrelated outer
computation effect. Capture/read keep the unchanged formal interface; their
correspondences are identities on the underlying structural path, indexed
by distinct source/target views. All maps are **supplied typed premises**.
Choosing these singleton maps is not proof that the source generator emits
them for the candidate.

Give the original packet one persistent profile incidence `chi_0(p_0,b)` and
one dependency incidence `D_0(k,p_0)`, with a shared ledger containing `k`.
Fix one jointly admissible `nu`. `b` retains its original receiver reference
`r_A`; nothing in this construction asserts that `r_A` remains dynamically
active after return. Nonempty profile/dependency data are conditional test
inputs, not a claim about an accepted instance of the exact program.

Both interpretations have the same lexical value `d_f`, source binder and
use, interfaces, original packet, maps, shared ledger, assignment and closure
code. They also retain the original packet in the surrounding evidence graph.
They differ only on **semantic attachment** at the private captured binding:

| Component | Interpretation A | Attempted interpretation B |
| --- | --- | --- |
| Lexical capture value | `d_f` | `d_f` |
| Original packet and rebound `g_1` | retained | retained identically |
| Private captured binding's view | `(d_f,t_2,g_2)`, with transported original incidences | same value/interface, but original packet incidences unavailable at that binding |
| Lookup of captured `u_f` | same provider with transported `g_3` | same provider without those incidences |
| Original receiver/current activity | same supplied references and configuration | identical |
| Dependence on comparison `Q` | none | none |

Local binding and returning `step` preserve the closure descriptor with its
private capture. They do not expose `f` as a field of `step`'s public Function
view or copy `f`'s profile onto that public interface. The model stops at the
captured lookup; it need not run `f`, introduce a later receiver, emit a
request, select a handler, or resume anything.

This is a minimal deletion witness for the targeted receipt/rebind/capture/
lookup route: one captured binding and one recognizable original incidence
suffice. The dependency incidence separately checks retention of the joint
packet. Empty evidence would not discriminate deletion. No alternative
provider, second outer valuation, recursive group or annotation is
needed.

## Why the second interpretation fails

P8 requires, at each supplied matching edge, the relational image equations

```text
chi_out(p',b) iff exists p. chi_in(p,b) and M(p,p')
D_out = M_*D_in
K_out = K_in under the same nu; inherited lineage is retained.
```

Consequently the finite instance gives

```text
chi_1(p_1,b) = chi_2(p_2,b) = chi_3(p_3,b) = true
D_1(k,p_1) = D_2(k,p_2) = D_3(k,p_3) = true.
```

Interpretation B makes the private binding unable to supply the `p_2`
incidences, while keeping the same source packet and `M_cap(p_1,p_2)`.
It therefore fails the capture instance of P8; lookup cannot repair the
failed captured-binding view. Preserving evidence somewhere in a global
graph is not sufficient to satisfy the semantic typed-binding requirement.
P3/P4 also disallow treating the resulting descriptor as preserving the
same typed evidence at its captured binding.

The attachment is semantic: an implementation can store a reference, inline
a packet or recover it through its certified graph. Omitting a direct memory
pointer is not this mutation if lookup still obtains the required view.
Similarly, introducing an unused Boolean named `Attached` and toggling it
would distinguish representations, not models of these transport clauses.

Thus no two interpretations of **this fixed supplied-correspondence instance**
can disagree on the original incidences at captured lookup and both satisfy
P3/P4/P8. This proves a consequence of the declared requirements, not that
their complete source premises are constructible.

## Formation boundary and precise stopping condition

If the input supplies only the ordinary `Gamma |- d : Value(A)` skeleton,
the receipt tuple, and lexical provider capture, then the maps above are not
yet justified by that reduced input. Permitting `M_cap` to be absent changes
the typed input rather than producing two interpretations that agree on all
of P2/P8's supplied capture-flow premises. Merely retaining type shape cannot
repair this omission; neither can `Q` success.

The exact remaining producer obligation is to derive a matching receipt-to-
formal rebind and formal-to-private-capture/read correspondence for this source
component, preserving its original view and one joint assignment. Common
transport then determines the packet image. The finite mutation identifies
the obligation but does not derive it. No further supplied-transition probe
would test that missing producer, so this lane stops.

Later current receiver realization and any new receipt at the later activation
remain separate. Transporting the reference to `r_A` is not reviving `r_A`,
retaining its activity, or deriving grant/handler eligibility. No lifetime
rule is selected by this result.

## Independence, checks, resources and omissions

No executable oracle was used. The two interpretations were evaluated against
the original declared equations and explicit descriptor/view requirements.
They share all supplied typing/maps/kernel assumptions; the failed mutation
tests preservation consistency, not independent source-rule validation. The
producer claims no independent review and did not read the transport note.

Checks: bounded governing/approval/direct-dependency reads; SHA-256 comparison
of ten filesystem dependencies against primary-supplied baseline hashes;
lease absence; final dependency, artifact and whitespace inspection. The
initial whole-core capture was truncated; decisive §§2–4,6 and the entry part
of §9 were inspected, with §§6/9 reread in bounded captures. No exhaustive
repository absence search is claimed.

Coverage is the finite four-view route and one semantic attachment-deletion
mutation. Seeds/ranges are inapplicable. No Git command, Cargo/test/probe,
compiler edit, shared-record write, formatter or child was used. At most four
lightweight read commands ran concurrently. No numerical CPU/RAM/wall-time
limit was supplied; CPU, peak RSS and elapsed wall time were unmeasured.

Unverified: production/source acceptance; generation of complete typed capture
and rebind inputs; U1–U5/registration; arbitrary conversions, mutable/opaque
providers, recursion and generalization; later invocation/activity; admission,
complete-domain containment, principality, adequacy and implementation.

Recommended next action: derive the typed rebind/capture/read correspondences
from the exact source component, then apply the existing packet image rule.

## Frozen dependency hashes

Whole-file SHA-256 values supplied by the primary for the assigned baseline;
filesystem values matched before use and at freeze. Git was not invoked.

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917` |
| `notes/design/2026-10-02-source-computation-role-elaboration.md` | `9a230eb023698666f4c3e518a527009d6915e65f658b230e6da6a29914ca3abb` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `questions/2026-10-05-nested-block-function-source-realization/approved-answer.md` | `04ee0dc089dc6ad19a184d31775a146c08b07f2f287099d2e5b54d7d1d5a643e` |
| `questions/2026-10-05-nested-block-function-source-realization/receipt.md` | `e5e59e176eb865a588b2843b18137571fe9c5b6f43bf1ca349bc60c9ad90f0ec` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-capture-evidence-attachment-falsification.md`.
- Baseline SHA: `90eee6c2a686394e669d0361d825977f82a74f8a`; current
  HEAD `e2ea106ff` was reported by primary, not independently queried.
- Changed dependency hashes: none; ten filesystem hashes matched the pinned
  values supplied by primary.
- Review status: frozen, independently compiler-referee-reviewed with no
  findings; conditional preservation result and failed deletion mutation only;
  no accepted-program counterexample, new attachment producer, lifetime rule
  or gate closure.
- Checks already run: governing/direct-dependency clause reads, dependency
  hash comparisons, lease absence and final path/whitespace inspection.
  No semantic executable checks, tests, builds or Git.
- Proposed one-line research-checkpoint commit message:
  `research: test capture attachment against typed packet preservation`.
- Shared-record deltas intentionally left for primary/curator: distinguish
  required packet preservation under supplied typed correspondences from
  the open source producer of those correspondences; retain later activation,
  admission, registration, principality and adequacy as separate open gates.

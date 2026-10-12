# Exact nested odd/even: source qualification and a missing demand input

Date: 2026-10-13
Status: frozen research characterization; independent `compiler_referee` PASS
after primary repair of the review's minor scope wording
Claim class: constructive application of approved source-incidence and origin
rules, with one missing original typing input; no source typing theorem
Baseline: `fd94dedee30c06f83a3a867ea8da413d3b688eab`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file only; leaf, no further delegation

## 1. Frozen statement

The complete source remains:

```yulang
my odd n =
    my even n = if n <= 0 { true } else odd(n - 1)
    even(n - 1)
```

Let O/E be its distinct definition-root Values and a/b its distinct outer/inner
formal Values. In even's initializer, each `n` resolves to b and `odd` to O.
In odd's final expression, `n` resolves to a and `even` to E. The inner
definition owns its initializer. O remains the enclosing monomorphic recursive
root until its initializer completes; E publishes at its own nested boundary.
No polymorphic recursive use of O, same-level local mutual group, root/result
identification, or substitution of another program is permitted.

The assigned conclusion is to construct the original source typing, its actual
call-demand extrusion records, their approved equalities, and the resulting
scheme/use judgments, or exhibit an original-source contradiction. For every
lawful formation of this exact source, preserve its original type scopes,
source-event binders, complete Call, actual providers, entry/receiver/return
evidence, effects, attachments, witnesses and residual lineage. No assumption
that a complete original typing or compiler run has succeeded is allowed.

The premises available for the *source-incidence subclaim* are exactly the
fixed lexical resolutions above and the adopted source ownership/origin rules.
These do not include an operator environment, selected Ord/Sub method,
independently typed complete primitive contract, conditional elaboration,
complete recursive-world introduction, successful source Generalize, or an
observed native type-generation history. Those are required evidence, not
silently added hypotheses of a success or failure theorem.

The original requested theorem remains OPEN. This artifact identifies one
missing original judgment needed to construct its inner demand. The separate
reference calculation in §4 identifies already known native coordinates; it
does not continue the source derivation through that input.

## 2. Exact governing sources

- [Top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md),
  §§1–5 and Authority and integration: native generation, accumulation,
  propagation, levels, extrusion, intrusion and generalization.
- [Parent-copy decision](../design/2026-10-10-parent-copy-scc-intrusion.md),
  Value-reference SCC clarification, Apply-result source-fragment ownership,
  Definition-root Value ownership and Retained boundary.
- [Occurrence qualification](../design/2026-10-12-intrusion-value-type-association.md),
  Approved extrusion-event qualification, Definition-root origin for nested
  call-demand extrusion, Qualification and Implementation and proof boundary.
- [Approved origin answer](../../questions/2026-10-12-nested-extrusion-origin-value/approved-answer.md),
  Exact approved draft content and Authorized scope: this wrapped call has
  origin E and receiver O; other expression wrappers use the same owner rule.
- [Local recursion](../design/2026-10-10-local-self-recursive-binding.md),
  Selected source behavior and Proposed source-to-solver seam: a nested helper
  uses the active enclosing root without scheme capture/freshening.
- [Source Generalize](../design/2026-10-08-source-generalize-definition.md),
  §§2–4, selecting [construction §§3–5](2026-10-08-source-generalize-definition-and-proof.md).
  Its L1–L5 remain genuine local premises, especially primitive laws and
  recursive introduction. §3.1 retains full Call/Branch operands; §3.2.5
  requires an actual registered method/adapter choice; §3.3 gives original
  declaration/event telescopes. Generalize does not supply these missing laws.
- [Call source interfaces](../design/2026-10-08-call-source-interface-definition.md),
  §§2–4: IF-Insert/IF-Use preserve independently typed whole interfaces;
  original operator typing, provider dispatch and phase validity remain inputs.

The rules read were orchestration budget, agent orchestration (including model
routing and proof delegation), research lab, design authority, compiler
engineering and Git concurrency. The yulang-proofs skill and actual prover
configuration were read. No coordinator authority was assigned.

## 3. Constructed source graph and occurrence qualification

At definition publication, O owns the Name `even` in its final Call, so the
definition-root rule inserts O → E. E owns `odd` in its own initializer,
including its else branch, so the same rule inserts E → O. Therefore O reaches
E and E reaches O, and `SCC(O)=SCC(E)`. Extra incidences cannot destroy these
two paths. This proves common-component membership, rather than asserting
that the entire component contains only these two vertices. Lexical/inference
levels do not restrict either edge.

The Apply-result rule separately inserts inner Call-result → O and outer
Call-result → E. These results, definition roots, formals, Lambda/Block rows,
type variables and eventual description frames are distinct. Neither these
result edges nor subtype/storage edges identify their endpoints.

For **any actual call-demand extrusion occurrence generated by this inner
`odd(n - 1)`**, the adopted origin constructor selects E because its body owns
the source call. The callee's fixed Name resolution selects receiver O.
This is a direct rule application for the displayed wrapped occurrence;
wrapper-origin ambiguity is resolved by approval, not an additional premise.
Its retained pairs therefore qualify under the adopted E/O SCC rule. For
each actual produced pair `(copy,parent,polarity,target)`, intrusion requires
`copy=parent`. It does not equate O and E, substitute C=B for C=T, place type
copies in the Value graph, or qualify a pair from another occurrence.

This derives the semantic origin/receiver and the eligibility of the actual
pair set. It does not manufacture an extrusion occurrence or determine its
pair set before authentic typed demand formation. Retaining/transporting that
source event through an implementation is also distinct from the selected
source constructor rule.

## 4. Original native levels and the known reference pairs

In native Simple-sub, publication boundary 0 introduces the outer recursive
type root o and formal A at level 1; a nested let initializer introduces its
root e and formal B at level 2; E's scheme boundary is 1; odd's final use of E
is at level 1. These follow `Typer.scala:48–55,64–67,81–83`. Monomorphic
`odd` lookup returns o itself (`:62–63,205–207`). They are rule instances of
the reference under faithful source formation, not measured source levels.

Let an authentic inner argument judgment generate native T, and let the native
App rule introduce fresh R at level 2. The generated comparison is
`o <: Function(T,R)` (`:68–72`). R forces demand level 2, so negative extrusion
to o's level 1 runs (`:115–126`). Function argument polarity flips, result
polarity stays negative (`:134–144`). Its actual memo always produces
`(D,R,-,target=1)`; if T is a level-2 variable it produces `(C,T,+,target=1)`
and traverses the selected bounds with the same polar memo (`:146–156`).
Additional wrong-level reachable variables can produce additional pairs.
A ground/low-level T does not produce C. No universal two-pair enumeration is
licensed by the source text or by the SCC alone.

For the previously fixed **integer reference elaboration**, the complete
[native derivation](2026-10-12-cross-level-odd-even-simple-sub-derivation.md)
§§2–5 does determine T: it is the fresh level-2 App result of the curried
subtraction, with lower bound Int. R is initially fresh with empty bounds.
Consequently that history has exactly:

| Copy | Parent | Parent level | Copy level | Sign | Origin/receiver under the approved rule |
| --- | --- | --- | --- | --- | --- |
| C | T, inner subtraction result | 2 | 1 | + | E/O |
| D | R, inner recursive App result | 2 | 1 | − | E/O |

C retains T's selected lower Int and T acquires upper C; D copies R's empty
upper side and R acquires lower D. The rewritten demand is `Function(C,D)`.
Insertion replays every existing lower of o (`Typer.scala:115–117`); storing
the demand is not proof of that replay's success. C's parent is T, not B.
The approved source qualification, when bridged to this actual history,
selects C=T and D=R. The reference itself has no intrusion/event constructor.

This is an exact reuse of an already calculated native history, with its
integer-elaboration hypothesis exposed. It is not an assertion that original
Yulang constructors emit that history. The reference supplies true/if but no
minus/comparison builtin (`Typer.scala:23–33`); its term grammar and curried
if translation do not supply Yulang's complete Branch/Call law. A scalar joint
Int/Bool assignment or its computed `int -> bool` scheme remains a reference
result and cannot discharge the source request.

## 5. First missing original judgment and stopping point

One demand-formation input still unconstructed for this exact source
is the scoped typed elaboration of the **inner argument `b - 1`**, retaining
the actual registered subtraction method, its whole operand/return/effect
interface, and its inference introductions:

```text
rho_live(O,b); original telescope of even's body
  |- source(b - 1) @ actual operands/world
       : Result(T, same returned descriptor/provider) ! epsilon_sub [d_sub]
  with actual method declaration/instance, all Call/entry/consumer obligations,
       native generation clauses, levels and their source correspondence.
```

This is one local constructor judgment, not a demand that the whole source
already be principal or that the enclosing recursion already be discharged.
It is needed before the actual argument port, T's declaration/scope and
selected bounds, and therefore the original extrusion pair set can be named.
Neither a bare `int -> int -> int` contract nor an integer result assignment
constructs it. Source checking §3.2.5 requires its actual method constructor;
Call-interface §§2–4 consume its whole independently typed law. No such
instance for the displayed original `-` occurrence was supplied by the packet
or constructed by the selected rules inspected here.

Owner: original source operator/method elaboration and typed local Call
construction, at this occurrence before/at demand formation. The enclosing
`n <= 0`/Branch law, recursive joint-world validity (L4), and nested source
Generalize registration remain additional required judgments. They are not
asserted solved or impossible. In source traversal the guard may require its
operator law earlier; the judgment above is the first missing *inner-demand*
input, not a claim to have typed the guard first.

Thus the strongest actual source conclusion established here is the O/E SCC
and the exact E/O qualification of any authentic inner occurrence's pairs.
There is no original-source success, rejection, contradiction, final scheme,
or principal-use consequence. In particular, no post-intrusion allocation map
is constructed. Source Generalize preserves active complete residual clauses
under original Shared/ViewLogic/Event scopes; it cannot be applied before the
actual clause program/registration is formed. Native `freshenAbove` retaining
level-1 C/D does not independently prove how C=T or D=R enters that complete
source package or its independent uses.

This is a missing construction instance, not a new semantic alternative or
permission to reject the user's spelling. No source domain was narrowed.

## 6. Actual compiler owners and bridge coverage

The compiler was inspected for correspondence, never used as type authority:

| Owner | Retained construction and coverage boundary |
| --- | --- |
| `crates/yu-hir/src/module/local_source.rs:338–372` | Self binder before parameters; parameter shadowing; restore then publication. Exact indented body remains outside `body`'s OperatorChain-only constructor (`:251–255`); `LocalSourceForm` has no If constructor (`:107–137`). No exact-source native rows were observed. |
| `crates/yu-solver/src/candidate_source.rs:394–411` | Apply retains callee/argument/results/effects and checking identity on an admitted carrier. `owner: source.definition_root()` alone is not the approved nested E-origin record. |
| `crates/yu-solver/src/shadow_apply.rs:1335–1390` | Negative Function retains argument Value/effect, invocation effect and result; native interface additionally retains callee/application effects. Two-port reference calculation omits these original effect/Call obligations. |
| `crates/yu-solver/src/candidate_extrusion.rs:82–163` | Copies actual wrong-level rows by polarity/target, records parent at creation, and traverses selected bounds. This does not construct authentic original primitive or E/O occurrence evidence. |
| `crates/yu-solver/src/candidate_extrusion.rs:763–804` | Opposite-side replay constructs and drives contextual replay. A stored comparison or pair does not certify its complete original source interpretation. |
| `crates/yu-solver/src/candidate_call.rs:81–130` | Explicit pending original whole registration, Gen-Call-0, whole-carrier Reify, receiver/result/future suppliers; negative Function and scalar provenance are expressly not original typing. |

Ordinary Call must retain callee evaluation, inert whole argument, actual
returned callee/current world, receiver receipt, actual entry, one designated
Force/rebind for Value entry, body consumer, invocation return and pending
suffix/future interfaces. Original Branch keeps its guards and ordered arms.
No empty recursive Call effect follows from pure integer operands. No live
attachment, provider, witness or residual was collapsed to a scalar port.
This artifact constructs none of those missing semantic suppliers.

## 7. Economy audit, checks and frozen handoff

The prior exact-source conditional derivation and complete integer-reference
derivation left original operator/Branch-to-native formation unconstructed.
The approved answer materially removes their wrapper-origin uncertainty,
which §3 applies directly. It does not remove the local typed-construction
cut. Another native integer suffix or algebraic quotient would leave this
same premise untouched, so no third equivalent derivation was attempted.

The local formation/complete Call obligations are required A/B. Retaining E/O
ownership and actual memo-produced pairs is constructional evidence at known
owners; reconstructing them later from storage is D. No classification closes
or weakens the parent gate. No copied-owner convention, new registration
component, or alternative source semantics is proposed.

Checks: static rule/source reads, read-only branch/HEAD inspection, SHA-256
snapshot and byte comparison of 14 repository dependencies against the pinned
commit; all matched. Leased-note whitespace and local Markdown target checks
are performed at submission. Zero compiler tests/builds, Scala/Oracle runs,
probes, benchmarks, children, Git mutations or external contacts. One
lightweight read/write process at a time; no heavy process. CPU/RSS and
reasoning wall time are unmeasured; no numeric packet limit was supplied.

Requested runtime: normal proof leaf, `gpt-6.1-sol/high`. Prover model/effort
pins are absent; configured defaults are Sol/high and callable role exists.
Observed effective model/effort metadata: unknown. No Astra or hot reload.

One next action: assign the original operator/typed-Call owner this exact
`b - 1` judgment, with original scopes and the authentic complete primitive
interface. It must construct T's source/native generation map, or return its
first missing local supplier. It must not substitute the existing eleven-App
integer model for an original-source derivation.

## Commit packet

- Exact leased/changed path: `notes/theory/2026-10-13-cross-level-odd-even-source-intrusion-proof.md`.
- Baseline SHA: `fd94dedee30c06f83a3a867ea8da413d3b688eab`.
- Changed dependency hashes: none; all 14 checked repository inputs matched
  the pinned baseline. Key SHA-256 inputs: occurrence design
  `28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775`;
  approved origin answer
  `eaa2b19ea059a3aa0fdc5feac40e198b4bc6ee6ef1c5f1bf1fdf3d5381be16ba`;
  source construction
  `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`;
  reference Typer
  `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9`.
- Review: `compiler_referee` PASS for the bounded characterization; the
  primary repaired its minor wording finding. No theorem promotion,
  production conformance or parent closure.
- Checks already run: narrow static source/rule inspection and frozen
  dependency equality/hash checks; final text/link check returned separately.
- Proposed message: `research: derive exact odd-even source intrusion qualification`.
- Shared deltas left for primary/curator: remove wrapper-origin ambiguity for
  this occurrence; record unconditional approved E/O eligibility for its
  authentic pair set; keep actual `b - 1` typed formation/pair enumeration,
  full source scheme/use transport, recursive validity, soundness, required
  principality, effects, complete Call and F5 OPEN. No shared record edited.
- Writes stop after the reviewed minor wording repair; source inference remains
  open.

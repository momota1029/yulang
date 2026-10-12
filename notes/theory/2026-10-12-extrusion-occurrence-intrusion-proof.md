# Extrusion-occurrence intrusion: source preservation proof boundary

Date: 2026-10-12
Status: frozen reviewed conditional research; original parent A/B theorem OPEN
Reviewed-by: fresh independent compiler_referee, 2026-10-12; no BLOCKING/major findings, single minor accuracy item repaired
Baseline supplied: `c15ecbaa32c3d681162e85dd6643ae3af8f8b53c`
Original Simple-sub supplied pin: `9bae772624c23b52a93c1b226157e16898b4d9db`
Producer: prover-equivalent generic fallback, leaf only; no custom prover execution claimed
Lease: this file only; no compiler/test/build/Git operations or delegation
Budget: one reasoning lane, at most 30 minutes, no heavy processes
Authority: existing selected operation; no new semantic or implementation decision

## 1. Original obligation and result

The parent obligation is classes **A/B** under `rules/compiler-engineering.md`:
preserve source correctness, required principality and natural inference
progress when adding the approved occurrence-qualified intrusion. It is not
the stronger requirement that every arbitrary pre-intrusion type assignment
survive unchanged.

Freeze the domain as all admitted source programs and lawful uses in the
original supported Yulang envelope, with original scopes, recursive roots,
complete Call, effects, source formation and generalization. For every actual
extrusion event e, retain its source Value, receiving Value and every actual
signed parent/copy pair produced by e. When those Values share an approved
Value-reference SCC, impose equality on those pairs. The required conclusion
is that successful inference remains source sound, the required principal
interface still covers its original lawful uses, and ordinary formerly lawful
source inference does not fail or lose its owned normal continuation because
of intrusion. The original principal-interface criteria remain unchanged.
Resource failure is governed by the top-level principles, not by universal
rollback or unlimited-input assumptions.

**Result: this original-scope theorem is neither proved nor refuted here.**
The precise source/Generalize bridge is missing. The approved source graph
and event endpoints do not imply equality redundancy, and native early
equality combined with the actual original level-based instantiation does
reject the exhibited ordinary original-Simple-sub source. That refutes this
particular preservation strategy. It does not establish rejection under the
complete Yulang source construction, whose component classification,
fixed-anchor incidence and equality/frame transport are not yet supplied.
The parent remains OPEN under the primary's ownership; no conditional leaf
result closes it.

Governing sources read:

- [Top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md), §§1–5 and Authority and integration.
- [Parent/copy operation](../design/2026-10-10-parent-copy-scc-intrusion.md), selected operation, actual Value references, Apply membership and definition-root ownership.
- [Occurrence clarification](../design/2026-10-12-intrusion-value-type-association.md), approved qualification and implementation/proof boundary.
- [Source Generalize](../design/2026-10-08-source-generalize-definition.md), §§2–3, selecting construction §§3–5 of [the source proof](2026-10-08-source-generalize-definition-and-proof.md).
- `rules/design-authority.md`, `rules/compiler-engineering.md`, `rules/orchestration-budget.md`, `rules/agent-orchestration.md`, `rules/research-lab.md`, `rules/git-concurrency.md`, `.codex/agents/prover.toml` and the available `yulang-proofs` skill.

The frozen [counterexample search](../progress/2026-10-12-intrusion-occurrence-counterexample-search.md)
and [source audit](../progress/2026-10-12-extrusion-occurrence-source-audit.md)
were leads. The decisive native rules, Source Generalize rules, HIR forms,
Apply construction and extrusion input were read directly below.

## 2. Unconditional constraint facts and an unsuccessful proof route

For a fixed algebraic constraint program P with a coherent declaration map,
adding equalities E gives

```text
Solutions(P ∧ E) ⊆ Solutions(P).
```

Proof: a joint assignment satisfying a conjunction satisfies every original
conjunct. This elementary result is unconditional at this constraint layer.
It does not establish full source soundness: the original program's source
adequacy, complete Call and publication correspondence are separate premises.
It supplies no completeness, principal-coverage or normal-progress result.

A sufficient proof route would show that every qualified equality is already
entailed in the relevant original source description, or construct a lawful
replacement description preserving the required public interface. The first
route fails for the native source in §3: an actual generated program has a
successful assignment with B different from C even though the normative F/G
source cycle qualifies the occurrence. This is a refutation of **equality
redundancy**, not adoption of arbitrary assignment preservation as a new gate.
The real discriminator is the subsequent ordinary source use that fails under
fixed-anchor equality, rather than merely that one internal solution is lost.

## 3. Original-source construction and complete native derivation

Use the supplied original reference's actual AST constructors:

```text
let rec f = lambda x.
  let g = lambda y. (lambda z. y) (f y)
  in {a = succ (g 0), b = g true}
in f
```

`syntax.scala` declares every used constructor: `Let`, `Lam`, `App`, `Var`,
`Lit`, `Rcd`. `Typer.scala:22–31` gives `succ : int -> int` and `true : bool`.
This is admitted original-reference AST source, not handwritten client
inequalities or an asserted Yulang parser result. Its evaluation may diverge;
native type inference does not require evaluation termination.

The following hand derivation checks the entire native source, including
recursive completion. Normal finite allocation is assumed. Let o and the
outer parameter A be at level 1. The g initializer is inferred at level 2,
with formal B, ignored formal Z, recursive Call result R and wrapper result S.

1. `typeLetRhs:48–55` registers o monomorphically. `Lam:64–67` allocates A
   and B at their actual current levels. `Var:62–63` with monomorphic
   `instantiate:205–207` returns o without a fresh copy.
2. `App:68–72` for `f y` requests `o <: Function(B,R)`. Since the demand's
   level is 2 and o's is 1, `constrain:121–123` invokes one negative extrusion
   with an operation-local polar cache. `extrude:143–156` flips argument
   polarity and preserves result polarity. B has no lower bound and R has
   no upper bound. The actual first two copies are therefore

   ```text
   C = extrude(B,+,1)    D = extrude(R,-,1)
   B <: C               D <: R
   o <: Function(C,D).
   ```

   The direction follows the actual selected bound lists, not Value graph
   adjacency. C and D have level 1.
3. The wrapper request is `Function(Z,B) <: Function(R,S)`. Function
   decomposition generates `R <: Z` and `B <: S`. The left-variable branch
   stores these at level 2. No clause equates the discarded R with returned B.
4. g publishes `PolymorphicType(1,Function(B,S))`. Its reachable description
   includes B's uppers C and S. The R/Z/D subgraph is not reachable from that
   root through these directed stored bounds. This is an actual consequence
   of the native representation, not a proposed Yulang residual projection.
5. `freshenAbove:166–188` uses one new unpolarized memo map for the first
   g Name. It copies B/S as B0/S0 and keeps C unchanged because C.level=1.
   Its clauses include `B0 <: C` and `B0 <: S0`. The first App adds
   `int <: B0` and `S0 <: V0`; the `succ` App adds `V0 <: int` and
   `int <: W0`. Opposite-bound replay propagates int through these paths and
   checks only int against int.
6. The second g Name has a different memo map: B1/S1 are distinct, C is the
   same level-1 anchor. It adds `bool <: B1 <: C`,
   `B1 <: S1 <: V1`. C acquires both int and bool lowers. It has no upper
   path to B0/S0/V0/int. Nothing replays bool against the first use's int.
7. The outer body forms `Record(a:W0,b:V1)`. Recursive completion constrains
   `Function(A,Record(a:W0,b:V1)) <: o`. Replay against o's stored demand
   generates `C <: A` and `Record(a:W0,b:V1) <: D`. A and D have no
   conflicting uppers. D has no upper edges, so its new lower does not
   propagate to R/Z; their existing lower bounds remain consistent. There
   is no bool/int failure.
8. f publishes at boundary 0; its final Name coherently freshens its reachable
   graph. No additional final consumer is imposed. Thus that source inference
   completes successfully under the actual native rules.

For an independent algebraic consistency check, let T=`{a:int,b:bool}`:

```text
A=top, o=top -> T, C=int|bool, D=R=Z=T,
B=S=bottom,
B0=S0=V0=W0=int, B1=S1=V1=bool.
```

These are semantic algebraic types, not additional SimpleType constructors.
`top -> T <: (int|bool) -> T` has the required contravariant direction.
All generated inequalities hold, with B≠C. The operational derivation above,
not this solution alone, establishes native algorithm success. At the source
typing level the helper has the bounded correlation
`forall beta <: int|bool. beta -> beta`, while one monomorphic f can have
`(int|bool) -> T`; the two uses choose int and bool under that same contract.
This does not prove the complete Yulang public principal scheme.

Under the approved definition-root incidences, F→G comes from f's source-owned
uses of g and G→F from `f y` in g's initializer. Thus F/G share one SCC,
independently of levels or type bounds. The native event is the same G→F
demand seam as the selected discriminator and produces the signed B/C and
R/D pairs. Applying the approved normative event association to this source
qualifies both. The Scala implementation has no event certificate, so this
last association is normative, not an observed reference transition.

## 4. Exact rejection theorem for the native fixed-anchor strategy

**Native strategy theorem.** Take the ordinary source and native
generation/instantiation above. If the qualified C=B equality is settled in
g's description before its independent uses, and those uses preserve equality
to the same native level-1 C anchor, source inference must fail.

Proof: the first use has `B0=C` and
`B0 <: S0 <: V0 <: int`, hence C<:int. The second source argument requires
bool<:B1=C, hence bool<:int. The original primitive rule rejects the distinct
primitive pair. This is an actual source use path, with no synthetic client.
Equating D and R does not remove either path. If equality is represented by
canonical merging at level 1, first use already constrains C directly; if
represented by two active inequality directions, their replay gives the same
consequence. A scheme that drops an equality direction would not meet this
theorem's equality-preservation premise.

This disproves preservation for the specific combination of ordinary native
fixed anchors and early occurrence equality. It does **not** quantify over
all lawful Yulang transport or SCC schedules. If original B and C are equated
only after B0/B1 have been independently allocated, equality does not
automatically identify those already distinct rows. A faithful late-history
interpretation still needs its source law; this observation supplies no
validated delayed policy. Likewise making C frame-local may avoid this
particular contradiction only if its genuine original eligibility, component,
scope and dependence permit it. No such change is adopted here.

## 5. Source Generalize consumes equalities but does not classify this event

The selected construction gives a useful exact allocation argument:

**Allocation lemma.** If a closure's retained program contains C=B, C belongs
to its fixed closure, and B is a template declaration, each independent
`new(p,i,g)` has `B_i=C_base`.

Proof: construction §4 retains the active clause with its original operands.
§5.1 retains all clauses, including constraints to fixed fields. §5.2 `new`
opens one coherent whole-component frame, gives B its `(i,q)` occurrence,
and routes fixed fields to their original base incidence. Substitution into
the retained equality yields `B_i=C_base`. `join` uses those same incidences,
so two frames cannot independently choose C_base. `alias` preserves the same
frame and introduces no alternative assignment. This proves the stated
allocation consequence directly from the selected rules.

Applying it to §4 would give a Yulang rejection **only after its premises are
established at the source owners**. Neither native numeric levels nor Value
SCC membership establishes those premises:

- A template is an actual `Desc(C_component,q,sort,sigma,Delta)` introduction
  outside the typed fixed dependency closure (§§3.3,5.1); it is not every
  younger solver row. Native C is an extrusion-created coordinate, not a
  Source Generalize Desc introduction supplied by the existing schemas.
- The validating component comes from recursive-group/definition
  registration (§5.1). The approved Value-reference SCC is the activation
  graph for intrusion; no selected rule equates it with that component.
- Own-component `Internal` retains one entire simultaneous relation per
  incoming frame. External `Mono/Established` fixes the full existing
  contract, while a Published family retains its bound parameters.
  Which of these edges the live outer f contributes at inner g publication
  cannot be inferred from provider identity or from C.level=1.
- All equality clauses in a supplied closure remain active. This does not
  determine when a subsequently discovered equality becomes part of a
  publication's program or how it is transported to existing frames.

Consequently the Source Generalize theorem cannot be invoked with
`C fixed because level=1` as an unstated premise. Its L1–L5 require the
genuine local primitive, constructor, complete Call and recursive laws. It
does not itself supply an intrusion/extrusion law or a translation of the
native polar copy to original source declarations.

## 6. Checked actual Yulang constructors and admission boundary

| Directly checked owner | Established fact | Missing theorem input |
| --- | --- | --- |
| `local_source.rs:107–137,329–364,640–675,710–819` | Unit, Integer, resolved Name, Apply, Group, Ascription, Lambda and sequential Block carrier; parameterized local function identity is installed before its initializer body, then published in order. | The exact Scala witness includes Record syntax, absent from this private carrier inventory. `true` is a reference builtin, not a supplied Yulang Bool constructor here. Full Yulang source admission/translation of that exact witness is unproved. This does not declare a language restriction. |
| `candidate_source.rs:250–327,369–410` | Local initializers enter the next level; active recursive references Link to the existing endpoint; later locals use the installed scheme. Apply operands and source positions are retained. | Every `ApplySourceInput.owner` is the enclosing definition root. It is not an actual nested G origin certificate. |
| `shadow_apply.rs:1335–1443` | Apply constructs an actual four-port demand using argument value/effect, invocation effect and result; value admission precedes effect forwarding. | This is not a proof that body Result equals complete invocation; no such collapse is used. No original/receiving Value event is passed to extrusion. |
| `candidate_extrusion.rs:4–35,90–175` | Inputs are endpoint/polarity/target; the local memo is populated before selected-bound traversal; true signed parent/copy pairs are retained. | No origin/receiver Value or common occurrence ID is accepted by this interface. Numeric levels cannot certify Source Generalize anchors. |
| Source Generalize construction §§3.1,3.3–3.4,4,5.1–5.3 | Full local Call and recursive clauses, original scopes, typed provenance, whole-component frames and alias sharing are selected. | Neither an event-to-clause owner rule nor this source's exact component/fixed-anchor mapping is supplied. Complete Call local laws remain genuine premises. |

The exact nested original discriminator is constructible in the native
reference and its Yulang parameterized local shape is represented by the
inspected carrier. This establishes useful construction seams; it does not
extend the heterogeneous Record witness to the complete Yulang source
judgment. The source audit's smaller `my odd n = { my even n = odd(n); even(n) }`
prefix likewise remains conditional on authentic admission and successful
Call. The original conditional/arithmetic odd/even text is not replaced or
restricted by this note.

## 7. Smallest decisive premise and owning handoff

The parent theorem needs an actual source-to-description/transport invariant,
not another finite graph calculation. For the exhibited witness the smallest
decisive instance is:

```text
At g publication and each of its two actual uses, determine the original
source declaration/edge represented by C and B, the validating component,
the fixed/template classification, and the active transported equality.
Does faithful allocation force rho_i(B)=rho_i(C)=C_base for both uses?
```

Source registration owns the component and introduction classifications;
owning Call/demand generation and replay own the actual G→F event and its
pairs; Source Generalize owns fixed dependency traversal and frame allocation.
Each premise must be justified there. The current extrusion signature lacks
the certificate needed to consume such a justification. Independently, the
exact witness needs admission/complete Call laws in Yulang, including its
heterogeneous values and original checking consumer.

If fixed-anchor transport is established on an admitted Yulang realization,
§§4–5 convert immediately to an original ordinary-source rejection, requiring
the existing independent review and user design-adjudication route. If it is
not established, that does not prove preservation: a lawful alternative must
retain original scopes, complete simultaneous recursive relation and actual
monomorphic roots, and discharge the unchanged A/B conclusion. Do not silently
choose a schedule, freshen C, change the source domain or retire the parent.

Recommended next action: assign one bounded **source publication/transport
construction** packet to establish this exact two-use incidence test and an
admitted Yulang realization before dependent production implementation. The
test must report the actual component, fixed edges, declaration introductions,
event certificate and active equality incidences, rather than assume them.
Two independent methods have now localized the same bridge; more variants
of the existing native counterexample would leave it untouched.

## 8. Verification, runtime and commit packet

Checks were direct `cat`, bounded `sed`/`rg` constructor reads, hand evaluation
of original generation/replay through final publication, dependency hashing
and a leased-note whitespace check. No parser execution, checker, builds,
tests, Oracle execution, executable search, performance measurement, Git
operation or child launch occurred. Sample/process counts: zero inference or
performance samples, zero heavy processes, one reasoning lane. Exact CPU/RSS
and reasoning wall time were not instrumented; work stayed within the assigned
30-minute cap. Some initial batched captures truncated, and decisive sections
were reread in bounded windows.

The primary reported that the registered prover launch failed because its
selected model was at capacity, without successful worker execution. This
assignment is the supported generic fallback. Requested settings:
`gpt-6.1-sol/high`. Observed effective model/effort metadata: **unknown**.
Configuration contents and this derivation do not establish runtime identity.
No Astra use, custom prover execution or parent closure is claimed. A fresh
independent compiler_referee review reported no BLOCKING/major findings; its
single minor accuracy item was repaired. The `yulang-proofs` skill was read and applied under the newer explicit
repository fallback and this leaf's no-delegation packet.

Unverified scope: exact Yulang witness admission and complete Call, effects,
general source-to-copy correspondence, fixed/template ownership of copied
coordinates, equality transport under all schedules/replay/memoization,
existing frames, canonicalization and errors, required public principality,
normal progress, combined termination and F5 cutover. None is silently
supplied by the native reference or the allocation lemma.

Direct dependency SHA-256 snapshot:

```text
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389 notes/design/2026-10-11-yulang-inference-top-level-principles.md
6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b notes/design/2026-10-10-parent-copy-scc-intrusion.md
0063b88d17104f85182439d80360e42f8f99a5af4793eab70640a66f955ede25 notes/design/2026-10-12-intrusion-value-type-association.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38 notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 notes/theory/2026-10-08-source-generalize-definition-and-proof.md
ef308b68e967d916278b2d6e106731c723368f0477ecc947a12eb99c7f17a956 notes/progress/2026-10-12-intrusion-occurrence-counterexample-search.md
2063fb4e1143c39972dac352a32534f4843d8286e2e38b1ab793e9221b0f709b notes/progress/2026-10-12-extrusion-occurrence-source-audit.md
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed crates/yu-hir/src/module/local_source.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49 crates/yu-solver/src/candidate_source.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0 crates/yu-solver/src/candidate_extrusion.rs
cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411 crates/yu-solver/src/shadow_apply.rs
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9 /home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala
f26f19f6905d42c247198c45da9b1675b22619dd59749047023efe5f7ee3c60f /home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/syntax.scala
```

- Changed path: `notes/theory/2026-10-12-extrusion-occurrence-intrusion-proof.md` only.
- Supplied baseline: `c15ecbaa32c3d681162e85dd6643ae3af8f8b53c`; Git/blob baseline comparison remains primary-owned. No dependency was edited by this producer.
- Review: frozen reviewed conditional research; fresh independent compiler_referee, 2026-10-12, no BLOCKING/major findings and single minor item repaired. Original parent A/B theorem remains OPEN; no producer certification or theorem promotion.
- Artifact SHA-256: computed after the final metadata repair and supplied in the handoff commit packet; not embedded as a self-referential digest.
- Checks already run: source/rule reads, complete finite native hand derivation and dependency/whitespace integrity; no executable verification.
- Proposed checkpoint message: `research: isolate occurrence intrusion equality and frame preservation bridge`.
- Shared-record delta for primary/curator: retain the original A/B gate OPEN; record the refuted native fixed-anchor strategy, direct conditional allocation lemma and exact missing source classification/transport/admission premise. No shared task/index/design/theory-map or question file was changed.

Writes stop at handoff.

# Shared origins and lazy nonpoint readback

Status: **Draft; additive compatibility repair, proof scope below.**
Date: 2026-11-13. Base: `50a826617`, `astra/nonpoint-provenance`.
Authority: spec/06-roles.md §6, B4 addendum 7, and the supervisor's explicit
classification of the [interval pump](2026-11-13-settled-cover-obstruction.md)
as an implementation gap. No new language decision is made.

## 1. The relation that must be retained

An interval is a pair of bounds. It is not the identity of its actual input.
An actual origin is a source identity followed by a finite structural or nominal
argument path; paths never inspect a nominal body. Reusing a head variable must
reuse its actual-origin relation. Two overlapping intervals, or two pairs with
equal endpoints, supply no such identity proof. No value is chosen between bounds.

For an incoming site, seed recursive inspection with its retained input origins,
rather than an all-None function. A structural descent extends the incoming path;
a nominal descent keeps the existing invariant argument path. A variable query
copies its origin verbatim, even if its bounds are strict. Every occurrence of a
repeated head variable must agree with one substitution; retaining only the first
occurrence is insufficient. Bare variable child arguments forward that same
origin. Compound arguments retain the old emitter's conservative fallback; their
actual-mode variable materializations need a certificate tying them to the
inherited origin. The new implementation does not construct a complete symbolic
origin for every compound argument. A later head-variable use without the needed
certificate stays pending.

For associated materialization, use one substitution σ for the whole packet.
An actual-mode input-variable occurrence at origin r means r=σ(x), not merely
lower(x)≤r≤upper(x). The equality is observational equivalence on the general
carrier. σ(x) is a retained input-origin leaf. An output-only binder is instead
substituted by the finite readback term of its settled producing child. Repeated
uses and later packets that reuse an origin thus refer to the same relation.
Ordinary interval checks and the complete ordinary journal are retained.

## 2. Two deliberately separate interfaces

The semantic interface is **coherent materialization**: existing schema tests
plus one actual substitution for all variable uses. Constructor/schema induction
then derives readback, rather than taking whole-output equality as a premise.
A finite term contains constructor tests and shared-origin leaves. Its meaning is
the existing observational decomposition relation, including every child position.
It is not a claim that all values of the general carrier have finite unfoldings:
a leaf may denote a recursive value whose interior is not inspected.

The operational interface is a **lazy compatibility relation** over the present
general journal. It uses coherent facts only when certificates are consequences
of the current packet/journal semantics. It does not silently strengthen the
old model set or turn interval fit into equality. If the old producer lost an
origin and cannot certify the substitution, expansion remains pending. This is
a conservative implementation stage; complete source-to-origin production and
all compound-emission certificates are separate obligations.

There are two distinct checks for generated input facts. `InputCoherence` checks
actual-mode uses in compound child inputs against the inherited substitution at
installation. Before such facts can explain another input head,
`InputExplanation` must derive the same relation using **source facts, earlier
trusted facts, and this packet's input facts only**. Including its output facts
or its cached full context here would allow an unfinished output to re-enter a
head explanation through an input fact. The latter check deliberately excludes
both. Associated output promotion requires that the packet is settled, every
requested output has a schema recipe, and every actual variable use satisfies
one coherent substitution. Output-only binders must refer to earlier readbacks.

The emission function may choose between recorded certified origins. Its choice
is a choice of a path with a proof, never a value inside an interval. `Same`
requires all observations at the two origins to be equivalent. There is no
rule deriving `Same` from equal endpoints or overlap.

In particular, a certificate asserting that the whole associated result already
has a given finite term would restate readback. The certificates below concern
individual variable occurrences and actual captured origins; the complete term
is obtained from the generated schema. Missing recipes for unsupported query
forms also defer their use. A leaf implementation with no generated inputs is
still selectable, including constant outputs and irrelevant nonpoint inputs.

## 3. The interval example and positive cases

At the initial P(V² A0,B) request, B=[V never,V any] has no retained actual source
origin. The b capture remains None. Since b is forwarded to both unnamed child
input lists, the lazy generation certificate fails at this first round. This
blocks the old infinite schedule without rejecting the declaration or selecting
an interval center. W has no children, so this generation check is vacuous for W.
Its uncertified b-based output cannot be promoted into a head explanation.

If a future source producer supplies a genuine shared b relation and coherent
materialization records it, W0 gives A0=V b and u0=b. The next round gives b=V b.
Once that equation is reflected into an inspected/root graph position, existing
K2 rejects expansion. This algebra is a separate route from the implemented
first-round deferral; it does not justify claiming a full repaired execution.

Display(list int) has a retained nominal-argument origin and no problematic
actual output. Wrap/Container use the same retained nominal path, and point or
retained-origin output uses have direct coherence certificates. Len(list μ)
requires no inspection of μ for a variable capture; a capture path alone adds no
K2 inspection. Leaf/settled pieces remain selectable. Which of these are complete
Step examples, and which are certificate lemmas, is recorded with the final
formal results rather than inferred from this argument.

## 4. Settled readback and the next budget obligation

For a finite schema recipe e and a coherent substitution σ, readback yields
Holds(e[σ],target). Every leaf of e[σ] is a leaf of σ(x) for a variable x used by
e. Substituting settled child readbacks is finite substitution; it cannot invent
an independent interval interior. This proves finite symbolic readback relative
to the certified shared input origins and child terms.

It does **not** yet bound all future input structure by the initial source size.
A finite origin can contain an arbitrarily long projection path. Also an unknown
source hole refined to V a exposes a new payload hole a; counting that as the
elimination of one original hole is unjustified unless a is itself read back over
a fixed finite set of source holes. Newly allocated IDs cannot simply be added
to that set as fresh atomic leaves.

A plausible conditional budget uses a fixed finite hole set H. Quotient pure
hole equalities. Each genuine constructor refinement must eliminate a remaining
hole in favor of a term over the others; an inspected constructor return to the
same hole is K2. There are then at most |H| such refinements. Between refinements,
Paterson descent bounds each dictionary depth by the fixed input size N and
finite declaration branching bounds the tree. If F(N) bounds its output size,
iterate a bound such as N↦N(1+F(N)) at most |H| times. A finite-signature cover
would then give the existing missing-facts measure, with administrative steps
handled by their separate accessibility theorem.

More explicitly, this conditional argument needs an origin representation with
a fixed finite set H and a decreasing set of unresolved members of H. A
refinement must assign one previously unresolved h to a finite term over the
remaining members and substitute that term consistently everywhere h occurred.
Pure aliases only shrink the quotient. If intermediate dictionary inputs have
depth at most N, the settled-tree argument must give a uniform bound F(N) for
the replacing term, including substituted child outputs. Finite substitutions
then give a new bound computed from N and F(N); induction on the unresolved set
terminates after at most |H| assignments. This is a conditional proof, not a
proof that the current general carrier supplies this representation.

The essential remaining theorem is that **every actual source refinement**
(normalization, interval projection, aliasing, and settled output installation)
has that fixed-hole elimination form. Neither finite symbolic syntax nor K2
alone proves it. No further counterexample with genuinely shared actual inputs
has been found; no unconditional SourceBudget or Acc is asserted here.

## 5. Formal results and validation

All new definitions are additive. `GeneralNominalSharedSteps.Step` installs the
new certified emitter, uses the new head explanation relation, and retains the
ordinary journal constraints, merging and K2 checks. Because its emitted sites
differ, it is not claimed to be a syntactic subrelation of the older settled
Step. `install_models` proves the unchanged ordinary model semantics;
`step_models` and `at_edges` prove the monotonicity needed by the budget proof.

| Obligation | Proved statement and exact scope |
| --- | --- |
| Input sharing | `variable_retains`, `repeated_capture_agrees`, `packets_share` and `SharedEmission.retains` preserve recorded origins and their actual relation. They do not manufacture missing provenance. |
| Interval example | `SharedPump.p_not_installable` blocks the concrete initial P packet of the checked, source-formed fixture. `leaf_output_deferred` prevents the uncertified W output from explaining a head. `shared_round_cycle` proves the alternative b=V b algebra; it is not a constructed K2 execution. |
| Settled readback | `SharedSupport.promoted_output_readback` gives one finite term, uniform over models, for every requested output in a trusted output fact. Every leaf belongs to the finite list `inputOrigins facts`. `settled_readback_leaves` also covers terms used through earlier output-only binders. No whole-result readback premise is assumed. |
| Substitution | `OriginTerms.holds_transport`, `recipe_readback`, `readback_over`, and `SharedPositive.binder_readback` derive and transport the whole constructor term from local variable relations. |
| Positive fixtures | `SharedExamples.display_guard` and `wrap_guard` prove the complete new packet guard for the existing Display(list int) and Wrap/Container source packets. `len_generation`, `len_input_coherence`, `SharedPump.leaf_generation`, and `pump_leaf_coherence` prove the added generation/input checks for Len(list μ) and the interval pump's W leaf. These are not full new-Step execution traces. |
| Source refinement budget | Open: the fixed-H representation, bounded projection/refinement theorem, and uniform settled-tree bound must be derived from actual source formation and checked declarations. A finite basis for each trusted history is insufficient. |
| Invocation sharing | Actual relation sharing is proved. A finite canonical representation of future occurrence/allocation identities and supports remains open. |
| Finite enumeration | `SharedEnumeration.bounded_enumerated` constructs a finite list containing every symbolic term over given finite leaf/test lists within a given depth. `bounded_bind` and `substituted_enumerated` handle substituted child terms. Deriving those lists/depth and representing the complete reports/signatures remain open. |
| Accessibility | `SharedBudget.accessible_of_signature_cover` proves Acc for a source-formed state supplied with a finite exact signature cover of its future installations. `checked_initial_accessible` still requires `SourceBudget`; Checked plus InitialSource alone is not proved sufficient. |

The termination measure counts signatures in the supplied finite list that are
not yet entailed by the current model set and recorded child edges. Installation
of a novel packet strictly reduces that count; all Steps preserve already-held
signatures. The remaining steps use the established administrative accessibility
relation. Nested well-founded induction proves `accessible_of_signature_cover`.
Signatures retain exact occurrence/child identities and semantic input/output
deltas, so finite syntax enumeration alone does not discharge the cover.

The source-to-certificate producer is intentionally incomplete. A supported
point or retained capture can use `point_use` or `retained_use`; constant outputs
use `constant_certificate` once their recipes are supplied. There is no general
theorem constructing all recipes or local certificates for every checked
declaration. The positive fixtures establish the stated guard/certificate scope,
not complete dictionary discharge or arbitrary nonpoint completeness.

Independent read-only review checked provenance propagation, the separate input
promotion predicate, binder transport, output recipe coverage, and the new-Step
finite-cover reduction. It found and helped close two earlier input-materialization
paths that lacked sufficient provenance. The final reviewed versions had no
reported blocking issue. The primary constructed the proofs directly; no
registered prover role was available and no prover agent ran.

Final commands, run from `lean/`, all returned exit code **0**:

```sh
lake build Yulang.GeneralNominalOriginTerms Yulang.GeneralNominalSharedCaptures Yulang.GeneralNominalSharedEmission Yulang.GeneralNominalSharedSupport Yulang.GeneralNominalSharedSteps Yulang.GeneralNominalSharedPump Yulang.GeneralNominalSharedPositive Yulang.GeneralNominalSharedExamples Yulang.GeneralNominalSharedEnumeration Yulang.GeneralNominalSharedBudget
lake build Yulang
lake env lean Audit/GeneralNominalSharedOrigins.lean
```

The standalone audit covers all 79 public theorems in the ten new modules.
Its only reported dependencies are `propext`, `Classical.choice`, and
`Quot.sound`. All ten modules have appended imports in `Yulang.lean`; no
previous Lean line was changed. Frozen files and git refs were left unchanged.
The final scope check and `git diff --check` also returned exit code **0**.

No further source-formed infinite execution of the repaired relation was found.
That is a search outcome, not a termination theorem. There is no new semantic
question for the owner in this change.

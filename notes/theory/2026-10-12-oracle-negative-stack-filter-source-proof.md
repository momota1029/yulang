# Frozen Oracle negative result-row construction and live filter checks

Status: independently reviewed bounded source derivation; not global H closure
or successor implementation conformance. The initial activation claim was
narrowed after a major review finding; fresh delta review found no remaining
issue in that repair scope.
Producer: primary-assigned prover leaf; no delegation.
Yulang3 baseline: `c88685703d3437a73ec4afa6121af5c275f5989f`,
branch `research/simple-sub-intrusion`.
Oracle source revision: `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
Exclusive lease: this file only.

## Frozen statement and scope

For every successfully resolved, non-wildcard `SignatureEffectRow` occurrence
`r` at a composed-negative Function result-effect position, with nonempty
concrete operands `C` and symbolic tail binder `x`, derive the exact frozen
Oracle producer output and the operational consumers reached when that output
is used in a subtype constraint. `C` retains resolved constructor paths and
invariant argument nodes; `x` retains the original lowering-session binder.
Concrete-atom collection may skip variable items; this is not permission to
delete the tail connection. The construction claim starts at the actual
`SignatureLowerer::lower_neg` Function branch, rather than an invented solver
transition.

For every nontrivial filter registration and every semantic lower insertion
completed through the inspected live registration/insertion owners, show that
the actual item checker is invoked on their pair, including already stored
lowers, later lowers, and recursively encountered lower variables. State the
operational completion and effect-family registration hypotheses explicitly.
This local induction does not assert that every compiler mutation uses those
owners, or that abnormal attempts complete their checks.

For every weighted row-upper reduction taking the inspected nonempty-retained
branch, derive both emitted constraints: source feedback through the retained
heads and gamma, and the exact weighted gamma-to-tail obligation. Characterize
the empty-retained and early-return branches separately.

Required conclusion: these source-owned checks and stack operations do not
authorize a global deletion of an unrelated same-family contribution merely
from nominal family identity. Distinguish that local statement from a complete
contribution-lineage preservation theorem and from Yulang3's selected distinct
residual-constructor lineage. Map the actual remaining Yulang3 producer and
consumer correspondence without assuming it.

Exclusions fixed before derivation: no compiler/test changes, build/test/probe
or Oracle execution; no general concrete-formal source admission; no asserted
callback scheme or Yulang3 output; no complete Call, soundness, principality,
termination, global H, capture/extrusion/intrusion or abnormal-path theorem.
No new source restriction, identity policy, semantic layer, or authority is
selected. Independent review and all shared-record/Git duties remain primary
owned.

## Authority, dependencies and claim classes

The governing policy is
[annotation hygiene integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5, [residual lineage selection](../design/2026-10-10-contextual-residual-lineage-selection.md)
“Selected policy”, [contextual attachment/admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§§3–6, and [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5 and “Authority and integration”. The last source controls necessary
abnormal-path safety; full restoration is not assumed.

The original universal H, with its original programs, scopes, copies, calls
and correlated contribution/residual binders, remains exactly the statement in
[global hygiene proof](2026-10-11-oracle-global-effect-hygiene-proof.md) §1.
This note does not redefine H. The earlier
[formal-port bridge](2026-10-11-oracle-effect-hygiene-source-bridge.md) proves a
bounded covariant construction and conditional reached-consumer result; it
does not supply the negative constructor premise.

The results here are (N) a bounded actual source-constructor derivation,
(F) a conditional operational induction over named mutation owners, and
(R) a bounded characterization of actual row-reduction emissions. None is a
freshly independently reviewed theorem, an executable probe, or evidence of
successor conformance. No checker is used.

Assumptions: normal completed calls; one live arena with fresh IDs before
counter exhaustion; declaration resolution and argument arities already valid;
fixed registered effect-family paths during F; and subtype work actually
reaching the specified consumers. A skipped/unregistered constructor is not
silently treated as an effect. Enqueued invariant constraints are not assumed
solved. Successful insertion alone is not complete queue delivery.

All Oracle locators below are paths at the frozen Oracle revision, not the
current Yulang3 files of the same name. Sources were read using `git show`.

## N: exact construction, including the tail binder

Write `H_C` for the actual `Subtractability::Set(path,args)` when `C` has one
member and `SetMany(C)` otherwise. The vector retains arguments and may contain
multiple operands with the same path; it is not a mathematical quotient by
family. Let `b` be the boundary coordinate and `s` the new arena-local stack ID.

1. `lowering/mod.rs:571–663` reverses Function parameter and argument-effect
   lowering, while retaining result/value and result-effect polarity.
   A negative Function uses `lower_ret_effect_neg` at 655. Nested recursion
   gives composed polarity; nearest textual argument/result is insufficient.
2. `signature_effect.rs:56–65,162–178` reaches
   `lower_ret_subtractable_effect_row_neg`. Since `C` is nonempty, the
   empty-items/tail-only shortcut does not apply. At 173 it obtains `b` from
   `function_boundary_effect_stack_inner`.
3. That owner at 319–333 returns `signature_var(x)` immediately when a tail
   exists. `lowering/mod.rs:849–855` reuses the lowering session's binder map.
   Consequently **`b = x` as a solver coordinate**, not a fresh boundary later
   equated with `x`. Closed-row caching and fresh-tail allocation do not run
   on this branch. The exact occurrence remains distinct from this coordinate.
4. `effect_row_stack`, at 382–421, calls `effect_atom_con` on the source items.
   At 453–460 a variable item contributes no concrete atom; named/applied
   constructors go through `constructor_path` (`mod.rs:811–827`) and retain
   invariant argument nodes. Resolution registers Act/Error family paths at
   831–845. With nonempty `C`, it allocates exactly one fresh `s` and returns
   `PUSH_s(H_C)` and `ids=[s]`. `mod.rs:314–319` selects Set/SetMany.
5. `register_stack_facts` (`signature_effect.rs:434–439`) declares the fact
   `(b,s,H_C)`. `arena.rs:198–209` creates an Annotation source boundary;
   `machine/entry.rs:915–944` retains the declaration origin, enqueues the
   SubtractFact and calls drain. Thus the declaration has an operational
   route, not only a stored marker. Completion/terminal behavior of that
   drain is not inferred from queue insertion.
6. The one active stack payload has intersection `H_C`
   (`signature_effect.rs:465–470`). The returned node is exactly

   ```text
   Neg::Stack { inner: Neg::Var(x), weight: FILTER(H_C) }
   ```

   `StackWeight::filter` (`poly/types.rs:319–323`) has **no entries**.
   In particular, this returned negative signature wrapper contains neither
   `PUSH_s` nor `POP_s`. The freshly declared `s` must not be invented as an
   operation in this node. `wrap_neg_with_stack` emits the wrapper because
   nonempty finite `H_C` is not All.

This proves N's constructor equation from the actual owning branch. This
owner does not call `connect_effect_tail_exact`: the link is already the same
coordinate. The separate general negative-row constructor at 143–159 uses a
fresh coordinate plus both tail constraints (336–357) and a PUSH wrapper.
It is a different branch and cannot replace the negative result-row equation.
Pure symbolic rows return a naked tail at 166–170; absent rows return the
empty-head/Top row at 60–62. Neither is a falsifier inside N's nonempty domain.

### The paired local parameter owner supplies the matching operations

The same distinction is visible in the actual annotation path, which is
additional source evidence rather than an assertion that every Oracle source
uses the signature owner. `lambda.rs:1244–1283` builds the annotation and calls
`connect_parameter_computation_detailed`; `annotation/constraints.rs:251–283`
sets `parameter_function_boundary=true` around the paired construction.
Its Function branch at 363–389 constructs the four ports with reversed
argument ports and retained result ports. For its non-wildcard nonempty
result row, 451–470 and 602–608 again select `b=x`, allocate one fresh `s`,
declare `(b,s,H_C)`, and produce:

```text
positive result effect: STACK(Var(x), PUSH_s(H_C))
negative result effect: STACK(Var(x), FILTER(H_C))
returned predicate:    POP_s with FILTER(H_C)
positive return value: NonSubtract(ret.pos, that predicate)
```

The predicate follows 465 and 921–924; return wrapping follows 373 and
848–851. Without the parameter-boundary mode, 454–456 instead allocate fresh
`b` and `connect_effect_tail_exact` at 636–654 emits both `x <: b` and `b <: x`.
Neither construction drops the binder. This paired owner returns only its
immediate `ret_eff.subtracts` at 389, not every nested descendant's predicate.
The lambda owner stores the actual parameter predicate on newly introduced
locals at 919–935, retains its frame at 938–942, and applies selected predicates
to output effect/value at 1232–1237. A complete call/output traversal is omitted.

## F: activation and the two live mutation owners

For an actual nontrivial task `p <: STACK(Var(x), FILTER(H_C))` whose lower
endpoint is neither `Pos::Stack` nor `Pos::NonSubtract`,
`machine/propagate.rs:38–56` calls
`constrain_pos_lower_by_filter(p,H_C,parents)`. Only then does it clear the
wrapper filter and enqueue the inner subtype with the remaining right suffix.
Here the suffix is empty: the wrapper had no entries, and
`ConstraintWeights::with_right_suffix` (`constraints/mod.rs:3584–3588`) extracts
only POP entries. This step registers/checks **the true positive receiver `p`**.
If `p=Var(a)`, the registration is on `a`; it is not automatically a global
filter on the tail `x`. The subsequent relation still has upper `Var(x)`.
If `p=Bot`, the trivial branch at 6–9 returns first; there is no concrete lower
to reject in that task. This is not evidence that future nontrivial tasks vanish.

For the excluded lower shapes, normalization at 11–37 precedes upper-stack
handling: it removes the positive wrapper and prefixes its weight onto the
task's left weight. If the resulting lower is `Var(a)`, the upper filter then
registers on that inner variable. The call at 42 takes the positive endpoint,
not the task's accumulated left weight. Consequently this activation derivation
does **not** establish checking of normalized-away stack payloads, or of other
payloads present only in the task's left weight. The weighted bound checker
below is a separate owner and cannot supply that missing activation check
without an actual reached invocation with those weights.

Define `Check(q,W,A)` to mean the actual invocation of
`constrain_weighted_pos_lower_by_filter(q,W,A,parents)`, including its emitted
checks, not acceptance of `q`. For completed normal calls through the two
owners, the local invariant is: every retained filter `A` and semantic lower
`(q,W)` on the same owner has encountered `Check(q,W,A)` since their pair
became present. Duplicate records need not be rechecked semantically.

The induction is over the ordered insertion/registration events, expanding
nested variable registration when it occurs:

- **New filter:** `bounds.rs:3213–3255` inserts `(var,A)` into `lower_filters`,
  records provenance, and iterates all current lower records. Every pair calls
  Check with both LowerFilter and Bound parents. Duplicate registration returns
  after retaining provenance; it introduces no new semantic pair.
- **New lower:** `add_lower_bound` at 630–766 extrudes to the target level and
  checks/erases the incoming left filter at 646. On the completed semantic
  insertion route, 714 calls `constrain_lower_bound_by_registered_filters`;
  3285–3300 iterates every already registered filter and calls Check. Equivalent
  lower insertion at 709–710 introduces no new semantic pair. Alias subsumption
  and proof-terminal/failed-admission early exits are not new completed
  insertion events in this induction.
- **Nested variable:** `constrain_pos_lower_by_filter` at 3350–3351 recursively
  registers on the encountered variable. New registration checks its current
  lowers; subsequent completed insertions invoke the second case. Marking a
  filter before walking its lowers makes duplicate recursive registration stop.

The base with no pair is immediate. Each new event checks precisely the newly
formed opposite pairs; existing pairs remain checked. Recursive checking only
adds registrations with the same owner rule. This establishes F over these
events. It does **not** show that direct table mutations, extrusion's internal
insertions, later effect-family registration, copying, or generalization all
follow this event grammar. A proof-terminal return after table insertion at
678–683 can precede 714; normal completion is an essential premise, not a
rollback obligation added by this proof.

The actual check is concrete and retained:

- `bounds.rs:3303–3315` checks active left stack payloads and intersects the
  lower's retained left filter with `A` before walking the positive node.
- `3318–3360` checks registered `Pos::Con` families; walks Row, Union, Stack
  and NonSubtract; and registers on Var. Non-effect value structures are ignored.
- `row_effect.rs:834–913` checks stack payloads and concrete families. For
  Set/SetMany, 925–953 finds matching resolved paths and enqueues two directions
  of invariant-argument constraints via 71–85. SetMany checks each matching
  operand. A missing family produces EffectFilterViolation at 988–1002.

Thus an unresolved Var is not itself a forbidden concrete effect, and a later
registered concrete lower on its checked owner cannot bypass the named owner
check merely because the variable was symbolic at construction. Path membership
plus enqueued argument obligations is not a proved acceptance decision or an
arity theorem; these loops use `zip`, and valid arities are an explicit premise.
Checks record/enqueue consequences rather than deleting nominal contributions.

## R: the weighted residual emits both directions

The actual `Pos::Var(a) <: Neg::Row(I,t)` dispatch calls
`add_effect_row_upper_bound` (`propagate.rs:130–137`). Let the incoming weights
be `(L,R)` and let `L0=L.with_filter(All)`. The row owner
`row_effect.rs:88–234` first checks negative concrete heads against L's filter
at 120–126, then clears only that filter at 128–131.

On the branch where weights remain nonempty, the self-tail/right-empty
shortcut at 145–149 does not apply, and retained heads `J` are nonempty:

```text
J  = collect_neg_effect_items(intersect_row_items_with_left_stack(I,L0))
Lr = subtract_row_items_from_left_stack_weight(L0, families(J))
gamma = cache key (a, sorted families(J), Lr), or fresh at level(a)

a     <: Row(J, Var(gamma))                 with empty weights
gamma <: t                                with MIX(Lr,R)
```

The two actual emission calls are 216–233 and share the WeightedResidual
derivation, including retained heads and producer/stack-fact parents.
The outgoing relation uses the **original `t`**, which is not replaced by a
marginal witness or an independent tail. `Lr` retains each original stack ID,
leading POP count and PUSH count while transforming its payload family at
1190–1216. Matching retained families enqueue invariant payload obligations
before subtracting from those stack payloads at 1219–1273. Directed mix remains
the actual normalization call, not a silently commuted operation.

This is genuine construction of source feedback and gamma-to-tail obligations,
not a gamma label alone. `enqueue_row_derived_subtype` (`entry.rs:1617–1640`)
still canonicalizes and may classify a relation trivial or reuse an existing
record. Emission through this owner is not proof of fresh queue insertion,
complete later drain, every future gamma replay, or mathematical equivalence of
the cached residual. The ordinary stored row relation is the owner selected
to support future reverse feedback; its comment at 218–219 is not a replay
theorem.

Other branches are material: initially unweighted input uses ordinary upper
storage or its existing-lower reduction (96–118); filter-only input becomes
ordinary upper storage (132–143); equal source/tail with empty right returns
(145–149); empty retained heads emit only `a <: t` with mixed remaining weights
(156–171). No universal claim that every negative row allocates gamma follows.
In particular, N's filter-only negative signature node is not itself a
`Neg::Row`: reaching R additionally requires an actual row-upper relation.

## Family checks, stack identity and lineage are different conclusions

Fresh declaration IDs are distinct even when `b`, C or its nominal families
coincide (`arena.rs:47–50`, `poly/types.rs:123–126`). Directed PUSH/POP combination
addresses the exact ID (`directed_weight.rs:16–42,145–179`), not a global family
lookup. The predicate operations above supply their actual locally created ID.
F is a check/registration procedure, and neither F nor N edits a complete
effect output by a family-wide erase operation. R transforms only its supplied
stack payload and constructs relations on its supplied source/tail.

Consequently these constructors/consumers supply no authority to delete an
independent same-family contribution on an unrelated route simply because its
family appears in C. The exact attachment/stack/row operation and its actual
route must first be established. This is a **local absence of a global deletion
rule**, not proof of H's universal contribution preservation.

The source also rules out a stronger careless claim: Oracle does perform
family-based matching within a selected row relation. `propagate.rs:1007–1041`
consumes a matching concrete upper head locally and emits payload constraints;
`row_effect.rs:1064–1089` coalesces duplicate negative heads with payload
constraints. Its residual cache at 180–202 merges equal keys, accumulating
derivations at 210–214. Nominal items need not carry a stack ID. These facts
prevent deriving a universal per-contribution lineage theorem from fresh IDs
alone. They do not prove unauthorized deletion of an independent original
source contribution: that requires the missing authentic route/attachment
correspondence. No source-qualified counterexample to H is claimed here.

Yulang3's Authoritative selection is stricter about residual identity: retain
separately constructed recipes despite row/key equality, with current/future
fan-out and exact outgoing context. Oracle's cache key is historical mechanism
evidence, not permission to replace that selected lineage policy.

## First Yulang3 gap and concrete owner handoff

At the pinned Yulang3 baseline, the first construction gap is
`candidate_source.rs:98,117–132`: formal descent starts Negative and rejects
concrete atoms in a composed-negative row. The actual constructor independently
rejects them in `candidate_effect.rs:1034–1070`, and the general signature owner
rejects them at 1507–1509. Thus there is no actual negative concrete action
from which to infer N's operational attachment. Preflight remains unchanged.

| Required native correspondence | Actual owner and remaining premise |
| --- | --- |
| Exact annotation set, scope, polarity and tail linkage | `candidate_formal_pair`, `candidate_formal_effect_port`, `candidate_signature_effect`: construct from the actual occurrence, with one set identity and exact operands/binder; present negative branches reject it. |
| Executable attachment operation | `candidate_signature_view:733–780` retains source weight but open-tail views have no closed executable filter; `candidate_context.rs:113–137` retains empty live words and a dormant unit-push marker. Metadata does not establish a nonempty operation. |
| Live receiver checks for current/future lowers | `candidate_context_execute_relation:2744–2815` consumes supported zero-word filters through exact Allowance bounds; `candidate_apply_effect` in `candidate_extrusion.rs:840–868` inserts and replays them. Need actual negative attachment context and its applicable receiver/fan-out correspondence. |
| Attached concrete residual and both obligations | `candidate_check_effect_operand:888–958` checks allowed atoms, forwards unmatched exact endpoints to the view tail, or reports mismatch. It does not construct R's lineage-owned gamma plus source feedback and exact gamma-to-tail relation. |
| Transport/use preservation | Capture, freshening, level extrusion, qualifying actual parent/copy SCC intrusion and replay must preserve the newly supplied attachment/recipe and correlated origins. Existing endpoint/zero-word transport alone is not that proof. |

The decisive next premise is an actual source-owned negative attachment
constructor and its live consumer contract preserving the original annotation
scope and contribution route. Do not discharge it by quantifying only over
currently admitted negative actions (an empty domain), assuming PUSH transitions,
or reconstructing authority from equal families/row IDs.

The earlier global induction and formal-port derivation left this same premise
open. Applying the existing proof-economy audit: negative source behavior and
consumer correctness are required A/B; reconstructing occurrence/scope/member
identity from solver equality would add D debt. Source formation already knows
those facts, so retain them at that owner. Actual contribution/route and residual
facts must be constructed by their operational owners. This audit supplies a
handoff, not proof progress on H or authority for a new representation/admission
rule. No third equivalent conditional proof is proposed.

## Verification, resources and frozen handoff

Read-only commands: `cat`, `rg`, `sed`, `nl`, `git status --short`,
`git rev-parse HEAD`, `git ls-tree -r --name-only`, and
`git show <revision>:<path>`; one in-memory Python/SHA-256 pass re-read the
frozen blobs and compared the named Yulang3 inputs to baseline. All four
primary-supplied Oracle hashes match. All ten named Yulang3 dependencies match
the pinned blobs byte for byte. Final artifact whitespace/link/hash checks are
static checks only. Early large output was truncated; quoted equations rely
on subsequent narrow owning-source reads.

No build/test/runtime Oracle/probe/measurement, Git mutation, additional worker,
external contact or shared-record edit occurred. At most three initial parallel
read commands; later source/hash commands run sequentially. No heavy process.
CPU/RAM and total process counts were not instrumented. Allocated wall budget:
45 minutes; the leaf stopped within it. Requested routing: `gpt-6.1-sol` / high
from the primary packet and normal configured defaults. Observed effective
runtime model/effort: unknown; role pins are absent, but configuration does not
prove runtime selection. No Astra invocation or override/reload claim.

Writes stop on handoff. Independent review and record integration are primary
owned.
The independent compiler-referee identified a major overreach in the original
activation paragraph: a positive Stack/NonSubtract task normalizes before the
upper filter sees its endpoint. This repair narrows only that activation claim
and states the omitted payload check explicitly. The task-level falsifier is
not an original source-program counterexample to H. Independent delta review
found no remaining issue in this repair scope; F's completed mutation-owner
premises and pair induction are unchanged.
Full H, negative source/consumer conformance, complete Call, soundness,
principality, lifecycle/normal progress, general negative admission and F5
replacement remain OPEN. One next action: independently review N/F/R on this
frozen artifact, then assign the source-owned negative construction/consumer
seam within its already selected internal gate.

### Dependency identity

SHA-256 values identify complete source bytes, not Git blob IDs.

| Oracle path at `a58eefc31` | SHA-256 |
| --- | --- |
| `crates/infer/src/lowering/signature_effect.rs` | `9eec35dcbe721cec20b8cab302c409ec0bc014781a36d5287a781a6cb9fe50ce` |
| `crates/infer/src/constraints/row_effect.rs` | `080472bb5dcb3f724e808ff745c6fba304cc7ea2574b8f8eb3e3466964e937c2` |
| `crates/infer/src/constraints/machine/bounds.rs` | `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7` |
| `crates/infer/src/annotation/constraints.rs` | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
| `crates/infer/src/lowering/mod.rs` | `244e5f8ea339d2e24aa1f8456e99072e4a491b97da58348a4e79eed188ce61a1` |
| `crates/infer/src/constraints/machine/propagate.rs` | `8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086` |
| `crates/infer/src/constraints/machine/entry.rs` | `00c70ca0938b24d4d2dd38de6598fe54217aebd28150ac279b52839046b340b8` |
| `crates/infer/src/constraints/mod.rs` | `ad3cf5fd60462cb1a08ef1a5d6fc57c4fd640148597bc3b331d09729616d8392` |
| `crates/infer/src/constraints/directed_weight.rs` | `de71ae7ed5a5aed22f3e5d35ca0ebcd52872ff965fcc22523a662cffdd6f28db` |
| `crates/infer/src/arena.rs` | `e407480ee4984e24ce214543bfe23ed83e34883129487878df034090688bd9db` |
| `crates/poly/src/types.rs` | `9211e62291b82e71e1b78763b83fe9f1d81e0fe4396d9e12d42e9a4a9b13b47c` |
| `crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |

| Yulang3 dependency at `c88685703` | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `crates/yu-solver/src/candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| annotation hygiene design | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| residual lineage selection | `d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98` |
| contextual attachment/admission design | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| top-level inference principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| original global hygiene proof | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| earlier formal-port bridge | `f61b3a4f720c120a0a25681cbc4160e162e13b32066198b3f07e460fbfa2f7ae` |

## Commit packet

- Exact completed lease: `notes/theory/2026-10-12-oracle-negative-stack-filter-source-proof.md` only.
- Baseline: `c88685703d3437a73ec4afa6121af5c275f5989f`;
  Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; named live Yulang3 inputs equal baseline.
- Claim/review: research-only N/F/R derivations. Initial review found one major
  activation overclaim; the frozen repair was independently delta-reviewed
  with no remaining findings. No H closure, implementation enabling or
  semantic adoption.
- Checks already run: narrow source-owner inspection, pinned-byte/hash
  comparison, artifact whitespace/link/hash checks; no builds/tests/execution.
- Proposed one-line message: `research: derive Oracle negative row filter construction and residual obligations`.
- Shared deltas left to primary/curator: link this bounded source note; record
  exact `b=x`, fresh set ID and filter-only negative wrapper; distinguish F's
  completed-owner coverage and R's two emissions from complete replay; retain
  the negative source-construction/consumer gap and full H as OPEN. No shared
  task/index/theory status record was edited.

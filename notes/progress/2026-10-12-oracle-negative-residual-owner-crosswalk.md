# Oracle negative filter and residual: source-owner crosswalk

Date: 2026-10-12
Status: frozen, unreviewed bounded source characterization; native residual equation OPEN
Producer: primary-assigned researcher leaf; no delegation
Baseline: `8ed50c86af67c2f43fd240dabe810fa2852e0ab1`
Branch: `research/simple-sub-intrusion`
Oracle checkout: `/tmp/yulang2-oracle-read`
Oracle HEAD: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this note only

## Objective, authority and premises

Identify the original Oracle producers and reached consumers for composed-negative
FILTER attachment and weighted Row-upper reduction, and distinguish their exact
outputs from the native Y3 contract. This packet supplies source correspondence
to the separate constructive proof lane. It neither proves Y3 conformance nor
repeats the existing payload-inventory proof or same-family falsification attack.

Authority: [annotation hygiene integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5; [attachment/admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§§3–6, especially §3.1 and the Negative-wrapper/Concrete-residual/Bound-insertion/
Opposite-replay clauses; [residual lineage selection](../design/2026-10-10-contextual-residual-lineage-selection.md)
“Selected policy”; [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5 and “Authority and integration”. The explicit decisions retain one attachment
identity per exact annotation atom set, independent same-family contributions,
distinct residual constructor lineages, both live relations and applicable
current/future delivery. General concrete-formal admission remains a later gate;
the withdrawn callback scheme supplies no expected output. Full restoration on
every abnormal path is not a premise.

Static premises are the frozen bytes below, resolved operands and valid arities,
one live allocation session before exhaustion, and normal completed owner calls.
Operational statements additionally require the indicated task to reach the named
consumer. Enqueueing an invariant or subtype obligation is not its discharge.
No actual negative Y3 constructor, route license, residual equation, complete
drain or source reachability is assumed. Oracle operands include invariant type
arguments; the inspected Y3 HIR fragment retains nullary `SourceEffectId`s.

The frozen dependencies are the [Oracle N/F/R derivation](../theory/2026-10-12-oracle-negative-stack-filter-source-proof.md),
[Y3 construction bridge](../theory/2026-10-12-y3-negative-effect-construction-bridge-proof.md),
[finite transition](../theory/2026-10-12-y3-negative-residual-transition-proof.md),
[native equation obstruction](../theory/2026-10-12-native-negative-residual-equation-proof.md),
[implementation seam audit](2026-10-12-y3-negative-effect-implementation-seam-audit.md)
and [recipe owner route](2026-10-12-negative-recipe-owner-source-route.md).
Their conditional claims retain their conditions. The actual demanded tail is
called `t` throughout this note: an earlier specialized/shorthand `g <: x`
equation supplies no universal identification of `t` with annotation binder `x`.

## Original Oracle sequence

All Oracle locators in this section are beneath `crates/infer/src/` in the pinned
checkout, except the explicitly named `crates/poly` owner.

1. **Compose variance and keep the original binder.**
   `lowering/mod.rs::SignatureLowerer::lower_neg`, 649–663, reverses Function
   argument ports and invokes `lower_ret_effect_neg` for the retained result
   polarity. `lowering/signature_effect.rs::lower_ret_subtractable_effect_row_neg`,
   162–178, calls `function_boundary_effect_stack_inner`, 319–333. A symbolic
   tail returns `signature_var(x)` immediately; `lowering/mod.rs:849–855` reuses
   the lowering-session variable map. Thus this branch has boundary coordinate
   `b=x`. Closed-row caching/fresh boundaries are different branches.
2. **Allocate one concrete-set attachment, then declare it.**
   `effect_row_stack`, 382–421, resolves all concrete atoms and allocates one
   `SubtractId s` for the nonempty vector `C`. `effect_atom_con`, 453–460,
   skips variable atoms without deleting the independent tail connection.
   `register_stack_facts`, 434–439, declares `(x,s,C)`.
   `arena.rs:198–209` supplies an Annotation boundary origin;
   `constraints/machine/entry.rs:915–944` retains declaration provenance,
   enqueues the fact and invokes drain. `crates/poly/src/types.rs:123–126`
   supplies fresh arena IDs. This grouping is set-wide, with resolved argument
   nodes retained; it is not a quotient of unrelated annotation occurrences.
3. **Return only the negative filter wrapper.**
   At signature lines 176–178 the returned node is
   `Neg::Stack { inner: Neg::Var(x), weight: FILTER(C) }`.
   `crates/poly/src/types.rs:319–323` makes FILTER with no stack entries.
   The fresh declaration ID is not a PUSH or POP in this returned node.
   The separate paired parameter owner, `annotation/constraints.rs:363–389,
   451–470,602–608`, supplies positive `STACK(Var(x),PUSH_s(C))`, negative
   `STACK(Var(x),FILTER(C))`, and `POP_s.with_filter(C)` predicates through
   `predicate_weights`, 921–924. `wrap_non_subtracts`, 848–851, wraps the
   positive return value. These objects share the actual paired creation;
   copying the negative wrapper alone does not supply its other operations.
4. **Check the true receiver before consuming its wrapper.**
   `constraints/machine/propagate.rs::step_subtype`, 38–56, calls
   `constrain_pos_lower_by_filter(constraint.lower,C,parents)` before clearing
   the wrapper filter and enqueueing the continuation to its original inner
   endpoint. `constraints/mod.rs:3584–3588` adds only right POP entries.
   The receiver is the actual positive endpoint, which may be a variable `a`
   distinct from `x`. Positive Stack/NonSubtract normalization at 11–37 happens
   first: the subsequent upper-filter call does not inspect accumulated task
   left weights. This does not establish checking of normalized-away payloads.
5. **Retain checks across the two completed mutation owners.**
   `constraints/machine/bounds.rs::constrain_type_var_lowers_by_filter`,
   3213–3255, registers on the encountered variable and checks every existing
   lower with its retained weight. `add_lower_bound`, 630–766, checks registered
   filters at 714 via `constrain_lower_bound_by_registered_filters`, 3285–3300,
   on each new semantic lower. `constrain_weighted_pos_lower_by_filter`,
   3303–3315, checks active left payloads as well as the node. `Var` recursion
   at 3350–3351 uses the same registration owner. Equivalent insertions,
   direct table mutations, later effect-family registration and terminal early
   exits are not silently included in this completed-event characterization.

The filter stage is a check plus continuation, not a residual allocation.
The actual residual stage requires a distinct task `u <: Neg::Row(I,t)`:
`propagate.rs:130–137` passes its source, actual heads, actual tail, incoming
weights and producer to `constraints/row_effect.rs::add_effect_row_upper_bound`,
88–234.

For that owner let `chi=(L,R)`. Its source statements determine:

```text
check actual negative heads I against L.filter                 [120–126]
L0 = L.with_filter(All)                                       [128–131]
A  = intersection of all active left payloads in L0            [794–815]
J  = collect_neg_effect_items(intersect(I,A))                  [153–155]
K  = subtract families(J) from every active left payload in L0 [174–179]
g  = cached gamma for (u,sorted families(J),K), or fresh level(u)
F  = u <: Row(J,g) @ identity                                 [216–221]
P  = g <: t        @ normalize_directed_mix(K,R)               [223–233]
```

This is an immediate source derivation for the reached nonempty-retained branch,
not a Y3 transition assumption. `A` is a common intersection, not the union of
the payloads and not automatically the annotation set `C`.
`intersect_row_items_with_subtractability`, 1005–1039, handles All, Empty, Set,
SetMany and complement forms; payload matches enqueue invariant argument
constraints at 1041–1061. `collect_neg_effect_items`, 1064–1089, locally coalesces
duplicate constructor paths while enqueueing invariant payload obligations.

`subtract_row_items_from_left_stack_weight`, 1190–1216, walks **every supplied
left entry**, retaining its exact ID, leading POP count and PUSH count, and
reconstructs PUSHs with the transformed family. `subtract_effect_families`,
1219–1273, handles finite and complement families and enqueues payload
obligations for matches. It takes a supplied weight, removed families and
parents; it takes no separate original contribution-fiber eligibility argument.
Retaining stack IDs alone therefore does not establish the required association
between an independent concrete lower fiber and this attachment's subtraction.
This observation stops at an owner-input gap, rather than asserting unauthorized
deletion or producing a source-qualified counterexample.

The live `ConstraintWeights::normalize_directed_mix` at
`constraints/mod.rs:3624–3637` invokes `DirectedWeights::mix` in
`constraints/directed_weight.rs:16–42`; the latter addresses entries by exact
ID and combines ordered POP/PUSH counts. This is an actual called owner despite
the module's `allow(dead_code)` attribute. The right input is the original `R`;
normalization is not a commutative operation assumed by the crosswalk.

Other branches do not use this two-relation construction: initially empty weights
use ordinary upper storage or existing-lower reduction at 96–118; filter-only
input after checks uses ordinary storage at 132–143; equal source/tail with empty
right returns at 145–149; `J=[]` emits only `u <: t` with directed mixed weights
at 156–171. These are Oracle facts, not new Y3 omission rules.

## Input/output crosswalk and source owners

| Required fact | Exact Oracle determination | Native Y3 owner and remaining premise |
| --- | --- | --- |
| Exact `(o,a,sigma,C,x)` and set identity `s` | Negative signature and paired annotation owners retain `x`, resolved operands and one fresh set-wide `s`. | HIR `module/source_annotation.rs` retains occurrence/member identities; `candidate_formal_effect_variable:979–997` owns scoped `x`; `candidate_context::source_weight:2174–2196` retains set/ordinals/scope. No negative concrete operation is emitted. |
| True receiver and check-before-consumption | `step_subtype:38–56`; bound-filter registration/current/future checks above. Normalized-away payload activation remains outside that claim. | `candidate_context_execute_relation:2744–2812` checks actual lower via Allowance and records discharge afterward, only for validated zero-word filters. `candidate_zero_word_filters:2649–2654` requires the weight to equal `boundary.closed_weight`; open views cannot satisfy it. |
| Actual demand `u,I,t,chi` | `add_effect_row_upper_bound` receives all four and producer directly; `t` remains unchanged in outgoing P. | `candidate_context_execute_relation` plus `candidate_apply_effect:840–863` is the reached contextual-demand seam. Current headed Allowance dispatch receives heads/tail but supplies no native residual reduction. Binder `x` cannot replace actual `t`. |
| Retained heads `J` | Common active-payload intersection then collection, with invariant argument obligations. | No native head-selection equation from authentic attachment and route is installed. `candidate_check_effect_operand:918–949` tests nominal Allowance membership; it does not apply local subtraction authority. |
| Residual context `kappa` | Oracle supplies concrete transformed left weight `K`; it does not supply a Y3 ContextExpr node or denotation bridge. | `ContextExpr:178–200` and detached `evaluate_context:1487–1533` retain order/sharing. `WithoutLeftFilter` changes only the filter; the separate reviewed inventory lemma rules out partial surviving PUSH-family change over unchanged inputs. No native transformation owner exists. |
| Lineage `lambda` and gamma `g` | `RowResidualKey` is `(source,retained_families,weight)`; 180–214 reuses gamma and accumulates derivations. It has no constructor-lineage key. | Selected Y3 identity is each actual residual creation. `RelationKey:203–206` is `(pair,context)` and supplies no residual lineage. Equal source/key/context cannot recover `lambda` or erase distinct creations. |
| Feedback `beta` and outgoing `pi_t` | Oracle emits identity feedback and exact `normalize_directed_mix(K,R)` projection to `t`; both share one WeightedResidual derivation. | Native `beta` and `pi_t` must be outputs of the same proved operation; neither identity nor an Oracle weight is automatically a native ContextExpr equation. |
| Preserve independent same-family lower | Oracle changes supplied payloads and checks actual nodes; no family-wide output deletion is authorized. These local owners alone do not establish full contribution lineage. | `Contribution:140–144` and its allocator at 864–886 retain effect/origin/instance, without an attachment/route argument. AnnotationMember retains its view, but the Allowance member branch uses only nominal effect membership. The actual license connecting fiber to operation remains missing. |
| Joint relation and origin evidence | Both emissions use `enqueue_row_derived_subtype`; canonicalization may be trivial or reuse a record. | `candidate_bound_origin_with_evidence:420–470` passes bound/origin/relation/cause jointly; `BoundEvidence::admit:530–573` groups `(BoundKey,RelationId)`. OwnerEmission explicitly retains authentication gaps. Do not form an origin × context product. |
| Both live installations and current/future fan-out | Ordinary upper/lower insertion has replay calls at `bounds.rs:714,727–741,897–905`. Emission itself is not completed drain or every future gamma replay. | `candidate_apply_effect:862–863` inserts then replays; `candidate_replay_bound:763–805` orders actual lower/upper inputs; `candidate_context_begin_replay:2911–2982` forms new fiber quadrants. `State::attach:2409–2421` and direct insertion alone schedule no replay. No residual installer or per-lineage activation owner exists in the inspected candidate modules. |

Oracle's key omits the actual tail, right weight and producer/derivation identity.
Distinct demands can reuse its gamma while emitting each demand's actual P and
retaining derivations. Such reuse establishes neither Y3's distinct-lineage
policy nor an exact-image congruence theorem. Y3 must preserve its selected
creation identities even when structural storage is shared. The source comparison
does not require copying Oracle's gamma cache or banning ordinary row equality.

The Y3 first producer remains `candidate_formal_pair:1035` /
`candidate_formal_effect_port:1054–1070` and
`candidate_signature_effect:1507–1538`: concrete-negative guards precede the
actual general tail lookup. Scheduling preflight is an additional separate gate.
`candidate_signature_view:733–780` gives open views `closed_weight=None`, and
`candidate_context_source:2488–2495` therefore provides identity, not FILTER.
Relabeling this open Allowance is insufficient: its matching-member branch
returns without the `q <: x` continuation; its nonmatching branch forwards to
the tail instead of applying a finite-filter mismatch. These static facts agree
with the frozen bridge notes; they are not new executed source examples.

## Minimal missing owner equation and stop

The shortest remaining bridge is one joint owner equation, before the generic
headed-Allowance dispatch loses the operation's authority:

```text
actual negative attachment (o,a,sigma,s,C,x), actual Row-upper demand
d=(u <: Row(I,t) @ chi), and their authentic operation/route and fiber parents
  => branch, lambda, J, kappa, g, beta, pi_t
  => live F_lambda=(u <: Row(J,g) @ beta), P_lambda=(g <: t @ pi_t)
     plus applicable current/future delivery with the same originating evidence.
```

The exact unresolved premise is the **native payload/contribution transformation
and its authenticated attachment-to-fiber association**, jointly determining
`J/kappa/beta/pi_t`. Oracle specifies its own weight operation; Y3's qualitative
contract specifies required ownership and preservation. Those facts do not
uniquely calculate the native equation or prove that every affected fiber is
licensed. A further `g <: x` requires the actual retained directed/contextual
connection from `t` to `x`. No missing term is reconstructed from family, row,
key or numeric ID equality.

Once the equation is independently established, correspondence must connect its
negative producer to the reached receiver check, both relation admissions, and
each initial/future lower event. Existing typed insertion/replay can carry the
consequences only with that association and explicit activation established.
This is an ordered handoff requirement, not a selected data layout or an
authorization to change compiler/tests. Stop here without a semantic proposal.

One recommended next action: give the constructive prover this exact joint
owner equation and source inputs for adjudication, keeping dependent native
implementation, general admission and original H OPEN until its premise is
established or a source-qualified counterexample is found.

## Checks, resource use and omissions

Static commands: bounded `cat`, `rg`, `wc`, Python line-range/complete-byte SHA-256
reads; startup `pwd`, read-only Git HEAD/branch inspection and Oracle HEAD
verification. No Git mutation occurred. All local reads were sequential, with
one lightweight command active at a time; the four-process concurrency budget
was not exhausted. Zero heavy processes, builds, tests, Oracle executions,
executable probes, measurements, mutations, seeds/ranges or child workers.
CPU/RSS and cumulative subprocess count were not instrumented; work finished
within the 30-minute allocation. Only this leased note was written.

Initial combined task/rule/note captures truncated; decisive owner statements
were subsequently read in bounded excerpts. One range read requested past the
end of `candidate_extrusion.rs` after printing the complete relevant owner and
returned IndexError. One initial arena locator named an absent path; the actual
`crates/infer/src/arena.rs` was subsequently read. No claim uses omitted output.
Broad task-history and exhaustive caller searches are not claimed.

Oracle independence: original Oracle implementations were read directly;
their inspected signature/row/bounds hashes match the separately frozen proof
snapshot. Y3 implementation was read separately. The two source characterizations
share accepted authority and normal-call assumptions; neither is an independent
execution oracle for Y3. No checker assuming supplied transitions was used.
The initial HEAD identities were verified, but this worker did not compare
every working file with its baseline Git blob; the primary owns that integration
check. The final snapshot recheck detects changes during this packet.

Unverified: actual negative source reachability, complete call/output traversal,
invariant argument discharge, parameterized Y3 effects, complement-form native
representation, all mutation/transport paths, gamma-upper feedback closure,
capture/freshening/extrusion/qualifying intrusion, mixed-cycle termination,
generalization, full hygiene H, soundness, principality and F5 cutover.
Changed source/authority/dependency bytes invalidate the affected characterization;
failed or terminal owner calls do not satisfy completed-event claims. No native
equation, counterexample to H, independent review or gate closure is claimed.

## Dependency snapshot

Complete-file SHA-256 values, unchanged at final recheck. Short path labels refer
to the exact directories given above and the linked frozen note names.

| Dependency | SHA-256 |
| --- | --- |
| Annotation hygiene integration | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| Attachment/admission design | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| Residual lineage selection | `d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98` |
| Top-level inference principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| Oracle N/F/R note | `b34465d7132259284389eb04507705239b46b40d6788f70567f3f58447689133` |
| Y3 construction bridge | `1a58d1134091e0b91acaf8014baca3a43f72b7764889ff15bbb3c382cd6245e6` |
| Finite transition note | `4a29e91ed916ecb87584f063e4c5885f7e19cb6a5706357c64e4557bc1ca2893` |
| Native equation obstruction | `b342082c43f5e0ebedb6736bc9b72ca722b0e7fa742e9575b579f7985be50779` |
| Implementation seam audit | `c4b0527f512da0e5e1c541d901a2ba0714b155dce4642760431f6bb7407ff8e3` |
| Recipe owner route | `759fbdb78f405f3e8e963e37f264e8c31097c25cb9fc9b29bfb256b3eb718d16` |
| Y3 `candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| Y3 `candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| Y3 `candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| Y3 `candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| Y3 HIR `module/source_annotation.rs` | `a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb` |
| Oracle `lowering/mod.rs` | `244e5f8ea339d2e24aa1f8456e99072e4a491b97da58348a4e79eed188ce61a1` |
| Oracle `lowering/signature_effect.rs` | `9eec35dcbe721cec20b8cab302c409ec0bc014781a36d5287a781a6cb9fe50ce` |
| Oracle `annotation/constraints.rs` | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
| Oracle `constraints/mod.rs` | `ad3cf5fd60462cb1a08ef1a5d6fc57c4fd640148597bc3b331d09729616d8392` |
| Oracle `constraints/row_effect.rs` | `080472bb5dcb3f724e808ff745c6fba304cc7ea2574b8f8eb3e3466964e937c2` |
| Oracle `constraints/directed_weight.rs` | `de71ae7ed5a5aed22f3e5d35ca0ebcd52872ff965fcc22523a662cffdd6f28db` |
| Oracle `constraints/machine/propagate.rs` | `8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086` |
| Oracle `constraints/machine/bounds.rs` | `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7` |
| Oracle `constraints/machine/entry.rs` | `00c70ca0938b24d4d2dd38de6598fe54217aebd28150ac279b52839046b340b8` |
| Oracle `arena.rs` | `e407480ee4984e24ce214543bfe23ed83e34883129487878df034090688bd9db` |
| Oracle `crates/poly/src/types.rs` | `9211e62291b82e71e1b78763b83fe9f1d81e0fe4396d9e12d42e9a4a9b13b47c` |

## Commit packet

- Exact completed lease: `notes/progress/2026-10-12-oracle-negative-residual-owner-crosswalk.md`.
- Baseline SHA: `8ed50c86af67c2f43fd240dabe810fa2852e0ab1`; Oracle SHA:
  `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none during this packet; complete identities above.
  Baseline blob comparison and current HEAD integration remain primary-owned.
- Claim/review: frozen unreviewed bounded source characterization; native
  equation, implementation, admission and original H remain OPEN.
- Checks already run: direct owner reads/search, HEAD identity verification,
  complete-byte snapshot/recheck and note link/whitespace/final-newline check.
  No execution/build/test evidence.
- Proposed one-line message: `research: crosswalk Oracle negative filter and residual owners`.
- Shared-record deltas intentionally left to primary/curator: link this owner
  matrix; retain actual `t` separately from `x`; record common-intersection J,
  all-entry payload transformation and cache-key omissions as Oracle facts;
  retain the joint native equation and authentic applicability/activation gap.
  No task, index, theory map, authority file or question bundle was edited.

Writes stop before frozen review.

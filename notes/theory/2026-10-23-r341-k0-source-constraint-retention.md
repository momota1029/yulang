# R341 — retention of the authentic K0 source constraints

Status: **frozen producer candidate, revision 1; fresh independent review required**.
Assignment: `R341-K0-SOURCE-RETENTION`; author:
`/root/r341_k0_source_retention_prover`. No coauthors or descendants.
This is a source-based hand proof, not machine checking, independent
certification, a whole native preservation theorem, or production authority.

## 1. Parent and result

The unchanged parent is the user audit, §§4, 6 S and 10.3. Its S0 statement is

```text
ValidK0(s) ∧ NativeComplete₀(s,S) ∧ ρ ⊨ H(S) ∧ Reifiable₀(ρ)
  ⇒ ∅ ⊢₀ s : ρ(v_s) ! ρ(ε_s).
```

Here `v_s` is the Definition-root Value row and `ε_s` is the body's Effect
endpoint. There is no Definition-root Effect row. `NativeComplete₀` retains
its audit meaning: authentic source collection/admission has finished, target
work is closed, and there are no typing conflicts or concrete pending K0
obligations. It is neither execution success nor `unresolved().is_empty()`.
The state, source, and row identities belong to the same native construction.

**Candidate result.** For every authentic `ValidK0(s)` construction reaching
such a completed live state S, every source inequality `q ∈ C_s`, including
the actual Definition-root Link, has its exact native interpretation entailed
by the physical bounds of S, or is reflexive. Consequently

```text
ρ ⊨ H(S) ⇒ ρ_s ⊨ H(C_s),
```

where the kind-preserving restriction/transport `ρ_s` is specified in §7.
Combining this result with reviewed R336 D1/G-sound and R337 J gives the
displayed S0 implication with precisely its original four premises. No
runtime/M premise is inserted. This remains an unreviewed candidate
application; Luna owns adjudication and any parent-status change.

The proof uses a property of the actual source family: **each generated
inequality has a row endpoint**. Lambda and Apply contribute whole Function
inequalities, but respectively of the forms `Fun ≤ row` and `row ≤ Fun`.
The argument therefore needs no general theorem that Function/Function
decomposition, its cache, or all discarded processing formulas preserve the
entire solution set. Those independent quantifiers remain OPEN.

## 2. Fixed interpretation and authenticated domain

Use exactly R336 revision 4's `ValidK0`, finite Value preorder, four-port
Function variance, finite Effect sets over the fixed Ω, independent source
rules, and `Reifiable₀`. The seven source forms are literal, enclosing-Value-
Lambda parameter Name, annotation-free single-binder Value Lambda, Apply,
else-complete If, Group, and binding-free Block/StatementBlock. All previous
K0 exclusions remain. Decoder-valid spelling and HIR ownership are retained;
the unused collected Value component of a Name is not its semantic endpoint.

For a same-sort native task q, let `φ(q)` be its independently interpreted
Value inequality or Effect inclusion. At a physical owner-side bound define

```text
β(owner,Positive,item) = item ≤ owner,
β(owner,Negative,item) = owner ≤ item.
```

This agrees with `bound_pair` (`candidate_context.rs:3311`) and reads actual
direct-row/exact-endpoint vectors, not scalar flags, provenance, a memo, or
acceptance. Let B(S) be their conjunction. Use the existing independent H
interpretation: B, pending typed tasks, initial/current/pending/saved processing
requests and actual caller transfers, unconsumed retained replay tasks, and
explicit remaining structural children. Inactive historical source facts,
completion bits and bare receipts add no formulas. In particular B(S) is a
subtheory of H(S) even after all active source-drain frames disappear.

Successful fresh and duplicate admission of q both have the semantic update
`H_after = H_before ∪ {q}` at admission, counting an actual caller/frame
owner until queue publication. This is the source-admission specification in
the audit and contract; it is not equality of solution sets. Successful store
receipts in `admit_collected_fact`, `admit_candidate_value_link_wide`, Lambda
admission and candidate-recipe admission all continue to the typed constraint
path. None returns merely because its FactId is duplicate. No prior entailment
is inferred from store identity.

## 3. Stable endpoints, exact extrusion and physical persistence

Reviewed R336 L0 supplies level 1 for all K0 rows and absence of high-level
extrusion copies. Reviewed R337 J supplies no Allowance, identity context,
default flow, and `candidate_context_execute = false` on every authentic K0
task. These are used with their successful-prefix premises, including
arbitrary symbolic latent Effect assignments; no Effect row is set to ∅ by
assumption.

Two source consequences make the exact-key argument below possible.

**Stable representatives/generation.** Candidate startup uses a fresh default
graph (`candidate_scheme.rs:2263`). `representative` returns a row itself if
there is no forest entry (`candidate_intrusion.rs:112`). The only successful
pending merge producers are qualified newly retained extrusion parents and
reactivation of groups containing such parents (`retain_extrusion_parent`,
`recapture_candidate_extrusion`, lines 304–420). L0 permits neither parent
creation nor a nonempty group to reactivate. The empty-pending settle branch
only clears dirty (`568–581`). `merge_candidate_rows` is called from that
pending-parent loop, and its generation update is at line 694. Hence that
loop, forest writes, generation increment and bound canonicalization are not
reached in this K0 construction. Raw row representatives remain themselves.
No claim about representative-changing K1 operations is used.

**Extrusion returns the exact endpoint.** This is stronger than saying that
no row is allocated. In `candidate_extrude`, a level-1 row at target 1 is
memoized unchanged and its bounds are not traversed (`candidate_extrusion.rs:
84–105`). Atoms and the two pure Effect endpoints are unchanged. For a
Function, Visit selects its four children with the actual variance; each row
child is unchanged. More generally induction on the finite structural term
DAG gives unchanged children; `Work::Function` then returns `original` under
`!changed` (`542–571`), keeping the original Term and ports. Row incidence
cycles are never unfolded by this induction. R337 excludes the effect-view
branches; K0 has no Tuple/record/variant constructor. No pending copied-bound
work is created. Therefore the `rewritten != key` dispatch branch is absent,
as is any retained-extrusion-rewrite entry, initially absent and installed
only by that actual rewrite branch (`lib.rs:14743–14762,15279–15292`).

Physical insertion chooses a same-kind owner and lane, appends the exact
payload, then reads that addressed slot back and checks the complete
`BoundKey` (`candidate_insert_bound_with_evidence`, lines 702–875).
Successful native source/dispatch/replay/diagnostic/acknowledgement operations
append or leave those vectors unchanged. They do not remove the cells.
Root boundary-0 capture reads the live bounds into a separate graph and
does not delete or reassign live row storage (`candidate_scheme.rs:2557–2827,
2829–2925`). Actual physical truncations at `lib.rs:9743–9790` belong to
failed-route rollback. Excluded incoming/local instantiation and local capture
do not become K0 callers merely because their helpers are in the same file.
The ordinary source driver propagates action failure with `?`, advances
`next` only after successful action return, and does not report a completed
result from a failed action (`candidate_source.rs:2316–2339,2351–2415`).
This proof concerns completed authentic runs, not acceptance of a resource-
failed private state or a theorem of exact abnormal restoration.

For clarity, a witness below is a mathematical choice of an actual physical
cell. It is not a new compiler certificate, new storage requirement or
identification of distinct source/relation/fiber incidences.

## 4. Completed row-dispatch witness invariant

Let E contain the following exact typed pairs on authentic K0 endpoints:

| Sort | Pair shapes in E |
| --- | --- |
| Value | row/row, positive base atom/row, row/negative base atom, positive Function/row, row/negative Function |
| Effect | lower in `{row,BottomPositive}`, upper in `{row,EmptyNegative}`, with at least one row |

Every member of C_s is in E after its native translation (§6). All source
occurrences remain distinct; E is a family of pair shapes for a proof, not a
deduplication of provenance. It also includes any equal exact pair reached
earlier through ordinary replay or a Function port.

At each boundary after a successful call to `dispatch_live_item`, prove:

> For every E key present in `typed_pairs`, either its endpoints are the same
> row or an actual surviving physical bound cell projects to that exact pair.

The initial memo is empty. The production insertion owner is
`record_typed_pair_admission` (`lib.rs:15295–15376`); the production calls
are in `dispatch_live_item`. Test-only fabricated insertions are not
constructors of an authentic state. The induction is on completed dispatch
calls, strengthened inside a call by retaining the current/initial q until
its physical witness has been appended.

For an E Value pair, the source cases of dispatch are exhaustive:

1. A current cache hit returns without a new memo insertion. Its key was in
   the memo at call entry, so the previous induction hypothesis supplies the
   physical witness or reflexivity. The cache Boolean supplies neither.
2. Canonical rewrite is absent by stable representatives. A retained actual
   extrusion rewrite is absent by §3. `incompatible_value_shapes` cannot
   return an incompatibility with a row endpoint (`lib.rs:16494–16525`).
   Bottom/Top shortcuts are outside this Value family. Tuple/record/variant
   and Function/Function tests require two structured endpoints and cannot
   select an E key.
3. In the remaining arm, any structural extrusion is exactly the identity
   by §3. `record_typed_pair_admission` precedes `apply_value_task`, but a
   successful return still executes that apply (`lib.rs:14705–14798`). It
   reaches `candidate_apply_value` (`16193–16201`). Equal endpoints return
   by reflexivity. Otherwise the selected owner is as follows:

| Exact q | Selected bound at level 1 | Physical lane |
| --- | --- | --- |
| Value row a ≤ row b | `(a,Negative,row b)` | `bounds[a].direct_upper_rows` |
| atom/positive Function l ≤ row b | `(b,Positive,l)` | `bounds[b].exact_non_variable_lowers` |
| row a ≤ atom/negative Function u | `(a,Negative,u)` | `bounds[a].exact_non_variable_uppers` |

The level tie in the first row selects a; it does not merge a and b or assert
equality. Each β projection is exactly φ(q). Appending and successful full
slot readback precede `candidate_replay_bound` (`candidate_extrusion.rs:
1115–1148`). The latter enqueues ordinary replay with `provenance=None`;
`candidate_context_drive_replay(...,None)` does not recursively dispatch a
child (`candidate_context.rs:4185–4228`). Thus an intermediate memo mark
cannot be observed by a reentrant duplicate dispatch before this append.

For an E Effect pair, R337 makes context execution return false, so the
`!context_consumed` guard permits `apply_effect_task`. On a miss, the memo
mark is followed by that call (`lib.rs:14439–14455`), which routes to
`candidate_apply_effect` (`13729–13738`). Equal rows are reflexive. Otherwise
row/row uses `(a,Negative,row b)` in
`effect_bounds[a].direct_upper_rows`; Bottom/row uses a positive exact lower
cell at the upper row; row/Empty uses a negative exact upper cell at the lower
row (`candidate_extrusion.rs:1151–1176`). Their β projections are the exact
source inclusions. This also appends before replay; no recursive dispatch
intervenes. A hit uses the previous invariant as in the Value case.

Dispatch of a key outside E does not create a different E memo key: Function
children are admitted as retained work and dispatched later, and direct
recording uses the current key. Such dispatches do not remove existing
physical witnesses. Later native allocations append fresh rows and do not
reassign old row ordinals. Diagnostic updates may alter the memo's diagnostic
fields, but not the physical cells. This completes the joint invariant.

**Exact relation/cache connection.** Source seed constructs its relation
from `candidate_context_pair(task_pair(task))` (line 3374 onward). Transport
asserts canonical pair alignment and returns the same relation when the key
is unchanged (`3767–3785`); context execution also asserts the exact key
(`3800–3809`). Function-port and replay constructors create relations for the
actual child task, then transfer that unchanged task with its relation. At
Dispatch, `context.processing` is that item's relation (`lib.rs:14295–14366`).
`mark_candidate_pair` records `completed[relation]=generation` only for an
exact canonical key (`candidate_intrusion.rs:423–455`), and
`pair_is_current` additionally requires memo membership (`lib.rs:13507`).
The stamp is indeed written **before** the append. During that interval q
is still in the current/initial frame, hence H still contains φ(q); at the
successful completed-dispatch boundary the physical witness exists. There
is no inference from the stamp alone to solvedness, no hidden use of a bare
relation as an H formula, and no claim about non-E cached structural parents.

## 5. Authentic Definition-root Link and retirement

Fix any authentic K0 source s and its body occurrence b. The collector uses
the semantic endpoint `endpoints[body]`, including the exact registered
formal for a parameter Name, and appends

```text
Action::Link { endpoint: endpoints[body], target: DefinitionValue root }.
```

The annotation-free root arm is `candidate_source.rs:2164–2165`. This is an
actual constructor, not an assumed arbitrary incoming task. Both native
endpoints are Value rows and the root has level 1. The action consumer at
2428–2432 resolves the lower endpoint and calls
`admit_candidate_value_link(...,30,lower,upper)`. The actual helper is in
`candidate_scheme.rs:4778–4788`; it admits/records the occurrence then calls
`constrain_live_value` for exactly `(v_body,v_root)` on every successful
store receipt.

`start_typed_drain` retains q as the initial request, seeds the exact
relation, and enqueues q (`lib.rs:14186–14239`). Queue pop transfers q to
`frame.current`; transport/context preserve its pair. A successful synchronous
drain return must have processed that enqueued initial item: Transport only
reaches Diagnostics when the queue is empty, and every popped item passes
the Context and Dispatch stages before its current slot clears. No fairness
or solver-termination theorem is needed for this statement about a completed
finite return.

At the root-Link Dispatch, a hit has an earlier physical witness by §4; a
miss marks then appends `v_root` to
`bounds[v_body].direct_upper_rows`, with the exact negative bound readback.
Its projection is `ρ(v_body) ≤V ρ(v_root)`. Reflexivity handles equal row
endpoints without requiring a cell. No equality of those row types is claimed.

Before append q remains in P. After append B contains q as well as the active
copies. Clearing current therefore retains q through B. Replay child
acknowledgement can retire its retained work but cannot remove this cell.
Diagnostics, source-drain-completion attribution, acknowledgement processing
and `ReturnReady` frame pop at `lib.rs:14918–14945` leave B intact. Inactive
receipt history is not needed for the conclusion. Later source/capture steps
preserve the cell by §3. Therefore final `H(S) ⊨ v_body ≤V v_root`.

This proves the root's requested obligation at retirement. It does not imply
whole-frame equality of solution sets for every other initial, designated,
processing or Function-port obligation owned by that frame. R339's separately
reviewed two-bound witness can discharge its actual replay-child instances;
it is not used to certify this source Link or those other families.

## 6. All seven authenticated constructor cases

For every occurrence of every permitted form, take the following exact
source family. Each row/endpoint is its authentic one from this same
construction. The table quantifies over all conditions, branches, prefixes,
binders and calls; it does not select a successful example or evaluate an If.

| Form | Entire generated source family | Actual emission/admission owners |
| --- | --- | --- |
| Literal c | `Atom(c) ≤ v_c`, `v_c ≤ Atom(c)`, `BottomE ≤ ε_c`, `ε_c ≤ EmptyE` | `candidate_source.rs:1558–1573`; `Action::Fact` and `lib.rs:11481–11524` |
| Parameter Name x | semantic Value endpoint is precisely the registered enclosing formal; `BottomE ≤ ε_x`, `ε_x ≤ EmptyE` | endpoint map `candidate_source.rs:1131–1137`; Name facts `1724–1741`; no constraint on the unused Name Value component is substituted |
| Value Lambda λx.b | `Fun(a,e_entry,e_return,v_b) ≤ v_λ`, `e_entry ≤ e_return`, `ε_b ≤ e_return`, `BottomE ≤ ε_λ`, `ε_λ ≤ EmptyE` | recipe `candidate_source.rs:2050–2077`; creation facts `shadow_apply.rs:3610–3619`; Function and two fresh Effect rows `lib.rs:11557–11700`; no default or Comp branch is in K0 |
| Apply f a | `v_f ≤ Fun(v_a,ε_a,κ,v_apply)`, `ε_f ≤ ε_apply`, `κ ≤ ε_apply` | `shadow_apply.rs:4085–4158,4167–4185,4207–4224,4247–4270`; κ is the actual fresh invocation row, shared with that demand's return-Effect port |
| Else-complete If | every `v_condition ≤ Bool`; every branch (including else) `v_branch ≤ v_if`; every condition and branch `ε_child ≤ ε_if` | `candidate_source.rs:1632–1655`; `Action::ValueConstraint` uses the authentic semantic endpoint and the same Link helper; Effect facts use `Action::Fact` |
| Group | `v_child ≤ v_group`, `ε_child ≤ ε_group` | `candidate_source.rs:2038–2049`; Group recipe `shadow_apply.rs:3458–3463,4195–4205` |
| Binding-free Block/StatementBlock | `v_final ≤ v_block`, `ε_final ≤ ε_block`; every expression-prefix `ε_prefix ≤ ε_block` | `candidate_source.rs:2078–2101`; final Group recipe plus prefix facts; prefix values remain discarded and expression order is retained |

The Function port order is `(argument Value, argument Effect, return Effect,
result Value)`. Every displayed inequality belongs to E. No source
Function/Function relation was substituted for a row/Function relation; a
later propagated structural comparison remains separate native work.

Each Value/Effect Fact, candidate recipe, Lambda recipe and explicit
ValueConstraint continues through its actual typed admission on a successful
receipt. Source `next` advances only on successful completion. Thus for each
displayed q, the successful synchronous drain has dispatched its initial q.
The completed-dispatch invariant supplies a physical witness or reflexivity.
That witness persists through the remaining construction, including all
later calls, cyclic replay and root capture. The authenticated Name equality
is endpoint identity, not an inequality guessed from a collected component.
Together with §5, this exhausts C_s, proving the stated retention claim.

## 7. Explicit source-row transport and S0 application

Give source rows tagged identities; integers from different sorts are never
identified. Define a construction map ι into the same native session:

| Source row | Native image ι |
| --- | --- |
| expression/root component of kind k | the corresponding `live_components[position]`, with checked kind k and its dense ordinal |
| Lambda formal for parameter p | Value row `parameter_live_base + parameter_position(p)` used by its actual Lambda recipe and every resolved Name endpoint |
| Lambda entry and return Effects | the two rows allocated by that occurrence's `admit_lambda_fact`; read in the exact negative-entry and positive-return Function ports |
| Apply invocation Effect κ | that occurrence's actual allocated invocation row, also retained in its negative Function return-Effect port/native interface |

Component initialization allocates separate Value/Effect ordinal spaces and
records kind (`lib.rs:10344–10398`). Lambda and Apply allocators use
`fresh_effect_at_level` and retain their actual ports (`11557–11700`;
`shadow_apply.rs:4097–4158`). Allocation appends rows without reusing ordinals
(`lib.rs:10456–10516`). The map keeps separate occurrences' auxiliary rows
separate. An unused Name component, if included in the allocation census,
retains its own image; the Name's semantic endpoint instead selects its
formal. It is not a quotient equating those two rows.

Let `D_s=FV(C_s)` together with the named output endpoints. It includes all
row occurrences nested in source Function terms: formals, body/result rows,
Lambda entry/return Effects and Apply invocation Effects, not just visible
expression components. There is no remaining auxiliary row hidden inside a
source endpoint: the constructor table above lists all fresh rows. An unused
Name Value component can be omitted from D_s because it occurs in neither
C_s nor its semantic output. It is never assigned the formal's meaning by
omission.

For final native assignment ρ define

```text
μ(r:Value)  = Value(repV_S(ι(r).ordinal)),
μ(r:Effect) = Effect(repE_S(ι(r).ordinal)),
ρ_s = (ρ ∘ μ)|D_s.
```

This is sort-preserving. In this K0 run §3 proves both representatives are
identity, so μ is exactly ι on its domain. No general representative-changing
transport theorem is silently imported. Extend μ structurally, fixing atoms,
the two pure endpoints and all four Function positions and their polarities.
Induction on finite source term structure yields

```text
interpret(t,ρ_s) = interpret(μ(t),ρ).
```

For rows this is the definition; atoms/pure endpoints are fixed; the Function
case applies the induction hypotheses to its four same-kind arguments.
The preorder and inclusion are fixed before construction, so this equality
transports each source inequality, without a new native/source typing axiom.

Now fix arbitrary s,S,ρ satisfying the four original S0 premises. Authentic
complete collection/admission supplies `CompleteK0Construction(s,C_s)` and
the map ι; this is already part of `NativeComplete₀`, not an added runtime
premise. For every q in C_s, §§4–6 give `B(S) ⊨ μ(q)` or reflexivity.
Since B is part of H, `ρ ⊨ H(S)` gives every μ(q), and the transport identity
gives `ρ_s ⊨ H(C_s)`. Restricting the given `Reifiable₀(ρ)` witness along
the kind-preserving μ gives `Reifiable₀(ρ_s)`; finite Function terms remain
finite when their finitely many row assignments are substituted. There is
no unfolding of cyclic bound incidence or new model-existence assertion.

Reviewed R336 D1/G-sound, with R337 J supplying its ordinary metadata premise,
therefore derives the body's judgment at `ρ_s(v_body),ρ_s(ε_body)` and uses
the authentic Link with Value subsumption to obtain

```text
∅ ⊢₀ s : ρ_s(v_root) ! ρ_s(ε_body)
       = ρ(v_s)       ! ρ(ε_s).
```

The displayed equality abbreviates equal output assignments through μ, not
an equality rule between unrelated types or effects. The Effect endpoint is
unchanged. This applies the retention result to the unchanged S0 source-
typing implication. S0 plus M is a separate composition; M is not used here.

## 8. Reuse, limits and mutual TODOs

Reused: R336 revision 4's exact algebra, source judgment, L0, root Link and
Value subsumption; R337 J's reviewed successful-prefix metadata result and
its source pins. R339 is compatible with, and supplies only, the already
reviewed actual ordinary replay-child two-bound family. The new argument
supplies the source-row family directly rather than treating it as a replay
child. R338's independent β/H notation is retained, but neither disputed
admission equality nor its pending amendment is a premise. R340 continuation
proof and its pending S0/S0+M amendment are not premises of this proof.

No source-qualified counterexample was found. A hypothetical state with an E
memo but no prior completed owner append is not reachable evidence. The
decisive falsifier remains an authentic NativeComplete K0 state S, exact
occurrence q∈C_s and explicit final-H solution ρ violating μ(q). A missing
production mutator that can delete a witness, an E dispatch branch that can
complete without it, or a reachable high-copy/generation change contradicting
§3 is a blocking source-census finding even before a concrete valuation is
constructed.

All seven source cases and the root are covered in this candidate. The exact
remaining acceptance premise is fresh independent review of this invariant,
constructor completeness and row map, followed by Luna adjudication. There is
no additional unproved runtime-realization premise hidden in its S0 step.
The broader N/cache theorem, non-E Function/Function retirement, designated
and foreign processing obligations, source completeness, W, Z, M, removal of
the four S0 premises, principality, original A/B, catalog and production remain
OPEN. The proof makes no claim about export/I-publish witness transport.

Mutual TODO `R341-RETENTION-REVIEW-1`: Luna owns fresh non-contributor review
of frozen proof/census plus pinned sources. First discriminating evidence:
challenge (a) exact identity extrusion, (b) all production E memo insertion
and physical-deletion paths, (c) absence of nested dispatch before append,
and (d) full kinded support/transport into D1. Output: bounded acceptance or
the first exact source-qualified missing case/falsifier above. No code change
is requested; the present argument uses actual constructors. A provisional
read-only state view, if later needed to exhibit a falsifier, requires its
own Luna allocation and must expose the exact physical E witness/history;
an execution test of assumed transitions would not prove this theorem.

Next step: freeze this result and return its two hashes to Luna for the
contract's independent review seam. No in-envelope writes continue while
waiting. This producer cannot certify the result or appoint its reviewer.

## 9. Frozen inputs and resource receipt

Baseline supplied by Luna: `d6610bb03cd1f9037df834982722e0022fc79209`.
No Git command was used. All following byte hashes were checked by
`sha256sum`; they matched the contract or its named reviewed source manifest.

| Input | SHA-256 |
| --- | --- |
| R341 contract revision 1 | `62cb4018db42e0266f0f357ed6f44c187d6397865905b68487fe143d00250769` |
| user audit | `b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895` |
| R341 primary source census | `729c224785d42ee3577351e6a001668fe97a17fb2323aa532f52bbc8a1be0eeb` |
| R336 D0/D1 rev4 | `4bcbe71ec9f2372baca884e3db737c16fc19ad2a51103965ade5ca4c2ecf4973` |
| R337 context proof | `e14b8125a505c3001021396b8c6e949e3b0a58f61ecf2785f915dbdde65dfc62` |
| R337 source census | `771c3c8ab2a69336579c78a7583097b8d1839bf0d6fe97f2e69da27e77500e6a` |
| R339 replay-child proof | `8797013ab5ea77655629fce45031fb28e1c5557979c1f213b9268abd31080c87` |

| File in `crates/yu-solver/src/` | SHA-256 |
| --- | --- |
| `candidate_source.rs` | `0dc798e48e70505093e52b31b2569e3b2d8ff1dee663095176aaf547ccb3289b` |
| `lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `candidate_context.rs` | `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5` |
| `candidate_effect.rs` | `d156fdbf0300387a5aa036053a2cc7eeb6312a803aaf38838e30dd2731ca4945` |
| `candidate_scheme.rs` (R337 manifest; actual Link helper/capture) | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `shadow_apply.rs` (R337 manifest; actual recipes) | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |

Requested model/effort: configured `gpt-6.1-sol` / `high`. Observed effective
model/effort: `UNKNOWN` / `UNKNOWN`; no runtime metadata was supplied to this
worker. Actual worker ID is the task path above; own runtime session ID is
UNKNOWN. Containing primary session read from current state:
`4a30d8bc-cf58-442a-ac35-a6026b4e35b5` (not asserted to be this child session).
First observed clock: `2026-10-23 06:29:47 UTC`; launch clock and exact total
active seconds are UNKNOWN. Grant: 2,400 seconds, no carryover; conservatively
retain the full grant charge. The handoff records the final clock.

Checks: direct source inspection, production-caller/mutator searches, hand
induction and byte hashing only. No tests, Cargo/build, execution probe,
network, Git, model-policy change, nested CLI or child launch. The only new
paths are this note and
`tasks/agent-loop/inbox/20261023-r341-k0-source-retention-prover.md`; no scratch
outputs. On submission both paths are frozen and all writes have stopped.

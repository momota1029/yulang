# Native replay coverage: checked scheduling and local Value/Effect blocks

Date: 2026-10-26
Status: constructed and kernel-checked finite lemmas; source induction candidate;
independent review pending; original whole-source saturation/soundness OPEN
Assigned baseline: `bf81a1bd444b3bcbecca6b754ea6fb603262f368`, branch `yulang3`
Author: bounded generic proof leaf `/root/native_saturation_construction`

## 1. Original claim, result, and historical correction

The unchanged A/B parent ranges over every supported original source program
and its actual lawful finite inference history. Successful native processing
must supply one joint source-lawful interpretation, with original Call,
optional records, effect contexts, scopes, fresh-use maps, intrusion
qualification, principal coverage, and normal progress intact. A certificate
already supplied by original `G_call` is not manufactured by `nativeOk`.

This packet proves finite scheduling facts in
`YulangClosure.NativeReplayCoverage`; it applies the live-index facts to the
actual complete-block constructor, and gives a bounded paper extension from
the reviewed all-local Value block to plain all-local Effect rows. It does
**not** obtain full native syntactic saturation or a model of every NativeTerm.
No `RegularSub`, solution, local semantic preservation, or saturation premise
appears in the finite scheduling theorems. Their source applicability still
has explicit operational premises below.

The initial investigation rediscovered that a saved total opposite count does
not preserve an initial atom's position if callbacks grow the direct prefix.
The primary identified the existing reviewed result before a redundant new
experiment was run. The relevant prior results are:

* `2026-10-13-restoration-temporal-coverage-proof.md`: complete Value-block
  activation, using equal mapped levels and DL/DU/EL/EU order.
* `2026-10-13-fresh-use-restoration-disposition-proof.md`: authentic capture,
  immediate preparation, and later upper-restoration compensation.
* `../progress/2026-10-13-restoration-live-index-pair-audit.md`: the actual
  Function callback that shifts a saved live index; no source failure claim.
* `../design/2026-10-11-private-candidate-suspension-contract.md`, section 4:
  selected saved-count/live-canonical-read semantics.

The illustrative Lean shifted-index lemma records this established boundary.
It is not new progress, a native bug, or grounds for a snapshot repair. The
useful new checked artifact is the finite scan and whole-block assignment
proof; the broader source argument is separately reviewable.

## 2. All eight lanes and the actual work owners

Let `q_k` be the current same-kind representative function. Physical occurrences
remain distinct even if their normalized directed constraints coincide.

| Physical lane | Normalized directed requirement |
| --- | --- |
| Value direct lower | `q_value(item) <= q_value(owner)` |
| Value direct upper | `q_value(owner) <= q_value(item)` |
| Value exact lower | `rigid_value(item) <= q_value(owner)` |
| Value exact upper | `q_value(owner) <= rigid_value(item)` |
| Effect direct lower | `q_effect(item) <= q_effect(owner)` |
| Effect direct upper | `q_effect(owner) <= q_effect(item)` |
| Effect exact lower | `rigid_effect(item) <= q_effect(owner)` |
| Effect exact upper | `q_effect(owner) <= rigid_effect(item)` |

`normalize` implements this table. Rigid identifiers retain their source-table
interpretation. In particular it does not interpret Allowance as an opaque
equality atom. The actual insertion owner
`candidate_insert_bound_with_evidence` (`candidate_extrusion.rs:702–875`)
canonicalizes both endpoints, chooses the lane, appends a physical slot, reads
that exact slot back, and emits its evidence only after matching the expected
BoundKey. Reading only a row's lower vectors loses half the stored graph.

Both `candidate_apply_value` and `candidate_apply_effect`
(`candidate_extrusion.rs:1115–1171`) store row/row constraints on one side:
when `level(upper) <= level(lower)`, append upper to lower's direct uppers;
otherwise append lower to upper's direct lowers. `selectRowBound` is that
branch and `equal_level_row_bound_is_upper` proves its equal-level case.
Canonical reflexive pairs return first. Levels therefore affect storage,
not the orientation of the normalized logical constraint.

`candidate_opposite_count`/`candidate_opposite_bound` (`:877–937`) enumerate
the opposite direct vector followed by its exact vector. Ordinary
`candidate_replay_bound` (`:1070–1113`) queues children using `None` provenance.
`candidate_context_consume_replay_child` (`candidate_context.rs:4156–4200`)
enqueues without running the typed child in this mode. Thus those physical
vectors do not change inside this ordinary enumeration: all current opposite
positions are generated before the enclosing typed drain resumes.

`candidate_context_begin_replay` (`candidate_context.rs:3993–4079`) implements
exactly two products of incidence fibers, newest first:

```
newLower × (newUpper ++ oldUpper)
oldLower × newUpper
```

The checked `replay_quadrants_cover` proves these plus the old/old product
cover the full current product. The source interpretation of old/old is its
previously retained dependency and its outstanding/completed work disposition;
the theorem does not assume that disposition completed merely because heads
advanced. `incoming_use=true` resets the old heads to empty and bypasses the
ordinary dependency skip, so `incoming_replay_covers_all` applies directly to
the actual restoration lookup. Ordered lower/upper RelationIds, BoundKeys,
contexts, and source sets remain in each `Dependency::Replay`.

## 3. Checked finite scheduling theorem and its applicability

`Owner` contains finite lower/upper occurrence lists and pending/completed
occurrence pairs. `step` is a concrete finite program:

* append a lower and enqueue its product with all current uppers;
* append an upper and enqueue its product with all current lowers;
* merge incoming lower/upper lists and enqueue the complete resulting product;
* consume one queued pair into completed.

`Route` runs a finite list of these actions only when committed. A rejected
route contributes no events. The root theorem is:

```
completed_routes_cover (routes : List (Route α))
  (finished : (runRoutes {} routes).pending = [])
  (l u : α)
  (hl : l ∈ (runRoutes {} routes).lower)
  (hu : u ∈ (runRoutes {} routes).upper) :
  (l,u) ∈ (runRoutes {} routes).completed
```

The coverage invariant is proved from this program, starting with empty lists;
it is not an input to the root theorem. Induction uses the new endpoint's
Cartesian product, the complete merge product, and conservation when one
pending item moves to completed. This is an actual finite scheduling result,
not source soundness by definition. Section 2 identifies the corresponding
ordinary physical-pair enumeration and delta-generation loops; applying the
scheduler also requires preserved pending/completed dispositions for work
skipped through recorded heads or dependency reuse. A restoration is **not**
automatically one such action:
its selected live indices can omit a formerly present atom, and the temporal
whole-block argument below is needed.

For merge, `merge_candidate_rows` (`candidate_intrusion.rs:599–708`) copies
both bound sides while retaining the old physical storage, changes the forest,
canonicalizes bound evidence, increments generation, reopens the supplied
root, then calls ordinary replay for every target lower. No typed children run
inside these loops, so every resulting physical target lower/upper pair is
visited. Each visit uses the recorded replay heads and emits only the new
quadrants; an already retained Replay dependency can also suppress a new child.
This establishes physical-pair visitation and incremental generation, not a
newly queued full product. Refining the abstract full-product `.merge` action
therefore still requires the old work's pending/completed disposition and
currentness after the generation change. Joint transport of every original
incidence at a third owner, and validity of later scheme reuse after that merge,
are also separate obligations. None is discharged by the physical loop alone.

`α` can include transaction epoch, append ordinal, kind, and physical slot.
The epoch is erased proof data, not runtime metadata. A reused numeric
`ReplayOperationId` after rollback is not a permanent global event identity.
Commit erases runtime retired operations without erasing an accepted ghost
event; rollback cancels the entire uncommitted ghost suffix. This corresponds
to context checkpoint/rollback (`candidate_context.rs:2081–2173`), which undoes
cursor progress, removes new operations, resets the next ID, truncates
evidence/dependencies and restores bound-incidence heads, and to retirement at
`:2190–2245`. Pending operations committed during suspension stay pending;
their ID's disappearance alone is never treated as child completion.

## 4. The actual live-index scan and complete-block coverage

The checked `scan` enumerates exactly the saved range
`0 .. direct.length + exact.length` and at index `i` reads

```
(direct ++ directGrowth i ++ exact ++ exactGrowth i)[i]?
```

It allows arbitrary callback suffix growth; it does not freeze endpoints.
`scan_direct` proves every original direct entry is read despite growth of
either vector. `scan_exact_without_direct_growth` proves every original exact
entry is read when the direct prefix does not grow. They prove these claims
by selecting the original physical index, showing it lies below the saved
count, and calculating the live indexed lookup. There is no subtyping premise.

`temporal_three_case_coverage` uses exactly three physical snapshot facts:

| Captured pair | Assigned restoration | Snapshot membership used |
| --- | --- | --- |
| DL with any upper | upper restoration | mapped DL is already in direct lowers |
| EL with DU | lower restoration | mapped DU is already in direct uppers |
| EL with EU | upper restoration | mapped EL is already in exact lowers |

The theorem's premises are these memberships and the explicit scan with a
constant lower-direct prefix. They are not semantic validity or prior replay
coverage. Current capture's Value branch is still DL, DU, EL, EU
(`candidate_scheme.rs:2137–2187`); freshening serializes each accepted bound
before moving the outer cursor (`begin_candidate_fresh_bound`, `:4587–4638`,
and retained Local cursor at `:5082` onward). Prior callback appends can add
other entries before the chosen slot, but they do not remove that slot.

The actual restoration owner (`candidate_extrusion.rs:970–1068`) saves one
count, canonicalizes at each live read, retains its active replay handle,
and advances only after that replay has returned. Thus a successful completed
restoration performs the whole scan. The lower-direct prefix condition is
derived from the concrete equal-level callback direction under the constructor
specialization below; it is not asserted for arbitrary executions.

## 5. Paper extension: plain local Effect rows with the same map

This extends the reviewed local Value-block mechanism to live Effect rows in
the four Function ports. It is a bounded constructor lemma, not a restriction
on the original accepted source domain. Use specialization P:

1. An authentic immediately captured graph has only local, generic Value and
   Effect rows, and preparation takes the fresh-allocation branch for every
   distinct captured representative. There is one use level `k` and one
   prepared map. The current representative/level/generic guard is checked,
   not inferred from the stale `Row.local` bit alone.
2. Effect endpoints in this mapped closure are only EffectRow, BottomPositive,
   and EmptyNegative. There are no capture-incidence Allowance records and no
   reverse-effect-frontier additions. Boundary zero is a sufficient reason
   for the latter branch to be disabled; the claim does not require all future
   source generalizations to use that boundary.
3. Retained contexts and callback-local contexts are identity. Scoped flow has
   transformer zero and no demand; no source wrapper, Call demand, support,
   contribution, annotation, role/field-tail activation, or external mutation
   is interleaved with this block. There are initially no retained extrusion
   parents and the typed worklist is idle.
4. The entire restoration block succeeds and completes. This is a termination
   and availability premise of the bounded trace claim, not a theorem that
   those properties hold for every source program.

Current preparation (`candidate_scheme.rs:4248–4283`) shares the
`canonical_rows` map across both kinds and allocates each eligible Value or
Effect representative at `use_level`. The same reconstructed term map supplies
all four Function ports. Thus every row reachable by these children has level
`k`; this equality is derived from the constructor under P1.

Induct on actual callback dispatch. For both row kinds the equal-level branch
is negative/upper storage, so it cannot append a direct lower. A non-row lower
received by a row appends an exact lower; a non-row upper appends an exact
upper. Plain effect leaves are handled by the BottomPositive success branch
of `candidate_check_effect_operand` (`candidate_effect.rs:1237` onward), and
introduce no new rows. Identity, empty-scoped context execution adds no
Allowance registration. These statements exhaust P's callback writes.

Structural extrusion of a mapped row sees `original_level <= target` and
returns it unchanged (`candidate_extrusion.rs:100–106`); no copy parent is
created. Parent-free intrusion settlement (`candidate_intrusion.rs:568–594`)
does not redirect representatives or lower levels. Therefore the next callback
has the same level and representative invariant. The reverse frontier and
capture-incidence cases were explicitly excluded in P2; they cannot be
silently hidden inside the plain Effect argument.

With those two Effect-specific prefixes absent, Effect capture has the same
DL, DU, EL, EU physical order as Value capture (`candidate_scheme.rs:2188–2255`).
Callbacks cannot grow a lower-direct prefix; outer restoration cannot insert
its next DL until the current restoration returns. The three temporal cases
therefore apply independently to each kind, using the **same** prepared map.
Every captured lower/upper record pair carrying original relations receives an
incoming-use product lookup. Fresh transport before physical admission
(`candidate_scheme.rs:4612–4638`) attaches both mapped fibers; incoming replay's
complete product contains their ordered pair even when ordinary replay had
previously advanced its heads. This uses the checked product lemmas.

Function dispatch (`lib.rs:14804–14853`) generates exactly:

| Port | Child comparison |
| --- | --- |
| Argument | upper.argument <= lower.argument |
| ArgumentEffect | upper.argumentEffect <= lower.argumentEffect |
| ResultEffect | lower.resultEffect <= upper.resultEffect |
| Result | lower.result <= upper.result |

`function_children_exact` checks that table. The staged dispatcher at
`lib.rs:14955–14981` admits each distinct port and enqueues it before moving
the cursor. The two Effect ports are not omitted or identified with Value
ports. Under P they stay in the closure just proved. Actual Call-demand
transformers in `candidate_function_port_admit` are explicitly outside P3;
their semantics and source certification remain untouched and open.

The conclusion is record-level activation and receipt delivery, as in the
reviewed Value result. It does not recover physical occurrences deduplicated
by capture or prove source-admission authentication from endpoint coincidence.

## 6. What native completion proves, and the remaining original premise

`step_typed_drain` (`lib.rs:14288–14420`) settles dirty intrusion when the queue
empties, proceeds to Diagnostics only when no item remains and dirty is false,
finishes diagnostic propagation, then acknowledges children and returns.
`candidate_step_typed_drain_terminal` (`:14881–14949`) completes the owned acks
and publishes the return receipt before removing the frame. A successful
incoming replay therefore reaches Context and Dispatch before its completion
receipt, or uses the actual valid current relation's memo. `pair_is_current`
(`lib.rs:13507` onward) must be interpreted with its relation/generation guard;
endpoint equality alone supplies no contextual completion witness.

Availability success can retain type errors. Even availability success,
`errors.is_empty()`, and an empty worklist jointly establish only completion
of the obligations actually admitted/generated by these owners. They do not
prove that every original-source obligation reached an owner. `finish_candidate`
(`lib.rs:10681–10693`) checks unresolved active field-tail selection then
packages `finish_observations`; it does not run a final semantic row-model
certificate checker. This is an owner-specific limitation, not a generic
empty-queue slogan.

For the adjacent row-model construction, the missing input remains a finite
same-kind table C containing normalized original requirements, with syntactic
row/row reachable-head inclusion, row/head lower-head expansion, and exact
head/head structural child clauses. This packet supplies local ordinary
product generation and the P-specialized temporal activation component. It
does not instantiate all those fields for arbitrary native histories.

The next unresolved native case is a genuinely mixed/shared FreshUse block
with its original captured incidence and lawful joint transport, including
callback direct-lower growth, actual merge/representative changes, contextual
Effect operands and later reuse activation. The reviewed shared-row audit
already has a missing direct Function comparison with later child
constraints; another shifted-index probe is not the next experiment. The
discriminating next task is to construct its exact original-relation transport
through all four ports and the later reuse, or exhibit an authentic source
failure after all compensating dispositions. No production repair is proposed.

## 7. Verification and freeze

The module imports only pinned `Std`; no root import, production Rust,
manifest, dependency, shared status, or Git operation changed. Verification
uses an isolated project/cache under
`/workspace/scratch/f98087c7ac1a/inference-native-saturation/project` and the
installed native Lake at
`/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
The recorded version is Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake reports 5.0.0-src for that Lean.
Each invocation is bounded by 120 seconds, `-j1 -M1024`, and one Lean thread.

The companion inbox records final source/olean/dependency hashes, every root,
full module-origin audit including private/generated declarations, failures,
checks, and the immutable stopped-writer receipt. Named theorem audit output
prints every exact type; full origin output prints every declaration type and
complete recursively collected axiom list. Standard axioms are reported,
not described as an axiom-free proof. Independent review is still required.

# Restoration live indexing: reentrant constructor discrimination

Date: 2026-10-13
Status: independently reviewed static constructor derivation; no source failure claim
Baseline: `9a30a208bd23b9b84cd601934b4b9697f051eca2`
Assigned branch: `research/simple-sub-intrusion`
Exclusive additional lease: this new note only
Budget: at most ten additional minutes, static only, zero heavy processes

## Objective and exact authority

Discriminate whether an actual typed callback can shift restoration's
direct/exact separator and cause an initially present opposite bound to be
unselected. This follows the original bulk-owner packet with a newly assigned
operational input: synchronous restoration child execution between successive
live physical-index lookups. It is not another copied-origin or persistent-memo
attack and does not inspect the constructive producer's unpublished output.

The private candidate suspension contract §4 explicitly requires saving the
initial opposite count and rereading current direct/exact vectors at each
index, including same-component callbacks. The older resumed-restoration
source-correspondence note's **Objective and frozen statement**, **Conditional
trace derivation**, and **Exact remaining premise** describe the same behavior
and already warn about direct-prefix growth. Top-level inference principles
§§1–3 and successful-suspension clause, repaired rebuilt-core **Lemma 1**, and
compiler-engineering **proof-obligation economy** govern interpretation.

Result: the non-test restoration owner admits a finite reentrant constructor
trace with selected opposites `[f1,f1]` although its initial exact uppers are
`[f1,f2]`. The intervening direct-row append comes from actual Function
contravariance and ordinary bound replay, rather than an externally injected
vector mutation. This refutes the local shortcut “saving the opposite count
enumerates each initial opposite incidence once” for this constructor interface.
It conforms to the selected live-index behavior. It does not refute the
original all-source theorem or prove an accepted-program failure.

## Hypotheses and constructors

Use a candidate-enabled private session with available identities/storage,
valid occurrence/cause, empty worklist at restoration entry, identity contexts,
no retained extrusion parents, and canonical distinct value rows `a,r`, both
level 1. Obtain them using `fresh_value_at_level(1)`; bound rows start empty.
No source restriction or pre-solved comparison is assumed.

All terms below use actual `live_value_term`, `positive_function_term`, and
`negative_function_term` constructors (`lib.rs:10230–10300`) and available
collected leaf terms. In this table, “argument” is the actual signed Function
field, not a reinterpretation of source annotation meaning.

| Term | Argument | Argument Effect | Result Effect | Result |
| --- | --- | --- | --- | --- |
| positive `g` | negative row `r` | `EmptyEffectNegative` | `EffectBottomPositive` | `IntPositive` |
| negative `f1` | positive row `a` | `EffectBottomPositive` | `EmptyEffectNegative` | `IntNegative` |
| negative `f2` | `BottomPositive` | `EffectBottomPositive` | `EmptyEffectNegative` | `UnitNegative` |

Admit the two original constraints `a <= f1` and `a <= f2` separately through
the real typed constraint driver (`constrain_live`/candidate typed drain), while
`a` has no lowers. Structural negative extrusion at receiving level 1 leaves
the only referenced row `a` unchanged; the direct application owner inserts
each negative Function into `a.exact_non_variable_uppers`. Opposite replay has
zero lowers. Thus actual constructors produce:

```text
a.upper.direct = []
a.upper.exact  = [NegativeFunction(f1), NegativeFunction(f2)]
a.lower.direct = []
a.lower.exact  = []
r has empty bounds
parents = []
```

No raw row-vector assignment is needed to construct this state. These two
constraints themselves produce no Function/Function child comparisons.

Now invoke the production, non-`cfg(test)` owner
`candidate_begin_bound_restoration(ValueRow(a), Positive, PositiveFunction(g),
occurrence, cause, OwnerEmission { processing: None })`, then drive its
retained handle through `candidate_drive_bound_restoration`. The cause is an
admitted internal constructor argument, not a forged FreshUse certificate.
Actual production freshening callers use FreshUse evidence; their reachability
of this exact pre-state is a separate unproved bridge below.

## Actual callback and ordering derivation

1. `candidate_begin_bound_restoration` (`candidate_extrusion.rs:659–678`)
   inserts `g` as an exact lower at `a`, then retains `N=2,n=0` and the
   accepted emission. The insertion attaches real identity fibers; the
   opposite side has real fibers from the two prior typed admissions.
2. `candidate_step_bound_restoration_child` (`:694–760`) selects `f1` at
   current index 0 and constructs the ordered inputs `(a,+,g),(a,-,f1)`.
   Incoming-use replay generates the full current fiber product, even if a
   replay frontier had previously been recorded. At least one identity child
   `g <= f1` exists.
3. On the next owner step, `candidate_context_drive_replay(...,Some(provenance))`
   synchronously starts and drains that child (`candidate_context.rs:3060–3123`).
   This synchronous adapter is why callback mutation occurs before the next
   restoration lookup. Ordinary replay with `None` provenance instead queues
   work to its outer drain; it is not the same timing premise.
4. Function dispatch builds its four children at `lib.rs:12498–12538`.
   Contravariant argument comparison is exactly `ValueRow(a) <= ValueRow(r)`:
   the negative Function's argument is the lower endpoint, and the positive
   Function's argument is the upper endpoint. Result comparison is
   `IntPositive <= IntNegative`; both Effect children are bottom-to-empty.
   Function-port admission applies identity specialization of swap, so no
   nonidentity filter/suspension is involved.
5. The staged dispatcher admits fields in reverse order and pushes each to
   the worklist front (`lib.rs:12643–12669`), yielding argument-first processing
   once it releases the Function stage. Regardless, the argument callback
   occurs before the enclosing child drain completes.
6. `candidate_apply_value` (`candidate_extrusion.rs:808–837`) sees equal row
   levels and selects the first row/row branch: owner `a`, negative side,
   bound `r`. It appends `r` to `a.direct_upper_rows`. This is the required
   concrete mutation; no shape-specific fixture or external callback is used.
7. That ordinary insertion replays the current exact lower `g`, retaining
   the child `g <= r`. Within the same typed drain, structural positive
   extrusion at `r`'s level 1 leaves `g` unchanged (all referenced rows have
   level 1). Its application stores `g` as a lower on `r`; `r` has no uppers.
   This creates no `g <= f2` work. The compatible remaining Function fields
   also create no such task.
8. Intrusion settlement cannot compensate through a merge: its explicit
   `parents.is_empty()` branch clears dirty and returns
   (`candidate_intrusion.rs:358–374`). No step above created an extrusion parent.
   Relation completion uses the unchanged intrusion generation.
9. Replay delivery completes the first restoration child and advances `n`
   to 1. The nontransactional reclaim guard preserves a replay still owned
   by live restoration (`candidate_context.rs:1682–1689`); no stale-handle
   failure is being assumed away.
10. At the second live lookup, the owner vectors are now
    `direct=[r], exact=[f1,f2]`. `candidate_opposite_bound(a,Positive,1)`
    subtracts the **current** direct length 1 and returns exact index 0,
    hence `f1` again (`candidate_extrusion.rs:596–630`). The saved `N` remains 2.
11. Identity relations are interned by endpoints/context; a repeated `g <= f1`
    can meet `pair_is_current` (`lib.rs:11463–11474`) and skip redispatch.
    Even redispatch of the same `f1` would supply only its fields, not `f2`.
    After this replay's completion the restoration advances to `n=2` and
    retires. It never selects `f2`.

The selected trace and final relevant storage are therefore:

```text
restoration opposites: [f1, f1]
saved N: 2
a.upper.direct = [r]
a.upper.exact  = [f1, f2]
a.lower.exact  = [g]
r.lower.exact  = [g]
```

The second initially present atom is the discriminating omitted incidence.
Two initial exact opposites are necessary for this one-append illustration;
one would retire before there is a later lookup. One direct append and two
equal-level rows suffice. No SCC redirection or suspension is required.

## What follows, and what does not

The selected operational contract and the stronger initial-incidence-coverage
claim differ. The trace is consistent with the former; it disproves the
count-only shortcut for the latter at this private constructor interface.
The older correspondence theorem compares aligned uninterrupted/resumed traces;
both executions can select `[f1,f1]`. Nothing here contradicts that conditional
trace correspondence.

`g <= f2`, if dispatched, would generate `IntPositive <= UnitNegative` at the
result port and the incompatible-value branch would retain a diagnostic
(`lib.rs:12381–12399`). The listed constructors/children generate no such
comparison. This establishes a missing **direct restoration comparison** in
the constructed private state, rather than an accepted source-program result.
Availability completion of an internal restoration is not a public typing
acceptance theorem; generation may retain unsolved constraints.

Actual freshening is not an arbitrary call to this helper.
`candidate_scheme.rs:569–666` captures local row lanes in the exact order
direct lowers, direct uppers, exact lowers, then exact uppers;
`prepare_candidate_fresh_use` (`:1006–1019`) allocates empty generic rows or
shares older/nongeneric ones; `begin_candidate_fresh_bound` (`:1221–1266`)
restores the captured order with FreshUse evidence. Earlier original solving
may also have retained consequences on shared/captured rows that lawfully
rescue a comparison which this one restoration does not select. This packet
has not constructed the capture/remap/canonicalization sequence that creates
the table above immediately before a real fresh-use lower restoration, nor
proved absence of all compensating dispositions there.

Thus the exact source/consumer blocker is: derive an admitted public candidate
or source fresh-use history reaching this reentrant pre-state with its authentic
saved graph/order/maps, and show whether earlier retained constraints or a
later restoration rescues the demanded `g <= f2` consequence. A raw Graph
fixture or direct private call does not establish that bridge. This is the
stopping point; no natural-inference bug, incorrect published result, universal
pair-coverage refutation, theorem weakening, or routine snapshot fix is claimed.
Changing the selected live-index behavior requires a concrete contradiction
and the existing authority process.

## Checks, resources, and handoff

Static checks: direct source reads of both Function constructors, dispatch
child order, level-selected row application, physical vector lookup, synchronous
replay driver, relation memo/current-generation guard, restoration advancement,
replay reclamation, empty-parent intrusion settlement, and actual freshening
callers; exact §4 authority and earlier correspondence comparison; SHA-256
dependency inspection. No execution, test fixture, checker, seeds, finite
search range, mutation run, formatting, measurements, compiler edit, Git
mutation, delegation, or interactive question occurred. Zero heavy processes;
only sequential light read/hash commands. CPU/RSS and exact wall time are
unknown; ten-minute added wall budget was assigned. Runtime model/effort
metadata were not exposed, so requested/observed settings are unknown.

There is no independent executable oracle: this derivation follows the actual
pinned source branches and shares its selected authority with other lanes.
It is not independent review of the constructive producer or of this note.
Unverified scope includes runtime confirmation, source admissibility, production
facade reachability, inherited disposition coverage, general lifecycle,
termination, effect hygiene, Call, principality, and F5 cutover.

Recommended next action: primary choose one source-capture/remap history that
can discriminate whether a real FreshUse restoration reaches the above state
without retained rescue; stop at that exact constructor seam if none is yet
available. Do not repeat abstract shifted-vector probes or authorize a snapshot
repair from this private trace alone.

## Frozen dependency hashes and commit packet

```text
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d  notes/design/2026-10-11-private-candidate-suspension-contract.md
032e5877d28e60cce2955a15bfffd1761dbc22f75975223f9ee4a396d51271e5  notes/progress/2026-10-11-resumed-restoration-source-correspondence.md
08f178b448c711c43938ec26dd438c18bbee5d47ee4d11f1a03d2e88839f6597  notes/theory/2026-10-11-simple-sub-rebuilt-core-proof.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
```

- Exact additional leased/changed path: `notes/progress/2026-10-13-restoration-live-index-pair-audit.md`.
- Baseline SHA: `9a30a208bd23b9b84cd601934b4b9697f051eca2`.
- Changed dependencies: none observed; primary rechecks before integration.
- Claim/review status: frozen unreviewed constructor derivation; no source-failure or parent-gate closure claim.
- Checks already run: the narrow static owner/authority/caller and hash inspections above; no tests/probes.
- Proposed commit message: `research: derive restoration direct-prefix shift through Function callback`.
- Shared-record deltas deferred to primary/curator: record that saved count alone does not justify initial-incidence coverage; preserve selected §4 live behavior and its separate trace-equivalence claim; assign authentic fresh-use reachability and compensating-disposition evidence before adjudicating a compiler or authority contradiction. No shared record was edited.

## Primary review and parent handoff

The same independent `compiler_referee` that reviewed the native bulk-owner
component reviewed this frozen constructor delta. There were no BLOCKING or
major findings. The primary corrected the sole minor source inaccuracy: capture
enumerates direct lowers, direct uppers, exact lowers, then exact uppers. The
producer handoff above records its pre-review state.

The original scalar store retains `g <= a` and `a <= f2`, whose conjunction
entails `g <= f2`. Thus the missing direct restoration selection does not
establish absence of all represented dispositions, nor prove their contextual
validity. Only the count-based initial-enumeration shortcut is refuted. The
Authoritative live-index contract and original coverage theorem keep their
separate scopes and status.

The next owner is authentic capture/prepared FreshUse restoration: establish
whether its exact lane order, sharing and remap can reach this pre-state, then
account for inherited and later consequences at the actual contextual consumer.
No compiler repair or user decision is justified by this private trace alone.
The primary synchronizes task records and checks the minor textual delta,
dependencies and artifact integrity without another build or executable probe.

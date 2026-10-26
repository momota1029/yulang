# Native execution history — independent M3 review r3

Date: 2026-10-26. Assignment/handoff revision: 1.
Reviewer: `/root/native_history_review_r3`, a fresh supported generic reviewer.
Requested model/effort: inherited; no custom-role or separately observed model
claim. No authorship, construction, counterexample or repair contribution to the
reviewed targets; no descendants.

## Verdict

**ACCEPT**, at the stated computed mutable-owner journal projection boundary.
No BLOCKING, major or MINOR finding requiring correction was found.

This accepts the mathematical construction and the accuracy of its explicitly
bounded source mapping. It does not accept a complete Rust execution refinement,
native accepted-drain theorem, recursive currentness theorem or original
`SourceProblem.InferenceSoundness` instance. Those obligations remain OPEN.

The governing review inputs were the primary's frozen assignment at baseline
`60e8684224a8a911a5627b845312750a192be777`, branch `yulang3`, root `AGENTS.md` and
`AGENTS.pre-sprint.md`, the Lean skill and its source/execution guides,
`rules/design-authority.md`, the orchestration budget and sprint rules,
`rules/compiler-engineering.md`, and the Authoritative 2026-10-11 inference
principles. The baseline/branch are the primary's supplied identity; this
review performed no Git command. Compact scheduling state was read as context,
not as a replacement for the current exact assignment and lease.

## Frozen identity and evidence

All eleven `review-inputs.json` pins were independently hashed at intake and
again after substantive inspection. They all match. Both review targets remain
at the supplied hashes. The isolated project source, preserved check-07 source
and repository source are byte-identical; the preserved check-09 audit source
and current audit program are also byte-identical.

| Object | Independently verified SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/NativeExecutionHistory.lean` | `44ad2a6d5b9ac0526ea36adc9180e0ed66e3892e48fa39aa40b20999dc7a1da6` |
| `notes/theory/2026-10-26-native-execution-history.md` | `72714bcfc9c30e34d13d08f3e63d121a5162fa63462dee0c39dc2d61e8fe3de2` |
| `native-history-r3/review-inputs.json` | `b3f858b08d19080261fdf2e163435cb03e43507ac3b35800db30bbee49fdcc0c` |
| `native-history-r3/check09-full-audit.log` | `13a11e35ad4e204519c5310c841641ac4bd347d4d632c866ab4fec8668690928` |
| `native-history-r3/authored-roots.json` | `926a200a056f975cdadecea04e6e391c5ac667d5709fd309859d8c1deee516a3` |
| `native-history-r3/theorem-inventory.json` | `3aa817547d7125085f8a4b45f56f0bf28e41cd8a8faacac605fba3f21d0ac155` |
| `native-history-r3/project/AuditNativeExecutionHistory.lean` | `78912e014695c0762e623003880df8579fd3955bb48fe92d83e213319c17aa9a` |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |

Evidence paths beginning `native-history-r3/` are under
`/workspace/scratch/f98087c7ac1a/`; other paths are repository-relative.
The eleven pins additionally cover the unchanged toolchain/configuration,
`Contracts.lean`, the lifecycle and merge-construction notes,
`NativeReplayAcknowledgement.lean`, and the inference principles.

## Mathematical review

The complete 628-line module and complete accompanying note were inspected.
The proof imports only `Std`; none of the older conditional project contracts
is an imported premise of this construction.

1. **Readback is constructed.** `step` obtains the old cell from the actual
   table. A caller cannot choose `Undo.before`, an old birth or a favorable
   restoration snapshot through `Event`. Allocation rejects an occupied
   selected address; update and preparation reject a missing owner; separated
   mutation also requires protection in the current undo suffix. Low-level
   `update`/`mutate` helpers take a `before` argument, but `Step` and the checked
   interpreter bind it to the actual cell. Those helpers alone are not being
   presented as authenticated execution.
2. **One chronological history supplies the invariants.** `checked_step` and
   `checked_run` derive the relations from successful computation. `History`
   starts at `empty`; each constructor adds an actual projected route.
   `history_wellFormed` derives occupied-index and birth-clock bounds, and
   `checked_history` derives both `History final` and `WellFormed final` from
   one execution of the transaction list. No independently supplied terminal
   table certificate or semantic/currentness conclusion appears here.
3. **Advance preparation is represented correctly for this projection.**
   `prepare` records the current tuple without changing it; several such
   records may precede consumption. Protection is retained, not removed by
   each `mutate`. `unwind_covered` proves that a retained snapshot makes the
   eventual unwind at that address independent of later protected writes.
   Duplicate snapshots and interleaving with other owners therefore do not
   require the false premise that each snapshot immediately precedes its
   corresponding mutation. The computed preflight witness exercises that case.
4. **Joint cancellation follows from the operations.** `update_unwind`,
   `prepare_unwind` and `mutate_unwind` preserve the unwind result. Allocation
   is invisible below the checkpoint frontier. Induction yields the below-
   frontier equality; checkpoint boundedness supplies absence above that
   frontier, where `restrict` removes every new address. Thus
   `cancel_table_exact` is equality of the whole table, including correlated
   payloads in both lanes, not a collection of separately chosen endpoint
   predicates. The arbitrary-predicate corollary preserves any predicate
   already true of the saved table; it does not establish that predicate.
5. **Two native undo vectors have a valid algebraic reduction.**
   `partitioned_unwind` holds for any fixed address predicate. Each key occurs
   in only one partition, and filtering preserves that partition's original
   reverse order. Cross-lane reordering therefore preserves the final table.
   The separate obligation that the actual native vectors are these projections
   of one event sequence remains explicitly stated.
6. **Birth separation is genuine and properly limited.** Allocation advances
   the ghost clock, cancellation retains that clock while rewinding `next`,
   and updates preserve the actual cell's birth. The retry theorem proves a
   strict birth increase for the allocation at the checkpoint frontier with
   any subsequent projected event tail. Its raw initial `allocate` is not
   itself a native-validity premise: application to a reachable checkpoint
   uses `history_wellFormed`, `fresh_at_frontier` and `allocation_checked`.
   Ghost birth is proof-history identity, not an existing runtime field or a
   checked rejection rule for stale native acknowledgements.

### Principal checked types and premises

All names below are in `YulangClosure.NativeExecutionHistory`; `α : Type`,
`saved/current/final : State α`, and event/transaction lists have their declared
module types. These are the actual conclusions and premises, not strengthened
informal replacements:

```lean
checked_history
  (checked : executeHistory empty transactions = some final) :
  History final ∧ WellFormed final

checked_cancel_exact
  (well : WellFormed saved)
  (checked : run (begin saved) events = some current) :
  (cancel saved current).table = saved.table ∧
  (cancel saved current).next = saved.next ∧
  (cancel saved current).clock = current.clock

history_cancel_joint
  (prior : History saved)
  (checked : run (begin saved) events = some current) :
  History (cancel saved current) ∧
  (cancel saved current).table = saved.table

partitioned_unwind
  (keep : Address → Bool) (undo : List (Undo α)) (table : Table α) :
  unwind (unwind table (undo.filter (fun entry => keep entry.key)))
    (undo.filter (fun entry => !(keep entry.key))) = unwind table undo

cancelled_allocation_not_reused
  (tail : Exec (allocate (begin saved) lane value) events current) :
  (cancel saved current).next = saved.next ∧
  saved.clock < (cancel saved current).clock ∧
  (allocate (begin (cancel saved current)) lane value).table ⟨lane, saved.next⟩ =
    some ⟨current.clock, value⟩
```

Each of those five roots has exactly `[propext, Quot.sound]` in the complete
transitive audit. The complete types and axiom sets of all 123 theorem constants,
including private/generated proofs, were inspected in the frozen audit; they
agree with the source declarations and inventory.

## Native-source and original-parent application

The following actual pinned bodies were read; the table in the construction
note is accurate at its stated projection boundary:

| Source scope inspected | Review result |
| --- | --- |
| `candidate_context.rs:126–170` | The projected replay tuple exactly matches `ReplayOperationUndo`; the restoration tuple exactly matches `BoundRestorationUndo`. Task/children/input and backlink/initialization metadata require separate authentication. |
| `candidate_context.rs:2313–2360,3992–4078` | Both allocations advance the shared `next_replay_operation`; successful reservation and bounded native arithmetic remain necessary for the `Nat` readback. Restoration linkage, replay children and dependency construction are not supplied by the opaque tuple model. |
| `candidate_context.rs:2336–2343,2376–2451` | Transactional preparation records the current tuple. Actual acknowledgement, wait, return and cursor guards are stronger than journal membership. Their omission is explicit, not silently turned into successful semantic completion. |
| `lib.rs:14260–14285,14881–14936` | `prepare_nonterminal_drain` can prepare multiple acknowledgements before their consumption. Terminal consumption can use those retained preparations. Separate `prepare`/`mutate` events remove the atomic-preflight mismatch. |
| `candidate_context.rs:2044–2115` | Checkpoints retain frontier and vector lengths. Reverse restoration and replay undo precede removal of new IDs and frontier rewind. Frame undo uses pop/reinsertion and is correctly excluded from the table theorem. |
| `candidate_context.rs:2195–2247` | Commit performs reclamation and frame preparation reset in addition to truncating undo suffixes. These effects are absent from `commit` and explicitly remain outside this construction. |
| `lib.rs:9498–9543` | `Ok` and `Err` select commit/cancellation storage routes. `Transaction.accepted` is a branch selector and is not evidence of an accepted typing or accepted recursive drain. |

The original `SourceProblem` fields and roots in `Contracts.lean`, the
`native_success_elaborates` composition boundary in `CoreComposition.lean`,
and the original scope in the whole-proof-closure document were inspected.
The original soundness quantification remains:

```text
supported(source) → generates(source,scope,constraints) →
solves(constraints,solution) →
∃ witness, sourceJudgment(source,scope,witness) ∧
           sameScoped(source,scope,witness,solution).
```

Native correspondence still separately requires actual native success to yield
the generated constraints, native realization and a solution. The construction
does not define source typing as table safety, import `LocalLaws` as if proved,
or change the source domain. The previous merge construction supplies historical
origins and local transport components; this journal theorem does not promote
those origins to current recursive dispositions.

The accepted reduction is precise: **once one native chronological projection
is authenticated**, separately assumed rollback correctness for favorable owner
snapshots can be replaced by the joint theorem. Authentication must still
cover native creation/preparation/mutation, checkpoint-to-vector correspondence,
metadata and ghost identities, frame/worklist ownership, commit effects,
nontransactional paths and the actual accepted drain. The current-disposition
graph and original contextual/Call/record-boundary witnesses remain separate.
The primary owns that continuation and all status/integration decisions.

The Authoritative inference principles §§4–5 do not require general full
rollback or retry. This artifact proves a property of the already selected
transactional projection and introduces no compiler behavior, capacity-restoration
requirement or general recovery gate. Its acceptance cannot be used to impose
such a requirement.

## Checker evidence and resource accounting

The pinned files specify Lean 4.35.0, no external packages and `-j1 -M1024`.
Check 07 records the resolved task-local Lake/Lean versions, a successful focused
two-job build of the exact frozen source, and the three named root audits.
Check 09 records exit 0 for the full originating-module audit. The audit program
enumerates by originating module index, requires all authored roots, rejects
project axioms and checks every theorem's transitive axioms; it does not merely
sample names in the public namespace.

Independent parsing verified 123 distinct, paired BEGIN/END blocks, all 48
authored roots, an exact match with the inventory's theorem set, and the final
`123 DECLARATIONS 311 ROOTS 48` census. Source enumeration also found exactly
48 authored theorems.

| Axiom set | All theorem constants | Authored roots |
| --- | ---: | ---: |
| None | 69 | 7 |
| `propext` | 20 | 11 |
| `propext`, `Quot.sound` | 34 | 30 |
| Total | 123 | 48 |

No `Classical.choice`, nonstandard axiom, proof hole, native-evaluation bypass
or final warning appears. The complete source was also searched for holes,
project axioms, unsafe/external replacements and checker bypasses; no match.
An initial reviewer log parser failed to count three line-wrapped axiom lists;
the whitespace-aware parse accounts for all 123 and confirms the stated census.
That was a read-only evidence parser issue, not a Lean or artifact failure.

All nine recorded call receipts and their log hashes were checked. Calls 02,
04 and 07 are successful focused checks; 01, 03, 05 and 06 preserve failed
source snapshots and actual diagnostics. Call 08 preserves the audit counter's
type-inference failure; call 09 fixes the counter annotation and succeeds.
The recorded nine-call duration totals 20.099826 seconds; final check 07 is
3.031603 seconds and check 09 is 1.118013 seconds. Earlier failure warnings,
including parser-recovery `sorry` warnings, are not misrepresented as passing
evidence for the final source.

Reviewer budget: 900 wall seconds; at most two focused 120-second Lean calls
only if a concrete risk required them. **New reviewer Lean/Lake calls: 0;
Cargo/native checks: 0; executable model probes: 0; network calls: 0.**
Existing frozen evidence and source inspection resolved the relevant risks;
no repeated build was necessary. Review began at 09:08:55 UTC and substantive
inspection had completed by 09:12:32 UTC, within the assignment envelope.

## Closure scope, omissions and cessation

Reviewed: every definition and proof in the new module, the complete note,
all printed theorem types/axioms in the final audit, the audit program and
inventory, all eleven source pins, preserved check outcomes, the original
parent definitions, relevant prior application boundaries, and the native
bodies listed above.

Not newly certified: the complete older acknowledgement/merge modules and
their dependency cones; native paths outside the inspected scopes; the complete
Rust operational semantics; full frame/worklist/metadata/reclamation readback;
recursive currentness/accepted-drain semantics; original source/Call/effect/
record obligations; the default integration build or public import closure;
runtime performance; Git baseline ancestry or integration. Existing prior
results are not recertified by this review.

Sole write: this leased review receipt. No construction target, compiler,
configuration, dependency, shared status, Git state or other inbox was written.
No scratch artifact, cache, background checker, worker or descendant was created.
The primary may integrate the accepted frozen artifact at the stated boundary.

**WRITES STOPPED.** Receipt byte hash is returned separately to the primary so
that the frozen file does not contain a self-referential hash.

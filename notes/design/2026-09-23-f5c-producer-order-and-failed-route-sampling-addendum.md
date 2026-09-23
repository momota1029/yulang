# F5c producer ordering and failed-route sampling addendum

Status: Authoritative for producer-order and failed-route sample decisions; implementation gates open\
Scope: F5c producer-order binder assignment, post-Q/R canonical normalization,
and one conditional resource sample after a failed incoming-route rollback.\
Approved-by: user's 2026-09-23 delegated design direction; primary adjudication
after clean architect and M3 review, 2026-09-23\
Drafted-by: primary\
Reviewed-by: architect preflight; M3 spec_auditor, compiler_referee, and
performance_auditor final delta review clean, 2026-09-23\
Supersedes: the narrowly named clauses in F5 §§7, 23, 25, 26, 32, 34, 36,
and 44 below; all other F5 authority remains unchanged.

## 1. Decision boundary

The user directed the primary to prefer weakening alpha/source-order
independence rather than retaining unrestricted factorial alpha ranking, and to
consider one conditional O(1) sample after an incoming-route rollback. The
direction permits the primary to overturn either choice if design evidence
requires it. This addendum resolves only the producer-order and sampling
choices; it does not close the producer, rollback, stack-safety, or F5e
certification gates by itself.

This addendum does not add public API, a public counter/resource family, a live
Union Term, or a new failure-recovery mode. The approved §44 first-member
representative projection remains in force.

## 2. Solver producer ordering: first surviving encounter

Do not alpha-normalize or alpha-deduplicate live-variable structure before
Q/R assignment. The current pre-Q/R local Union/Intersection normalization and
grouped alpha-key pass are removed from the binder-selection path. They impose
independent ordering stages and factorial label searches before the whole
predicate-and-bounds forest has one defined variable-identity order. Existing
identity-preserving exact-duplicate removal may remain only when it compares
full live identities, not variable-erased or alpha keys, and cannot discard the
first encounter of a distinct identity.

Preserve §8 and §23's normalized polarity census and its normative phase:
after expansion, before one-sided elimination and R pruning, over the complete
reachable producer forest then in scope (predicate and all expanded reentry
bounds). The census is a set of live-variable identities with positive and/or
negative incidence; commutative sorting and exact identity-preserving duplicate
removal do not change that set, so it can be collected from the raw stored
children without pre-Q/R normalization. Use this same pre-pruning census for
positive-only/negative-only elimination and bipolar eligibility; do not
recensus after later R pruning. During R-survival reasoning, current guarded-R
candidates are protected from one-sided elimination; only eligible non-R rows
are replaced by polarity extremes, as §33 requires. Retained R owners are
excluded from both elimination and Q. This retains §23/§33 classification
semantics while allowing Q ordinal emission to follow the retained producer
sequence. Retained R owners are identified before non-R one-sided elimination
and remain protected through the survival fixed point; the first surviving
trace sequence only determines their final ordinal order.

After provisional guarded traces, the pre-pruning incidence census,
non-R one-sided elimination, and retained-R classification/reachability have
settled:

1. Build the recursive-owner sequence by scanning `self.reentries` in its
   stored order. Retain an owner only on its first trace that survives path,
   bound, and reachability filters. Candidate/survival sets are membership
   filters only. Retain the first surviving trace for each owner; never emit
   owner order by iterating a `HashMap` or `HashSet`.
2. Keep the retained predicate and each selected R owner's lower/upper bounds
   in that sequence, without pre-Q/R alpha deduplication. Visit the predicate
   first, then each R owner's lower bound before its upper bound. Within a
   value, visit Function fields in existing fixed order and Union/Intersection
   children in their stored producer order.
3. Assign Q ordinals to eligible non-R variables marked
   bipolar by the §23 pre-pruning census, on first encounter in that traversal.
   One map from live-variable identity to Q ordinal spans the predicate and
   every selected R bound. The same variable therefore retains one identity
   wherever it occurs; no owner-local relabeling is allowed. Maps and sets may
   answer membership/lookups but never define output order.
4. Assign R ordinals after the Q range, in the selected owner sequence.
   Rewrite every retained live variable to its Q/R reference or its polarity's
   effective extreme. Reject any remaining live `Variable` or `Shared` node
   before closed normalization.
5. Normalize and then preserve §23's final unreachable-R pruning and closure
   validation. The retained-R fixed point already computes reachability after
   non-R one-sided replay. Q/R substitution is injective on retained live
   identities, and closed normalization only sorts and removes exactly equal
   children; both operations preserve the set of Q/R references in the
   predicate and each retained bound. Therefore final pruning must remove zero
   R owners, and each emitted Q remains referenced because Q is numbered only
   after its first encounter in the retained forest. Assert this no-op/dense-
   closure invariant. If a future normalization operation can absorb or
   otherwise remove distinct Q/R references, return to design before changing
   the final-prune contract.

The full relation and sharing identity must survive: do not merge branches or
bounds merely because they have the same variable-erased shape. Canonical
Union/Intersection sorting and exact duplicate removal still happen after Q/R
substitution and before public scheme publication. Consequently producer
reordering may change Q/R ordinals and, through those ordinals, the normalized
member order even when the branches have different structural shapes. The
approved §44 projection remains the first member of the final normalized
Union; its value may therefore change with producer order. This is the
deliberate alpha/order-independence relaxation, not a reduction of the Union's
meaning or a change to private-member constraints.

The current `yu-types` `positive_union` and
`negative_intersection` finalizer methods preserve supplied child order;
they do not currently perform the §36 descriptor ranking. A post-Q/R canonical
normalization gate is therefore mandatory before §44 publication. Its owner
and placement remain open: a private solver pass is one candidate, while a
finalizer change requires its separate authority path. Whatever owns it must
sort and deduplicate closed Q/R structure, must not search binder-label
permutations, and must satisfy the existing bounded-work and stack-safety
requirements before the producer gate can close. This addendum does not
authorize Candidate B or another new `yu-types` API, and does not certify
the current recursive `F5cKeyForest::tree` implementation as bounded or
stack-safe.

Emit Q first-occurrence order while replacing the existing
post-retained-R `retained_occurrences` traversal; this is not part of the
earlier pre-pruning incidence census. Collect ordered unique identities
directly instead of materializing path maps and sorting them, and do not add a
second walk over that same retained forest. This does not remove the earlier
pre-prune census, materialization, or candidate fixed-point work. Account for
producer nodes and child edges explicitly and prove that total work remains
charged to the approved generalization/output bound without rescanning a
component-shared acyclic cone per root. Do not rename path-expanded work as
distinct-node work or silently weaken §14/§25. If the proof does not fit the
approved bound, return with a narrowly stated bound change for adjudication.
The existing boxed expansion and stack-safety gate remain open.

### Narrow supersession

- In §7, replace normalized-first-occurrence binder ordinals with the explicit
  producer traversal and shared live-identity map above.
- In §23, keep the normalized polarity census at its existing
  pre-elimination/pre-pruning phase and keep its one-sided classification
  semantics. Replace only normalized-first guarded re-entry for R assignment
  and normalized-first retained occurrence for Q assignment with steps 1–4
  above. Keep the requirement to normalize after substitution, now before
  closed publication.
- In §33, retain R classification before elimination, R exclusion from
  elimination/Q, and all trace/safe-sharing requirements. Clarify that its
  final post-Q prune is distinct from pre-Q retained-R classification; no
  R-retention semantics are superseded.
- In §25, supersede only the normalized-order requirements for R/Q selection
  and source/admission-permutation equality when that permutation changes Q/R
  assignment. Keep identical outputs across forward/reverse/rotated root-draft
  evaluation order when each root's producer sequence is unchanged, as well as
  F0/F2 order, Function-field order, frozen bounds, per-root namespaces, and
  component-summary ownership.
- In §32, leave the `alpha_eq` implementation unchanged and preserve its
  binder-renaming guarantee when corresponding Q/R structure is positionally
  aligned. Ordinal-label changes alone are not an exception: the comparison
  explicitly maps binder ordinals. It need not equate outputs when producer
  order changes the positional R-bound sequence or normalized
  Union/Intersection member order, which the current comparison does not
  permute or rematch.
- In §36, keep the descriptor-rank algorithm and `O(N + W + C)` bound.
  For a fixed Q/R assignment, retain reversed-Union-input, allocation,
  collision, traversal, and root-draft-order independence. A source-permutation
  exception applies only when it actually changes Q/R assignment before the
  indexed draft is formed; otherwise §36's identical-rank/scheme/counter
  expectations remain. Do not treat the current `yu-types` finalizer as
  implementing §36 ranking, or authorize a new API here.
- In §44, retain one public representative route/fact, the first member of the
  final normalized order, all other members as private constraints under the
  same cause, and all-or-nothing route publication. Supersede independence of
  that representative from source/admission order when changed producer order
  changes Q/R assignment and final member order.

Reclassify the existing fixtures individually:

| Fixture | Required disposition |
|---|---|
| `f5c_quantifiers_follow_normalized_occurrences_not_admission_order` | Replace cross-admission draft equality with forward/reverse witnesses that each Q sequence follows the explicit predicate-then-R-bounds producer traversal and preserves one identity across the forest. |
| `f5c_distinct_symmetric_recursive_owners_are_retained_alpha_equivalently` | Keep both R owners and their guarded bounds; replace cross-order equality with R ordinals matching first surviving `self.reentries` order. Do not require alpha-equivalent normalized member order after the ordinal change. |
| `f5c_key_forest_canonicalizes_commutative_roots_with_shared_alpha_variables` | If the generic `finish` helper remains, retain its direct cross-root assertion because this fixture has no producer Q/R assignment. The helper is not required solely to preserve unrestricted alpha search; if removed, replace the fixture with fixed-input producer-order, sharing, and §36 rank witnesses, without adding a generic alpha-key oracle. |
| `f5c_reversed_exact_and_direct_admission_keeps_canonical_recursive_order` | Replace equality across reversed admission with the explicit first-surviving reentry order in each fixture and a check that hash-container iteration does not choose R order. |
| `f5c_recursive_binders_follow_guarded_reentry_order_not_row_visit_order` | Retain and sharpen as the fixed-input first-surviving-reentry witness; assert the exact owner sequence from the stored trace. |
| `f5c_key_forest_distinguishes_shared_and_independent_non_owner_variables` and `f5c_grouped_keys_preserve_cross_owner_variable_sharing` | Preserve the semantic no-conflation property with a producer-level case sharing one live variable between the predicate and multiple R bounds. Direct helper assertions remain only if the helpers remain; replacing a helper must not drop this identity witness. |

Also require fixed-input output under varied hash seeds/insertion order,
first-surviving trace selection, binder-renaming `alpha_eq` coverage for
positionally aligned R/member order, no live variable reaching finalization,
and a §44 witness that checks the published representative against the first
member of the final normalized Union actually produced. Assert the final R
prune removes no owner, R ordinals remain dense, and every Q ordinal remains
referenced after normalization. Add a §8/§23 census witness
where a variable's opposite-polarity incidence occurs only in a provisional R
bound later pruned: if that variable still occurs in the retained forest, its
pre-pruning bipolar classification remains normative and it is Q, not a
one-sided extreme. Pair this with a variable found only in the pruned bound,
which receives no Q because it is never encountered in the retained forest.
This is an intentional consequence of the pre-pruning census; changing it
requires a separate semantic amendment to §§8/23/33. Keep
every §36 rank test unchanged unless its upstream source permutation
demonstrably changes Q/R assignment before the indexed draft is formed.

## 3. One conditional sample after failed incoming-route rollback

Supersede §26's sample-boundary whitelist and §34's sentence that sampling
remains exactly at §26's named boundaries for this one additional boundary:

> After an incoming route attempt fails and its transaction/setup rollback and
> cleanup have completed, take exactly one additional O(1) aggregate sample if
> that attempt recorded any route-owned physical capacity change or
> capacity-owner transition.

Begin one incoming-attempt accounting scope after use validation and before
`begin_route_transaction`. Reset an O(1) attempt-local physical-change flag
there. Set it at the owning event site whenever a route-attempt lane's
capacity changes (including a failed reserve that leaves changed capacity), or
its membership in the counted owner/retention set changes. Cover every lane
contributing to semantic/session totals, including nested value/effect-row
payloads, outer row tables, typed-pair and diagnostic scratch, instantiation
scratch, and active/spare journal storage. A transfer between active/spare
owners in one continuously counted family is not itself a change if the
sampled aggregate and ownership family remain the same. Do not trigger the new
sample for a validation failure before setup begins or a logical-only failure
with no physical/ownership event. If partial setup changes capacity and then
fails—for example, one seen-vector reserve succeeds and the next fails—run
cleanup and apply the same rule.

One outer incoming-attempt exit owns the final sample decision for both setup
failure and body failure. It takes exactly one additional post-rollback sample
when the attempt-local flag is set, and none when it is clear. Sampling runs
only after setup cleanup or route rollback has restored logical state, removed
fresh rows, cleared transient scratch, reconciled retained preexisting nested
payload and surviving outer table capacities, restored public
store/provenance/receipt and routed-use state, and returned the active journal
and instantiation scratch to their post-attempt owners. It observes the final
simultaneously retained state through the existing fixed-size aggregate
snapshot; it performs no row, map, or batch scan and allocates no new ledger
storage.

The new sample supplements, and never replaces, event-time accounting:

- At every actual capacity growth or changed failed reservation in every
  contributing lane, record the observed capacity and same-time
  semantic/session peak before rollback can truncate or drop the storage.
- If a newly created row and its nested payload are later dropped, include the
  temporary bytes in the peak at the event but not in post-rollback retained
  bytes.
- Reconcile outer vectors whose lengths are truncated but whose capacities
  survive, and preexisting nested vectors whose capacities grew, before the
  post-rollback sample.
- Preserve per-lane owner identity through active/spare journal and scratch
  transfers. Combine only capacities that coexist at one instant; never add
  unrelated historical lane peaks.
- Keep all logical counters and solver state transactional. Physical requested
  slots, observed capacities, growth events, and peak evidence remain
  monotone where the existing resource contract requires them.

No second post-failure sample is permitted for one attempt, even when several
lanes changed. Existing actual-growth samples and the §26 incoming-scratch-peak
sample remain authorized at their event boundaries; they do not substitute for
the one post-rollback sample. Split scratch metric reconciliation from
sampling so a counter flush after a failed transaction cannot take a duplicate
post-attempt sample. A successful incoming route retains its existing sample
behavior. All incoming-route event and final samples use checked, fallible byte
totals. Compute the complete fixed-size sample into checked local totals before
mutating published counters or the test ledger. An unrepresentable total
returns the existing `IdentityExhausted` availability error without partial
counter publication. The consuming production path drops the private session
on this terminal accounting error and publishes no `SolvedModule`; the
private `&mut self` route method must not be retried after it. Ordinary
recoverable route failures retain their existing retry behavior. No persistent
poison state or new error variant is added, and the boundary adds no public
observer surface.

The independent ledger must prove both sides of the boundary: event-time peaks
include storage that rollback drops, while the new boundary's current retained
totals equal independent per-lane enumeration after rollback. Include at
least: preexisting nested value/effect-row growth; fresh-row nested growth and
drop; outer row-table capacity surviving truncation; typed-pair/payload plus
diagnostic scratch growth; instantiation scratch growth and reattachment;
active/spare journal ownership transfer; and every other touched F4 lane that
contributes to semantic/session totals. Include a no-physical-change failure
proving the new sample is skipped, and a setup/begin failure after one
seen-vector reserve changes capacity but a later reserve fails. Assert exactly one post-rollback sample invocation for each changed failed
attempt. Representable totals publish exactly one boundary record. Also assert
none for a no-change failure. Inject checked-byte overflow at the fallible
incoming sample boundary and assert exactly one invocation and
`IdentityExhausted`, complete rollback, no route/result publication, and no
partial resource/test-ledger publication. Exercise this through the consuming
solve path so the session is dropped rather than retried with stale totals.
No O(number-of-rows/maps/uses) work may be added to the production sample.

## 4. Authority retained and gates

The user preference does not authorize Candidate B's proposed new §24
`yu-types` indexed finalization API. That API still needs its own clean M2
review and explicit user approval. This addendum also does not certify the
producer traversal's §14/§25 work bound, post-Q/R normalization complexity,
stack safety, component sharing, complete failed-route accounting, or F5e
public resource matrix.

After review/adjudication, implementation proceeds as separate bounded gates:

1. replace normalized-first Q/R selection with the explicit producer sequence,
   keep one Q identity map across predicate and R bounds, and remove all
   pre-Q/R alpha-based deduplication;
2. close the owner and algorithm for post-Q/R canonical normalization, with
   bounded work and stack safety, without assuming current §36 implementation
   or authorizing an unapproved finalizer API;
3. revise only the enumerated order-sensitive fixtures and add fixed-input,
   cross-bound-sharing, closed-finalizer, and §44 representative witnesses;
4. implement complete event-time accounting plus the conditional
   post-rollback sample and independent per-lane reconciliation witnesses;
5. obtain focused semantic/specification/performance delta closure before
   updating the F5c handoff and current-task navigation.

Any review finding that producer order can merge distinct sharing patterns,
that Q/R identity is not global across the retained forest, that the traversal
defeats component sharing, that closed normalization cannot meet its bound
without an unapproved API, or that a resource lane is unobservable returns the
affected choice to the primary for adjudication. Do not silently restore
factorial work or weaken the §44 atomic first-member projection.

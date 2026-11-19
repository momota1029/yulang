# Cycle 266: stutter-aware source compression

Exact forward simulation should count one strict finite step for each genuine source edge with differing projections, and none for equal projections. A mathematical witness relation may use the real end state's liveFacts; that is not an executable observer and is intentionally distinct from a caller-supplied proposal list. The executable observer result will assume coverage of those proposals along a source trace. For reverse lifting the source representative matters, so pairwise witness edges must not be glued across different representatives unless an explicit lifting condition is verified.

Candidate goal: for any source trace annotated by cycle264's strict-change count, reproduce that exact count and endpoint in finite Runs, provided the observer lists each strict edge's exact live-fact proposal. Instantiate the strict install regression as an actual checked finite step. No language changes; old kernel nontermination remains separate.

The checked-write entry can discharge its basis-side error using the actual source-wide finite pool. Its exact return should distinguish none on a stutter from some on a strict step, not conflate either with source acceptance. An optional separate measure for source stutters would yield source accessibility by lexicographic descent; the existing 239 loop rules out such a measure for the unmodified old kernel.

A separate finite *specification observer* can enumerate possible projected states and choose a candidate precisely when some real source edge witnesses both projected endpoints. The choice uses classical predicates and is not the missing executable inspector. It will give exact strict one-edge correspondence; concatenating projected witness edges can select different representatives and is not a general lift of executions. Prove representative-sensitive lifting as a separate sufficient condition rather than implicitly joining witnesses.

Use the cycle264 exact install and affected-only merge squares to avoid the full-live rescan in the checked adapter. Each local proposal is a subset of after-state live facts. Starting from a formed source, one fixed finite basis obtained before choosing any future installation/merge therefore admits all these checked writes. This is still an adapter from a *selected actual source step*, not an implementation of selecting the source step.

A terminal state of the specification observer rules out any future change in projection across an arbitrary real finite source suffix, from any concrete representative of that terminal state. This still allows unbounded source stutters. For reverse lifting, the weaker useful condition is one strict projected change plus any number of source stutters for each abstract step; use exact-count concatenation of cycle264 traces.

Also separate an executable observer on a **caller-supplied finite list of certified edges** from the classical complete specification. A compiler from such a list can filter by decidable projected field equality and emit supported proposals. It does not discover the list, or certify that it covers all possible edges.

## State-dependent observer stability

The scheduler supports more than fixed proposal batches. A sufficient condition for one terminal state is *pending fact persistence*: whenever the remaining list shrinks by sublist, any previously proposed fact still remaining in the smaller list is still proposed somewhere. Use sublists, not merely fact-membership antisymmetry: duplicate basis entries are permitted. A terminal above the starting state is an upper bound in the refinement order for every possible run, so any two terminal runs agree. This premise is not automatically true for selected old-kernel source representatives. Test it on positive finite dependency rules (known premises trigger a still-pending conclusion), whose computation and examples are genuinely executable without classical source-edge discovery.

For positive rules, identify terminal states with ordinary Horn-style closure of present facts and show successful settlement reaches the least such closure above the start. A separate pointwise interpretation that validates each supplied rule preserves exactly the model set, without turning the finite completion into a general solver capability. Verify an executable three-step dependent example and rule list reordering.

## Certified-edge rule envelope

Compile each supplied certified edge into positive implications: every fact presently known at the projected source is a prerequisite, and each fact known at its projected destination is a conclusion. The resulting rule closure contains every projected fact along any abstract run using listed edges. In general it is an envelope, not an equivalent execution graph: it can combine facts from distinct edges and is not evidence of a lift to any single source trace. Pointwise model preservation is equivalent to semantic validity of the corresponding per-edge implications. Seek exact settlement for the singleton genuine edge as the narrow regression.

## Certified paths and versioned recurrence

A certificate spine pairs each old source edge with a continuation from its
actual target (unlike an arbitrary table). For every supplied spine and
owner/output basis, remove exactly the projected stutters. The compiled
observer has at most one strict successor at each state: a strict first edge
drops remaining-length below any later return to its origin. Prove settlement
equals the projected final source state, and exact successful Step count equals
the number of non-stutters, bounded by initial remaining length.

For any old path whose endpoint projections agree, rank monotonicity forces
every edge to stutter, so its table emits no proposals even on arbitrary
abstract inputs. Convert a nonempty source round proof into mere existence of
a spine, use established point-kernel erasure for the old 240 round, and test
both actual recurrences. This is about projection of certified rounds, never
source accessibility or full current candidate discovery.

## Reverse replay of one supplied spine

Goal: for every abstract run from the projected first vertex of one supplied
certified spine, exhibit an actual concrete vertex and a cut of that same
spine into prefix/suffix. The prefix must have exactly the abstract count of
strict transitions, its projection must be the abstract endpoint, and its
concatenated edge list with the suffix must equal the input list (not just be
contained). Derive count comparison and endpoint uniqueness for a
deterministic relation whose reference run ends terminal. Then cut the spine
constructively with respect to its projected edge test. This does not provide
reverse lifting for the table formed from unrelated paths.

## Rule settlement on a single spine

The positive rule compilation may jump across states in general. For one
composable spine it should nevertheless settle to exactly its projected final
state. At every edge, every known target fact is also known at the final
projection. Thus that projection is a saturating upper bound. The exact
certified run gives the reverse inclusion. Use the shared list/sublist
invariants and the write-to-final square to retain duplicate/order structure.
This result is only about terminal facts, not step count or the full journal.

## Branching certificate tables with a common target

Given a nonempty finite list of actual certified paths with shared concrete
first and last states, concatenate their table entries. Individual runs can
choose strict edges from different paths when their projected vertices
collide; do not claim representative-sensitive lift. Prove nonetheless that
all maximal runs from the common projection reach the designated final
projection: any certificate edge target on a path can follow its own suffix
within the union table; common-final rank rules out any strict edge out of the
target. Show the Horn table reaches the same final projection.

## Exact journal interpretation of the computed terminal value

Use one source-derived finite owner/output basis for any family of actual
paths beginning at a declared initial source. Reachability will derive ledger
synchrony and live fact coverage. Combine the certified/positive common
terminal value with the journal decomposition, retaining the concrete final
remainder and an explicit fixed-representative compatibility premise for each
assignment in that remainder. No model iff is asserted for a projected state
alone or with a discarded remainder.

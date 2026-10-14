# Copied symbolic cuts: continuation owner audit

Status: unreviewed bounded static source characterization. No source-qualified
counterexample, universal activation theorem, H2/U closure, or implementation
authority. Frozen at handoff; primary assigns fresh independent review.

Baseline supplied by primary: `d8a6209c1dc181858948c4d811259aa20683d64e`,
branch `research/simple-sub-intrusion`. Exclusive lease: this file only.

## Objective, authority and hypotheses

Trace a subsequent lower on the existing observer's original symbolic row,
including original cuts, actual incoming-tail incidence, copied cuts, replay
fibers and completion. Then discriminate a genuinely remapped symbolic row at
`Visit`, and distinguish completed original processing from pending processing
at the positive gamma snapshot. This is an owning-construction audit,
complementary to the constructive proof, with no new executable experiment.

The original parent remains every originally admitted shallow Catch H under
one original scoped sigma, with its original scrutinee, operation/value-arm
binders, provider, raw resumptions and dependent interfaces. Protected,
eligible consumed, unmatched, outside-arm and raw-resumed contributions retain
their original categories. No independent marginal assignments are introduced.
H1/H2/U remain OPEN; H3/P remain disabled; production/F5 is separate.

Governing sections: top-level inference principles §§1–5 and §1.1; residual
lineage selection, Selected policy and Preserved contract; attachment/admission
§§3–4. The native-handler-residual-cut §§3–4 primitive is reused only with its
plain-context and actual successful-processing premises. The original lineage
gate's §6 and current-cut construction §§2–4 locate this operational seam.
Compiler-engineering, Natural compiler behavior and proof-obligation economy,
does not permit replacing this missing A/B correspondence by endpoint evidence.

Hypotheses for the bounded continuation result: valid live handles; the exact
observer's successful pre-copy admissions and structural extrusion; no discarded
output; the subsequent lower is admitted through the ordinary typed owner;
all actually emitted work completes successfully. Context is IDENTITY on this
fixture, derived from the constructors below. This does not infer source
protection from empty words. General nonidentity contexts, arbitrary histories,
complete source admission and publication are not assumed proved.

Notation: original source s has level 2, gamma g has level 2, symbolic row x
has level 1, and the structural extrusion target is 1. Two distinct original
views v_i have the same heads J={E} and tail g. Primes denote actual outputs
of this one extrusion map. B(y,+,z) and B(y,-,z) denote actual BoundKeys;
F(B) is the actual set enumerated by `bound_relations(B)`, not an origin count.
The exact copied view identity is the output of the operation-local key
`(v_i,Some(g'))`: the s and x incidences reuse that identical ID; different
v_i allocate different IDs even with this identical tail. Every such copied
view has tail literally `Some(g')`. Numeric runtime IDs were not captured by
this static leaf and are not inferred from endpoint equality.

## Transition table

Locators are relative to `crates/yu-solver/src/` at the frozen source hashes.
Each bounded conclusion concerns actual native constraints and their consumers.

| Transition / owner | Bound fibers, context and work ownership | Bounded conclusion or missing evidence |
| --- | --- | --- |
| Observer pre-copy `x <= s`, then `s <= A(v_i)`; context_tests:5726–5740; extrusion:843–867 | Since level(x)<level(s), the former stores B(s,+,x). Each latter stores B(s,-,A(v_i)) and replays against x. Open views have no closed_weight (effect:759–772); source relations and their bound fibers have IDENTITY context. Replay of identity fibers has IDENTITY, with both original input BoundKeys and parents retained (context:3131–3208). | Completed pre-copy drain actually dispatches `x <= A(v_i)`, rather than merely retaining a dependency on it. |
| Original symbolic dispatch `x <= A(v_i)`; extrusion:843–867,409–570; effect:553–560 | Ordinary EffectRow-to-Allowance admission stores B(x,-,A(v_i)), attaches its processing relation through `candidate_context_bound`, and registers capture incidence `(g,x,v_i)`. The observer has no lower on x initially, so this does not yet forward an atom to g. Incidence also retains `(g,s,v_i)`. | The symbolic row itself is a registered incoming source of g before g's snapshot. This is the additional route absent from the observer's reported copied-source-pair census. |
| Positive `Visit(g,+,1)`; extrusion:89–179 | Allocates g', installs B(g,-,g') with an extrusion-processing fiber, and scans the current incoming-incidence bucket. For each of x and s, and each v_i, it schedules source Visit then IncomingAllowance. The incidence walk itself does not drain typed work. | It schedules copied cuts for x as well as s. No inference from equal endpoints is needed. |
| `Visit(x,+,1)` and `Visit(s,+,1)`; extrusion:89–179 | x is reused immediately because level(x)<=target; its bounds are not traversed. s is copied to s', gets B(s,-,s'), and selected-lower Work::Bound installs B(s',+,x), transferring the original B(s,+,x) fibers. | x'=x in this fixture. Merely inspecting the s' lower does not enumerate all continuation owners. |
| `IncomingAllowance(g',v_i,Key(x,+,1),old)` and corresponding s route; extrusion:295–327; context:3403–3416 | The common `(v_i,Some(g'))` map yields the same copied view v_i' for both x and s routes. Distinct i remain distinct. Installs B(x,-,A(v_i')) and B(s',-,A(v_i')). Each insertion attaches its owner-emission fiber; transfer attaches children of every original cut fiber, preserving post-check context and source set. `attach` interns an identical RelationId, so two origins do not imply two fibers (context:2609–2628). | x now has actual copied Allowance uppers. Initialization creates no direct current-pair replay, but the particular x had no initial lower to cross. These reconstructed cuts are executable future-check owners. |
| Subsequent Contribution q admitted to original x; extrusion:843–867,766–806 | Stores B(x,+,q). Its replay enumerates all retained physical uppers, including A(v_i), A(v_i'), and any actually present row link. For each newly paired fiber, the exact child context is IDENTITY when both inputs are IDENTITY; otherwise it is ordered `Replay { lower: c_lower, upper: c_upper }`. Dependencies retain both BoundKeys and RelationIds; replay-progress suppresses already covered quadrants, not a newly attached lower fiber. | Both copied cuts receive an actual typed `q <= A(v_i')` child. This establishes future activation for this ordinary lower on the observer's original x, despite absent direct Replay for B(s',+,x) versus the copied s' cuts. |
| Copied Allowance consumer and tail admission; effect:985–1019; lib:12378–12404 | If effect(q) is E, each cut consumes q without forwarding. If unmatched, each queues the same q to g'. `enqueue_task` creates a relation and Derived dependency from its current parent; it does not copy an arbitrary parent ContextExpr into the child (context:2754–2776; lib:12884–12920). All these contexts are IDENTITY here. Ordinary q-to-g' admission inserts a lower and replays its existing uppers. | Native nominal membership and unmatched forwarding hold separately for every retained v_i'. Coincident endpoint work may share a relation, while the separate cut dependencies remain. No source Catch eligibility law follows. |
| Original Allowance alternative and gamma link; effect:985–1019; extrusion:843–867,766–806 | Original unmatched q-to-g admission meets B(g,-,g'), producing an actual replay child q-to-g'. The link fiber was emitted by the structural Value processing relation. Original matched q emits no tail task. | This is an additional real route for a later original-x lower, not the only justification for copied-cut continuation. |
| Reused x with existing contents, unlike the observer's initially empty x | IncomingAllowance installs B(x,-,A(v_i')) by bare insertion even though x'=x. It does not replay x's existing lower set. If an unmatched Contribution q was already physically forwarded into g before its selected-side snapshot, positive g copying installs that same q into g'. If q-to-g is only pending, eventual ordinary admission to original g explicitly replays B(g,-,g') instead. | These are separate compensation routes for completed-before-snapshot and pending atom forwarding. A matching q needs no residual forwarding. Existing remapped symbolic contents and nonidentity contexts are not discharged merely by this account. Reuse of x itself does not turn bare upper installation into replay. |
| Queue transfer and completion; context:3281–3344; lib:12283–12368,12630–12692,12894–12920 | Replay children with acknowledgements transfer into the typed worklist. `ReplayDriveOutcome::Queued` leaves completion with the enclosing typed drain. Transport and Context run before Effect dispatch. The drain empties emitted work, settles pending qualified intrusion, runs diagnostics, completes replay acknowledgements, then returns/removes its frame. | Ordinary successful return covers emitted q-to-copied-cut and q-to-g' descendants. A stored fiber or Queued result alone is not this completion. A memo hit relies on prior completion of the exact admitted relation/current generation, not endpoint equality alone (lib:11513–11525). All-history memo correctness is outside this audit. |
| Genuinely remapped x: target l<level(x)<level(s), with original x-to-cut dispatch already complete | `Visit(x,+,l)` allocates x', snapshots only its lowers, installs B(x,-,x'), and records the parent pair. Its old Allowance uppers are not selected. Nevertheless the pre-existing `(g,x,v_i)` incidence independently schedules IncomingAllowance and installs B(x',-,A(v_i')). A lower later admitted directly on x' meets these cuts. A lower later admitted on original x also meets the actual x-to-x' link; ordinary admission of that lower on x' then replays them. | Completed original symbolic dispatch supplies a future-check owner even for remapped x. For nonidentity fibers the route via x-to-x' first forms Replay with that link fiber, and then Replay with the copied cut fiber. This is not silently equated with the original context operation. |
| Current lowers already on remapped x' and original forwarding complete before g snapshot | Any already forwarded unmatched Contribution present on g is selected into g'; original AnnotationMember additionally needs its actual shared view-map key. Matching atoms need no residual forwarding. The copied x' cuts and selected current x' lowers are installed by bare insertion. | This recovers the existing conditional atomic factorization. It does not prove activation of every current symbolic/context pair or already stored g' upper. The observer's empty x lower set supplies no evidence for those cases. |
| Original symbolic dispatch or atom forwarding still pending when g is scanned | If only atom-to-g forwarding is pending, its eventual ordinary g admission can meet the retained g-to-g' link. If `x <= A(v_i)` itself is still pending, `(g,x,v_i)` need not exist in the scanned bucket; later registration does not rerun that already finished Visit. The existing `(g,s,v_i)` still reconstructs s'-to-cut, and pending original dispatch, original-x links and gamma links remain possible compensation routes. | **First unsupported transition:** universally lifting the pending/remapped current symbolic continuation through those alternative routes before dependent rewritten-Value use. Needed evidence is their joint ordered fiber/discharge disposition, or an authenticated trace excluding all of them and showing a necessary absent consequence. No absence claim follows from missing direct replay or late incidence alone. |
| Qualified equality / later fresh use alternatives; intrusion:519–624; construction note §4 | Actual qualifying equality transfers both sides and replays merged pairs; fresh-bound restoration has its own explicit replay/completion owner. Unqualified parent/copy pairs are not merged merely to repair the diagram. These operations are not present as a universal pre-use hypothesis. | They must be included in any negative witness that actually reaches them. They do not supply the presently unavailable universal lifting premise by assumption. |

## Result and exact stop

The observer's completed-before-snapshot, unchanged-symbolic-row case has a
bounded commuting continuation for a subsequent ordinary Contribution lower:
original symbolic-cut admission registers incoming gamma incidence; gamma
copying rebuilds copied cuts directly on that same symbolic row; later lower
admission actually replays them; the typed drain owns their completion. The
same incidence argument supplies future checking on a genuinely remapped x'
when the original symbolic cut was registered before the scan. This conclusion
is derived statically; the observer did not measure that added continuation.

For an inherited nonidentity context, copied cut transport retains
`post_check_context(original_cut_fiber)`, while a source/copy link receives its
own actual construction fiber. A subsequent traversal through the link then
the cut constructs ordered nested Replay nodes. Neither Transport nor Derived
alone establishes equality of these operations with a missing direct current
pair. Even ordinary `enqueue_task` on atomic forwarding starts the child-local
context and retains parent ancestry separately. The detached evaluator's
ordered mix law (context:1682–1686) is not a live source/consumer theorem.
Thus no arbitrary context commutation or protection conservation is claimed.

The first unsupported transition remains the pending/remapped current-pair
case identified in the table, including the nonidentity ordered-context case.
There are two distinct time boundaries: original x-to-Allowance registration
must precede the incoming-incidence scan to reconstruct x's copied cut; an
atom's forwarded lower must precede g's selected-bound snapshot to be copied
as an already accumulated residual. The former does not imply the latter.
When the latter is pending, the positive g-to-g' link is activated by later
ordinary admission on g, rather than by its own bare installation.
This is an unavailable joint operational premise, not a demonstrated compiler
failure. The audit does not exhibit a necessary consequence absent from every
alternative and therefore supplies no negative counterexample. Repeating the
observer's direct Replay absence would not reduce that premise.

Recommended next action: have the constructive lane apply this direct
symbolic-incidence route to the parent and isolate the remaining live-context
or pending-dispatch obligation at its actual typed-drain/forwarding owner;
request an authenticated discriminator only for that reduced case. Preserve
the original source Catch bridge, quantifiers and residual categories.

## Checks, dependency freeze and limits

Commands used: bounded `rg`, `rg --files`, `sed`, `cat`, `sha256sum`, a
read-only path-absence `test`, and terminal-byte `tail | od`. Artifact trailing
whitespace search found no matches; its terminal byte was `0a`.
Initial broad combined reads were truncated;
the task-specific authorities, prior artifacts and actual code ranges used
above were subsequently read in focused chunks. No exhaustive repository
search is claimed. No Cargo, tests, builds, probes, mutations, seeds/ranges,
performance samples, Git command, child launch or interactive question ran.
There is no independent executable oracle: this audits the actual source
transitions and shares the primitive's valid-handle/successful-drain premises.
No checker transition assumptions are presented as source proof.

One static leaf, 20-minute wall cap; exact elapsed time, CPU and peak RAM were
not measured. Requested role: researcher with configured routing, no override;
effective runtime model/effort metadata unavailable. No parallel heavy process.
The primary supplies branch/commit identity; this leaf performs no Git check.
The frozen file hashes below match the primary's supplied artifacts and the
construction note's code dependency hashes. No observed dependency change.

SHA-256 (bare filenames are under `crates/yu-solver/src/`):

```text
ec7eca2ba441ac0f971c7a25bbe3411038396f5b9f726e7d2690f51348f21b7e candidate_context_tests.rs
ed3e213e943a553943784e409194723f64acb810a0bcf06607ee95b0eb4e4ed1 candidate_extrusion.rs
f414efa7efdb17644f4dfa6b0bba621c1bb7cccd0f83735c33a0acb875da6b91 candidate_effect.rs
6301ca80eec137df3f2c2c44e2edaa7dbdf1ed7a78c69617228888e63654e461 candidate_context.rs
4a2b87ebf6e5e219c06763bc4e589517fd48c575c89038f2a11fc1e6494fe90e candidate_intrusion.rs
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5 lib.rs
f234b87510c7d8f2b4841bca9a53985a007d6d1d71587b5aa9a015243287c077 notes/theory/2026-10-15-extrusion-current-cut-activation-construction.md
10e45154a2a3c20452a968d6f503f39512a3e497a23abc03fb76e0828c16860e notes/progress/2026-10-15-extrusion-current-cut-activation-falsifier.md
b8a8e4b521f4285c5d30c761eb2efc9cf6a7ac0c8f96e6e907f226f83d9fbb2e notes/progress/2026-10-15-extrusion-current-cut-activation-observation.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81 notes/design/2026-10-11-yulang-inference-top-level-principles.md
d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98 notes/design/2026-10-10-contextual-residual-lineage-selection.md
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc notes/design/2026-10-10-contextual-attachment-admission-design.md
469677cc50b1dfd5327fa330e85bb83124c9e17cec391866dbf71ee23c40d50b notes/theory/2026-10-14-native-handler-residual-cut.md
1781952afd258038345ba2dbe5a3c425bc193a04c7d77c72b2eb52a636466822 notes/theory/2026-10-15-native-residual-view-lineage-lifecycle.md
4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9 rules/compiler-engineering.md
```

Unverified: complete source Catch admission/eligibility and original-sigma
correspondence; all current remapped symbolic pairs; pending-dispatch histories;
arbitrary ContextExpr evaluation/termination; complete capture/freshening
coverage; all-history memo and publication barriers; suspension and abnormal
paths. No new restriction or required production mechanism is proposed.

## Commit packet

- Exact leased path: `notes/progress/2026-10-15-copied-symbolic-cut-continuation-owner-audit.md`.
- Baseline SHA: `d8a6209c1dc181858948c4d811259aa20683d64e`.
- Changed dependency hashes: none observed; pinned observer hash matches.
- Claim/review status: unreviewed bounded static correspondence and explicit
  remaining premise; producer claims no independent review or gate closure.
- Checks already run: focused static owner/consumer/fiber reads, dependency
  SHA-256 checks, output-path absence, trailing-whitespace and terminal-byte
  checks; no executable verification.
- Proposed checkpoint message: `research: trace symbolic copied-cut continuation owners`.
- Shared deltas for primary/curator: record the direct symbolic incoming-gamma
  incidence route and its before-snapshot condition; retain pending/remapped
  contextual activation and original H1/H2/U OPEN, H3/P disabled. No shared
  task, theory map, authority or index was edited.

Writes stop at handoff. Primary owns adjudication, independent review and Git.

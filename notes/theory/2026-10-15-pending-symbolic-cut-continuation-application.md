# Applying the symbolic-incidence continuation to H2

Status: reviewed bounded conditional derivation and source/operational
obstruction. A fresh M2 `compiler_referee` found no findings in this note and
its paired falsifier. This applies the reviewed owner audit; it does not
establish the original H2 theorem or authorize implementation.
Exclusive lease: this file only. Leaf; writes stop at handoff.

## 1. Frozen parent, narrower claim and authority

The original parent is unchanged: for every originally admitted shallow Catch
H, under its one original scoped assignment sigma, preserve H's scrutinee,
original operation/value-arm binders, provider, raw resumptions and complete
dependent interfaces. Remove exactly eligible scrutinee contributions actually
consumed by H. Preserve protected and independent contributions, unmatched
requests, outside-arm contributions and raw-resumption contributions, including
same-family survivors and future effects. Preserve residual constructor
lineage, within-use sharing and between-use independence through the existing
levels, extrusion, capture/generalization, freshening and qualifying Value-SCC
parent/copy intrusion. No marginal projection receives an independently chosen
witness or replacement sigma.

The selected local introduction remains at the original upper Function demand
`f <: A [Ein] -> [Eout] B`'s `Eout` only. This step grants no new protection to
`Ein`, positions inside B or an existing provider/recursive Function lower's
output. Independently inherited protection remains. Empty executable words do
not certify that a source contribution is unprotected.

The narrower claim C is conditional native continuation, not a restriction on
that parent. Fix a finite set of distinct original open Allowance views v_i,
with heads J_i and tail g, an actual source s, and an actual symbolic lower x.
All handles are live and valid and the input native graph is consistent.
Assume all of the following operational premises:

1. Ordinary admission of `x <= s` and the original `s <= A(v_i)` comparisons
   has actually dispatched `x <= A(v_i)` and registered `(g,x,v_i)` before the
   positive Visit(g) incidence scan. Mere queued or stored s-to-cut work is
   insufficient.
2. One successful extrusion at target l copies g to g' and reuses x because
   `level(x) <= l`. Its one view map reconstructs
   `v_i' = R(v_i,Some(g'))`. No discarded output or unqualified equality is
   inserted into this history.
3. After extrusion returns, an ordinary Contribution q is physically admitted
   as a lower of the canonical x. Relevant retained cut, construction and
   lower-admission fibers have actual IDENTITY contexts. This is the audited
   plain case, not a test for protection based on stored empty words.
4. The emitted work completes through its actual typed-drain owner. An exact
   relation/current-generation memo hit is reusable only on its established
   completion premise; no all-history memo theorem is supplied here.

Required C conclusion: every retained copied view v_i' receives activated
checking of q, or reuse of that exact completed check. Membership in J_i emits
no q-to-g' tail task at the plain consumer; nonmembership emits the same q to
g', whose ordinary admission checks its current uppers. Subsequent ordinary
g' upper admissions check the stored q as well. Exact view identities and
Replay input dependencies survive relation interning. C asserts no equality
of arbitrary gamma valuations to a least residual.

Exclusions: no complete Catch admission/eligibility or complete Call bridge,
new source restriction, attachment/provider/witness merging, inferred
protection classification, arbitrary-context termination, abnormal-path proof,
source-qualified counterexample, soundness/principality closure, or production
cutover. H1/H2/U remain OPEN; H3/P remain disabled; production/F5 is separate.

Baseline supplied by primary: `055ef0de1dd6d970f464b98a51922c2e47d13f06`,
branch `research/simple-sub-intrusion`; native source baseline
`d8a6209c1dc181858948c4d811259aa20683d64e`. Governing sources are top-level
inference principles §§1–5/1.1; residual-lineage selection, Selected policy and
Preserved contract; attachment/admission §§3–4; and directional inferred
protection §§1–2. The later top-level policy governs older general rollback
clauses. Compiler-engineering's Natural compiler behavior and proof-obligation
economy governs the stopping decision. The reviewed owner audit's transition
table and Result and exact stop are the immediate evidence; current-cut
construction §§2–5 and native-view-lineage §§3–6 remain dependencies. Native
handler-residual-cut §§3–5 supplies P and its separate U premise.

## 2. Direct derivation at the actual owners

Source locators below are relative to `crates/yu-solver/src/` at the hashes in
§6. Write B(x,+,q) for the actual lower BoundKey and B(x,-,A(v)) for its upper;
these are existing native keys. Fibers mean `bound_relations(B)`, not origin
counts or physical duplicate counts.

First, ordinary `x <= A(v_i)` dispatch stores a negative Allowance upper on x
and replays its current lowers (`candidate_extrusion.rs:843–867`). Insertion
registers capture incidence at `candidate_effect.rs:553–560`. Thus the completed
original admission supplies a separate incoming-gamma entry `(g,x,v_i)` for
each original view, in addition to the entry whose source is s. This is the
construction that retains the symbolic continuation.

Second, positive Visit(g) reads those entries and schedules Visit(x) followed
by IncomingAllowance for every v_i (`candidate_extrusion.rs:165–179`). Visit(x)
returns x unchanged at/below l (89–95). IncomingAllowance uses the same
operation-local `(old view,mapped tail)` map as the s route and installs
`x <= A(v_i')` (295–309). Consequently the copied source cut and the direct x
cut name the *same* v_i', while distinct original v_i yield distinct copied
IDs. This follows from the construction key, not equality of heads, source
rows or tail rows. Bound transport retains post-check context/source
association and a Transport dependency (`candidate_context.rs:3403–3416`).

This second step alone is storage and attachment, not replay. In particular,
it does not check pre-existing x lowers. C concerns the later admission in
premise 3; it does not need an unproved current-pair activation rule here.

Third, actual later Contribution-to-x admission inserts B(x,+,q) and calls
`candidate_replay_bound` (`candidate_extrusion.rs:843–867,766–806`). Enumeration
visits every physical opposite upper, including each retained A(v_i'). For
each new fiber quadrant, `candidate_context_begin_replay` (3131–3216) retains
both input BoundKeys and parent RelationIds. Its child has IDENTITY when both
inputs have IDENTITY; otherwise it constructs ordered Replay. Interning an
identical child does not delete the distinct Replay dependencies. Progress
heads suppress covered quadrants, not a newly retained lower fiber. Exact
previously completed relation reuse has the separate premise stated in C.

Fourth, `candidate_context_drive_replay` transfers emitted children into
`enqueue_item` (context:3281–3344; `lib.rs:12894–12920`). The live typed drain
transports and executes context before Effect dispatch
(`lib.rs:12072–12119,12283–12368`). Actual IDENTITY returns ordinary dispatch
(context:2964–2973); `dispatch_live_item` reaches the native Effect consumer
(`lib.rs:12378–12404,11735–11743`). At
`candidate_effect.rs:985–1019`, q's resolved effect is tested against J_i:
membership returns, and nonmembership queues the exact q to canonical g'.
This applies separately to every v_i'; nominal equality of q's effect is not
used to merge the cuts or grant a source cancellation license.

Finally, ordinary q-to-g' admission inserts a lower and replays its current
uppers; later ordinary upper admission replays the existing lowers. Queued
replay is completed by the enclosing typed drain, not by the return value
Queued itself. Worklist exhaustion, qualified-intrusion settlement and
diagnostics precede acknowledgement/ReturnReady
(`lib.rs:12283–12368,12630–12692`). Under C's successful-completion premise
these emitted comparisons finish. This proves C's bounded continuation from
the native owners without assuming a missing replay for the copied s' pair.

## 3. Application to the unchanged parent

C discharges one *operational subcase* needed by H2: completed pre-scan symbolic
registration, reused x, a later ordinary Contribution lower, actual plain
fibers and successful emitted-work completion. It supplies future checking
even when no direct Replay dependency exists between the copied s' lower x
and s' cut. Repeating that direct-Replay census cannot refute this continuation.

To use P at an actual H boundary, U must independently map H's original typed
contributions to this plain filtered input and preserved outer/bypass outputs:

| Original category under the same sigma | Required source application premise; what C supplies |
| --- | --- |
| Eligible scrutinee contribution actually consumed by H | Authentic delivery and operation/arm coverage must license filtering. C then supplies nominal native checking for its stated history. Head membership alone does not establish eligibility or actual consumption. |
| Protected or independent same-family survivor | U must keep its live bypass or an independently justified contextual consumer. C grants no cancellation license for it and cannot establish that bypass. |
| Unmatched request, including another operation in a handled family | Original ordered matching/coverage must retain the request and suffix. A nominal family head cannot stand for complete operation coverage. C supplies no coverage proof. |
| Outside-arm/pattern/default/guard/response computation | Its source-owned outer projection must remain separate from the scrutinee cut. C does not redirect this projection through the cut. |
| Raw resumption and its dependent future interfaces | Its original binders, scope and outside-H effect flow must be retained, with authentic complete Call/typed transport. C does not synthesize that correspondence. |

Thus there is a conditional application of C on U-certified plain histories;
there is no implication from C to the universally quantified parent. The first
missing *source application* premise is authentic typed eligibility/coverage
and preserved bypass/outer flow at source formation, typed transport and Catch
selection. This is the existing H1/U responsibility, not an invitation to
restart its proofs or narrow admitted H. Even granting that correspondence
conditionally, H2 still requires the native cases in §4. A proof of one native
history cannot quantify over all of them by changing the meaning of H2.

## 4. Remaining cases and the first native unsupported premise

There are two distinct times: original symbolic-cut registration before the
incoming-incidence scan, and original forwarded-lower accumulation before g's
selected-bound snapshot. Neither timing premise implies the other.

| Case | Established native route and exact remaining issue |
| --- | --- |
| Registered x genuinely remaps: `l < level(x)` | Visit allocates x', copies selected lowers and retains x-to-x'. Pre-scan `(g,x,v_i)` reconstructs x'-to-A(v_i'). A later ordinary Contribution admitted on x' activates these cuts; one admitted on x reaches x' through its actual upper link. Existing mapped lowers and copied cuts, however, are installed by bare insertion. Their complete current contextual consequences remain unsupported. |
| Original `x <= A(v_i)` is pending at the scan | `(g,x,v_i)` need not yet be registered. Its later registration does not rerun the completed Visit(g). The s incidence still reconstructs s'-to-cut; eventual original-cut processing, x-to-x' and g-to-g' remain real alternatives. No loss follows solely from late incidence. Their joint disposition of every mapped symbolic continuation remains unproved. |
| Original unmatched atom-to-g is pending | For a Contribution q, if its exact lower is already physical at g's snapshot, Work::Bound copies that same q into g'. If its ordinary admission on g occurs later, that admission replays the retained g-to-g' upper. Under actual plain contexts and successful emitted drain, the latter emits q-to-g'. This timing factorization concerns the exact Contribution; AnnotationMember requires its actual shared view-map key. Neither route by itself proves checking against an upper already installed on g' by bare copying. |
| Retained nonidentity ordered context | Transport copies `post_check_context(original_cut_relation)`, including source association. Link traversal and subsequent cut checking form additional ordered Replay nodes. Endpoint membership, Transport ancestry or Derived ancestry does not establish that these have the required direct comparison's checking/discharge meaning. Atomic forwarding through `enqueue_task` creates a child-local context and separately retains Derived ancestry; it does not copy arbitrary parent context. |
| Typed-drain completion and dependent reuse | A drain completes work actually emitted, including replay receipts; it is not a generator for unqueued current pairs. Structural Value dispatch queues the rewritten Value comparison after extrusion (`lib.rs:12469–12516`), without establishing a universal internal-effect pre-use barrier. Exact memo generation/completion, suspension continuation and publication remain separate obligations. |

The first unsupported *native lifting* premise is this: for a pending original
symbolic cut or pre-existing remapped symbolic lower, the actual original-cut,
source/copy-link and gamma-link alternatives jointly execute or validly
discharge every required transported cut continuation, with its original
ordered parents, shared sources and active checks, before a dependent result
is reused as complete. No inspected owner establishes this universally.

More locally, let c_cut be the transported cut fiber context and c_map the
transported current-lower fiber context. The unperformed direct comparison
would construct `Replay(c_map,c_cut)`. An actual link path first constructs
`Replay(c_old,c_link)`, admits its resulting bound with that relation's
post-check context, and then constructs Replay with c_cut. The implemented
constructors do not equate those operation trees or their source sets. The
required premise is their source-established operational checking/discharge
correspondence in the histories where this path is used, not an invented
equivalence asserted from matching endpoints. The detached ordered mix algebra
alone cannot supply that live premise. All-IDENTITY C avoids this equality
question only for its explicitly delimited operational subcase.

Owning seam: selected-side initialization and incoming-cut reconstruction in
`candidate_extrude` (`candidate_extrusion.rs:89–179,295–330`), with relation
transport/replay/forwarding at `candidate_context.rs:2754–2776,3131–3216,
3403–3416`, and actual dispatch/completion at `lib.rs:12283–12368,
12469–12516,12630–12692`. Current storage ends after insertion/incidence/evidence
(extrusion:409–570). These owners know emission, contextual discharge and
completion; the concrete membership branch does not know the missing joint
history. Qualified equality and fresh-bound restoration have explicit replay
owners, as in the reviewed lifecycle/construction notes. They must be included
when reached; they are not universal pre-use assumptions or repair merges.

This is an obstruction to the proposed universal derivation, not a false
theorem, a missing-effect counterexample or a proof that no compensation route
exists. No source-qualified necessary consequence has been shown absent from
all alternatives.

## 5. Proof economy and one next action

The earlier lineage induction and atomic-link factorization left current
symbolic/context activation open. Their existing audit classified this A/B
when required for accepted ordinary inference, and reconstruction from stored
evidence alone as D debt. This application consumes new owner evidence: the
direct symbolic-incidence route proves C, so it removes a real subcase from
the unsupported universal lifting attempt. It does not reclassify H2, add a
third equivalent reconstruction, or adopt a carrier/scheduling change.

One next action for the primary: assign an authenticated, bounded disposition
trace for a genuinely remapped symbolic lower with original x-to-cut dispatch
pending at the gamma scan, recording the actual ordered relation fibers,
original/link/gamma alternatives, discharge and typed-drain receipts through
the first dependent rewritten-Value use. The discriminator must establish the
required consequences or a necessary absent consequence across *all* reached
alternatives. Do not spend that packet on another direct-Replay absence census
or assume a nonidentity source context that no constructor produced. No Cargo
or executable budget was used here; future verification remains primary-owned.

## 6. Dependency freeze, checks, resources and commit packet

Commands: focused `cat`, `sed`, `rg`; read-only branch/HEAD/status and named-path
Git diff; `sha256sum`; output-path absence and note whitespace/newline checks.
The read-only Python note-integrity check verified all 25 listed dependency
hashes, found no trailing whitespace and confirmed a terminal newline.
Initial combined reads exceeded capture limits; decisive task, authority and
owner ranges were subsequently read in bounded chunks. No exhaustive repository
coverage is claimed. The named native source paths have no diff from d8a6209c1.
During this lane HEAD advanced to `9675907dfb1d37ab46e31573f0470e2f29de3fc5`;
the supplied audit changed only its review-status text relative to 055ef0de1.
Its technical transition table is unchanged. The hashes below freeze the
actual supplied reviewed input and task locators; task files are coordination
inputs, not independent semantic authority.

No compiler/test edits, probes, Cargo/build/test process, measurements, child
launch, Git mutation or shared-record write occurred. One proof leaf and
lightweight read commands only; assigned wall cap twenty minutes. CPU, peak
RAM and exact elapsed proof wall time were not measured. Requested normal
routing is Sol/high; effective runtime model/effort metadata is unavailable
and remains unknown. `.codex/config.toml` registers prover and Sol/high defaults;
the inspected role has no model/effort pins. This does not prove runtime
inheritance, hot reload or a native override. No Astra assignment was launched.

SHA-256 dependencies (bare `.rs` names are under `crates/yu-solver/src/`):

```text
1e6d42dc59ca4e82c62fa78fd4bcb6188f72b35aac964095883fcf03bb5beaf6 notes/progress/2026-10-15-copied-symbolic-cut-continuation-owner-audit.md
f234b87510c7d8f2b4841bca9a53985a007d6d1d71587b5aa9a015243287c077 notes/theory/2026-10-15-extrusion-current-cut-activation-construction.md
1781952afd258038345ba2dbe5a3c425bc193a04c7d77c72b2eb52a636466822 notes/theory/2026-10-15-native-residual-view-lineage-lifecycle.md
469677cc50b1dfd5327fa330e85bb83124c9e17cec391866dbf71ee23c40d50b notes/theory/2026-10-14-native-handler-residual-cut.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81 notes/design/2026-10-11-yulang-inference-top-level-principles.md
d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98 notes/design/2026-10-10-contextual-residual-lineage-selection.md
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc notes/design/2026-10-10-contextual-attachment-admission-design.md
6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7 notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md
f414efa7efdb17644f4dfa6b0bba621c1bb7cccd0f83735c33a0acb875da6b91 candidate_effect.rs
ed3e213e943a553943784e409194723f64acb810a0bcf06607ee95b0eb4e4ed1 candidate_extrusion.rs
6301ca80eec137df3f2c2c44e2edaa7dbdf1ed7a78c69617228888e63654e461 candidate_context.rs
4a2b87ebf6e5e219c06763bc4e589517fd48c575c89038f2a11fc1e6494fe90e candidate_intrusion.rs
c8ef7cc472f0dcb60d793c6f9b4f6ba1aefb76f919ff2a3ce9310f85eb647dcd candidate_scheme.rs
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5 lib.rs
c679f82c2b7229790f5b8bce148ef83823a4f22967f5b4b14e2cd3b9ee392a34 tasks/current.md
487264d861413e23d3293c2868e4bb0d6952f74b8200d929438388704e2a4336 tasks/effects-handler-next.md
ee791ca3593cf52dbe1237b5bb5409701de689b24b3281be3e96873109a8fde4 tasks/research-lab.md
8b418f8ed02606205ecdfedcf5da72dae074e1c799237b8cc034fdfbd71ab7a1 rules/agent-orchestration.md
3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69 rules/research-lab.md
e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1 rules/design-authority.md
4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9 rules/compiler-engineering.md
2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6 rules/git-concurrency.md
993d4c2a7743669b4c7a6c46f054c4caae492873f0a5f20a1ea566ebf9dea3c1 .codex/config.toml
485a26c7409e16c692ad10095031ab0e7084726ec5da5666082b3bbc4a5daf98 .codex/agents/prover.toml
db55dfb7568805ac6b6372fe8bc05cc00731ae5b5ed33c6af72007a7ce885810 /home/momota1029/.codex/skills/yulang-proofs/SKILL.md
```

Unverified scope: universal pending/remapped contextual continuation; source U,
authentic complete Call, dynamic typed receiver/protection and Catch coverage;
all-source capture/freshening; all-history memo/publication barriers;
termination and suspension/abnormal paths; full effect hygiene, soundness and
required principality. No new semantics or implementation policy is proposed.

Commit packet:

- Exact leased path: `notes/theory/2026-10-15-pending-symbolic-cut-continuation-application.md`.
- Baseline SHA: `055ef0de1dd6d970f464b98a51922c2e47d13f06`; native sources
  `d8a6209c1dc181858948c4d811259aa20683d64e`.
- Changed dependency hashes: native sources unchanged; supplied owner audit
  has review-status-only changes from 055ef0de1, frozen at the hash above.
  Shared task locators were read at their listed live hashes.
- Claim/review status: fresh M2 `compiler_referee` found no findings in this
  bounded conditional derivation/application and its paired falsifier. Explicit
  source and native obstructions remain; no parent or theorem promotion.
- Checks already run: focused owner/consumer reads, named source-baseline diff,
  dependency hashes and output whitespace/newline checks; no executable checks.
- Proposed checkpoint message: `research: apply symbolic-incidence continuation and isolate pending context`.
- Shared-record deltas left for primary/curator: apply C to H2's completed
  pre-scan/reused-row/plain-later-Contribution subcase; retain current remapped,
  pending registration, exact ordered-context and pre-use completion premises
  at the named native owners, and source H1/U separately. H1/H2/U stay OPEN;
  H3/P disabled. No shared record was edited. Primary owns fresh review,
  adjudication and Git integration; producer writes stop at handoff.

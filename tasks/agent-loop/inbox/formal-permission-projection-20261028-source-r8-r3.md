# Formal permission projection r8-r3: admitted helper effects and context boundary

Status: FROZEN revision 1 on submission; producer-authored, NOT_REVIEWED.
Outcome class: incomplete static source evidence and conditional derivation.
STOP at an unadmitted owner. No reachable falsifier or preservation theorem.

## Identity, authority and authentication

Actual assignment/session: `/root/formal_permission_projection_source_r8_r3`,
as delivered by NEW_TASK; separate session UUID unavailable. Startup ACK and
active-work receipt were sent to the primary before source bodies were read.
Requested model/effort were initially unavailable, then observed as requested
`gpt-6-luna` / `high` in current.json; effective model/effort remain UNKNOWN.
No descendants, prover launch, independent self-review or Git command occurred.
The primary owns ACK recording and worker-state adjudication.

Primary baseline: `3cc8a897fe08980576b1582952a95acab55f09d2`.
This is the authenticated contract's baseline, not an independently resolved
Git revision. Working source bytes matched every prescribed baseline pin before
body analysis. Hash equality authenticates bytes, not their semantic properties.

| Input | SHA-256 |
| --- | --- |
| Original r8 contract | `99835a8d22b3b61c90500706245fd5e28aeee238905cca1eb217d8c2f274cd46` |
| Amendment 01 | `3c2782ff6e375b4f22278ead3d7f5834b4d2d291f83ab6b9b7b68624c2b040d1` |
| Amendment 02, governing packet | `c50bb1d2f500f6604eab456de1ea8c157415ed608518c5ff3be54e675aa3f7fc` |
| Frozen r8 outcome, history/formal-permission-projection-20261028-r8-outcome.md | `c69858fa3119d304d5990b8f520855becfe9e81d5f4ab6feba21c119727ade54` |
| Reviewed r8-r2 source | `19bffa5c2fdfdd38d8205dc1368b61b475811acaf2d00073cccbda0f6fecb8c9` |
| Independent r8-r2 review | `6ff6c8e8a9c343c93aaf673903b69acce4633f0df52a035844b1af6f9870f99a` |
| crates/yu-solver/src/candidate_source.rs | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| crates/yu-solver/src/candidate_intrusion.rs | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| crates/yu-solver/src/candidate_effect.rs | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| crates/yu-solver/src/candidate_scheme.rs | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| crates/yu-solver/src/shadow_apply.rs | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| crates/yu-solver/src/lib.rs | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| crates/yu-solver/src/term.rs | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| tools/inference-playground/src/scheme.rs | `82019fd22ad565c753461d8962934fcfe8e6663f8a7971b4fcbc5f5067026be0` |
| notes/design/2026-10-10-annotation-effect-hygiene-integration.md | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| Newly admitted crates/yu-solver/src/candidate_extrusion.rs | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |

All MATCH. Dependency hashes changed: none. The old outcome-pin mismatch stays
resolved only by amendment 01; no historical artifact was rewritten.

Read root/base instructions, research/design/Git rules, current state, README,
sprint child-scope instructions and the sequential r8 contracts/outcome/review.
The yulang-proofs skill's conditional/source distinction applies; this child
does not acquire its primary-only dispatch duties. Governing selected meaning
remains annotation policy §§1, 1.1, 1.2 and 4, with §6 retracted, and inference
principles §§4–5. No semantic reinterpretation or new general rollback duty.

## Objective and precise claim

Audit the interval starting with `state.rep(copy)` / `state.rep(parent)` at
candidate_intrusion.rs:613–614 through the final parent write at :679 or :691.
For distinct same-kind selected roots r,s, the requested equation is:

    Immediately before F[r] := s, r,s are still in range, F[r]=r, F[s]=s,
    and every effective intervening forest write has a correctly ordered
    inverse entry associated with the same checkpoint.

The in-range and closed-forest premises at selection are explicit hypotheses,
not consequences of a missing-entry representative fallback. A stronger
sufficient condition would leave both forests and the active checkpoint/log
association unchanged throughout this interval. Neither condition is established
transitively by this packet. The following inventory distinguishes direct writes
from uninspected callees; an inventory is not a transitive effect certificate.

## Newly admitted helpers

`candidate_opposite_count` (candidate_extrusion.rs:877) canonicalizes the owner,
then reads the addressed Value/Effect bound row and adds the two selected vector
lengths. It directly writes no field. Non-row endpoints return IdentityExhausted;
indexing and unchecked usize length addition are not independent row-validity
proofs. `candidate_opposite_bound` (:902) canonicalizes the owner, reads either a
direct row entry or exact atom entry according to n, then canonicalizes that
endpoint. It directly writes no field. Invalid indices can panic; an unsupported
owner is unreachable!(). Their bodies expose no direct reentrant merge.
Canonicalization dispatch at candidate_intrusion.rs:293 selects canonical_value
or canonical_effect; no transitive theorem is inferred merely from &self.

`candidate_insert_copied_bound` (:619) reads the context's scoped_enabled and
processing fields. In unscoped mode it calls
candidate_insert_bound_with_evidence with OwnerEmission. In scoped mode it calls
context.evidence_snapshot(source,None), adds MissingOriginAssociation to that
snapshot, then mutably calls context.import_evidence and delegates insertion
with BoundTransport. Those context bodies are outside this packet. The body
itself does not assign either representative vector, but this does not establish
the complete effect of its calls.

Its admitted insertion callee (:694 onward) canonicalizes owner and bound,
checks the owner against bounds/effect_bounds length, selects a physical lane,
calls candidate_bound_origin_with_evidence, reserves context evidence emission,
journals the destination bound row, reserves and appends the selected physical
bound entry, and updates bound flags/counters. It reads the appended slot back
and errors on a mismatch. Here capture=false, so the conditional
candidate_register_capture_bound call is skipped. It marks intrusion.dirty,
calls context.evidence_emit, and samples resources. This is a concrete bound
storage mutation path, not a forest write in its direct statements.
The physical readback helper reads the addressed vector without direct writes.

## Admitted transfer, splice, journal and resource effects

`candidate_transfer_bound_origins` (candidate_effect.rs:685) reads a context
bound cursor/entry chain and, for each entry, calls
candidate_context_transport_witness_with_evidence at :697. It then reads the
origin table; for each origin it obtains/imports an evidence snapshot and calls
candidate_bound_origin_with_evidence. It directly assigns no forest entry.
The first loop has an unrestricted session helper call whose body is absent
from the admitted union, so the receiver of the outer helper is insufficient
to prove root or checkpoint stability.

`candidate_bound_origin_with_evidence` (:530) reads processing/provenance,
calls context evidence_attempt, and conditionally calls context relation helpers
(OwnerEmission uses candidate_context_bound; scoped BoundTransport takes None).
It reserves origin and undo containers, updates origins/origin_keys and
evidence_bytes, records origin undo, and delegates evidence admission/sampling.
The context helpers are uncovered dependencies; direct metadata writes do not
certify their transitive effects.

`candidate_splice_capture_incidence` (:651) has concrete metadata effects:
reads source/destination buckets, reserves undo and destination capacity,
records both old buckets and the destination-tail next link before modifying
that link, removes the source bucket, installs the destination bucket, then
samples resources. Its direct writes affect capture incidence/links and their
undo, not values/effects parent entries. This local journal-before-write order
does not establish the separate forest log's full checkpoint association.

`push` in candidate_intrusion.rs:91 reserves the passed Vec and appends the
entry. Consequently the merge's :624–630 block appends `(copy,from)` to the
current intrusion undo before the row-journal call and bound-copy helpers,
when such undo exists. Under the in-range self-root premise, from is the old
parent value. No-undo execution has no such inverse entry, so a rollback claim
must separately require the intended checkpoint exists.

`journal_value_row` / `journal_effect_row` (lib.rs:9548/:9597) skip absent,
new or already-seen rows; otherwise reserve their row-undo vector, observe
capacity changes, mark the row seen, and append bound-vector lengths/capacities,
flags, level, metadata and mark. They directly modify route-journal bookkeeping,
not forest parents. Their observe_typed_route_capacity call (:9253) can mark
route_attempt_physical_change, invoke sampling, and mark sample failure.

`preflight_bound_capacity_growth` (:16578) checks counter headroom without direct
writes. `record_bound_capacity_growth` updates payload bytes/counters and
retained growth accounting; `record_incoming_bound_capacity_growth` (:16669)
also updates route growth/accounting and delegates resource observation.
These statements do not directly write the forest. Error-return paths are
present and are not successful merge/capture witnesses.

Resource sampling follows lib.rs:10774 -> :10791 -> :10821 -> :11017.
The visible wrapper gathers retained-byte counts, including intrusion/undo
bytes, and passes mutable execution counters plus shared container references
to resource accounting. Its graph/undo size reads themselves delegate into
effect/context accounting. This partial trace leaves those transitive size
helpers unverified; no purity claim follows from the resource helper's name.
It supplies no evidence that an active checkpoint is replaced, but absence of
such evidence is not a complete transitive proof.

The final direct branch writes levels/non_generic and then exactly one forest
entry, effects[from]=to or values[from]=to. Later context canonicalization,
generation updates and replay are after this interval; their preservation and
all other merge invocations remain outside the proved result.

## Exact boundary and conditional composition

Additional required owner: `crates/yu-solver/src/candidate_context.rs`.
Its module is declared by admitted lib.rs:229; a filename-only rg --files search
confirmed the file. No bytes/body from that owner were opened or authenticated.
The required equations include the effects of copied-bound evidence calls and,
particularly, `candidate_effect.rs:697`'s
candidate_context_transport_witness_with_evidence on the selected forests and
route_journal/intrusion checkpoint association. The admitted-union declaration
search located only that callsite, not its definition. Body inspection stops
here; this is not a claim that :697 is the first dynamically executed unknown
call on every branch. Earlier journal/resource and evidence paths also have
unverified transitive calls.

Conditional composition with reviewed r8-r2 is precise: assume (i) the selected
same-kind roots are distinct and in range in a closed finite forest; (ii) every
intervening transitive call preserves these two root entries and their vector
lifetimes, and preserves the checkpoint/log association; (iii) no effective
intervening forest write requires an out-of-order inverse entry. Then the
prospective `(copy,from)` entry records the actual old parent, and the final
link preserves the forest by the r8-r2 root-link lemma. With complete inverse
logging across all subsequent operations on the same checkpoint, r8-r2's
reverse-replay/truncation lemma applies. Premises (ii)–(iii) remain unsupported
at the owner boundary above. This is a conditional local implication, not an
established reachable-session preservation result.

No r7 premise is removed. B's transitive construction/parameter/domain/store/
export association, D's successful capture/export, reachable forest/lifetime
preservation, r1 Lean verification, parent A/B, source/native, full inference/
executor and production remain OPEN. No reachable cycle, invalid successful
association or successful wrong-image export was established. No minimized
counterexample exists in this packet; no synthetic state is substituted for one.

## Checks, coverage and resources

Only static cat/sed/rg/rg --files, sha256sum, clock and the single artifact write
were used. Required authentication passed. One initial outcome locator under
inbox did not exist; the actual frozen history locator was then read and matched.
Some large instruction/read outputs were truncated by output limits; the audit
does not claim an exhaustive transitive inspection. No tests, probes, builds,
Cargo, Lean/Lake, compiler edits, Git, network or quarantined-path reads/writes.
There is no executable oracle, seed/range, mutation campaign or independent
formal checker. The reasoning shares ordinary Rust/std and sequential-call
semantics with the source; hashing is independent byte authentication only.

Budget: <=200 seconds, one CPU, 1 GiB RSS. Work began with startup ACK before
the first recorded clock at 22:45:39 UTC; owner-stop clock was 22:46:36 UTC on
2026-10-27. Exact launch-to-stop duration, total CPU and peak RSS are UNKNOWN.
Only short sequential shell reads/hashes ran; charge the full 200-second grant
and preserve all earlier charges. No descendant/resource renewal requested.
Writes cease with this revision; freeze before non-author review.

Recommended next action: primary adjudicates the minimum context-helper effect
boundary, then admits a bounded authenticated context-owner packet if warranted.
Its success criterion should certify the complete transitive interval effects
and checkpoint association, not repeat the already observed direct-write scan.

## Commit packet

- Exact leased/changed path: `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r8-r3.md` only.
- Baseline SHA: `3cc8a897fe08980576b1582952a95acab55f09d2`, primary pin.
- Dependency hashes changed: none; all sixteen authenticated pins above MATCH.
- Review status: NOT_REVIEWED, frozen producer evidence; no independent review claimed.
- Checks already run: required SHA-256 authentication; admitted helper/field/callsite inspection; filename-only next-owner resolution; no executable verification.
- Proposed checkpoint commit message: `research: trace permission merge helpers to context effect boundary`.
- Shared-record deltas intentionally left for primary/curator: record STOP and full 200-second charge; retain all OPEN gates and conditional r8-r2 lemmas; record admitted helper inventory plus unverified context/resource dependencies; decide any next authority amendment and independent review. No shared records edited.
- Worker state: STOP on submission; writes stopped; no descendants or unresolved descendant leases.

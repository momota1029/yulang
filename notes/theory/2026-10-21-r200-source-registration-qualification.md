# R200 — Source registration and qualification audit

Status: source-owner correspondence established; universal provider-Capture coverage remains OPEN. No semantic approval or production gate is claimed.

## Exact sources

| Owner | SHA-256 |
| --- | --- |
| `candidate_value_graph.rs` | `7ba8d2a38487e5ad204fc6b19a3aa5a6f4984ee03249a9fc2210ee01993594ae` |
| `candidate_source.rs` | `937ce62065be19473fcb37a104f1aaf68e9a9431b8683d8e9a33d221c9e6c26a` |
| `candidate_context.rs` | `a08ff10637f1ff9a67005f96c5e1bc26a44778f911944054a25cf28bec5ce733` |
| `candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |

R177/R183 remain the parent application receipts. This audit read only the four pinned owners and those receipts. No source edits, Cargo process, or tests occurred during R200.

## Source Apply event construction

`ConstraintBatch::emit_candidate_source` first requires the exact LocalSource object owned by the HIR, checks the matching Definition or Expression root, and verifies every source expression occurrence is owned. It then records the expression-to-source-root association and calls `references.retain_source(source)`.

`Graph::retain_source` maps the source root to a Module or Expression Value, walks the local source tree, and assigns nested binding initializers to their exact Local Value owner. Resolved Names add owner-to-Value edges. Catch and Case binders receive their own identities. Apply, If and Sequence syntax uses fragment vertices so expression/branch reachability remains explicit; branch and operand children are all visited. Every Apply creates exactly one association `(lexical owner, resolved callee Value)` and indexes it by `ConstraintOccurrenceId(apply occurrence, slot 0)`. Group and Ascription callee wrappers peel to their semantic child; a resolved Name selects its resolved Value; other callees select their expression Value.

`Graph::seal` computes SCCs over the retained directed graph with an iterative two-pass traversal. `qualifies(event)` is true precisely when the event's lexical owner and resolved callee receiver have the same sealed SCC. It is a source-call-cycle test. It does not say which type/effect bound was admitted or emitted by that call.

## Transfer into candidate relation state

`candidate_context_seed` looks up the exact `ConstraintOccurrenceId` in the checking-event map. On a hit it interns a singleton source-event set and attaches that set to the seeded relation; on a miss it attaches no source set. The relation helper carries the processing relation's source set into ordinary child relations. Bound construction preserves the processing parent's source set when its pair matches the active origin; derived/transport/replay owners retain their own distinct relation dependencies and inputs. Source sets are sorted, deduplicated event identities, not a bound-by-bound admission trace.

Intrusion reads the active processing relation's source set and qualifies when **any** attached event passes the SCC test. Qualified extrusion-parent records enter the pending queue and their completed pair groups are marked activated. Thus the lifecycle is:

`exact source Apply slot 0 → singleton event set → relation/source-set propagation → SCC qualification → candidate intrusion activation`.

This closes R177's named registration producer question: the event is not guessed from matching endpoints; the current owner registers the HIR Apply and exact checking occurrence, then the seed performs an exact map lookup.

## Remaining parent gap

The registered event is an Apply-level call-cycle witness. The set may union event identities, and the intrusion predicate is existential over that set. Neither `Association` nor `checking` names the particular source Name/Lambda effect admission, physical bound lane, bound-evidence admission, or emission that supports each edge of the R183 chain. The current source-owner read therefore does not establish that the required original source inequalities reach the same actual provider Capture, nor that a shared anchor has the needed physical edge to that local row.

R195's concrete Capture finding remains limited to one fixture. R198's event-to-merge-transport join remains separate from Capture-bound ownership. R199's Cargo query failed before compilation and established no run-specific admission/emission result. The next missing evidence is the exact relation/source-set-to-bound-admission/emission-to-provider-Capture path, followed by a universal argument over all original source routes and rollback/replay cases. The full computation-forwarding parent, A/B, source/native correspondence and production gates remain OPEN.

## Closeout

R200 closed as a source-registration construction result; 90 seconds charged of 300, no carryover. The sample package suite passed at current worktree in the preceding goal continuation (`RUSTC_WRAPPER= cargo test -q -p yu-playground`); it is ordinary execution evidence and closes none of the proof gates. Solo primary; no independent review.

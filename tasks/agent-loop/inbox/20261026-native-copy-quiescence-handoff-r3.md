# Native copy quiescence obstruction: bounded contributor handoff

Date: 2026-10-26. Contributor: `/root/finite_copy_certificate`.
Owner of integration, independent review, and any verification: `/root`.

## Packet and exact claim

Authored only:

- `notes/theory/2026-10-26-native-copy-quiescence-obstruction.md`
- this handoff, `tasks/agent-loop/inbox/20261026-native-copy-quiescence-handoff-r3.md`

The manuscript constructs Proposition NQ for the actual candidate drain:
from the solver/control state immediately before trace dispatch event 1229,
there is no finite normal forward continuation to its next `Transport`,
`current=None`, empty-worklist boundary before settlement. Hence this drain
cannot return through its ordinary diagnostics/acknowledgement completion.
Errors, checked exhaustion, allocation failure, abort, cancellation, rollback,
test mutation, external state mutation, and session replacement are outside
the claimed normal continuation. Their impossibility is not assumed or proved.

The earliest root-copy seed is `T276<S47` at dispatch 1172, extrusion
occurrence 87 at 1173. Event 1229 is deliberately the cut: merely seeing
`extrusion-finish` at 1228 would not yet certify successful final bookkeeping
and enqueue. Reaching the next dispatch does.

## Constructive native derivation

The proof fixes the original high path `B48->J21->C20->S47`, high rows at
level 2, the low path `S47->39->32->A45` at level 1, `C20.lower T276`, and
`A45.upper U301` whose argument is `C20`. Every selected path edge is backed
by a nonempty actual relation fiber named in the manuscript.

Before the first empty boundary, pending copy parents cannot settle, so those
levels and representatives remain fixed. An actual positive `T276` copy
into an anchored low receiver makes a fresh negative `B48` copy `N` and
transports its upper path to `N->Jcopy->Ccopy->S47`. Its rewritten Function
is enqueued only after that path's fibers have been installed.

Insertion-triggered replay then propagates the rewritten Function through
the receiver's existing path and `S47->39->32->A45`. Meeting `U301` gives
the actual Function argument child `C20<N`. The native row-row level guard
stores that bound on `C20.upper`; its retained lower `T276` replays `T276<N`.
An actual earlier or current root extrusion for that pair produces a newer
negative `B48` copy `N'>N`. Retained rewrites are safe for this inequality:
their actual extrusion happened after receiver `N` already existed.

This is derived from the code rather than assumed as a `Closed`/successor
law. In particular copied one-sided bounds are not assumed to replay
automatically. The proof uses only an ordinary insertion after its required
opposite fiber already exists. Duplicate replay keys and pair-current memos
are handled by their earlier actual constructor/dispatch history; the first
empty boundary forces completion of all those queued or staged consequences.
Taking the largest anchored copy in a hypothetical finite boundary history
then contradicts the derived successor.

One historical-replay overstatement was found and repaired before freeze:
an outer incoming restoration can preconstruct replay dependencies for
siblings not yet queued. The proof therefore includes an explicit ownership
exclusion for every distinguished dependency. Along the propagation path and
at `F_N<U`, the exact lower endpoint and lower input `BoundKey` contain fresh
Function `F_N`; for `T<N`, the exact upper endpoint and upper input `BoundKey`
contain fresh row `N`; the Function-port pair `C<N` also retains `N`. These
are born inside this active drain, after any suspended outer replay product.
No restoration is created inside ordinary dispatch. Thus matching old keys
for these fresh obligations can only come from ordinary replay that already
queued its child. No unrestricted dependency-exists-implies-queued law remains.

## Original target remains unchanged

No registered original termination theorem is refuted by this packet alone.
`SourceProblem.InferenceTermination` in `YulangClosure/Contracts.lean`
quantifies `supported`, `inferInitial`, and
`Acc (fun next prev => p.inferStep prev next) n`. A finite native failure can
terminate without reaching normal quiescence. The manuscript explicitly
leaves the original supported-source/initial-state instance, transition
correspondence, availability of the unbounded mathematical constructors, and
progress/nonstuttering bridge open. No source principality/soundness or
abstract qualification conclusion is claimed.

## Frozen inputs and checks performed

The exact eight native owner hashes and four observer artifact hashes are in
the manuscript. The native hashes were independently read with `sha256sum`
and agree with `native-termination-trace-r3/source-manifest.json`. The source
SHA is `f617815f862683495c3e8d040f4b378f14573cf1ef730a764ff254d748f07a84`;
trace SHA is `40b3c69d1cd992d73c411e85927eca640c57d21d701507ccd86dbd0bab9d2b1e`.

Performed: bounded static reads of the exact source owners and selected trace
events; source/trace hashing; source-code case analysis. No native rerun,
build, Lean invocation, dependency/config change, Git operation, or child
agent. No new Lean declaration or unverified Lean proof term exists.

The paper proof is constructed and awaits independent review. The primary
must not report the finite observer cutoff as native divergence or this
native proposition as a negation of original `InferenceTermination`.

Final manuscript and handoff hashes are sent out of band to the primary at
freeze, avoiding a self-referential handoff hash. Only the primary may change
shared status or integrate the packet.

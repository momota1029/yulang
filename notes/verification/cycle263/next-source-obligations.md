# Exact next source obligations after cycle263

The new address basis and executable checks no longer require externally supplied
representative Plans, Layout agreement, head models, or Ready for all states.
The semantic theorem now chooses its fact interpretation from actual registered
source Plans, before base/inspector/assignment. Two context variants coexist:
SourceMeaning263 uses all source futures; SourceLocalMeaning263 needs only finite
representative witness snapshots and the entire inspector image. Neither is an
automatic consequence of Checked/Initial. The localized version needs a nonempty
registered future; the previous theorem handles the completely empty family.

## 1. Construct an observer from a concrete source machine

Current inspector has type State(finite basis) -> VersionedJournal.State roles.
Each inspector result is independently old-source reachable. Nothing connects
inspect(before) and inspect(write before proposal). In particular, choosing an
arbitrary reachable snapshot at each finite state is not the requested source
compiler, even though the table faithfully records that chosen snapshot's effects.

A next proof should define a concrete inspector/decoder, show exact source
observation and installation preservation for a strict table step, and state
explicitly which administrative old moves stutter. Finite fact growth bounds
strict steps only. Unbounded old stuttering cannot be used to prove old Acc;
239/240 counterexamples remain untouched. This is the highest-priority gap.

## 2. Derive the head context for that concrete machine

Representatives are noncomputable witnesses for meaning, not a runtime Plan
search. Each chosen witness needs all its retained producer heads, not just the
selected head. The inspector likewise needs all registered producer heads in
each image snapshot. Show these from the chosen public/source Models, or weaken
the source theorem to a precise branch-specific invariant with a proof. Do not
replace these with desired ClassEffects or assume an Effects-to-Effects equality.
SourceHeadsContextProbe proves a real uniform-assignment context is inhabited
for a concrete source, but not a joint nonempty mixed-installation execution.

## 3. Assemble packet/source semantics only after 1–2

Current exact Models iff priorModels AND per-write ClassEffects is not an
existential assignment-extension theorem for the full mixed journal, a Frame,
Permitted, or EvidenceNode. Map all private/public journal fields to the existing
completed readback/packet interfaces, keep current-time/old-time centers distinct,
and prove both projection directions. Only then migrate source regressions and
the twelve properties. No language acceptance decision or new question was
needed for the conditional bookkeeping and transport results in this cycle.

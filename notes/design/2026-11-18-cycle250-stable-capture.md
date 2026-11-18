# Cycle250: stable capture view from actual occurrences

Status: Draft materialized compiler component.

Build a Bounds expression for each actual capture: singleton occurrences read
both old endpoints through the old ordered mapping; non-singletons use this
owner's reserved stable lo/hi keys. Actual lower/upper equations produced by the
covered coherent raw merge prove those terms equivalent to the actual
lower/upper occurrence folds under the old snapshot readback. For nonempty
captures, Bounds.Fits is therefore exactly the conjunction of every original
occurrence interval. The definition also handles empty captures, with explicit
bottom/top fold equivalence; no nonempty source restriction is introduced.

This is one compiler component, not the complete new packet: raw context and
projection origins refer to the old snapshot, while head/binder/schema aggregate
uses must refer to these new bounds. Emitted defaults, shared-center equations,
children and changing live requests still need that mixed-time compilation.

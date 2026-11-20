# C304: maintaining the slice observation across replay

The current-head interface and merged-slice contract require different
proofs. A matched same-context plan can be installed with a reconstructed
current effect snapshot. The archived-history predicate gains exactly the
installed plan's semantics and the new effect's stored validity. The live
class predicate gains the new effect in the focus's alias class.

If each install preserves request membership for every class, old live
outputs are unchanged even when historical requests are nonempty. A
checkable sufficient condition is that each emitted raw row has no output
request: the install leaves aliases alone and appends only these rows.
With that condition, the slice contract advances alongside a paired install,
without comparing raw effect lists or assuming equality of the diagnostic.

This is not a solution for genuinely new output requests from emitted
children. Those require a transport theorem for archived effect bodies on
the newly exposed output targets.

The same request stability also discharges all existing legacy/versioned
live-effect checks exactly. With an exact current snapshot, post-install
Models is old Models plus the selected plan and its output class, with no
assumption that every old model survives. A same-plan resnapshot therefore
preserves full Models and the slice semantics across the install separately.
The actual revised install guard still needs a cache sound for that revised
history and equality of previous chosen-ID projections. It is not enabled
merely because the models or projections agree.

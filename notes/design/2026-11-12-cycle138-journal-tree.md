# Cycle138: finite recorded journal readback

`GeneralDictionaryJournalTree.recorded_tree` constructs an ordered finite
Dictionary from pure syntactic journal coverage and accessibility of every
recorded packet-child edge. Neither semantic Evidence nor a preconstructed tree
is assumed. Exact occurrence equality is used; aliases are not collapsed.
Alternative recorded packets all contribute edges, so accessibility is stronger
than existence of a single terminating choice. Ordered children and duplicates
are retained in the constructed payload.

`uniform_dictionary` additionally requires a real initial trace of the existing
restricted ordinary/fixed-view-refresh relation. The current journal invariant
then gives the same chosen tree's recursive Evidence for every final journal
model, without old-packet-to-final Extension assumptions.

Coverage and accessibility have not been derived from general Stable or selected.
This is conditional soundness/readback, not a completion of B4 EvidenceNode,
completeness, principality, language decidability, or Y2 runtime adequacy.
`missing_packet` makes lack of coverage an explicit syntactic obstruction.

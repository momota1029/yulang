# A rooted selector need not validate an unrelated table entry

A bounded traversal records the indices visited by reading the root's
selected child lists. Its members have genuine table-edge paths from that
root (or are the root); this alone does not prove all rows were present. A
successful complete run certifies child closure of the visited set. Show
that trimming the read table to those indices reproduces the exact
ordered dictionary, and that the trimmed table is a right-sized input
for the independently checked rooted same-model composition. An
unrelated cyclic entry in the wider read table should not make a
successful root fail; explicitly distinguish this scope selection from
ignoring a reachable missing child or changing the raw source's state.

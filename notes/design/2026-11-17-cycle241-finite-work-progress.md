# Finite fact and dirty-owner progress calculus

This module is an abstract scheduler, not a Yulang successor boundary. Parameters are arbitrary natural numbers factCount and ownerCount; facts and dirty owners are Boolean functions on their corresponding Fin types. A fact transition preserves every old fact and adds at least one genuinely new fact; it may reset dirty owners arbitrarily. A drain transition is permitted only for a dirty owner and clears exactly that owner's bit, leaving all facts and other dirty bits unchanged. There is no transition for unchanged recomputation.

Rank is lexicographic (absent fact count, dirty owner count), encoded as absent*(ownerCount+1)+dirty. Dirty count is bounded by ownerCount, so a new fact strictly reduces the encoded rank even with a full dirty reset. Clearing one dirty owner reduces its second component. Natural-number accessibility gives accessibility for every transition sequence, without fairness.

Explicit missing producers: a finite ground-derived universe of actual observation facts and owners; an interpretation of every real operation as one of the two transitions; preservation of source projections and all live consumers under rebase. The abstract result alone supplies none of those producers.

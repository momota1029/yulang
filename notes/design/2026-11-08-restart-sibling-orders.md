# Two sibling orders in the concrete declaration example

This extends the already checked fixed Right seed / two Index dependency / Parent dictionary example, without changing any registry. Forward edges `[0→1,1→2]` complete in one sweep, whereas reverse edges `[1→2,0→1]` require two. Compare the model sets of final ordinary states, not raw atom lists; reverse order adds a duplicate equality. Compare the actual final materialized argument and dictionary answer through a projection that drops the internal state. Quantification is over every ordinary assignment and every reported result of this fixed example, not every possible source graph or edge permutation.

No new source semantic decision is required: sibling conjunction/order independence is explicit in spec 6.3 and inbox I-3. This bounded result does not prove general saturation, Paterson/K2 termination, or arbitrary graph scheduling.

The scheduling comparison concerns the two associated Index dependency edges. The Parent declaration's where list is unchanged in both runs. This does not by itself prove arbitrary permutation of Parent's where clauses.

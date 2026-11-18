# Exact merge request classification

Joined classifies the closure after adding one undirected alias edge: old reachability, old reachability to the first endpoint then from the last endpoint, or the reverse direction. The proof derives this from actual Alias constructors and proves the relation symmetric/transitive; no assumed merge correctness theorem is used.

For the actual versioned merge transformer, requests at any root are exactly old root requests, plus old last-endpoint requests when the root was in the first endpoint's old class, plus the symmetric term. This includes third-party and one-sided requests. Roots outside both old endpoint classes retain request membership. The theorem applies to the structural transformer without operational guard assumptions; an actual permitted Step retains its original guard requirements. It does not claim list order/duplicates unchanged, that every merge strictly adds requests, or that endpoint requests cover only the endpoints' own outputs.

This identifies which historical Plan classes can need rescanning. No finite projection equation or desired request preservation is assumed. Strict build and five theorem axiom probes pass with standard axioms only.

# Restart cycle 3: source valuation descent

Status: proof design, not a new language decision.

Input: a finite table of source identities and an occurrence valuation. The existing identity atoms identify type components, not effect components. A deterministic first-occurrence lookup supplies a source valuation, with an arbitrary explicit default for absent identities.

Independent judgment: every occurrence has a type equivalent to the value of its source identity. Target: for every table and occurrence valuation, coherence is equivalent to existence of such a source valuation; the executable first-occurrence descent witnesses it. No injectivity or semantic nominal interpretation is assumed. This does not establish a complete source graph allocator or the general saturation theorem.

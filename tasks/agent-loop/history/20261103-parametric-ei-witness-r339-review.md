# R339 — parametric EI fragments and durable witness integration

Baseline `790cbe408`. The original IF construction quantifies over independent
well-typed primitive contracts and their laws; selecting a concrete W/Z
interpretation is not a prerequisite to the universal construction. Actual
source-to-contract instantiation remains a separate obligation.

`OriginalWitnessIntegrationR339.lean` embeds the exact R338 and historical
R335 generated witnesses under distinct enclosing namespaces, preserving their
different run IDs and source/declaration fields. Independent source review
compared the payload and selected proof bytes. The generated witness, selected
return application and original primitive module now compile in one Lean
environment. This repairs the R338 combined-import collision and makes the
previously scratch-only selected application durable. It does not establish
original `Inputs.traceForm`, world/provider semantics or R159 admission.

`OriginalDeclaredUnionR339.lean` derives an R293 trace packet from the same
receiver's developments and constructs a licensed primitive child through
R306, then applies the unchanged computation consumer. Independent review
confirmed a conditional reduction: the receiver's checked-observation-to-trace
projection, exact independently licensed reified packet and original target
Checking remain inputs. No complete R159 parent is constructed.

`OriginalSourceEIConstructionR339.lean` builds an abstract dependent response
and current-world telescope, retains request/continuation fields, and applies
the R311 callee-request constructor at R330's static registration. Independent
review found its schema is not yet authenticated as the original response
domain: e.g. an empty response type can make the quantifier vacuous. Whole
record restriction is constructed from component maps, but the restricted
theorem separately assumes changed-world callee/primitive inputs and therefore
does not transport EI evidence itself. Scoped arm semantics, actual Code
interpretation, R306 licensed child and R159 remain open. These limitations
must not be confused with rejection of the theorem's stated implications.

Independent pinned Lean 4.35 `-j1 -M2048` checking compiled all three modules
together, authenticated 92 sources/configs and reused artifacts, and audited
36 authored roots and 1,249 originating theorems. Only standard Lean axioms
occurred. Independent receipt SHA-256:
`233545a0bd917d24f42e586d35f35dada3f57d1aee16db760972b49eec6e8752`.

# R207 — Captured Origins for the R187 local route

The targeted test passed once. Captured stdout SHA-256: `61b4b58f9f830d0b39b17ea67d99d28032e281e9e88cc6140d73b266f7f2852e`; stderr SHA-256: `1f97b3d3e80b42218786e48198dc4a535de6065b00d050cc494b2a1f967b9efe`.

The same local route's Capture snapshot relations include these exact source-slot Origins:

| Captured relation | Captured bound | Source origin | Local form | Drain complete |
|---:|---|---|---|---|
| 74 | Value(8) ≤ PositiveFunction(314) | Origin 39, occurrence 12 slot 2 | Lambda parameter `u` | true |
| 56 | Effect(23) −≤ Effect(12) | Origin 31, occurrence 15 slot 1 | Name `u`, Parameter 2 | true |
| 57 | Effect(12) −≤ Effect(23) | Origin 32, occurrence 15 slot 2 | Name `u`, Parameter 2 | true |

The first row is Lambda argument/result structure on the Value side; it is not the effect-result slot 4. The second and third rows are the exact completed Name slots from R206. Among captured rows, this readback found no source Origin for local slot 4.

Other relevant rows remain distinct: relation 62 carries event 1 at occurrence 13 slot 0; relation 53 is a FreshUse from source bound Effect(22) −≤ Effect(9) to captured Effect(29) −≤ Effect(9) with observer gaps. The absence of slot 4 from this capture-associated Origin subset is not yet evidence that slot 4 was not emitted elsewhere. R208 will inspect the exact Lambda occurrence's slot-4 Origin and physical bound, then determine whether it is captured.

R183 remains OPEN. This is one accepted fixture and one local route, not proof across all source histories or a source-qualified counterexample.

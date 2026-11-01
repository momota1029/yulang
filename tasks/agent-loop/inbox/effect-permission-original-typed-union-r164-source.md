# R164 source handoff — typed Union supplier is not specified

Assignment: Luna source intake under
`tasks/agent-loop/sprints/effect-permission-original-typed-union-20261102-r164.md`
revision 2 (SHA-256 `fbd0895f1cb48f1741ac8c438659dab32d2133c48291df833bbcd35aa439db48`).
Baseline: pushed `3247451a7`; dependency-pin correction pushed as `e38633292`.

Disposition: **STOP_MISSING_ORIGINAL_TYPED_UNION_RULE**. No source rule was
invented and no Rust code was changed.

The generic source contract's Union is a whole-tuple alternative. IF §3.2
retains tagged alternatives, both branch interfaces and the original result
interface, but its contextual inclusion does not define satisfying branch-to-
result semantics. Native signature authority and incidence §3.4 require the
original dependent field map as an independently constructed input. In Lean,
`Node.alternative` is only graph topology; `Relations.alternative` is a supplied
family consumed by `DeclContribution.alternativeLeft/Right`. Existing
projection preserves an already licensed child field but does not establish
that it is governed by the original result telescope.

The full source-by-source matrix, exact missing law, dependency hashes and
bounded scope are frozen in
`notes/theory/2026-11-02-original-typed-union-r164.md`. Its final hash is
recorded with the R164 closure. No theorem or semantic assumption is authorized
until an authentic original typing/contract rule supplies the exact selected
branch/result relation and dependent field equations.

Rust disposition reuses R160–R163's independently reviewed five-owner map:
`NO_SAFE_CODE_SLICE`; no supplier appeared to map. R159 P/A, source/native and
production gates remain open.

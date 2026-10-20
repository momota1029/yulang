# R179 Luna implementation and source-mapping handoff — prospective only

Contract: `tasks/agent-loop/sprints/capture-coverage-20261021-r179.md`.
Proof packet: `tasks/agent-loop/inbox/20261021-r179-proof.md`.
No semantic source read or compiler change begins before prospective CLEAN and
Luna activation. Exact dependency hashes and snapshot manifest are recorded in
the contract and R178 proof handoff.

After activation, use only the exact eleven immutable owner pairs from R178.
Independently trace each required original source inequality from its source
emitter through `candidate_source.rs`, `candidate_value_graph.rs`,
`candidate_scheme.rs`, Capture frontier movement, canonical/local/shared
ownership, and any later shared-anchor consumer. Bind the selected provider/use
identity; challenge whether any required inequality is omitted or represented
only by an unconsumed anchor. Apply the mapping to unchanged R171 fixture as a
worked instance, never as universal evidence. Keep both ordered Replay inputs,
current/reuse semantic discharge and resource erasure separately OPEN unless
their constructors are established.

Current implementation result remains `NO_SAFE_CODE_SLICE`. No code, tests,
builds, probes, compiler/evaluator/Yulang2 execution, network, nested CLI, Git
or scratch output is authorized. If an exact correction becomes derivable,
stop and submit the smallest proposed lease/prerequisites for prospective
review before edits.

Exact Luna lease after activation: this file, the R179 contract's sequential
revisions, and `tasks/agent-loop/current.json`; 600 seconds, elapsed UNKNOWN
charges full grant. No overlap with the proof writer. Return source pins,
required/omitted cases, anchor-consumption path, implementation prerequisites,
artifact hash, accounting and STOP receipt.

## Luna source mapping — active R179

Source domain is only the immutable candidate root
`/tmp/r178-inputs/candidate-e9a7a4f/` and its eleven R178-manifested files.
This is a source-only mapping; it authorizes no implementation or execution.

- `candidate_source.rs:1293–1304` classifies a computation-formal `Name` and
  emits `FormalNameEffect`; `:1736–1739` connects the formal's registered entry
  effect and that Name occurrence with `candidate_formal_effect_equal`. This
  is the source origin for both directed effect relations at a consumed Name.
- `lib.rs:11322–11447` makes the Lambda body effect feed its returned effect
  (slot 4), while the registered computation-formal entry is kept as the
  function's argument effect. For a value formal, entry is also constrained
  by slot 3; computation formals deliberately use the body Name carrier.
- In the R171 forwarding fixture, each `t:[signal] int` is a computation
  formal. The `terminal t` and `relay t` occurrences therefore enter through
  the formal Name carrier; `relay (signal::ping())` is an Apply consumer. This
  identifies the worked source path only and does not establish universal
  coverage.
- For a block initializer, `candidate_source.rs:1048–1056,1126–1136` schedules
  the initializer one level below the block, then `Work::Install` emits its
  initializer-effect-to-block-effect relation. `:1715–1720` publishes the
  initializer's positive value endpoint as the local. These constructors
  distinguish a younger initializer row from the enclosing block effect.
- Capture starts from the selected positive provider value root
  (`candidate_scheme.rs:1259–1268`), follows live function children and then
  only expands local rows. For local effect rows, `:1180–1234` follows direct
  lower and upper row edges in their stored polarity and also follows capture
  incidence. A nonlocal/shared row stops at `:1131–1137`; a proof must show
  what later constructor consumes any retained anchor.
- Candidate-versus-legacy row insertion must remain distinct. The pinned
  `candidate_extrusion.rs:944–970` canonicalizes both endpoints and selects
  one owner lane by effect levels; `:600–652` stores and reads back that
  selected lane. The provisional trace identifies the bridge as an actual
  replayed `t ≤ blockE` edge represented on `t.upper`, not as a mirrored `n`
  edge. Legacy reciprocal-adjacency writes are not the basis for this result.
- A local Name route captures the stored local root at
  `candidate_scheme.rs:2047–2121`, freshens the captured graph, then restores
  each captured bound before linking the fresh root to the actual Name value
  (`:2244–2262`). A ModuleDef route similarly recaptures the stored root and
  frontier and instantiates it under the same `DefinitionUseId` (`:1541–1570`).

The proof worker's provisional block example is not a counterexample. In the
pinned candidate owner, `candidate_apply_effect` chooses one owner lane by
canonical row levels (`candidate_extrusion.rs:944–970`); negative insertion
stores the selected direct upper edge and `candidate_replay_bound` joins it
with the actual opposite lower edge (`:602–652,869–929`). For `t ≤ n`,
`n ≤ t`, and initializer `n ≤ blockE`, the latter insertion replays the two
ordered inputs `(n,+,t)` and `(n,-,blockE)`, deriving `t ≤ blockE`. Since
`t` and `blockE` are at the same level, candidate insertion stores the result
on `t.upper=[blockE]`. The Lambda slot-4 body relation stores
`blockE.upper=[returnE]`; Capture from the provider function reaches its entry
and return effect rows, then follows `t → blockE → returnE`. The younger `n`
need not itself enter Capture, and the argument does not invent a fresh `n`
row. One authentic FreshUse restoration of this captured chain yields
`μ(t) ≤ μ(blockE) ≤ μ(returnE)` for that worked route.

This refutes the proposed local obstruction but is only a worked successful
route. The universal cut-compression argument still needs a premise that the
same selected provider/use materializes both ordered source relations and the
consumer edge on a Captured row across contextual/current/canonical paths,
shared anchors and valid rollback. The fixture and this one trace do not prove
that universal premise.

Current result: `NO_SAFE_CODE_SLICE`. The source mapping explains the ordinary
constructors and the candidate obstruction's likely refutation, but universal
coverage across arbitrary frontier changes, shared anchors, repeated uses and
valid rollback remains the proof lane's task. Ordered Replay authentication,
current/reuse semantic discharge, resource erasure, and all parent/A/B/source-
native/production gates remain OPEN. No code, test, build, probe, compiler or
Yulang2 execution was run.

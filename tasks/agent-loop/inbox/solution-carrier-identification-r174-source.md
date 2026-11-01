# R174 source result: distinguish the returned inference carriers

Outcome: **BLOCKED_SOLUTION_CARRIER**; **NO_SAFE_CODE_SLICE**. This is bounded
static source evidence, not an inference soundness theorem, a semantic
counterexample, or independent review. The original parent remains OPEN.

## Assignment and frozen inputs

Worker `/root/solution_carrier_identification_r174_source`, assigned by `/root`;
registered role `researcher`. Requested model/effort were inherited and not
specified in the packet; observed effective model/effort are UNKNOWN in the
available runtime metadata. Active-work and exact-contract acknowledgements
were sent before writes. Primary-pinned baseline: `yulang3/bb9b5826a`.
Contract revision 4:
`tasks/agent-loop/sprints/solution-carrier-identification-r174.md`, SHA-256
`72425107a3ad4d71844f666b2ff3fd2eefa4b34e26dd53f3737c0d2ee9430e79`.

The primary reported integration of revision 3 in `451739410` and revision 4
in `c20460072`; no Git command was used by this worker. Revisions 1 through 3
were superseded explicitly by the primary. A pre-write revalidation detected the revision-3 change,
and work paused until its acknowledgement; no mixed revision was silently
accepted. The sole write lease is this handoff.

All representation dependencies below matched their contract hashes before
content reads. The original nine inputs were revalidated after the initial
trace; all revision-3/4 additions were hash checked before their first read.

| Input | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| `crates/yu-types/src/lib.rs` | `fb3d53cdcce6a2d7149508ba0bdc9dad643cfc795fefdb9914afcb461e4aa6d8` |
| `crates/yu-solver/src/candidate_scheme.rs` | `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e` |
| `crates/yu-solver/src/shadow_f5.rs` | `b6a6c70da75329ff66cd9e6c0a2598a54cc8f0de7ba956f6f28b24616ca3a994` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_effect.rs` | `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15` |
| R173 contract `lambda-inference-generation-adequacy-r173.md` | `a67521efc53a0ac98af0e91414fd6cd58e7cfa9ab06f89a0d5d5149479f40078` |
| R173 proof handoff | `8666a46cca3e2d20f01a6cdff64cc67616c3840fbb394679dc6829a032a1749d` |
| R173 source handoff | `c07c17baaf32608a4ce526686b17ede584912fb717d7d5ca510b50fea487fe17` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `OriginalParameterWorld.lean` | `7b5f849f744dbe56f374d8be6b11a5a218176abf6eeda2fb9da8180c7b1ff802` |
| `OriginalFormalAdmission.lean` | `77230ab7984ee544db16fe4d9663b73f98b9afa9c5d2610fad59c26753d5ac7c` |
| `OriginalSourceEnvironment.lean` | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |

The five revision-2 governance-only pins were also verified and read:
root AGENTS/base map and research-lab/design-authority/Git-concurrency rules.
Their exact hashes remain in the revision-4 contract. They supply workflow
constraints, not representation or semantic evidence.

## Actual return paths and retained state

The pinned source distinguishes these owners; none is thereby identified
with the parent theorem's abstract `a`.

1. **Public existing solver result.** `SolvedModule::solve(batch)` at
   `lib.rs:20387` returns `Result<SolvedModule, SolveAvailabilityError>` via
   `InferenceSession::try_new(batch)?.run()`. `run` executes and calls
   `finish` (`10732`). `finish` requires a genuine closed-finalization
   session and constructs `SolvedModule` (`20037`). Its fields (`7747`)
   retain HIR ownership, occurrence projections, root-to-scheme positions,
   finalized `ClosedValueScheme`s, the exact `ClosedTypeArena`, errors,
   and `ConstraintStore`. This is the legacy publication route named by
   the implementation's own comments/assertions.
2. **Private source-candidate result.** Under `shadow-apply-candidate`,
   `run_candidate` returns `CandidateSolvedResult` (`10738`). It executes,
   completes candidate field-tail work, rejects an unresolved active
   field-tail selection, then calls `finish_observations`. It asserts
   `closed_types.is_none()` and `schemes.is_empty()` before publishing
   `CandidateSolvedResult { data }` (`10746`). The result struct is private
   and contains only `FrozenInferenceData` (`7864`). It is not the
   finalized legacy scheme result.
3. **Frozen candidate data.** `FrozenInferenceData` (`7792`) retains the
   candidate reference graph, candidate calls and optional `GraphState`,
   alongside HIR ownership, projections, errors and constraint store.
   `finish_observations` transfers these fields (`20326` onward).
   The internal `InferenceSession` (`7933`) separately owns the whole batch,
   live component map, value/effect bounds, levels, metadata and typed
   worklist. These session fields are not fields of `SolvedModule` or
   `FrozenInferenceData`. This does not prove that the retained candidate
   graph loses their relevant meaning; that requires inspecting its owners.

`ConstraintStore` retains term arena, facts and provenance (`3425`) and
exposes term views, facts and provenance (`3768`, `3917`, `3920`). Retaining
these syntactic objects is not itself a source-semantic solution relation.
In particular a returned `Ok(SolvedModule)` is not evidence of an empty
error list: the result explicitly retains `errors`, and its documentation
states that local relation errors do not stop other components.

## What callers can observe

`projection_for` checks occurrence ownership and returns a `SolvedProjection`
(`20467`), whose value is one of Int/Unit/Bool/Str/Unknown/Never and whose
effect is Empty/Unknown (`4160`). `finish_observations` recognizes selected
primitive lower/upper combinations, and recognizes Empty only from
`has_bottom_lower && has_empty_upper`; other cases become Unknown (`20075`).
These are coarse observations, not a complete type or named effect row.

`root_value_for` (`20485`) reads the retained closed scheme, returning a
primitive or Never for the corresponding predicate. Quantified, recursive,
Function, union and tuple predicates all return Unknown. The smallest
structural discriminator is the Function match arm: none of its four child
fields affects that result. Consequently that observation alone supplies
no readback of the original formal's complete interface. This is a direct
branch derivation; no claim that two chosen source programs inhabit those
branches was tested or required.

The default-off `shadow-f5` observer does expose the existing full closed
scheme: `shadow_closed_schemes()` (`lib.rs:20384`) returns `ClosedSchemes`,
`for_root` borrows this exact result's root and scheme
(`shadow_f5.rs:189–220`), and `ClosedSchemeRef.endpoints` opens its own arena
(`249`). This observer takes `SolvedModule`, not `CandidateSolvedResult`.
Its module header explicitly limits Q/R to current scheme-local binders.

In `yu-types/src/lib.rs:646–745`, positive/negative Function views contain
separate argument, argument-effect, result-effect and result handles;
schemes retain quantifier counts and recursive bounds. However the closed
effect views in this representation are only positive Bottom and negative
Empty (`683–689`), with unit payload arrays in the arena (`808`). This
representation must not be treated as the source-candidate's complete
named effect algebra merely because both expose Function nodes.

## Candidate representation boundary

`candidate_scheme.rs:6` shows that `GraphState` retains
`candidate_intrusion::State`, module/member/operator/local graphs, fresh-use
routes and source obligations. `Graph` (`188`) contains structural nodes,
value/effect row keys, bounds and evidence, negative formal roots, and exact
Lambda argument-effect incidence labels. `Node` (`376`) includes Function
children and an effect operand with endpoint, tail and polarity. Its bounds
refer to `candidate_effect::BoundKey` (`415`). This is concrete retained
algebra, not an original Descriptor/Interface interpretation.

The primary added both next owners in revision 4 before their content was
read. `candidate_intrusion.rs:10` retains value/effect canonicalization
vectors, parent/copy groups, active roots/uses and an effect-algebra state.
`candidate_effect.rs:299` in turn retains formal domains and permissions,
annotation value/effect maps, contribution/view objects, origins and a
`candidate_context::State`. Contributions retain a source effect identity,
source-node origin and instance (`336`); views retain allowed source effects,
an optional row tail, scope owner and local weight handles (`363`).
`FormalEntryPermission` retains the exact formal/owner/annotation/entry row
and concrete permission list (`435`). Its comments distinguish retained
source permission from provider/Catch consumption. These are richer source
candidate objects than the legacy closed effect views, but no original
Descriptor/Interface readback is defined by those record declarations.

The next unpinned representation boundary is
`crates/yu-solver/src/candidate_context.rs`, owning the retained context state
and local-weight meanings. It was not read. More importantly, no registration
equation from any of the pinned Rust owners to the independent original
`FormalAssignment` appears in the pinned semantic interfaces. Traversal
stops here; further structural pinning alone would not establish that equation.
No claim of exhaustive absence over other Rust modules follows. The pinned
`lib.rs` also reexports a separate receiving experiment, but its owner and
callers were not read and are not substituted for an ordinary inference API.

## First missing semantic equation

The original parent at `Contracts.lean:127–130` is unchanged:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

Here `Solution` is a type parameter; `generates`, `solves` and `sameScoped`
are independent fields (`103–117`). The pinned interfaces do not register
either Rust result owner as that type or construct a source interpretation
from its fields. `OriginalParameterWorld.Contract` (`53–59`) needs an
original `s.Descriptor` for Value and an original `s.Interface` for
Computation. `FormalAssignment` consumes parameter, route and the prior
type-scope values. `OriginalFormalAdmission.Introduction.selection` and
`.description` (`28`, `51`) still take that assignment as an input;
`readContract` reads an already interpreted decoded state (`32`).

Thus the missing equation remains a justified interpretation from the
**same actual selected solver carrier**, through prepared `native_root`
(and Computation `entry_effect`), to that original pre-invocation
`FormalAssignment` under its prior telescope. The scalar observations,
closed legacy schemes and retained candidate graphs are distinct candidate
inputs to investigate; none supplies this equation in the frozen inputs.
Neither the complete interface nor `sameScoped` can be replaced by an effect
port or endpoint equality. The R173 proof handoff's missing readback maps
remain requirements, not existing functions. This is a missing registration,
not a demonstrated contradiction in the approved inference algorithm.

## Method, coverage and resources

Method: exact `sha256sum`, bounded `rg -n`, and source slices. Assumptions:
ordinary Rust ownership/move semantics and the displayed feature guards;
no hidden caller or imported callee behavior is assumed. No semantic oracle
was used. The static match-arm discriminator is independent of any toy
checker; no checker, executable experiment, seed/range or mutation was run.

No Rust/Lean edit, runtime path, build, Cargo, test, Lean invocation, cache,
environment query, target, scratch, Git command or descendant was used.
Only this leased handoff was written. CPU time/RSS and exact wall duration
were not instrumented; work used lightweight reads. The assigned budget was
600 seconds; exact budget compliance cannot be independently established
from these uninstrumented readings and contract-pinning pauses. Unverified:
candidate context owner, external public candidate callers,
whole-program publication and semantic soundness, actual parent carrier,
original source interpretation and shared witness. Independent review is
pending; this author does not certify the result.

Recommended next action: Luna should admit one semantic-registration packet
that selects the actual inference output and states the original readback
equation at its native endpoints, using the retained candidate algebra and
permissions as evidence rather than equating success with satisfaction.
Pin `candidate_context.rs` only if that construction needs its representation.
The packet must resolve
the carrier and original meaning before another conditional formal lemma.

## Commit packet

- Exact changed/leased path: `tasks/agent-loop/inbox/solution-carrier-identification-r174-source.md`.
- Baseline: primary-pinned `bb9b5826a`; representation dependency hashes changed: none.
- Contract revisions: explicit primary upgrades 1 → 2 → 3 → 4; final SHA above.
- Claim/review: static bounded source evidence; `BLOCKED_SOLUTION_CARRIER`,
  `NO_SAFE_CODE_SLICE`; fresh independent review pending; parent OPEN.
- Checks already run: contract/dependency/governance hashes and bounded reads;
  no executable verification authorized or run.
- Proposed checkpoint message: `Distinguish inference result carriers and record readback blocker`.
- Shared-record deltas intentionally left to Luna: exact frozen handoff hash,
  stopped worker/lease state, three carrier distinctions, next context boundary,
  semantic-registration blocker and independent review verdict. No shared
  record was edited here. Writes STOP after submission.

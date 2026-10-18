# R49 Luna owner map: active-root Apply admission

Status: frozen read-only owner map, pending independent review. No source edit,
build, test or runtime probe was performed.
Sprint `active-root-admission-20261019-r49`, revision 1, contract SHA-256
`6a8fa0a9f1189e247b6462b45083f814e0420ee53000f60b19d6d6ffcb3a57ff`;
baseline commit `49f7680234ddfd2c9f3ad198c81a502ebdc916a1`.
Parent inference/evaluator theorem and original Simple-sub A/B remain
**OPEN, 0 -> 0**.

## Owner path

| Stage | Current owner behavior | Evidence available to next stage |
|---|---|---|
| Active initializer lifetime | `candidate_source.rs:903–904, 1090–1098` records the parameterized local initializer endpoint in the local `active_initializers` map before visiting its initializer. `Install` removes it at `:1102–1105`. | Exact `HirLocalId -> endpoint` exists during schedule construction. This temporary map is not retained in `GraphState` or a dedicated Apply authentication record. |
| Recursive Name | `candidate_source.rs:1239–1249` emits `Action::Link { occurrence, endpoint, target }` when the resolved Local is active; otherwise it emits `Action::Local`. The authoritative design requires this shared open monomorphic link and forbids LocalScheme/FreshUse during initialization. | `Action::Link` contains exact Name occurrence, active endpoint and target component. `execute_candidate_action` at `:1668–1673` admits the value link. It does not publish a `LocalFreshRoute`. |
| Apply source record | In scoped mode, `candidate_source.rs:1255–1305` unwraps allowed syntactic wrappers and records `LocalCalleeRoute { expression, occurrence, local, slot }` for an unannotated Local Name. `:1330–1359` stores it in `ApplySourceInput` with exact source owner and callee/argument/result endpoints, then schedules `Action::Candidate`. | The Apply record retains the exact callee Name and occurrence, but no active-initializer flag, root-owner token, or `Action::Link` receipt. |
| Scoped authentication | `candidate_call.rs:689–735` checks the exact Local Name/witness, then requires `local_route_by_occurrence[witness.occurrence]`, matching route/local/slot, an installed scheme and `authentic_use_instance()`. `shadow_apply.rs:1772–1775` calls this before admitting a scoped source Apply. | Only a committed FreshUse route for that occurrence satisfies the gate. No active monomorphic Link alternative is read here. |
| Route publication | `Action::Local` calls `route_candidate_local` (`candidate_source.rs:1687`). It captures an installed scheme and prepares FreshUse (`candidate_scheme.rs:1995–2045`). After the Local frame completes, `lib.rs:9287–9317` calls `GraphState::commit_local_use`; that method installs both `local_routes` and `local_route_by_occurrence` (`candidate_scheme.rs:661–692`). | Publication is tied to an installed Local scheme and successful completed route transaction. Rollback removes new routes/index entries and restores prior cursor (`lib.rs:9470–9490`). Link has no such route transaction/publication. |
| Failure cut | `Action::Candidate` calls `admit_candidate_fact` (`candidate_source.rs:1678`). Scoped `authenticate_scoped_apply` runs before candidate Apply relation processing (`shadow_apply.rs:1772–1775`). | On the unchanged R48 fixture, the direct active-root Apply precedes the helper uses and has no exact LocalFreshRoute. The fixture's later `session.execute().unwrap()` is statically unable to establish the requested inspection. No runtime failure was observed. |

The two sides are distinct source modes. Active recursion is intentionally
monomorphic and uses one open root; an installed generalized local use carries
a capture/FreshUse route. The active-root Apply has the correct local-callee
syntax witness and source endpoints, but the current scoped authenticator only
accepts the latter route protocol. A sibling helper route has another
occurrence and cannot authenticate the recursive Name.

## Authority and result

The authoritative [local self-recursion decision] pinned by R49 says the active
recursive reference must link directly to its initializer root and must not
route through `LocalScheme`, capture or freshen. The user-approved answer fixes
that source scope. The R48 `LocalFreshRoute` requirement is implemented in the
scoped candidate experiment; no inspected approved authority declares that a
monomorphic active-root link is itself a FreshUse route, or specifies how it
satisfies this gate. The separate local-use-retention document is explicitly
an unapplied draft and supplies no authority.

Therefore the unchanged scoped path has no current complete
producer-to-authentication route in the inspected owners. The first missing
contract is an explicit rule for authenticating an active monomorphic callee at
the scoped Apply consumer, tied to the exact Name occurrence and the exact
active initializer Link/root. The architecture/semantic decision owner is
Luna/user approval before any new admission protocol; implementation owners
would be `candidate_source.rs`, `candidate_call.rs` and the scoped gate only
under a fresh contract. No code slice is authorized by R49. This is a bounded
`NO_SAFE_CODE_SLICE` for the current scoped path, not a claim that recursive
applications are ill-typed or impossible under the language semantics.

A future proposal would have to preserve Link (never replace it with FreshUse),
prove exact occurrence/root identity and active-lifetime ordering, reject stale
or sibling records, and show a complete owner transfer to the consumer. It
would need a new reviewed contract and semantic approval if the consumer's
meaning changes. R49 does not claim this proposal is already licensed.

## Frozen dependencies and checks

Contract: `6a8fa0a9f1189e247b6462b45083f814e0420ee53000f60b19d6d6ffcb3a57ff`.

- Active-recursion authority `notes/design/2026-10-10-local-self-recursive-binding.md`:
  `38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895`.
- User-approved answer:
  `1c0ea94c359f08496185594848ab9082b4eac174ab247d67d37f316462db145b`.
- `candidate_source.rs`: `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c`.
- `candidate_call.rs`: `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479`.
- `candidate_scheme.rs`: `d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278`.
- `shadow_apply.rs`: `d5e6b179fd4f6fbca579b0fa4d479d8bd11b520d774acbf27f414451c4691137`.
- `lib.rs`: `2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee`.
- Existing fixture:
  `47ced76fe8f0f136c42802b2376ca09f7cadec0fc8e5b1b3d4c6acc7bc613e55`.
- R48 closeout: `35de4c623562f01c636b3c5e463f0dd105fe996136fefdf39a5149d5825c7e98`.

Static `sed`/`rg` owner inspection only. No build/test/Cargo/runtime, no compiler
or fixture edit, no Git operation. This mapping is producer evidence, not an
independent review or source-semantics approval. Parent remains OPEN 0 -> 0.

# R114 pinned Rust admission/transport source receipt

Status: FROZEN; unreviewed source characterization. No theorem, kernel acceptance,
source/native closure or production promotion is claimed. Worker: `/root/r114_source`.

## Objective, authority and baseline

Trace source scheduling -> registered computation entry -> permission producer ->
actual consumer, solely for R114's source-derived admission/transport obligation.
Method: immutable source inspection and a conditional derivation from binder guards.
The constructive theorem belongs to the separate proof lane.

Baseline: `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`.
Read governing rules `research-lab.md` (including its preserved contract),
`design-authority.md` (Authority order, Natural compiler behavior and
proof-obligation economy, Approval and implementation gate), and
`git-concurrency.md` (Integration ownership, Disjoint-file mode).
Also read root operating instructions, current sprint/state, and governing
inference principles §§1.1, 3, 4 and Integration. Applied `yulang-proofs` for the
source bridge handoff; this leaf dispatched nobody. The R114 contract fixes
original judgments, checking, selected formal contracts, Shared witness,
full telescope and one lawful joint strategy. Those meanings are not revised.
Primary explicitly authorized read-only `git show` of these three exact paths
after the initial packet's blanket Git exclusion; no Git mutation occurred.

All source locators below are baseline line numbers, not live-tree locators.
Paths share prefix `crates/yu-solver/src/`.

| Input | SHA-256 | Git blob |
|---|---|---|
| `candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` | `16f30e032b4c3a7687986085dca35ede00491bac` |
| `candidate_call.rs` | `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f` | `d15dd11dbb25ba69e3b2359128d47d0a9dcf0570` |
| `candidate_effect.rs` | `1c80c55c62b724b9d2080bd2ddcdabfa35a5ba641c1bf45d9735dfd7fd05be41` | `20c1635c7c3974a22ff14b62916cad76062e256c` |

## Closed local seam and its hypotheses

This is a bounded source characterization, conditional on an unchanged,
constructor-produced batch, successful initialization before execution,
successful guards/allocation, and the corresponding action actually executing.
It does not establish all callers, successful scheduling for arbitrary sources,
or publication/consumer correspondence.

1. **Registration owner:** `candidate_source.rs:1104-1118` registers each Lambda
   parameter by exact parameter recipe, source owner, lambda index and scope.
   An outer annotation effect row selects Computation; otherwise it selects Value.
   Both native root and entry are initially absent.
2. **Entry allocation owner:** `candidate_source.rs:2303-2325` checks recipe
   identity and absence of a previous native root, obtains the positive Parameter
   endpoint, allocates a fresh effect at the parameter's level for Computation,
   and retains that entry in the same registration. Value retains no entry.
3. **Action owner/order:** `candidate_source.rs:1323-1339` clones the actual
   parameter annotation into `FormalEntry` when its outer effects exist, then
   schedules `FormalAnnotation`. `step_candidate_source` selects
   `actions[frame.next]` at `2432` and increments only after successful action
   execution at `2453-2454`. Dispatch is at `2460` and `2463`.
4. **Entry permission producer:** `candidate_effect.rs:1762-1783` checks at most
   one symbolic variable, Computation role, source owner/scope, parameter recipe,
   source occurrence ownership, exact Lambda/formal occurrence, absence of an
   existing formal domain, and absence of another permission for the registration.
   It uses the retained entry. For nonempty concrete members, `1786-1802` creates
   `FormalEntryPermission` retaining registration, formal, parameter, occurrence,
   owner, scope, annotation position, source row, entry and concrete source order.
   `1818-1821` publishes it. With a symbolic name, `1813-1816` equates the entry
   and the scope/name-derived tail. Empty concrete rows produce no permission.
5. **Actual local row consumer:** `candidate_source.rs:1766-1776` schedules
   `FormalNameEffect` only for a resolved computation parameter name;
   `2464-2467` retrieves the same registration's entry and equates it to that
   expression's live effect. `candidate_effect.rs:1750-1757` records two directed
   constraints with their own occurrence/cause and invokes `constrain_live_effect`.
   This is actual constraint consumption of the entry, not consumption of the
   concrete permission as a provider/arrival/Catch grant. Solver implementation
   behind that call is outside the read set.

Nested permissions have a separate owner: `candidate_effect.rs:1660-1685`
constructs paired Function ports; `1700-1734` retains negative concrete port
permissions on an open fresh row, with structural path and source row.
`1896-1958` constructs the formal pair, admits value links at slots 43/44,
retains permissions, and publishes the negative formal domain. This records
construction and constraints; it does not turn a nested port into an outer
entry. The explicit comments at `256-272` distinguish source permissions from
arrival/provider/consumer evidence. Concrete permissions are not closed upper
bounds (`1702-1705`, `1831-1833`).

## Exact remaining consumer premise

`NO_SAFE_CODE_SLICE` for a complete original-Judgment -> normalized admission /
event-consumer transport in the authorized three-file domain.

The retained-permission binders exist, but they delimit the missing owner:

- `candidate_effect.rs:396-440`, `bind_formal_entry_permission_use`, checks a
  unique retained permission and registration/owner/formal/scope/occurrence/entry
  equality, plus that `mapped_row` is an Effect row. It copies the caller's
  mapped row, DefinitionUse identity and context-use number into a borrowed view.
  Its contract explicitly assumes already-authenticated incidence/FreshUse.
- `candidate_effect.rs:447-488`, `internal_formal_entry_permission`, also checks
  the Definition target root. Its contract explicitly assigns Internal-route
  and constructor-to-target authentication to its caller.
- The three allowed files contain definitions of these binders, but no invocation
  of either. The projection iterator at `387-390` only enumerates permissions.
  Thus no actual consuming caller/route owner can be identified from this read
  set. This is not a claim that such callers are absent repository-wide.
- `candidate_call.rs:216-248` validates a computation source plan and exposes
  retained root/entry; its comments at `209-213` disclaim independent Lambda-port
  and fresh-use correspondence. `407-436` still exposes pending suppliers for
  OriginalGenCall0, argument reification/whole carrier, receiver dispatch and
  complete future interfaces. A supplier declaration is not a supplier result.

**Discriminating conditional derivation:** suppose binder guards succeed for one
nonempty permission and supplied `RowKey::Effect(r)`. Replacing it with another
well-formed `RowKey::Effect(s)`, or replacing the supplied DefinitionUse/context
identity, leaves every guard unchanged, because no mapping or route lookup occurs
in this body. The returned fields change to those caller inputs. This proves
only that the binder alone cannot authenticate their relationship to the source
entry. It is neither a source-reachable counterexample nor an assertion that a
real caller supplies incorrect fields. No candidate transition oracle was used.

The missing premise belongs to the caller that authenticates the source
constructor/entry to the actual route, mapped row, event/provider/consumer, and
preserved original checking/Shared/telescope/joint-strategy evidence. That caller
is outside this packet's allowed source domain. No path outside that domain was
searched to guess its identity. The primary must locate and lease the exact owner.

## Commands, coverage and limits

Read-only commands: `git show BASE:crates/yu-solver/src/{candidate_source.rs,
candidate_call.rs,candidate_effect.rs}` with `rg -n` and `nl -ba | sed -n` for
the listed identifiers/ranges. A Python 3 standard-library process reread these
three pinned blobs, computed SHA-256 and Git blob SHA-1, and counted bytes/lines:
212009/2995, 32230/763, 301836/5227 respectively. Initial `python` invocation
failed because that executable was absent; `python3` succeeded. One combined
identifier search returned exit 1 because `candidate_call.rs` contained no
permission-binder match; this was a negative search result, not a build failure.

No compiler, Cargo, Lean/Lake, checker, tests, mutation experiment, cache,
installation, environment change, worktree, Git mutation or descendant was used.
No random seed/range applies. Coverage is the three exact immutable blobs and
the cited producer/binder bodies, not whole-source reachability. Oracle
independence: hashes authenticate bytes relative to the pinned commit; source
inspection supplies evidence independently of a supplied toy transition system.
It shares the assumption that these constructor-produced batches and external
solver/route contracts are respected. It does not independently validate those
external contracts, accepted semantics, or buildability.

Excluded: `candidate_scheme.rs`, runtime, dirty/quarantined/isolated source,
other callers, formal source rules/Lean derivations, all-history replay and
publication/use correctness. A changed pinned dependency, missing initialization,
mutated action/batch, failed guard/allocation, or unauthenticated consuming route
prevents the conditional handoff. One lightweight shell/process group at a time
per tool batch; independent read-only commands ran concurrently. No heavyweight
process. Peak RSS/CPU and exact elapsed time were not measured; stopped within
the assigned 240-second wall budget.

Recommended next action: primary grant a narrowly pinned caller-owner audit for
the two permission binders and their actual event consumer, carrying the original
source-Judgment transport requirements unchanged into that packet.

## Commit packet

- Exact leased/changed path: `tasks/agent-loop/inbox/effect-permission-admission-transport-r114-source.md`.
- Baseline: `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`; dependency hashes above;
  no dependency was changed by this lane; live-tree equality intentionally untested.
- Review: FROZEN, independent review pending; source characterization and
  conditional binder derivation only; complete admission/transport remains OPEN.
- Checks already run: pinned source reads, identifier searches and byte hashes;
  no executable correctness/build/kernel checks.
- Proposed checkpoint: `research: record R114 pinned entry-permission transport seam`.
- Shared-record deltas intentionally left to primary/curator: attach closed local
  entry-production seam, retain original source/native/production gates OPEN,
  and assign caller-owned route/event admission correspondence. No shared record
  or authority file changed. No further writes after submission for frozen review.

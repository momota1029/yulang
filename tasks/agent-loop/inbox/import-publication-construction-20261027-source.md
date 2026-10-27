# Import publication construction — source-owner handoff

Sprint: `IMPORT-PUBLICATION-CONSTRUCTION-20261027/r1`.
Contract SHA-256:
`f8f8e5293bbf79490e2762d53345fc87f148192b89cedc06c6e0930083c30574`.
Baseline: `19d12985b`; baseline identity was supplied by the primary, not
authenticated by a worker Git command. Assignment/handoff revision: 1.

Claim class: bounded static source characterization plus an explicit
independence derivation. No provider execution, original source derivation,
checked theorem, complete certificate, semantic choice or parent closure is
claimed.

Worker `/root/import_publication_source` sent START ACK before inspection;
the actual identity is the collaboration task path, session UUID unavailable.
Observed model: `gpt-6.1-sol`; effort UNKNOWN. The capacity synchronization was
acknowledged: nine UNKNOWN assignment reservations were already released
idempotently, with their observations and quarantined paths retained.

## Pin receipt

All 17 contract inputs independently rehashed unchanged. Receipt:
`/tmp/yulang-import-publication-construction-20261027/source/pins.json`, SHA-256
`051d4e57e55ffa999815f20fee8964194b06573cd9c4d77511d5bf0a583e49a5`.
The following additional directly needed owner files were read and frozen by
hash in `source/owner-pins.json`, SHA-256
`c1b80da1ea84c7b6e3b425251fa635b60328ed095bbdc2f31d05d1245fe19577`:

| Path | SHA-256 |
| --- | --- |
| `crates/yu-hir/src/shadow.rs` | `b964bab6dcdb7ebeca9f964c134ac8fb041c928c20ce0a895fea6b6af0fbb93e` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-core/src/lib.rs` | `3a2c2befd0dd38df3c06458a7fd918b8f32124a75d264ed51d859ec036c4ab5e` |
| `notes/theory/lean/YulangClosure/OriginalEffectHygiene.lean` | `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

## The actual retained Rust path

The fixed contract uses `pub id x = x`, explicit exposure `identity`, and
prelude exposure `id`. The previous exact resolver fixture at
`module.rs:4817–4835` checks common provider identity; it was inspected again,
not run. The prior failed caller adapter supplies no executed provider or
consumer join for this task.

The raw provider owners do retain the necessary source syntax rather than
only a provider key:

1. `HirBinding` retains its exact definition root, spelling, named parameters,
   value and range (`module.rs:1729–1740,1766–1787`). Named-parameter lowering
   wraps the body in actual `ResolvedExpr::Lambda` nodes using the corresponding
   parameter IDs and occurrences (`3673–3691`).
2. LocalSource formation joins every named `HirParameter` to the admitted
   source parameter and annotation, retains its source key, range, spelling
   and ID, creates the Lambda incidence, and records the named group owner and
   body (`module/local_source.rs:1138–1193`). Identifier lookup selects the
   same registered parameter before falling back to module/import resolution
   (`2130–2151`). This is a concrete owner path for the named formal `x` and
   its body occurrence, conditional on successful lowering of this provider.
3. `resolve_source_export_owner` checks the resolved public declaration,
   module path, exact source key and range, and unique matching public HIR
   binding (`shadow.rs:76–126`).
4. `candidate_imported_definitions` joins each exact `SourceExportId` to that
   provider's `DefId`, requires its owned definition root, and rejects a
   conflicting ID association (`shadow_apply.rs:512–537`).
5. `CandidateInference::solve_modules` supplies all HIR artifacts to one
   candidate inference world (`1587–1590,1755–1764,1823ff`). Candidate preflight
   rejects an Imported Name absent from that map
   (`candidate_source.rs:650–655`). The source collector maps Imported to the
   same `PendingDefinitionUse`/`Action::Module` path as a module definition
   (`1785–1793`); the action retains its actual occurrence and calls the
   incoming-use router (`2490ff`).
6. `execute_candidate_graph_plan` processes SCCs in dependency-first order,
   executes source member schedules, captures all member graphs, and only then
   writes `state.graphs[position] = Some(graph)`
   (`candidate_scheme.rs:2829–2953`). Incoming uses access the stored provider
   graph and retain their FreshUse reconstruction (`4102ff,4120ff`).

This is a real, inspected source-to-inference storage path. Its stored
`Graph` has source regions, rows, bounds, evidence snapshots, obligations,
root and boundary (`candidate_scheme.rs:188–219`); it is not the
`OriginalSource.PublicationRecord` payload containing actual event prefixes.
The API itself identifies complete Call, source admission and public scheme
correspondence as open (`shadow_apply.rs:506–509`). The neighboring
`CandidateValueObservation` explicitly excludes invocation/evaluation effects
(`498–504`). The synchronous candidate source driver also states that
production certificate creation remains disabled
(`candidate_source.rs:2374–2377`).

The existing test
`candidate_scheme.rs:5386–5485` exercises a closely related provider
`pub id x = x` through implicit prelude imports at two concrete types and
requires distinct FreshUse local rows. Its provider is in `std::prelude`
rather than this packet's `std::core`/explicit-alias fixture. The test was read,
not executed, and supplies no original runtime publication witness.

## Candidate reconstruction, name publication and the fixed map

`OriginalSourceGeneration.lean:533–545` explicitly makes `anchors` and
`publications` fixed solution data. No existing source event in the inspected
Environment operations inserts a publication record into this map:

| Operation | Actual constructed data | Required input left outside it |
| --- | --- | --- |
| `enterInitializer`, 547–551 | Captures current event path, names and fixed entry frames | Actual incoming Environment and legitimate original initializer |
| `extend`, 566–575 | Appends the supplied frame and extends an actual-event path when appropriate | Actual candidate payload, original binder and independent admission |
| `publicationCandidate`, 585–605 | Reconstructs entry snapshot, Return/rebind path, Shared prefix, captures, fixed frames and initializer suffix | Actual matching initializer/return/shared frames already present |
| `publicationValid`, 607–611 | Requires the reconstructed record to equal the record in `environment.publications` | The independently supplied fixed map and its realization equation |
| `publish`, 613–618 | Adds lexical Name-to-PublicationId pairs | It leaves `publications` unchanged |
| `publishGroup`, 777–780 | Builds a judgment from validity, successful name publication and suffix derivation | It assumes validity and the actual source premises |

`restore` and `aliasPublication` also preserve the fixed map. The existing
`source_publication_constructs_replay` result in
`OriginalEffectHygiene.lean:130–152` starts from `publicationValid`; it does
not derive validity from the candidate. The complete publication readback
and alias theorem (`OriginalSourceEnvironment.lean:1313–1362`) depend on the
installed stored record.

Thus a request to find a mutation that installs this OriginalSource map has no
such mutation in these owners by design. Its semantic role is a fixed solution
witness. What is missing is an independently justified construction/readback
of that witness from this provider's actual source derivation and event data.
The candidate Graph insertion above is a different typed payload; calling it
"publication" does not establish this readback equation.

## Smallest independence witness

For any `Environment Value` `e`, let `e0` differ only by
`publications := fun _ => none`. For any site `s`, direct unfolding gives

```text
publicationCandidate e0 s = publicationCandidate e s.
```

Yet for a singleton binding `[(n,s)]`, `publicationValid e0 [(n,s)]` is false:
instantiate validity at the singleton member, obtain an identity and record,
and its last conjunct is `none = some record`, a contradiction. This argument
does not depend on whether the candidate succeeds. If it does succeed with
`(p,r)`, the map satisfying `publications p = some r` and the always-none map
have identical candidate inputs and different validity outcomes.

This is an unchecked definitional derivation, not a new Lean theorem or an
execution. It isolates the exact unsupported inference:

```text
actual source/HIR ownership + candidate reconstruction
  does not by itself supply the fixed-map equality required by validity.
```

It does not refute the adopted semantics or require a mutable runtime map.
A source-to-solution realization could construct the fixed map once its
independent provider derivation and all actual prefixes are supplied.

## First unavailable witness and parent application

The inspected actual artifact set still has no accepted provider-specific
OriginalSource `Source`/incoming-Context allocation and no realization of the
provider's actual initializer/Return-rebind/Shared prefixes as an
`Environment.publications` entry. The accepted owner-table instance concerns
the selected nested-shadowing subtree and retains arbitrary incoming Context;
it does not authenticate this separate named provider declaration.

The next missing construction is therefore:

```text
owned provider HIR/formal/body + actual independent source judgment/events
  -> original provider Source, Context and fixed publication-map realization
  -> exact publicationCandidate/Valid witness
  -> consumer exposure lookups preserving that complete record.
```

The source lane cannot release the contract's Lean execution gate: it has not
supplied those actual source-owned semantic inputs. This result was sent to the
proof lane before freeze. Complete import-root elaboration, runtime frames,
all supported source forms, soundness, effect hygiene, principality,
termination and the original A/B gates remain OPEN. No dependent production
code slice is justified by the inspected path.

Only source reads/searches and Python SHA-256 checks ran. Cargo, compiler,
Lean/Lake, tests, formatters and Git commands: 0. No executable experiment or
version/axiom audit is claimed. The source allocation is 600 active seconds;
an independent elapsed/CPU/memory receipt is unavailable.

Recommended next action: have the fresh reviewer test the precise fixed-map
independence and Rust Graph-versus-publication correspondence boundary, then
construct the provider source-to-fixed-solution witness under the existing
source rules. If it needs additional semantics, return concrete reviewed
alternatives; do not choose an import classification from identity.

Writes stop at submission. No processes, shells or descendants remain. Exact
new outputs: this handoff, scratch `pins.json`, scratch `owner-pins.json`.

Commit packet: leased handoff path
`tasks/agent-loop/inbox/import-publication-construction-20261027-source.md`;
baseline `19d12985b`; no dependency bytes changed; independent review pending;
17 contract hashes and nine new owner hashes recorded; proposed message
`Record provider publication owner and fixed-map boundary`. Shared-record
deltas left to primary: source worker STOPPED; verifier expenditure 0; Lean
gate unmet; source-to-fixed-publication realization and complete import roots
remain OPEN; capacity release remains idempotent and path quarantine retained.

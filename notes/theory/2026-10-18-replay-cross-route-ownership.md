# Replay cross-route ownership: missing classification observation

Status: frozen research evidence; independent review pending. Author:
`/root/cross_route_owner_audit_20261018`; no contributing descendants.
Claim class: source-native-evidence with a conditional source derivation,
not a theorem or a source-qualified counterexample.

## Objective, authority and baseline

Classify ValueRow 44 as borrowed/shared or local/generic at the actual captures
and retained uses, preserving Module route 0/use 1 and Module route 1/use 2.
Method: inspect the pinned capture/reconstruction and Replay constructor/consumer
owners against the single frozen diagnostic. No new execution was performed.

Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, as preserved by
`tasks/agent-loop/sprints/npair-replay-cross-route-ownership-20261018.md`,
sections Fixed outcome, Frozen inputs, Required report and falsifiers.
Original quantifiers, source domain, accepted semantics and fixed `c` are
unchanged. Original-condition closure remains **0** and the parent remains OPEN.
No Operation candidate rule is adopted.

HEAD baseline: `7704277586c5b5b7dcf5b9b1138c4cb122590165`.
The five source inputs include frozen uncommitted bytes; HEAD alone is not
their identity. Governing rules: `rules/design-authority.md` Authority order,
Natural compiler behavior and proof-obligation economy, Approval and
implementation gate; `rules/research-lab.pre-sprint.md` One semantic baseline
and Evidence quality; `rules/git-concurrency.md` Disjoint-file mode;
`rules/goal-driven-sprints.md` sections 1, 2, 5, 6. The Authoritative inference
principles dated 2026-10-11 sections 1/1.1 and Authority and integration govern
the interpretation: source construction, accumulation and propagation remain
required; a diagnostic join supplies no new language rule.

Verified SHA-256 pins:

| Input | SHA-256 |
| --- | --- |
| Sprint contract | `48f9efa39434561c4c565699468bf22dea35ad406b905f7c44202ab22d08ced0` |
| Prior closeout `npair-provenance-complete-replay-and-operation-rules-20261018-closeout.md` | `bb598941f3444baec8177e50665a22380e1337e858f2a6064359c9c424d83b32` |
| Operation candidate `notes/design/2026-10-18-operation-complete-source-semantics-candidate.md` | `5418bd332dfbc2f9cd5dcd23064d66e36affb47838cf6db90c24a868bc44b4be` |
| Candidate handoff `tasks/agent-loop/inbox/20261018-operation-complete-source-semantics-candidate.md` | `e692a18c9133370b26444466b8c5f9d0816e3730c9ed1ee6571deb3e712495ea` |
| `crates/yu-solver/src/candidate_scheme.rs` | `0c55d3d47bc88166a68eb5f5797043b136a2d2bc0ace55de832e8e27ca20a07f` |
| `crates/yu-solver/src/candidate_context.rs` | `f2ecbadcc33e4439c57429cb6a6ce5bcdfd5c3131f5b5ebb9d1e03a0e224f569` |
| `crates/yu-solver/src/shadow_apply.rs` | `6508a3f39a6d3742110ca1f33e927fa26bd3b112c3f378fc345294675b7f69e3` |
| `crates/yu-solver/src/candidate_source.rs` | `1a65c7afb02a4afd538a34c34086108959579e06aafe8fbcab8ad6a6b3a65f3e` |
| `crates/yu-solver/src/candidate_call.rs` | `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479` |
| Diagnostic stdout | `05c536a2d2a5265687b16362fec6d0909a8dfbed178d69c8feb90a83972cf813` |
| Diagnostic stderr | `6966e24792eb97eaf26498f7e975cdc919fd0d19cb283666b613d78adcac49a3` |
| Diagnostic metadata | `6e0dda42a13b1ff8273904a0a4e239ea7d77b789d9cc94ec7d55bfa5ed740f47` |

Runtime paths share prefix
`tasks/agent-loop/runtime/20261018-replay-positive-provenance.diagnostic.`
and suffixes `stdout.log`, `stderr.log`, `meta.json` respectively.
Additional owner reads, pinned here (not changed dependencies):

| Input | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `ddd1395877d4a76e27a1dcf32af90c6fcb0e58c739610a0115c03955628350e1` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `7a57a93481095c6e7d4b8781810b1a5aa0d174e41ede29ac3f2b2b96bce10b0c` |
| `crates/yu-solver/src/candidate_effect.rs` | `9ea9498692bdff12c2a7ebd8546ca2b443a095c0700f3e87ad6c956cc690e212` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

## Source-established classification rule, missing actual inputs

`Capture::intern` canonicalizes row endpoints (`candidate_scheme.rs:694–704`),
then `Capture::row` applies `intrusion.rep(key)`, reads the representative's
level and metadata, and stores
`local = level > capture_boundary && !non_generic` (`706–731`).
The representative follows the parent forest (`candidate_intrusion.rs:85–119`);
`InferenceSession::canonical_value` delegates ValueRows to that representative
(`lib.rs:11570–11575`). `Capture::expand_row` stops on `!local`, keeping that
older coordinate's mutable bounds in the session (`candidate_scheme.rs:996–1001`).

Reconstruction does not use only the stored flag. For each graph row it recomputes
`source = rep(row.key)` and reads the current level/non_generic. With a fresh
per-use `canonical_rows` map it reuses a prior image of that representative, or
allocates a fresh row exactly when
`row.local && level > graph.boundary && !non_generic`; otherwise it retains
`source` (`prepare_candidate_fresh_use`, `1491–1533`). Row terms are constructed
from that mapped row (`1655–1657`); Function terms use the four reconstructed
children in order A, AE, RE, R (`1669–1678`).

Conditional derivation: given the actual captured row and the actual
reconstruction-time representative/metadata, the branch above determines its
image. A false stored flag, a level at/below the boundary, or non_generic true
preserves the current representative; all three freshening tests true allocate
an image owned by this fresh-use preparation. Canonical aliases within that use
share the image. This follows from source branches, but its premises have not
been observed for ValueRow 44. Capture-time and reconstruction-time metadata
must remain distinct; a captured local flag alone does not prove freshening.

For **both actual routes**, capture key, representative, levels, non_generic,
boundary, local flag and row-map entries are UNKNOWN. Route 0 is known to map
the selected upper bound's owner to ValueRow 44 through the successful checks
below. That does not disclose which capture key mapped there. Route 1 retains
the lower Function root, but its row-map incidence with ValueRow 44 is also
UNKNOWN. Equal graph node indices across routes do not establish equal graphs.

## Retained producer-to-consumer path

The runtime evidence is stderr lines 54–55. All Term indices below have
`TermArenaBrand(1)`; these are observations from one run.

| Stage | Observed identity/evidence | Limit |
| --- | --- | --- |
| Native selected negative Function | Term 264; ports `[260,262,263,261]` | Original call 0 |
| Module route 0/use 1 | copied upper Term 299; ports `[295,296,297,298]`; positive node 1 retains Term 290, children `[3,4,5,6]`, terms `[286,287,288,289]` | Contains no retained positive Term 310 |
| Module route 1/use 2 | positive node 1 retains Term 310; children `[3,4,5,6]`, terms `[306,307,308,309]` | Unique exact lower-root match in the logged ten-route census; does not identify its capture row owner |
| Lower producer | Relation 58: positive Function 310 <= ValueRow 44; transformer 0, demand None | Producer is a bound emission, not a demand |
| Admission/emission | Admission 56, group 55, `OwnerEmission { processing: Some(RelationId(58)) }`; Emission 56 links admission 56 to `Value(44)/ValueLowerAtom/index0`; identical bound read back at `ConstructorAfterAppend` | No FreshUse cause on this admission to identify a source capture/route map |
| Upper | Relation 35: ValueRow 44 <= negative Function 299 | Selected demand use 1, output scope 32/input route 8 |
| Replay | child Relation 61; lower 58, upper 35; exact lower/upper BoundKeys; both pair-match flags true | Distinct lower and upper use identities retained |

The remaining positive roots in the census are Module routes 2–7/use
3,4,6,8,10,11 with roots 329,349,402,439,473,496 and Local routes 0–1/use
5,7 with roots 384,421. None equals 310.

The lower emission source owner is `candidate_bound_origin_with_evidence`
(`candidate_effect.rs:457–485`), which derives OwnerEmission from the processing
relation and retains an admission. The physical constructor canonicalizes the
owner/item, selects the lower-atom lane, admits, appends, reads the physical slot
and emits the admission-linked record (`candidate_extrusion.rs:510–548,653–667`).
These are the generic source rules corresponding to the logged lower record;
the record does not encode which source occurrence caused Relation 58.

`candidate_context_begin_replay` enumerates lower/upper fibers, constructs the
ordered child, composes their flows, takes the upper demand, and retains both
the Replay recipe and dependency (`candidate_context.rs:3719–3783`).
`replay_demand_rows` reads those dependencies directly (`2716–2727`), so line 54
is evidence of the retained dependency, rather than a join guessed from IDs.

There is a further source-control-flow inference. The observed first rejection
is `positive-function-node-absent` at `candidate_scheme.rs:494`, on route 0/use 1.
Before reaching it, the authenticator has checked the selected use, unique
source bound, imported snapshot, demand and scope/input maps, copied four ports,
FreshUse transport, physical emission/owner, exact retained Replay recipe, and
`authenticate_replay_ancestry` (`390–482`). Thus, conditional on execution of
these pinned source bytes, these checks succeeded in this run. In particular:

- The selected upper has an authentic source-to-FreshUse chain; retaining an
  older row is explicitly permitted without merging use origins
  (`begin_candidate_fresh_bound`, `1767–1813`).
- The ancestry checker establishes one exact Replay dependency, upper Relation
  35 as the fresh relation, lower Relation 58's bound membership, matching child
  pair, and demand/transformer conditions (`candidate_context.rs:2749–2805`).
- Four distinct FunctionPort children of Relation 61 exist, with operations
  `[Swap,Swap,Preserve,Preserve]` for `[A,AE,RE,R]`. A/R transformers are identity,
  AE stamps input 8, RE protects output scope 32/input 8 (`2807–2842`). Concrete
  port RelationIds/transformer IDs are not printed.
- The consumer returned by that checker is Relation 61 itself, a checked
  zero-step consumer relation (`2843–2852`). Replay dispatch passes each retained
  child relation to `start_typed_drain` (`3830–3846`). The diagnostic does not
  separately print the specific drain identity or its completion.

The later same-route typed-port comparison (`candidate_scheme.rs:500–503`) was
**not reached**. Therefore existence of the FunctionPort children does not
establish their endpoint correspondence to the sibling route's four terms.
The present source check requires both Function roots in the selected graph;
its failure establishes that check's failed premise, not invalidity of the
native cross-route join.

## Exact blocker and next discriminating evidence

The census implementation (`candidate_scheme.rs:336–347`) prints Function nodes,
children, retained terms and context_use only. The test logger (`2311–2322`)
prints Replay, lower records and negative Function ports. Neither prints the
classification inputs or route row maps. The neighboring assertions at
`2240–2256` concern a different test's capture, not this failing run, and cannot
fill this gap.

Required missing observation, at the owning construction points:

1. For the selected upper owner and the actual lower emission's owner: source
   definition/use/occurrence and capture identity; graph row index/key;
   capture-time canonical representative, level, non_generic, boundary and local.
2. For each relevant route's reconstruction: pre-map key, current representative,
   current level/non_generic, graph.boundary/local, mapped `route.rows[index]`,
   context_use and use/occurrence identity. Include any representative change
   between capture, reconstruction and lower admission; do not infer a map
   solely from final owner 44.
3. Link Relation 58/admission 56 to its actual owner occurrence and lower
   Function producer, then retain the four Relation 61 FunctionPort relation
   pairs alongside both routes' reconstructed endpoints. This decides whether
   their pairs agree without assuming same-route containment.

These observations would distinguish legitimate shared anchoring from lost
fresh separation. They require a separately authorized constructor observation
and runtime successor; this contract stops here. No choice between the two
ownership alternatives is established.

## Checks, coverage and limits

Commands run: read-only `rg`, `nl -ba ... | sed -n ...`, `cat`, `sha256sum`,
`git rev-parse HEAD`, `git status --short`, and absence checks on the two leased
outputs before creation. All prescribed input hashes matched. No code, tests,
runtime, checker, mutation, seeds or range search were added or executed.
Coverage: one existing failed diagnostic, ten positive-Function route entries,
one Replay row and one lower admission/emission; no general ownership theorem.

Oracle independence: source inspection checks the actual branch conditions and
logger omissions independently of the diagnostic's formatting. Runtime and
authenticator share this implementation, so their agreement cannot independently
validate source semantics. The successful-prefix inference assumes the frozen
log came from the pinned executable source and ordinary Rust control flow; this
audit did not independently authenticate the binary. No independent review is
claimed. False source/runtime association or changed dependencies invalidates
that inference. Metadata absence, concrete port relation IDs, source occurrence
lineage and actual drain completion remain unverified.

Resources: author allocation 360s; one sequential lightweight read/write process
at a time, no builds/probes/descendants, Astra 0. Exact CPU/RAM and pre-timestamp
startup duration were not measured. Audit timestamp interval and final hashes
are returned in the handoff. Both output paths are frozen on submission.

Recommended next action: Luna should authorize one constructor-owned observation
packet for the fields above, preserving distinct routes and current semantics;
keep the original parent OPEN with closure 0. Shared task/theory status and any
successor contract remain primary/curator responsibilities.

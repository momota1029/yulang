# R50 independent review — BOUNDED PASS

Reviewer: `/root/r49_review`; no authorship or contributing descendants. Live
roster confirmed both authors completed with explicit **WRITES STOPPED** receipts
before review.

**No open BLOCKING, major, or minor finding remains in this bounded correction.**
The R49 compatibility blocker and dependency-hash transcription finding are
closed. Compilation, concrete Rust runtime success, parent closure and
production remain unverified.

## Correction and five attacks

The repair separates source authentication and handler/provider selection from
suppression authorization.

| Attack | Independently inspected evidence |
|---|---|
| Actual signal Catch/write provider forwards | `candidate_receiver.rs:794–849` retains the resolved handler and provider independently. The old admission equality guard is absent. `source_operation_match`, lines 634–648, returns KnownUnmatched for distinct complete identities; lines 915–916 produce Forward without requesting suppression permission or arrival. |
| Same spelling, distinct resolved operations remain unmatched | Classification compares `SourceOperationId`, not spelling, family inequality or pointer inequality. Identity includes the declaration source node and nominal family/module identity. HIR resolution at `local_source.rs:2282–2293` supplies a unique declaration; unresolved, ambiguous and private outcomes do not pass assembly. |
| Matching operation with missing permission/arrival is unavailable | For a matching provider member, lines 935–945 still require `provider_entry_certificate()` and exact terminal/view/Catch-fact agreement. Failure returns unavailable while building the plan, before publication. |
| Unknown identity never becomes KnownUnmatched | Assembly requires actual `Resolved` source constructors. Lines 638–642 reject inconsistent identities or unavailable source-shape evidence before identity comparison. Missing suppression evidence is never used as mismatch evidence. |
| Authenticated matching suppression remains supported | Match reaches the existing R45/R47/R48 certificate path, followed by the same snapshot construction. The final Lean positive witness retains authenticated suppression; this is model evidence, not successful Rust execution. |

The existing source expectations at `candidate_receiver.rs:1199–1240` remain
unchanged. No test was run.

The Rust KnownUnmatched branch forwards every extracted original terminal
directly. The Lean model additionally requires successful native endpoint reads
before forwarding; `known_unmatched_plan` and `known_unmatched_publish` expose
that premise rather than assuming an accepted plan.

## Publication, siblings and retained evidence

`publish_authenticated_residual`, lines 879–899, obtains the complete immutable
plan before the first residual constraint mutation. Each Forward call uses
precisely:

```rust
constrain_live_effect(
    decision.endpoint,
    pending.upper,
    &pending.fact.id,
    &pending.fact.cause,
)
```

KnownUnmatched does not rewrite the endpoint. In Match, foreign annotation
endpoints and distinct Contribution endpoints remain Forward; there is no
family-wide deletion.

The inherited Support-member representation still distinguishes logical view
expansion from authenticated physical lower edges. It retains the addressed
view/member/family and closed-tail checks without inventing a physical
emission. Suppression still consumes the same R45 permission, R47 owning entry
emission and R48 common-endpoint/Catch evidence.

The planner borrows the experiment immutably while checking certificates.
Publication uses the completed owned plan within the private constructor. A
forwarding failure returns an error and prevents successful return of the
experiment.

## Closed findings and preserved receipts

**R49 BLOCKING compatibility finding — CLOSED.** The new classification
preserves a known nonmatching operation as Forward while retaining fail-closed
authorization for matching suppression. The corresponding Lean distinction is
present in `SelectedArmReads`, `IdentityReads`, `classifyIdentity` and
`decideEndpoint`.

**R49 minor hash finding — CLOSED.** Rust handoff revision 2, line 96, records
the correct independently rehashed `candidate_source.rs` value:

```text
96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a
```

Revision 1 remains preserved. Extracting its archived bytes reconstructs Rust
handoff hash
`aa9f7a2c28615850a4f78dcd6f35d38725e8a2a1104265f89e37506a2f9b8ae7`. The proof
handoff archived revision 1 likewise reconstructs
`90bb99675de20fe8cf58c41fb14b7366f83eea2cd7487c0ba2fbf87419a85e71`.

## Lean statements, correspondence and axioms

All 35 theorem declarations, proof bodies and complete final printed types were
inspected against Audit 11. The receipt contains exactly those 35 roots in
source order.

The new statements distinguish the cases:

- `classification_match_iff`: Match iff both identity reads succeed and
  declaration/family agree.
- `classification_known_unmatched_iff`: KnownUnmatched iff both identity
  reads succeed and complete declarations differ.
- `known_unmatched_plan` and `known_unmatched_publish`: construct the all-Forward
  plan and exact ordered endpoint/upper pairs from KnownUnmatched and valid
  native reads.
- `unknown_identity_unavailable`: missing identity reads imply Unavailable,
  exclude KnownUnmatched and prevent every successful endpoint decision.
- `suppression_complete_authentication`: suppression recovers Match, complete
  authentication, the same R45 certificate/permission and R47 entry, both
  arrivals and the matching source arm.
- Concrete R50 witnesses cover known-unmatched provider forwarding, equal
  spellings with distinct identities, absent source reads, missing matching
  permission/arrival, and authenticated matching suppression.

Corrected `unavailable_no_publication` and `matching_gap_no_publication`
explicitly require authenticated Match. Their former application to known
nonmatching handlers was the rejected behavior. Original parent claims are
unchanged.

Complete transitive axiom census, namespace
`YulangClosure.AuthenticatedResidualConsumerR49`:

**`[propext]` — six roots**

`support_member_sound`, `lower_path_arrival`, `classification_match_iff`,
`classification_known_unmatched_iff`, `fold_correspondence`, `fold_all_forward`.

**`[propext, Quot.sound]` — remaining 29 roots**

`path_sound`, `physical_path_iff`, `authenticated_identity_match`,
`authenticated_target_candidate`, `authenticated_prerequisites`, `lift_r48`,
`suppression_iff`, `unmatched_decision`, `plan_correspondence`,
`unmatched_count`, `same_family_sibling_preserved`,
`unavailable_no_publication`, `accepted_suppression_applies`,
`invalid_support_rejected`, `evidence_gap_rejected`,
`concrete_support_and_sibling_witness`, `publication_has_complete_plan`,
`published_unmatched_count`, `concrete_authentication_failures`,
`unavailable_endpoint_blocks`, `matching_gap_no_publication`,
`known_unmatched_decision`, `known_unmatched_plan`, `known_unmatched_publish`,
`unknown_identity_unavailable`, `suppression_complete_authentication`,
`concrete_known_unmatched_forwarding`,
`concrete_same_spelling_distinct_identities`,
`concrete_r50_classification_boundaries`.

No project axiom, proof hole or checker bypass was found in the inspected cone.

All eleven preserved stdout blocks independently reproduce their recorded
hashes. Only Audit 11 authenticates the final R50 module:

```text
Input SHA-256:
d4ac170074404781684896c0e914347a9b75d5eddf5c5f208a81b777eb3c7442

Stdout SHA-256:
0b2057978b9b51658c4e574007ec8373daef71ddfc866fe0eb2c5a5138e52bb1
```

The retained receipt reports Lean 4.35.0, bounded stdin execution, one CPU,
`-j1 -M1024`, exit 0, empty stderr and no final warnings. The two R50 audits
report 14.089589 seconds total wall time and 877,876 KiB peak child RSS. These
are producer measurements; this reviewer did not rerun the checker.

## Frozen hashes and isolation

Independently rehashed:

| Artifact | SHA-256 |
|---|---|
| R50 contract | `54a680db4806ca2387cb1a159c752f6495675225c76e017209a5a882e7ce33d2` |
| R50 admission | `b5bda4d96775235e8f0874e0a3c1d93db93c2ffd67994adef4c014d70c243792` |
| Rust source | `88b833dacc1bce6e444ec1da2fb47a87475384473384cd4e0b1b5c3089d8f4c3` |
| Rust handoff revision 2 | `8a0682f9f34b90baf34c9d1d086dba88f0bd1ff941297bcc0b37fdc895357085` |
| Lean module | `4fc4380f3ad1827ecf155f982e5186b32d6d66d91909039fb118063d8f1e2df2` |
| Proof handoff revision 2 | `1ef4d84b78797b84286915d5baf5b41821a10267de2139413a8ea2e107f94994` |

Context, effect, scheme, source, lib, HIR local source, R39/R45/R47/R48 Lean
and project configuration match inherited admitted dependency pins. Dirty
dependency bytes were retained as inputs. No clean substitute or Git operation
was used. Commit membership is primary-supplied evidence, not independently
checked here.

## Limits and STOP

This PASS closes the narrow R49 classification regression and receipt typo.
Remaining premises include exact source/native extraction, complete candidate
inventories, identity and lifetime interpretation, terminal
traversal/canonicalization correspondence, actual native forwarding execution
and resource-failure behavior. Mathematical list multiplicity does not
establish Rust extraction multiplicity.

Concrete Rust compilation/runtime, Catch execution authorization, full
subtraction/hygiene, original A/B, soundness, principality, termination and
production remain **OPEN**.

Reviewer effective model, effort, active-time and overall resource telemetry:
**UNKNOWN**.

**Reviewer STOPPED.** Complete report returned for primary placement. No files
written, descendants, builds/tests/compiler/checker reruns, Cargo/Lake, Git,
scratch/cache/target/environment/worktree creation, persistent processes, or
quarantined-path access.

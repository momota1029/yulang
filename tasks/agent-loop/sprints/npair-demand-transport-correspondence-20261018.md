# Sprint `npair-demand-transport-correspondence-20261018`

Status: CLOSED-REVIEWED-PARTIAL. Original parent remains OPEN; original conditions closed 0. Branch
`research/simple-sub-intrusion`; baseline `f2d66da08`. Original parent
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN; preserve all
quantifiers, source domain and fixed-c requirement. Astra0; no rollover.

## Fixed outcome

Establish and exercise the exact transport from an admitted source Apply's
omitted-formal native demand through use introduction, FreshUse remapping,
value rewrites and a retained typed Replay dependency. The preceding runtime
fixture is accepted and its six selected tests pass, including integer-result
propagation, but the typed observer reports `native_root_matches=false` while
both Replay endpoints match. This raw equality is a falsified success test;
do not change the observer boolean or call this compiler-unsoundness without
the transport derivation.

Success requires:

1. A reviewed derivation mapping the original call index, use instance, input
route, demand root, output scope and all four Function ports across each actual
FreshUse/value-rewrite/Replay owner on the fixed source. The theorem application
must state exactly which P3/P4 transport premises this discharges and which
universal cases remain open.
2. Existing-semantics implementation that preserves enough authenticated
transport evidence to distinguish the correct copied demand from another
FreshUse or a port mix-up, plus regression coverage for two separate uses of
the same source and final integer propagation. Existing raw root mismatch must
remain visible. No constraint, solving, root-transport, scope, consumer or
source meaning change is authorized.
3. After independent clean review, one focused regression and one example run
exit 0. Full capture must show the formal `invoke` Apply's original demand
linked by actual checked transport to the Replay row and all four typed ports;
an ungrounded equality flag is not enough.

Original parent conditions closed before and after: 0 unless a reviewed proof
is applied to an exact original obligation. The fixed-c semantic candidate
from the preceding sprint remains unadopted and outside these leases.

## Pinned inputs

| Input | SHA-256 |
|---|---|
| preceding closeout contract | `9c8b711295f5569b13e69c93dcc6eab7a61a6c26559929d4bb1b3263dd0d6b3a` |
| preceding runtime metadata | `efeee94c80260617a79d33d1abe6c4ddb95c488b53adb13071f8847badccf11c` |
| preceding focused test stdout | `03aa813ca0866b88c7024fdfb5e7dafcbcd9e2fe0c1bfd096e6201d98c86c48a` |
| preceding focused test stderr | `1ecaf9fbc0573bb464535cc865bcca4aa45e9fcc67f53bb73e28c669d13bd75c` |
| candidate context | `46f0b74c8aa942c629a456272c3ae601827f1794b25d7034479edee62bc13e4f` |
| candidate scheme | `ea48b5ec33ba9724bb761e3e04aa05cbf3eea22641830c442c8ecdcde54243d6` |
| shadow apply observer | `51d1d1534d86181dce6caf0638f5c55e7c3bad6d764c3da5c4c9af10421335ac` |
| candidate graph regression baseline | `c113ac60c41eff2cee32239c3ba7e035e17270c4769bf9e95164298c3622d785` |
| previous example | `30c0e01e6d76ba4e807fd4a362dd91003ee164021368ebcab3f0c92f7eaa9179` |
| yu-solver manifest | `7a599e95800c67ca4688b0f91917609345a252aae6d2ea6cd0f413eb1c07893c` |

Read only the exact original NPAIR P3/P4 obligations and the actual call,
FreshUse, extrusion/rewrite, replay-demand, and solver-candidate owners needed
for this derivation. A false raw equality does not establish that transport is
valid; actual map identity and its retained route must witness the link.

## Lanes, leases and resources

**Proof — Sol/high, cap720s:** write only
`notes/theory/2026-10-18-demand-root-transport-correspondence.md` and
`tasks/agent-loop/inbox/20261018-demand-root-transport-proof.md`. Construct the
proof from the actual `ScopedDemand` and typed dependency constructors through
all four ordered Function ports. Track `original_call`, `use_instance`, input
route, original/copied root, output scope, witness/map owner and final Replay
row. State hypotheses for each rewrite; handle multiple FreshUse siblings
without aliasing. Apply only the exact established route to P3/P4. Astra0; no
new semantic c rule.

**Implementation — Luna/high, cap840s:** write only
`crates/yu-solver/src/candidate_context.rs`,
`crates/yu-solver/src/candidate_scheme.rs`,
`crates/yu-solver/src/shadow_apply.rs`,
`crates/yu-solver/src/tests/candidate_graph_call.rs`,
`crates/yu-solver/examples/research_scoped_formal_replay.rs`,
`notes/progress/2026-10-18-demand-root-transport.md`, and
`tasks/agent-loop/inbox/20261018-demand-root-transport-impl.md`. Code changes
are limited to preserving/authenticating transport evidence and exposing the
actual map/use/port correspondence. Keep `native_root_matches` raw and keep all
existing solving/transport behavior. New storage must use checked arithmetic,
fallible reservation and atomic failure; account storage explicitly. Include
two distinct FreshUse paths and reject wrong-use/root/four-port substitutions.
No code authoring after 600 seconds; protect 240 seconds for runtime.

Primary-only runtime receipts:
`tasks/agent-loop/runtime/20261018-demand-root-transport.meta.json` and the
four `.test/.example.stdout/.stderr.log` files with that stem. Following frozen
independent review and a fresh capacity check, run each exact command once,
sequentially, timeout <=120 seconds:

```sh
timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo test --offline -p yu-solver --features shadow-apply-candidate candidate_graph_call --lib
timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo run --offline -p yu-solver --features shadow-apply-candidate --example research_scoped_formal_replay
```

No retry on command failure or transport falsifier. Keep the old raw mismatch
in the capture and separately report the proof-backed transported correspondence.

**Fresh independent reviews:** proof/spec review cap240s and compiler review
cap240s. The first checks the derivation against actual map constructors,
port order, siblings and exact P3/P4 hypotheses; the second checks implementation
route authentication, storage/accounting, noninterference and full runtime row.
At code freeze, retain at least 840 seconds total for these reviews (480), both
runtime commands (240) and Luna integration (120). Total cap2400s:
proof720 + implementation840 + reviews480 + primary120 + reserve240. Astra0.
No rollover. At each material lane outcome, update current state and batch
commit/push explicit paths; only Luna integrates.

Stop on an untransported or ambiguous witness, a same-source distinct-use
counterexample, a semantic/core behavior change requirement, pin mismatch,
command failure, budget boundary or writer cessation uncertainty. Unaffected
safe proof/code work continues until the fixed outcome or its precise boundary.

## Parent application and closeout

Preserve original Operation fixed-c, R/W/Z, consumer, F1/FK1, N-Transport,
complete Call, soundness, principality, termination and production gates. A
transport theorem for this fixture is provisional and does not prove universal
P3/P4 coverage. Closeout states only genuinely discharged original premises,
new working implementation/test behavior, and the single next exact obstacle.


## Primary closeout rev2

The conditional constructor proof was independently reviewed CLEAN: it verifies
four ordered ports, owned FreshUse siblings, and upper-fiber Replay inheritance
under explicit canonicalization/root hypotheses. It closes no original condition.

The implementation candidate was frozen and independently reviewed, but is not
accepted or runtime-released. The compiler review found:

- BLOCKING: the observer authenticates a source-to-FreshUse tuple and mapped
  Function shape, but discards the actual Replay lower/upper/BoundKeys and does
  not traverse `Transport`, `Derived`, or `FunctionPort` ancestry. It therefore
  cannot establish that the selected Replay row is descended from the mapped
  source relation or that its current upper is the checked root.
- MAJOR: `four_typed_function_ports_reject_every_pairwise_swap` expects all four
  entries to differ after a two-entry swap; exactly the swapped entries differ.
  The authorized focused `candidate_graph_call` filter omits this unit test.

No Cargo, test or example command ran; `git diff --check` passed. The implementation
remains an unapproved research candidate. Parent conditions closed: 0. All
writers/reviewers STOPPED. Conservatively charged 1800/2400 seconds; 600 seconds
expired at closeout, no rollover. Astra0.

The next exact obstacle is Replay ancestry authentication: carry the selected
Replay coordinates and verify source snapshot -> FreshUse Transport -> any
root-changing Derived/Transport steps -> current upper/root -> ordered
FunctionPort dependencies. Reject unrelated relations with matching metadata.
A successor also needs to correct the swap expectation and run the test that
contains `authentic_demand_capture_tests`, followed by the focused fixture and
example after fresh independent review.

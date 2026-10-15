# Delayed computation controls and local permission

Date: 2026-10-15
Branch: `research/simple-sub-intrusion`
Compiler baseline: `af3ed318b4c022e6baa211134ef89d0f3810eecb`
Task baseline: `1bd0ad3bf`
Status: six source regression controls pass; finite source permission/profile
construction reviewed; lexical-only deletion refuted; native Catch suppression
and full hygiene remain OPEN

## Authority and completed controls

The user's continuation explicitly reaffirms delayed effect-taking arguments.
The [selected scheduling rule](../design/2026-10-02-source-call-scheduling-choice.md#11-direct-reaffirmation-delayed-computation-arguments-2026-10-15)
reifies the whole argument inertly, retains Computation parameters and forces
Value parameters before the receiving body. The outer formal annotation selects
the role; body use and inferred support do not select it. No memoization or
multiplicity policy is added. Ordinary result bindings still evaluate their
RHS under typed-computation-core elaboration §6.

[The new test target](../../crates/yu-solver/tests/candidate_computation_laziness.rs)
uses genuine parser/HIR/candidate inference and covers:

1. Unused Computation with a whole argument block containing two operations:
   the empty result allowance remains admissible.
2. A Computation Name forwarded to an unused Computation formal: the empty
   result allowance remains admissible.
3. Value entry before forwarding to an unused Computation formal: an actual
   effect conflict remains against the empty result allowance.
4. A Computation Name passed to an unused Value consumer: an actual effect
   conflict likewise remains.
5. Nested relay/keep raw resumption with pause inside the delayed argument:
   source admission succeeds with both io and pause allowed.
6. A distinct source with pause in relay's body before `catch thunk`: source
   admission likewise succeeds with both effects allowed.

Negative assertions exclude incidental Value conflicts. The last two controls
establish admission only, not handler eligibility, subtraction, runtime order
or an output value. Production compiler code is unchanged.

## Construction and remaining premise

The independently reviewed [root-permission construction](../theory/2026-10-15-computation-formal-permission-construction.md)
derives the finite concrete licence from the original annotation, formal, root
position and resolved family, preserving the original parameter Value row and
authentic AE/RE correspondence. Its exact-operation classifier follows the
outer signature constructor; raw operation provenance alone also occurs on
nested annotation members and is insufficient.

Residual preservation remains conditional on the actual receiving instance,
path and guaranteed operation coverage. Same-Lambda/direct-Name is not dynamic
owner evidence. Semantic suppression is on HOLD; current Catch forwarding is
unchanged. Permission alone removes no effect; Allowance is not subtraction.

The first resumption attack assumed a saved-binding load before query without
a source constructor. That claim was corrected. The body-pause variant instead
has an explicit formal Name lookup after raw reentry. At initial checkpoint
`7cf804e85`, both investigations still lacked source construction of keep's
RootComp protection and its correlated typed transport into relay. RootPermit
supplies permission only, so that checkpoint claimed no source-qualified
refutation or output 2.

The subsequent independently reviewed [root-profile construction](../theory/2026-10-15-root-computation-profile-source-construction.md)
closes these finite source premises. The selected receiving default constructs
protection at the explicit Computation root, separately from annotation
permission; actual entry instantiates its boundary on the received view. The
exact Name/Delay/Argument constructors generate the root map. After body pause,
the actual formal read supplies Receive for the same view consumed by Observe.
Keep's boundary remains live, while the expired relay grant does not revive.

Consequently a static same-Lambda/direct-Name check cannot justify permanent
flat deletion of io: that source has an escaping io future after raw reentry.
This refutes the proposed unconditional mechanism, not the conditional theorem
requiring actual same-instance evidence. No current native bug or runtime
output is established. The next implementation owners are Comp-entry/profile
instantiation and complete-future transport to the actual Catch consumer.
Current conservative forwarding remains intact; native and global gates stay OPEN.

Frozen non-authoritative handoffs remain under `/tmp`:

| Report | SHA-256 |
| --- | --- |
| `yulang-permission-resumption-proof-20261015/REPORT.md`, corrected original | `7e5f8ff8d9552db3093af120dc41a1b424a25996245f819a5fc9e170033d6457` |
| `yulang-permission-resumption-proof-20261015/body-pause-discriminator.md` | `2d7ff434f886e37db29c44d4ec121b3bc60050e0db8de2be56bca68d805878b1` |
| `yulang-pause-resume-consumer-falsifier-20261015/REPORT.md` | `9897c7bdf2aa6fed9e77dad019248a2184bf1bc4c60fd4fc871f71c32ab4af90` |
| `yulang-pause-resume-consumer-falsifier-20261015/body-pause-discriminator.md` | `233836e30fb9549d13ef13ee3b7c0194eb68a5b3ab3fe21fc134668e70381147` |

These remain historical research handoffs. The reviewed repository note above
contains the finite source construction and the applied feasibility result.

## Review and bounded verification

M2 used one scoped spec auditor for scheduling and one compiler referee for the
conditional permission note and tests. Both scopes closed without remaining
findings. The referee separately reviewed the sixth-test delta and verified
that the prior five tests were byte-identical.
The later root-profile proof received a separate frozen-artifact review from
the independent compiler referee, with no blocking or major findings. Ten
dependency hashes and six linked paths matched. This proof review closes its
finite source premises only; it does not certify native enforcement.

Exact focused command:

```sh
CARGO_BUILD_JOBS=2 timeout 180s cargo test -q -p yu-solver --features shadow-apply-candidate --test candidate_computation_laziness -- --test-threads=1
```

Three serialized invocations: first 4 pass/1 fixture-pattern parse failure;
supported `tick(p)`/`stop(p)` spelling repaired that failure; second 5 pass;
third 6 pass after adding the distinct body-pause source. Successful runs had
no warnings. Logs: `/tmp/yulang-computation-laziness-20261015`.
Final test SHA-256:
`df5d567dca1b8d0569e1afacfda0992baf11b848205a0c7c38c449609270e5b2`.
New-file rustfmt and diff checks pass; all 15 permission-note dependency hashes
match. No broad suite, workspace check, native execution or benchmark ran.

One separately guarded [Oracle observation](2026-10-15-resumption-oracle-probe.md)
stopped during poly lowering with a missing Catch-arm body. No runtime result
was obtained and it was not rerun. Independent provenance review found no
findings. The earlier original/identity Callback Hygiene successes were reused.

Task, research-lab and design-index records are synchronized for this slice.
The historical unintegrated question remains excluded from commits. Omitted
callbacks, native selective Catch, source/runtime correspondence, full soundness
and exact native playground execution remain OPEN.

# Captured callback helper: scoped transport repair

Date: 2026-10-15
Baseline: `860f891df` on `research/simple-sub-intrusion`
Status: constructor and test-contract reviews converged; seven focused tests,
workspace check and four final source controls pass. Original hygiene gate OPEN.

## Authority and scope

The [identity decision](../design/2026-10-15-callback-identity-forwarding.md)
requires ordinary `id` to preserve the callback's outer return. It gives `id`
no identifier-specific semantics and preserves the selected compose contract.
The [receiver construction](../theory/2026-10-15-callback-identity-receiver-construction.md)
has an independently reviewed finite conditional argument. Its native frame,
latent-value, activation and runtime correspondence remain OPEN.

This change repairs source-qualified failures in the grouped local helper
retained by the [attachment checkpoint](2026-10-15-callback-receiver-attachment.md#unresolved-local-helper-evidence):

```yu
act signal:
    our ping: () -> int

my invoke cb = cb 0
my g h = catch ({ my step i = h i; my direct = signal::ping(); invoke step }) {
    signal::ping(), _ -> 1,
    v -> v
}
my callback_first i = signal::ping()
my callback_second i = signal::ping()
my first = catch g callback_first { signal::ping(), _ -> 2, v -> v }
my second = catch g callback_second { signal::ping(), _ -> 3, v -> v }
```

Ordinary inference previously succeeded; scoped inference stopped with
`ReceiptMismatch`. The unchanged grouped source now solves without candidate
conflicts. Catch still conservatively forwards effects. No handler subtraction,
receiver discharge or native execution result follows from this admission.

## Observed constructors and repair

Four successive diagnostic stages exposed the following responsibilities.
Relation and term numbers below identify those frozen diagnostic runs, not
stable public identifiers.

1. **Typed bound payload.** While processing captured h's Value demand,
   negative extrusion emitted an Effect-row copy link `15 -> 44`.
   `candidate_context_bound` copied the enclosing Value qualifier onto it.
   Bound construction now keeps deferred demands on appropriate Value links
   and executable transforms on Effect links. Structural Value-to-Effect
   construction retains ordinary context, source provenance and dependency,
   with no callback demand. Genuine Function ports remain the owner of
   `StampInput` and `ProtectBody`.
2. **Capture completeness.** The next run retained a demand whose negative
   Function root was absent from the captured graph. The existing incremental
   bound worklist now interns retained demand roots through the same graph
   interner, pending worklist and reconstruction maps as structural roots.
   This is a completeness provision for retained payloads. The later diagnoses
   show that this run alone does not establish a legitimate source-produced
   root reachable only through a latent payload.
3. **Structural Value copy link.** Source relation 24 qualified
   `Value47 -> NegativeFunction281`. Extrusion bootstrap relation 28,
   `Value52 -> Value15`, inherited that same demand. FreshUse faithfully copied
   it onto a lower replay bound; replay correctly rejected it. The actual
   `Work::Visit` source/copy constructor now has explicit `ExtrusionLink`
   purpose. Its structural Value link does not inherit the enclosing call's
   qualifier. Ordinary callable bounds retain their qualifiers; Effect links
   retain their executable transforms. No generic demand erasure or weakened
   lower-demand guard was introduced.
4. **Whole-Function rewrite.** Before FreshUse, relation 30 already changed
   upper Function 281 to copied Function 288 while leaving demand root 281.
   FreshUse mapped those different originals to 434 and 467. The initial and
   cached Value extrusion enqueue sites now construct an explicit rewrite
   relation from the actual old/new task pair. It validates the processing
   parent, transports an authenticated root to the actual copied upper
   Function, and preserves Call/use/scope/input identities. Lower-only
   rewriting preserves the root. No consumer guesses or repairs a root by
   matching its fields.

The existing malformed-flow, Function-root authentication and replay guards
remain. Capture ownership still uses the existing boundary/non-generic test;
borrowed outer rows remain shared. Capture adds no executable relation or
identity fiber. Whole-task rewriting adds constant work per rewritten task;
payload traversal uses existing interning and work accounting. No performance
benchmark or global complexity claim accompanies this bounded repair.

## Review and test contract

M2: one implementer, one compiler referee and one spec auditor; a separate
read-only source-evidence producer supports the referee. The referee found no
defect in the final constructor changes, including the initially missed cached
extrusion sibling. A major verification gap remained: successful admission and
a separately invoked projection method did not establish the actual helper's
ports or exclude a demand-free sibling path.

The final test-only repair executes this exact helper, authenticates h by its
source owner/formal registration, and finds actual copied positive/negative
Function comparisons. It checks the actual FunctionPort dependencies, typed
ports, variance operations and AE/RE transformers; requires at least two use
instances and protection reaching real source contributions; and scans the
complete relation table for demand-free siblings with the same pair and source.
Independent delta review closed the major with no remaining findings. The
test adds no synthetic constraint and does not invoke projection manually.

The spec auditor approved a pre-write correction to a provisional new test:
the specific source had not established a strictly latent-only root. The
replacement selects `outer`/`local`, the authentic h Call/formal registration,
and the real local scheme/frontier. It requires nonempty authentic demands,
checks each captured bound's actual upper root, and uses exact original
relation/use lookup after reconstruction. All four ports share the term map;
borrowed rows retain identity; two FreshUses have distinct copied scopes and
inputs. Post-write spec review found no findings. This corrects an unsupported
test premise; it does not weaken the helper's required successful inference.
Strictly latent-only executable source evidence remains unestablished.

## Final verification

Production files were frozen before these checks. The last helper assertion
was a test-only addition and received its own focused command afterward.
All Cargo commands used
`CARGO_BUILD_JOBS=2 timeout 180s`; tests used one test thread.

| Command after `cargo` | Result |
| --- | --- |
| `test -q -p yu-solver --features shadow-apply-candidate --lib structural_bound_scoped_payload -- --test-threads=1` | 2 passed, 697 filtered |
| `test -q -p yu-solver --features shadow-apply-candidate --lib whole_value_rewrite -- --test-threads=1` | 1 passed, 698 filtered |
| `test -q -p yu-solver --features shadow-apply-candidate --test candidate_receiver_boundary_release -- --test-threads=1` | 3 passed |
| `test -q -p yu-solver --features shadow-apply-candidate --lib grouped_helper_actual_copied_h_ports -- --test-threads=1` | 1 passed, 699 filtered |
| `build -q -p yu-playground` | passed, no warnings |
| `check -q --workspace` | passed, no warnings |

After the final cached-path repair, one normal build replaced all temporary
instrumentation. Four sequential CLI runs used
`timeout 15s target/debug/yu-playground --scoped-experiment --intrusion SOURCE`.
Each exited 0 with empty stderr and a 1 MiB per-output-file bound:

| Source | stdout bytes |
| --- | ---: |
| grouped helper above | 348768 |
| `tools/inference-playground/examples/compose-scoped-identity.yu` | 104539 |
| `tools/inference-playground/examples/compose-scoped-two-uses.yu` | 173149 |
| `tools/inference-playground/examples/compose-scoped-independent.yu` | 150417 |

The saved helper records retain original h Call 1 through rewrite relation
`24 -> 30` and FreshUses 3/5 to actual Function comparisons 325/499. Their
result-effect replays 334/508 carry protections 63/91, respectively. The
argument-effect ports have `StampInput` and Bottom replay; this source supplies
no concrete argument-effect member to observe being stamped. The private
whole-helper test independently checks those actual port transformers and
the full internal same-pair/source relation table.

All recorded final compose contribution observations were inspected:

| Source/use | Final row/relation | Retained protections |
| --- | --- | --- |
| identity, use 1 | 15 / 232 | empty |
| two uses, first / second | 15 / 232; 22 / 388 | empty / empty |
| independent, use 2 | 22 / 325 | 53 |

There is one emitted member observation at each destination. These finite
censuses reproduce the earlier selected states; they do not enumerate every
semantic derivation. The evidence packet is
`/tmp/yulang-callback-helper-final-evidence-20261015/{REPORT.md,audit.py,findings.json}`.
Its report hash is
`daec001afe2d46bbec544b06c71f8b88856441bfc67310d42fd8e6a3e733a037`;
the four output hashes are retained there. The artifact explicitly separates
rendered projection evidence from hidden relation metadata covered by the unit.
The same referee checked the raw records and frozen production hashes. One
minor provenance wording issue was corrected: `audit.py` is a one-time
snapshot generator that overwrites its output, not a reusable read-only
verifier. The frozen findings and script were preserved without rerunning or
repinning; the report-only delta passed review. All assigned findings closed.

`git diff --check` and `rustfmt --edition 2024 --check` on the integration
test pass. Broad solver suites, the known separate Effect
fixture failures, native runtime execution and benchmarks were not rerun.
Record-only synchronization does not cause another build or test round.
New and changed local links pass. A whole-record link scan also encountered
15 existing missing references in the historical portion of `tasks/current.md`;
comparison with HEAD confirms that this change introduced none of them.

Worker-owned accounting from first helper diagnostic through final check:
9 builds (4 instrumented diagnostic, 5 normal), 12 focused Cargo test commands
(7 successful, 5 diagnostic failures), 1 workspace check, 24 direct source CLI
runs (17 successful, 7 failures, no timeouts), and 5 debugger inferiors stopped
at their requested diagnostic. These are command/process counts, not distinct
test counts. Earlier attachment syntax checks and other agents' prior work
belong to their earlier checkpoint; this is not a session-wide total. No
performance samples or timing repetitions were added.

Logs, diagnostic patches, source and exact command ledger are under
`/tmp/yulang-callback-helper-diagnostic-20261015/`, including
`final-delta-{unit,rewrite,integration}.log`, `final-actual-helper-unit.log`,
`final-primary-summary.md` (before the final test-only command),
`final-primary-cli.json`, `final-primary-*.stdout`, and the binary hash.

## Remaining original gate

The primary owns the next source bridge: retain the actual named parameter
group and selected terminal-body frame at HIR formation, then jointly transport
the corresponding protection key and discharge. Actual latent values, active
receiver lifetime, selective Catch consumption and runtime remain OPEN.
The exact original and ordinary-id samples run on frozen Oracle; this helper
repair does not make either exact sample run on the native playground.

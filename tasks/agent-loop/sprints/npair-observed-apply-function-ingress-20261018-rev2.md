# Sprint `npair-observed-apply-function-ingress-20261018`

Status: ACTIVE, sequential revision 2 issued 2026-10-18.
Branch/baseline: `research/simple-sub-intrusion` /
`5c45c1807fc6f4fa495a2f0b85c4bdba1672820d`.
Supersedes rev1 contract SHA-256
`f1b4610c17189becb92ba9e773c6cd667f265bb2129424ef1f3bf7f5cfae9be3`;
rev1 is preserved at
`tasks/agent-loop/sprints/npair-observed-apply-function-ingress-20261018-rev1.md`.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`; original theorem,
domain, quantifiers, receive route, C1/C2 and F1/FK1 are unchanged.

## Fixed outcome

Observe the actual added binding `my received = receive f0` from parsed source
through HIR LocalSource and candidate collection, including the exact outer
Apply occurrence and operands. In the same candidate snapshot, correlate that
source occurrence and its typed endpoints with its authenticated `source_call`
and actual native demand; report all four Function children. Then identify any
actual Replay dependency on this route and report both ordered lower/upper
BoundKeys and their relation fibers, or state that this API does not expose the
correlation. Do not pick a call by count, first entry, family equality or a
nearby source occurrence. Do not synthesize a missing call or Replay input.

The proof lane derives the source-owned constructor/dispatch rules and applies
only established edges. Keep Operation root Self `s0` separate from returned
Written `s1`; trace the same returned `R1` and Permission negative port `D`.
The native output authenticates candidate construction only; it does not prove
the original contribution judgment, `eta`, `At`, full N-Transport, or the
original theorem. A source refusal or unestablished edge does not refute the
parent. No domain restriction, field movement, new semantic assumption or
expected-output change is allowed.

## Lanes and exact writes

1. **Constructive proof, Sol/prover/high, cap600s.** Continue the rev1 proof
packet over the same pinned source owners. Derive actual Apply demand, complete
Function children, same-R1 install/fresh-use and the exact `s1`/D field route.
Name any remapping (including receive-use row scope) and the exact whole
transport law required; do not identify scoped rows with original rows by raw
key equality. State both Replay constructor inputs with their order and exact
dependency. Apply only established premises to the original witness/H0, L2
`eta`, P3/P6, preserving all quantified alternatives. Write only:
`notes/theory/2026-10-18-npair-observed-apply-function-ingress.md` and
`tasks/agent-loop/inbox/20261018-npair-observed-apply-function-ingress.md`.

2. **Implementation/source path, Luna/implementer/high, cap720s.** Continue
rev1 using the expanded read-only pins below. Extend only the research example
to report the `received` binding/HIR node, LocalSource result, collected Apply
and operands; query `source_call` and the native demand in the same inference
snapshot, correlating exact source occurrence, operands, typed endpoints and
scope. Print all four children. Inspect scoped dependency/relation-flow views
for a Replay tied to those actual bound keys; preserve lower then upper order
and both corresponding relation inputs. If the public API cannot correlate an
edge, report it as unobserved. Do not infer absence from `UnsupportedExpression`
or selective output.

Before spending the sole Cargo run, freeze the harness-query diff and send its
exact hash to Luna. A fresh independent implementation/compiler review checks
that every query ties to the actual binding/endpoints and cannot select by
count/index/family coincidence. Run only after a clean review, or after Luna
adjudicates and resolves any finding within the existing review/resource
envelope. Add the one reversible source line to the fixture, run the command
below once, then restore fixture bytes. No production compiler code, tests,
expected output, manifests, public API or semantics may change. Write only:
`notes/progress/2026-10-18-npair-observed-apply-source-evidence.md`,
`tasks/agent-loop/inbox/20261018-npair-observed-apply-source-evidence.md`,
the research example and the one-line fixture (fixture restored exactly after
the run).

   ```yu
   my received = receive f0
   ```

   ```sh
   timeout 120s cargo run --offline \
     --manifest-path crates/yu-solver/Cargo.toml \
     --example research_source_registration \
     --features shadow-apply-candidate
   ```

## Pinned inputs and access

All rev1 pins remain valid and keep their prior access. Rev2 adds these
read-only pins for the implementation query; no owner may be modified:

| Path | SHA-256 | Access |
|---|---|---|
| `crates/yu-solver/src/candidate_call.rs` | `2bcbab3d27e259fc4b22824980bd625014d4a19f4fa257cd74c69683c1be0359` | read-only, implementation query |
| `crates/yu-solver/src/shadow_apply.rs` | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` | read-only, implementation query |
| `crates/yu-solver/src/candidate_context.rs` | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` | read-only, implementation query |

The full rev1 pin table is retained unchanged; see
`tasks/agent-loop/sprints/npair-observed-apply-function-ingress-20261018-rev1.md`.
The corrected source-path disposition SHA-256
`071b87b2e08acf6845de2b8fd16199fe0c84590abda5fc2f4bb41aae7fa39586`
supersedes the old LocalSource-absence inference.

## Review, resources and stop

Fresh independent proof/spec review: 180s. Fresh independent
implementation/compiler review: 120s, front-loaded on frozen query code before
the sole run. Luna primary/integration: 120s (120s charged at rev1 start);
reserve60s. Total1800s, Astra0, descendants0. Only the exact existing example
command above may run, once; no other tests/builds/probes. Any pin mismatch,
need to edit production compiler/HIR, missing writer cessation or budget cap is
a stop with its exact first unresolved edge. Existing original semantic
alternatives, W/Z, source/native correspondence, Call, N-Transport, soundness,
principality, termination, F1/FK1 and parent closure remain separate.

After the run, Luna checks the fixture is restored, integrates reviewed receipts,
updates compact state and stages explicit paths for a non-forced push.

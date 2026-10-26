# Source-signature construction r5 — independent review

Assignment-ID: `source_signature_review_r5`; receipt revision: **1**.
Reviewer: `/root/source_signature_review_r5`, fresh nonauthor; no descendants.
Producer: `/root/source_semantics_route_r5`, frozen during review.
Baseline supplied by primary: `97788357754a57562607dd8ff41ac55ffcb3c9b8`.
Role: independent source-correspondence/compiler-referee review of a research
proof slice. Requested settings: inherited defaults; observed settings: UNKNOWN.

## Verdict

**ACCEPT for the explicitly delimited static graph/support/provenance and Call
allocation slice. No BLOCKING, major or minor findings in this frozen scope.**
This accepts neither complete Theorem SIG nor an original Kernel instance,
original inference soundness, native correspondence or production closure.
The producer's explicit distinction between static frame retention and original
semantic validity is necessary to this verdict and remains intact.

## Frozen bytes and review method

The following exact SHA-256 values match the assigned snapshot and the
producer's freeze manifest:

| Reviewed file | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/SourceSignatureConstruction.lean` | `ed07890e29b4dcb38cabd18ec0e196efde9e95c64902942a9906a470b38c3311` |
| `notes/theory/2026-10-26-source-signature-construction-r5.md` | `fd70940c5791eb0c3af496796163e55b0afdbcc8a2497583094fbb1eb1782f85` |
| `tasks/agent-loop/inbox/20261026-source-signature-construction-r5.md` | `27558ae43ead5744ee5f58b57d062b411b72128ced361ca4359526842a3094ac` |

Applied root AGENTS/pre-sprint, design authority, top-level inference
principles, proof-closure and compiler-engineering requirements, testing and
orchestration rules, the `yulang-lean-proofs` skill with its source/execution
references, and `.codex/agents/compiler-referee.toml`. Inspected actual Lean
declarations and their direct syntax dependency before using the producer's
explanation as the claim to be checked. Read the adopted native-signature
definition §§2–4, signature-incidence construction §§3.2–4.1, 5 and 7, Call
source-interface definition §§2–3 and construction §§3–6, and the relevant
whole-proof/Kernel/source-App boundaries.

Review was by constructor and quantifier inspection, targeted adversarial
traces, byte comparison and independent parsing of retained checker evidence.
No fresh Lean run was justified by a remaining concrete checker risk: **0 of
the at-most-2 risk-driven reviewer checks used**. No Cargo/default Lake build,
external research, Git/index/status mutation, source edit or shared record edit
was performed. An initial read used a nonexistent `check10.log` spelling; the
actual retained `check10-origin-census.log` was then read and independently
validated. That read-path error was not a checker failure.

## Source-to-construction assessment

1. **Independent graph grammar.** `SourceEdge` (Lean 188–202) inspects each
   source-node constructor without referring to `Node.edges` or compiled
   membership. The compiler computes the separate concrete edge list
   (133–147). `source_edge_exact` proves both directions for alternative,
   conjunction, indexed image operand, every indexed Call phase/arm,
   reference, scope, rename, insertion and annotation. `build` performs the
   actual list-map compilation and retains the entire source node. No desired
   global source-placement, typing-success or incidence theorem is a premise.

2. **Finite provenance and cycles.** `PortProv` and `Developed` (280–295) have
   independent source-edge/compiled-edge premises and the same complete
   introduction/route indices. `compile_provenance`, `read_provenance` and
   `provenance_iff` establish the exact finite correspondence. Every finite
   origin development terminates at an introduction; a cycle has no special
   origin constructor. `no_introductions_no_provenance` and `no_new_origin`
   correctly cover origin-free cyclic graphs. A cycle with an actual reachable
   introduction can have multiple finite routes, which are retained rather
   than collapsed. This agrees with the adopted finite-development discipline.

3. **Support before applicability.** `Catalogue.Port` and its dependent
   `Packet whole port` are arbitrary types, so the finite graph imposes no
   finite bound on providers, future interactions or witnesses. `Support`
   requires the actual catalogue port without a packet/license witness;
   `ContextualSupport` adds a finite route and endpoint support. Both
   alternative branches and both conjunction operands remain in the graph.
   Empty and unselected license fibers cannot prune these constructors.
   `SupportPath.here` alone permits an unallocated index, but it is not a
   supported port: `ContextualSupport.support` separately requires the actual
   endpoint lookup. Thus this does not fabricate support or provenance.

4. **Owners, receivers and occurrences.** An occurrence retains its full
   original introduction and route. Root insertion sets only the receiver and
   prepends its insertion step. Actual reference/operand history determines
   inherited classification; owner/receiver equality is never used to reset
   it. `reference_stays_inherited_at_equal_owner` checks precisely the repaired
   declared-Ref case. Conjunction's left/right route tags distinguish repeated
   occurrences even when their introduction and owner data coincide. All
   owner/receiver equations used here follow by projection of constructed
   records, rather than an assumed global attribution relation.

5. **Whole tuple and dependent leaf evidence.** `Step.action` applies an
   original whole-row function only at an actual reference/rename step;
   `routeAction` folds these actions once per route occurrence in the stated
   outside-to-inside order. It assumes neither idempotence nor commutativity.
   Other contextual steps preserve the same row, so conjunction operands use
   one shared row. Packet and license types use the same transported row and
   original port. `insertField` retains the entire `LeafLicensedField` object;
   readback and injectivity preserve its original dependent packet and license
   witness. These are retention results, not an action/naturality theorem for
   independently legal source substitutions. Their original legality remains
   explicitly open at its owner.

6. **Actual Call allocation.** `installCall` (639–644) appends the six ordered
   `CallRegions` nodes plus every arm, then constructs the Call node with
   computed addresses. It does not assume an existing Call certificate or
   successful solver result. `installed_region_node` returns each exact
   appended object; `installed_call_arm` and `installed_arm_support` range over
   every indexed arm and port without a license premise. Old allocated nodes,
   registration and substitution tables are preserved. `call_entries_exact`
   covers all six fixed phases and the entire indexed arm list. The raw App
   atom preserves the original context/site and ordered callee/argument sites
   from `OriginalSourceGeneration.sourceRules`. No phase or arm is selected by
   endpoint equality, provider shape or applicability.

## Acceptance boundary and parent application

The graph is a total raw carrier. Arbitrary supplied catalogues, local
introductions, references and Call-region data are **not** proved to be
authentic original source formations. The existing note and handoff explicitly
retain that boundary. In particular, the formalized `PortProv` is a graph
introduction/route judgment; identifying it with every original per-port
dependent governed-field partition still needs the genuine schema/field and
registration maps. Merely choosing arbitrary `Packet` types does not discharge
that semantic identification. The graph correspondence remains useful without
asserting that missing bridge.

`StaticCallIncidence` (587–592) means the static Call-node component. It is not
the full original `Kernel.atom` interpretation of `sourceCallIncidence`.
`raw_call_static_incidence` constructs this static component without a
pre-registered Call lookup; it supplies no original descriptor, phase/world,
provider, admission or C0 law. The complete source atom and its original
semantic requirements remain unchanged.

`LeafLicensedField` is explicitly primitive/local and is **not** composite
`DeclContribution`. It neither selects an applicable Union branch nor proves
the original operator's governed-license-field law. Complete same-row
contribution packaging, independent L/A grammars, their compiler/readback
maps, upper scalar subrecord correspondence and certified whole/joint-hiding
operations remain OPEN. Original schema authentication, source/environment
registration, lawful substitutions, C0, full contextual admission/observation,
annotations and conversion realization likewise remain OPEN at their owners.
The independently published predecessor `OriginalSourceInterpretation` result
was not re-reviewed or expanded by this packet.

Within those explicit limits, this supplies constructive graph-edge,
finite-provenance and contextual-support correspondence, and actual Call
region allocation, for later faithful original source interpretation. No
circular premise disguises full original soundness as a new leaf, and no
original source form/domain/quantifier is retired by these results. The next
parent step remains the genuine schema/registration bridge and full
`DeclContribution`/L/A construction, followed by the native-success-to-original
shared-witness seam. This receipt closes only independent review of this slice.

## Verification evidence checked independently

- All **35** recorded input hashes match their current bytes, including the
  external predecessor locator. The isolated checked module, syntax import,
  toolchain pin, Lake configuration and manifest match the repository bytes.
  `receipts/check09-source.lean` is the exact reviewed module, with final LF.
- Check09 records Lake `5.0.0-src+eb6cafb`, Lean `4.35.0` commit
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, focused module build exit 0 and
  audit exit 0. All **45** authored public theorem names match source discovery
  and the root manifest, each with one complete begin/end and PASS record.
  Their complete types are present in the frozen handoff appendix.
- The final origin-census source selects declarations by Lean module origin,
  includes private/generated declarations, rejects originating project axioms
  and checks transitive axioms for every declaration. Its actual direct Lean
  exit **0** is separately captured in `receipts/check10-exit.json`.
- Independently parsed **848** unique census begin/end pairs in matching
  order, including **383** theorem constants and **18** private theorem
  constants. The theorem axiom sets are **249 none**, **104 only propext**,
  **30 propext + Quot.sound**; no extra axiom result occurs. The 867,224-byte
  census reaches its exact final count/EOF marker and has SHA-256
  `ab6709196efc32c8d61393453c28ec88be8ca2a0b83dbb3b71b7337f980f5475`.
- Material earlier failure logs and source snapshots remain present. Check07's
  missing separately captured direct exit is honestly superseded by check10,
  not treated as independent final acceptance. The old in-repository scratch
  directory is absent. No proof-hole, project-axiom or checker-bypass token was
  found in the reviewed module/direct syntax dependency.

Reviewer evidence-only parsing summary:
`/workspace/scratch/c10e953a5453/source-signature-review-r5/evidence-audit.json`.
This is inspection of retained producer execution, not a claim that the
reviewer reran Lean or independently certified the original semantics.

## Freeze receipt

Only this assigned inbox file and the reviewer's exact scratch directory were
written. No producer artifact, configuration, import, Rust source, Git/index or
shared status was edited. No children or active checker processes exist.
**Review complete; all reviewer writes stopped after this frozen revision.**

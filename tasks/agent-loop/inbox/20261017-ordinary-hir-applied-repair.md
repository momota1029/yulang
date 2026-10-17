# Ordinary HIR applied-conformance repair: Luna adjudication and implementation handoff

- Handoff revision 2. Sprint:
  `ordinary-hir-applied-conformance-repair-20261017` rev3, SHA-256
  `006ffcf86d526f6eb5f668307ab81a2ae6dda2067a547889095d74fd89b25fd2`;
  parent unchanged, original theorem conditions closed: 0.
- Baseline: failed candidate `4f4dcb7b9`; adopted grammar rev4
  `2e61e2acb1a8981bb78592accc48207a24a5cc4c75278e100f63eb960acfeea3`; adopted
  `O(V+E+R)` resource correction
  `e8b53a773675ba54f0cb5dcc4d62a993e8dd16954e0c92c58fdfc80c620d411e`.
- Frozen source packet: theory `1f3afae18e36ca0abf5a9be1fbf2d1220fad0836a0cce3c370e6cce15a027a28`,
  handoff `7bd7cfe427f498c88bab2fab71ae1f24b4ab7f30c24552bbd2030404dcbdf6c3`;
  worker STOPPED; its 240s cap conservatively charged because exact elapsed is
  UNKNOWN.
- Luna plan: `notes/design/2026-10-17-ordinary-hir-applied-repair-plan.md`,
  SHA-256 `45c4cebfc6b5f35cf2f081db61959558721757f6a3a3f802ae310181f5ea4dc3`.
- Outcome class: candidate implementation plan, not proof or implementation.
  It specifies all seven review repairs and the exact counterexamples in the
  theory packet. `HIR-APP-REPAIR-1` and every original parent gate remain OPEN.
- Exact missing premise: `ChainParser` discards constructor-owned `SyntaxNode`s
  from public `HirExpr::Value`; current `module.rs` searches by kind/range,
  forbidden by adopted rev4 §5. Proposed small seam is a crate-private
  provenance-bearing result from the same association construction, leaving
  public `HirExpr` and existing callers unchanged. Shape/path agreement must
  hold by construction; no second association walk or reconstructed key.
- Fresh architect review: CLEAN, recorded at
  `notes/progress/2026-10-17-ordinary-hir-repair-architect-review.md`, SHA-256
  `635cd68b611d652f4d6760026888945518423b8be69729560418807d9fbbc339`.
  It confirms feasibility for the frozen plan, not implementation. Luna has
  adjudicated CLEAN and grants the following exact sequential writer lease
  (<=1110s):
  `crates/yu-hir/src/lib.rs`, `crates/yu-hir/src/module.rs`,
  `crates/yu-hir/src/source_identity.rs`, `crates/yu-hir/src/shadow.rs`,
  `crates/yu-hir/tests/ordinary_application_admission.rs`,
  `crates/yu-solver/tests/research_accepted_call_vertical.rs`, and this shared
  handoff. `lib.rs` is newly added only for the private provenance constructor.
- Current pins are in the frozen plan; the sprint's `5fbceb68d` hashes are
  historical, not current inputs. Three inherited UNKNOWN leases remain
  quarantined.
- Static workflow check `python3 tools/agent_sprint.py check` passed; it is not
  compiler execution. No Cargo/test/build has run in this repair sprint.
- Next bounded step: implement all seven repairs under the exact paths above,
  account for allocations, report `V/E/R` and actual list reference storage,
  add all falsifying regressions, run only the contract's allowed formatting
  check, and freeze with hashes/resource receipt. Do not run Cargo until fresh
  applied reviews and regression pre-run clearance.
- Worker state: architecture reviewer STOPPED; implementation lane authorized
  but requires a fresh active acknowledgment before writing.

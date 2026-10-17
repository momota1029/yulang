# Pre-code architecture review: ordinary HIR applied repair

Sprint `ordinary-hir-applied-conformance-repair-20261017`, rev2. Reviewer:
`/root/ordinary_hir_repair_architect_rev2` (`architect`, requested
gpt-6.1-sol/medium; observed model and effort UNKNOWN), read-only; STOPPED.
Review cap 120s; exact elapsed unreported, so Luna conservatively charges the
full 120s. No edits, tests, builds, probes, Git operations or descendants.

## Frozen targets

- Plan: `notes/design/2026-10-17-ordinary-hir-applied-repair-plan.md`, SHA-256
  `45c4cebfc6b5f35cf2f081db61959558721757f6a3a3f802ae310181f5ea4dc3`.
- Sprint rev2 SHA-256
  `056ac4651fbba8a5062d5cd61f9100b33937712c34bd9579f3c8af8960d5dbc3`.
- Repair invariants SHA-256
  `1f3afae18e36ca0abf5a9be1fbf2d1220fad0836a0cce3c370e6cce15a027a28`.
- Adopted ordinary-HIR successor rev4 SHA-256
  `2e61e2acb1a8981bb78592accc48207a24a5cc4c75278e100f63eb960acfeea3`.
- Adopted resource correction SHA-256
  `e8b53a773675ba54f0cb5dcc4d62a993e8dd16954e0c92c58fdfc80c620d411e`.

## Finding and Luna adjudication

**CLEAN for the pre-code feasibility gate.** A private construction result can
pair the existing `HirExpr` with a matching provenance shape from the same
`ChainParser`: `value` retains its actual node; nested collection moves paired
children; `structural_continuation` retains the actual tail and keeps the prior
left expression as child zero. Existing adapters can discard metadata. This
does not require a public `HirExpr` change, a second association walk, range
lookup or whole-subtree cloning. The proposed exact seven-path implementation
lease is sufficient; `lib.rs` is added only for this private provenance seam.

The review also confirms the implementation obligations are bounded and
visible: account for existing `collect`, nested `push`, `with_capacity`,
`vec!`, operand boxing and final boxed-slice conversion; do not describe
infallible standard allocations as fallible. Use checked reservations for the
projection-owned result, avoid unchecked boxed-slice shrink allocation, and
cache/forward Group aggregate error views. Actual punctuation must be inspected
before operand resolution. Stage operand events after `DuplicateDefinition`,
bind final IDs, build each Apply list once, finalize a saved item index, validate
the root before stage merge, and recompute classification from the final
binding value. Structural refusal keeps old fallback and emits no child
identity; identity/capacity failure publishes no module.

Luna adjudicates the review CLEAN within the exact frozen plan and adopted
contracts, and authorizes the already proposed sequential implementation
lease. This does not prove the seam in code, certify allocation-failure
behavior or measured complexity, close `HIR-APP-REPAIR-1`, or discharge any
original theorem condition. All seven falsifiers, exact-key fixtures,
`V/E/R`/allocation accounting and many-bindings discriminator remain required.
Fresh applied compiler, spec, architecture and regression reviews remain in
the contract. Original theorem conditions closed: 0.

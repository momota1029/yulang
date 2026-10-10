# Expression-ascription source-to-solver bridge

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Status: private construction bridge implemented and reviewed; cycle
recognition and lifecycle remain open

## Authority and scope

This slice implements the already-Authoritative
[contextual attachment admission design](../design/2026-10-10-contextual-attachment-admission-design.md)
§§3–6 and the same-actual-Value invariant in the
[recursive PUSH source invariant](../progress/2026-10-10-recursive-push-source-invariant.md).
It adds no language decision and does not enable ordinary source admission.

## Construction correspondence

The private HIR local-source representation now retains an expression
ascription as a node containing its child and the exact lowered annotation
tail. Source identity, lexical scope, and occurrence are retained. Candidate
source planning visits the child before its ascription. It resolves the
ascription through transparent Group/Ascription wrappers to the deepest child
and maps the ascription occurrence to the same canonical candidate component
as that child.

The solver emits the two value directions against that child's actual Value
endpoint, preserving a Parameter endpoint when the child is a formal. The
annotation computation-effect check uses the child's actual Effect component.
It keeps the existing source ordering and does not introduce a generalized
intermediate scheme. Exact annotation occurrences remain distinct. Local
annotation scope and formal-name provenance pass through the ascription action,
so formal Call observation keeps the original lexical name and registration.

Expression ascriptions can share their HIR occurrence with a binding
annotation. The expression pair/effect use slots 45/46/47 and its empty-source
bundle anchors at 46. Existing binding annotation slots 40/41/42 and formal
slots 43/44 remain unchanged. Context seeding associates each pair with the
bundle for its own slot namespace.

## Evidence and limits

Focused checks passed:

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test --offline -p yu-hir module::local_source::tests -- --test-threads=1` (5 passed).
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test --offline -p yu-solver --features shadow-apply-candidate --lib expression_ascription_ -- --test-threads=1` (8 passed).
- Scoped `git diff --check` over the changed HIR and solver paths.

Independent compiler-referee review found no semantic issue in component
aliasing, paired slots, bundle routing, or endpoint provenance. Independent
spec-auditor review found exact conformance to the cited source/constraint
contract. These are reviews of the construction bridge, not certification of
the overall contextual solver.

This slice does not implement exact PUSH or POP/PUSH cycle recognition, an
inferred-entry certificate, dependency-indexed invalidation/withdrawal,
unsupported-edge deferral, rollback/retry of certificate state, or recursive
nonempty-context admission. It does not establish complete Call semantics,
full effect hygiene, soundness, principality, ordinary/default inference, or
F5 replacement. The next gate remains the source-owned cycle certificate and
lifecycle described in the current task record.

# SCC intrusion end-to-end capability matrix

Date: 2026-09-30
Purpose: connect frozen-Oracle source observations to the Yulang3 replacement path
Status: evidence inventory; not a selected support boundary or equivalence proof

The user's objective remains Oracle-capable SCC intrusion followed by a
complete replacement inference machine. This matrix does not select a smaller
acceptance target. It separates source facts already observed from the work
needed to model, prove, and implement them.

| Capability witness | Frozen Oracle evidence | Current Yulang3 source path | Intrusion obligation still open |
|---|---|---|---|
| Identity used at `int` and Function types | `pub id x = x; pub number = id 1; pub function_value = id (\\x -> x)` succeeds; both uses format as expected (`notes/progress/2026-09-29-intrusion-oracle-ledger.md`, source-level independent uses). | Expression application and expression lambda are rejected before solver collection (`notes/progress/2026-09-29-intrusion-rust-replacement-map.md`, HIR gap; `crates/yu-hir/src/module.rs::lower_simple_chain`). | Relate type and latent-effect endpoints through independent incoming-use maps and match public schemes/diagnostics. |
| One-sided argument projection | `pub k x = 1` yields `any -> int` with no ordinary or recursive binders; the negative-only unconstrained argument is erased (`intrusion-oracle-ledger.md`, one-sided Function parameter). A constrained negative variable can instead project to its informative upper bound (see `intrusion-bounded-negative-counterexample.md`, §§1 and “Source-level anchored alias probe”). | A simple parameter lambda exists, but current root projection remains F5-backed and cannot yet be compared to the Oracle scheme contract. | Prove root projection preserves the projected upper-bound meaning, and permits unconstrained erasure only when no informative bound is lost. |
| Captured local diamond | `my outer x = my inner y = ({left: x, right: x}, y); inner` retains one shared outer identity through both record fields (`intrusion-oracle-ledger.md`, local diamond row). | Tuple/record values have no resolved-expression-to-solver path. | Define product subtype and projection rules, preserve anchored outer identity, and prove shared descendants are not captured or duplicated. |
| Unproductive mutual recursion | Top-level mutual call cycle succeeds with both members `any -> never`; forward-cycle SCC scheduler fixture is recorded in the ledger. | Only leaf Integer/Name bodies and one simple parameter lambda reach constraints; applications do not. | Preserve live internal SCC uses and derive the Oracle observation without using F5 scheme shape as a premise. |
| Nominally guarded recursive Function SCC with independent incoming uses | `helper`/`g` guarded through `wrap`, then used at integer and identity-Function arguments; one two-member component, two internal uses, three external uses, recursive intervals and distinct immediate use variables (`notes/progress/2026-09-30-intrusion-bounded-negative-counterexample.md`, §§ guarded multi-member component). | No resolved nominal, record, tuple, or application expression path in current HIR/solver. | Specify nominal variance/matching, guardedness, recursive interval semantics, publication ordering, and transitive use isolation. |
| Implicit latent Function effects | Ordinary lambdas/functions allocate effect variables without explicit effect syntax; a forced effect binder is fresh per use while eleven unlisted identities remain shared (`notes/progress/2026-09-30-intrusion-oracle-latent-effects.md`). | `yu-types` has Function effect slots but current exposed effect view is only Bottom/Empty; no equivalent source constraints/use path. | Model effect bounds, forced generalization, use-site freshening, unquantified anchors, and interaction with sequential root preparation. |
| Annotated local effect-binder uses | The source with `l: int`, `sink: 'e -> int`, and outer result `: int` retains the local scheme; two reads freshen the forced effect identity independently while eleven other effect identities stay shared. Without the outer result annotation the reads remain live (`notes/progress/2026-09-30-intrusion-bounded-negative-counterexample.md`, forced effect use rows). | Multi-parameter annotated local functions, these effect constraints, and local saved-scheme instantiation are not present as one resolved HIR/solver path. | Preserve annotation constraints and the annotation-dependent local read route before comparing per-use effect identities. |
| Per-member fetch and ordered root preparation | Oracle uses `FetchValue` and `FetchComputation` at different boundaries and generalizes component roots sequentially; the ledger records root epochs and publication order. | F4 scheduling exists, but replacement has no component/member-root authority independent of F5 schemes. | Preserve member-specific boundary selection, root-local projection evidence, epoch changes, and the all-member publication barrier in one simulation. |
| Public failures and diagnostics | Existing probes record selected successes and a few exact diagnostics; there is not yet a normalized full diagnostic contract for this family. | HIR has source diagnostics for unsupported expressions, which are observably different from successful Oracle lowering. | Include status, ordered diagnostics, source locations, semantic payload, and public type output in the source simulation; do not compare solver graphs alone. |

## Current source-path boundary

The current resolved HIR expression algebra is limited to lambda, integer,
name, and error forms. `lower_simple_chain` rejects non-leaf application
before atom lowering; tuple, record, nominal, and handler forms have no
resolved-expression-to-solver route. The SCC scheduler exists, but member
generalization, incoming use instantiation, and root projection are coupled to
F5 closed schemes. See `notes/progress/2026-09-29-intrusion-rust-replacement-map.md`
and the read-only map in the source-envelope review history.

This means the next gate remains semantic and cross-layer design: construct the
event alphabet and observable relation for the actually observed witnesses,
define effect and recursive-interval operations in that relation, and prove a
root-indexed simulation before selecting replacement storage. Source-language
production then needs the missing HIR and solver routes as explicit parts of
the eventual implementation, rather than treating graph-only probes as
source-level parity.

No compiler code changed and no test or measurement was run for this inventory.

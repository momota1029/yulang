# Flat LocalSource depth and simple projection integration

Date: 2026-10-13
Status: proof-supported private implementation; independently reviewed and compile-checked
Baseline: `06eb3e80c7dd8032b6d9ef39b357714dc43da536`
Branch: `research/simple-sub-intrusion`
Mode: M2 implementation; semantic compiler_referee and static performance_auditor
Runtime tests / whole-module stack certification / F5 cutover: not established

## Authority and decisive evidence

The selected [inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§2–4 govern natural source processing, avoiding unnecessary construction,
proof before implementation and necessary abnormal-path safety.
Source Generalize's [owning rules](../theory/2026-10-08-source-generalize-definition-and-proof.md)
§3.3 require the existing source identities and scopes.

The [flat formation proof](../theory/2026-10-13-flat-local-source-formation-proof.md)
establishes finite descendant scheduling, single-write slots, identity/scope
preservation and root recovery ancestry. It also exposed a real downstream
obstruction: after successful formation, simple body lowering constructed a
recursive associated HirExpr before discarding it. Merely removing the
builder's expression cap would newly reach that construction at greater depth.

The separate [projection proof](../theory/2026-10-13-formed-local-source-simple-projection-proof.md)
and freshly reviewed §6.1 bridge cover every authentic cap-lifted F-success
Binding. Successful retained grammar excludes every association-reachable
dynamic use. Existing direct_atom therefore gives the same lower_leaf result
or outer Unsupported result without building the discarded tree. This theorem
does not cover arbitrary forged CSTs; the actual private parsed-plan caller
supplies its authentication premise.

Independent specification review permits this internal optimization within
the opt-in source formation scope. The September 19 ordinary association
contract and the still-unapproved ordinary-HIR source-carrier migration are
separate; this implementation adopts neither a new public API nor that migration.

## Actual implementation and removed dependency

| Owner | Implemented operation |
| --- | --- |
| `module/local_source.rs::form` | Completes all source work, slots and root annotation, then returns LocalSource plus private SimpleBodyProjection from the exact queued root body using unchanged direct_atom. |
| Binding `module.rs::lower_plan` | Receives that successful product, installs the same carrier and passes its projection only to the same Binding's body consumer. |
| `module.rs::lower_body` | After existing validation and shadow dispatch, calls unchanged lower_leaf for Atom, the same common Unsupported branch/range otherwise, and the original associator when no projection exists. |
| Existing flat Work scheduler | Removes expression/initializer depth fields, arithmetic and three 128 refusals. Lexical Publish/Restore lengths retain their meaning and ordering. |

The opted-in formed-Binding simple fallback no longer depends on recursive
association/ownership of an unused HirExpr. Its supported expression and
local-initializer depth is bounded by actual resources and checked identities,
rather than the artificial 128 counter. The redundant nested BindingStatement
recovery scan is removed under the retained whole-root recovery invariant.

Root parameters remain capped at 127 because their separate legacy output is
boxed. Annotation depth remains capped at 128 before recursive type parsing.
Syntax, visibility, operation, identity and allocation checks remain. Ordinary
default, unformed, DirectExpression, public association and shadow application
routes retain their original selection. Those real recursive consumers remain
explicitly outside this local withdrawal; no whole-module migration is claimed.

## Reviews and costs

The guarded projection and the larger-input bridge received separate fresh
independent compiler-referee reviews. The frozen implementation received one
semantic and one static performance review; both passed with no findings.
The primary inspected the narrow diff and rechecked both code hashes.

The existing work stack is reused. For the proof's constructor counts,
slots are `1+R+P+2A+C+G+K+I`, popped work is `E+2I+K`, and lexical pushes
are `R+P+I+J` with `J<=I`. The private projection adds constant phase state
and the same direct-token copy; it introduces no new traversal or cache.
Removing repeated initializer-subtree recovery eliminates that O(N*D) cost.
Header, annotation, root/body recovery, hashing, copied payloads and transient
Option/final vector coexistence remain in the cost model. Expected formation
work is `O(N+R+P+S+I+H+Q+payload)` under the stated library assumptions,
not unconditional linear whole-lowering work or a bounded-RSS guarantee.
Existing infallible allocations and incomplete retained-byte accounting remain.

Timing measurements were unnecessary for this static implementation decision:
zero benchmark processes, warm-ups and measured samples.

## Exact verification and residuals

Primary compile checks passed without warnings, sequentially on the frozen code:

- `RUSTC_WRAPPER= cargo check -p yu-hir --features shadow --all-targets -j 2 --offline`
- `RUSTC_WRAPPER= cargo check -p yu-hir -j 2 --offline`
- `RUSTC_WRAPPER= cargo check -p yu-solver --features shadow-apply-candidate -j 2 --offline`
- `git diff --check`

The first command compiles test configurations; it executes no tests. No tests
were added or run, and no runtime deep-source, small-stack return/drop or
performance probe was run. Those observations are unverified. Three scoped
Cargo check processes were used; no workspace-wide or heavy suite was run.

Frozen code SHA-256, unchanged through review and verification:

```text
8008b84738990cb22199d386129ecb810f86c907e222da40411cddb18eb279f7  crates/yu-hir/src/module/local_source.rs
2fd2114389a595721c0b7631b5fdf602ccfbc024df7db144649eae05f681f133  crates/yu-hir/src/module.rs
```

This implements and compile-checks the proof-supported source formation seam.
It does not prove native solver correspondence, actual complete carrier-domain
formation, Call/effects, general recursive L4, soundness, required principality,
public export or F5 replacement. Next evidence for this local slice is focused
runtime depth/identity/recovery and return/drop verification; broader source and
inference consumers retain their original gates and owners.

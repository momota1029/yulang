# R269 — direct-root binding shapes and publication seam

The same embedded 40-source Y2 bundle used by R268 was reauthenticated against
its Git blob IDs before parsing (40/40 matched). A temporary focused Cargo probe
parsed each source after equal-length projection of line-leading `--` comments
to `//`, then counted only direct children of the file root. The probe was
removed after capture.

## Parsed source shape

The current Y3 CST reports 318 direct-root `BindingStatement`s: 313 have a
`BindingBody`, and five are signature-only. All 318 begin with `my` or `pub`
(110 and 208 respectively). For the single `Pattern` in each header, an
argument tail means a descendant `PatternCallTail` or
`PatternMlApplicationTail`. By that predicate, 258 bindings have argument
forms (253 with bodies, five signatures), and 60 are no-argument forms (all
with bodies). These counts differ from R260's source-line locator (307
assignment-shaped candidates: 247 argument, 59 no-argument, one `(mod)` form).
The 11-header / six-body-bearing discrepancy is unresolved; neither count is
promoted to Y2 parser evidence.

The root has 36 `OperatorHeader`s and 36 `OperatorChain`s. Every chain is the
immediate next direct root node after one header, so the 36 direct chains are
operator-definition bodies, not unowned expression roots under this CST
projection. Direct binding bodies consist of 184 `IndentedStatementBlock`s,
128 `OperatorChain`s, and one empty/recovered body. The latter needs source
inspection before classifying it as a successful initializer.

## Publication owner correspondence

The current Y3 lowering maps a direct root `OperatorChain` to
`RootPlanKind::DirectExpression`; direct `BindingStatement`s pass through
`plain_binding_header`, then `lower_plan` creates a `HirBinding`, wraps each
admitted parameter in `ResolvedExpr::Lambda`, and computes its
`EvaluationClass`. The playground's `runtime/program.rs` visits each
`HirItem`, records definitions, and adds a definition to `source_schedule`
only when its existing instruction walk classifies it as a computation;
direct expression roots are scheduled separately. This identifies the
current constructor/consumer seam but does not show that Y2 parsing, Y2
`ModuleMap` composition, imported names, or published runtime roots correspond
to these Y3 representations.

## Status and next premise

R269 is primary-only, unreviewed CST locator evidence. The comment projection
and the known Y2 external-`mod` recoveries still prevent treating Y3 parser
output as an authentic Y2 parse. R260's conditional no-imported-computation
conclusion remains unclosed because the parser census disagrees with its
lexical counts. The next discriminating work is to enumerate the exact
source/range rows behind those 11 extra CST headers and compare each to R260's
307-row locator, then determine whether the accepted Y2 runtime path has the
same binding/expression publication rule. R149 module identity, import
composition, accepted public types, specialization, Request reachability,
outputs, parent proofs, and production remain OPEN.

The focused command `cargo test -p yu-playground r269_root_binding_shapes --
--nocapture` passed (the temporary test was removed afterward). Existing
workspace warnings were emitted. No sample was executed and no compiler
semantics or retained tests changed.

## Proof-plan constraint

The proof companion distinguishes the completed typed-kernel safety theorem and
local implementation preservation results from whole-compiler safety. It fixes
four outstanding connections: source constraints to a declarative derivation;
solver transformations back to that derivation; every public scheme instance to
the same sharing anchor; and elaborated execution to machine steps, including
no `Unavailable` path in the typed domain. R269 establishes none of these by
itself. Its CST statistics cannot be promoted into Y2 semantics or closure of
R149. The next implementation evidence should follow one actual source
constructor through its stored occurrence/context, type/effect facts,
Value/Computation publication and execution consumer, as the companion's §7.2
requires. The companion also preserves the negative open-row case: a callback
with `[io]` in contravariant position may perform `state`, with that effect
remaining in the enclosing result.

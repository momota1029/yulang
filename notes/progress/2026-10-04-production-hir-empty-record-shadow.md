# Production HIR: empty-Record structural-shadow theorem

Date: 2026-10-04
Status: source-generation result; no implementation or semantic authority
Scope: the structural value shadow of complete current `yu-hir` bindings
Depends on: [source-generated structural theorem](../design/2026-10-04-source-generated-callback-structural-theorems.md), §5–7

## Statement

For every finite error-free `HirModule` produced by the current local
`lower_module` path, its monomorphic structural value shadow has a finite
descriptor graph over `Int` and `Function` only. In particular, its nonempty
Record alphabet is empty (`Λ = ∅`). The result remains true with recursive
references between local definitions. After finite rational equality
normalization, the package has no directed structural inequalities and no
rigid-name permission obligations; therefore it satisfies Theorem S's
closed-anchor/one-open-anchor predicate. If the generated equations are
satisfiable in the arbitrary-tree structural domain, they have a regular
witness. This is an application of Theorem S, not a new general regularity
argument.

The source property is independently checkable before solving: enumerate the
finite HIR nodes and verify that every node is one of the admitted cases below.
The proof does not inspect a solution, regularity, or a solver outcome.

## Source generator and proof

The current `ResolvedExpr` has exactly `Lambda`, `Integer`, `Name`, and
`Error`. For this theorem, exclude `Error` and require resolved names. The
current lowerer admits a binding body as one atomic integer/name; a
parameterized binding wraps that atom in one `Lambda`. Direct expressions
are also integer/name atoms. There are no source annotations or external
semantic roots in this lowering path (`SemanticImports` is empty and ignored
by `lower_module`).

Allocate one structural endpoint for each local definition, parameter, and
expression occurrence. Generate clauses as follows:

| HIR source | Structural shadow clause |
|---|---|
| integer | endpoint equals `Int` |
| parameter name | endpoint equals its parameter endpoint |
| resolved local name | endpoint equals the referenced definition endpoint |
| unparameterized binding | definition endpoint equals its body endpoint |
| parameterized binding | definition endpoint equals `Function(parameter, body)` |

The traversal is finite because it visits the finite HIR graph once and
allocates definition endpoints before resolving references. A recursive name
uses its already allocated endpoint; it does not unfold the target definition.
Thus every generated descriptor is either `Int` or a finite-arity
`Function` node. No case emits a Record, an inequality, or a rigid name.
The equality quotient may merge aliases and recursive endpoints, but cannot
introduce a new constructor label. Its free/free inequality graph is empty,
so each free component has no anchors and is a grounded G component in §6 of
Theorem S. With no rigid identifiers the rigid-scope premise is vacuous.

Theorem S therefore supplies the stated regular witness whenever the shadow
equations are satisfiable. The existence claim is conditional; this record
does not claim every HIR module is well typed. It also does not change the
original equations or infer that a particular chosen witness is principal.

## Boundary with production inference

This theorem concerns a deliberately named **structural value shadow**. It
does not erase or interpret the four Function ports in the current polarized
`yu-solver::TermView`, whose Function nodes include effect components. Pure
role and empty-effect handling remain governed by the source introduction
rules; this proof makes no effect-row, `never`/`Any`, or port-subtyping claim.
The shadow is not proved equivalent to the current F5 solver's generated
constraints, and is not the full successor inference generator. Applications,
Records, callback expected interfaces, annotations, imports, and open-world
clients remain outside current HIR or this theorem.

Relevant source locations: `crates/yu-hir/src/module.rs` (`ResolvedExpr`,
`lower_module`, `lower_body`, `lower_simple_chain`) and
`crates/yu-solver/src/term.rs` (`TermView` / `TermNode`). No compiler code or
tests changed.

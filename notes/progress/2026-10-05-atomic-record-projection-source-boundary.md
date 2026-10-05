# One-hidden-required-Record projection: source boundary

Status: independently reviewed source characterization; no implementation
authority.
Baseline: `f65d68c5d43623f0d8a02194142828ec144755ab`.
Method: committed-source correspondence and exhaustive downstream-algebra
inspection, independently of the conditional proof and executable model lanes.

## Claim and scope

The existing Yulang3 `yu-hir` semantic lowering / `yu-solver` pipeline does not
derive the supplied mathematical package for projection of one hidden variable
subject to required Record fields and rigid permission sets. Record and `forall`
CST support exists. The decisive boundary is the admitted semantic expression,
live-term, generalization and closed-type algebras below; syntax presence alone
does not establish typed solver support.

This is a characterization of that pipeline at the pinned baseline, not a claim
that every retained compiler path or fixture lacks Records. It establishes no
source-generation theorem, principal projection theorem or production adoption.

## Pinned correspondence

All locations below refer to the baseline commit. The eight production source
files listed here were byte-identical to their working-tree versions when
checked. Shared dirty task/theory/design records were not used as evidence.

| Layer | Exact locator | Observed boundary |
| --- | --- | --- |
| Record type CST | `crates/yu-syntax/src/type_expr/record.rs:34`, node construction at `:50` | `type_record_normalized` constructs `NamedRecordType`; it owns parsing and recovery, not type elaboration. |
| Quantifier CST | `crates/yu-syntax/src/type_expr/forall.rs:29`, node construction at `:45` | `type_forall_normalized` constructs `ForallType`; this parser is not a rigid-binder or permission elaborator. |
| Structural expression HIR | `crates/yu-hir/src/lib.rs:458`, `:658` | `structural_continuation` retains the receiver and tail children in `HirExpr::Value`; `is_fixed_postfix` includes `ProjectionRecordTail` at `:664`. |
| Semantic leaf admission | `crates/yu-hir/src/lib.rs:176`, `crates/yu-hir/src/module.rs:1402` | `direct_atom` accepts exactly one Integer/Identifier child; `lower_simple_chain` requires its associated expression to have no children. A retained structural Record projection does not become a supported semantic leaf. |
| Semantic expression algebra | `crates/yu-hir/src/module.rs:426` | Exhaustive `ResolvedExpr` variants are Lambda, Integer, Name and Error; no Record constructor, field projection or annotation/rigid elaboration variant exists here. |
| Collection | `crates/yu-solver/src/lib.rs:914`, `:1003`, `:1038` | Body-status matching and emission cover the admitted Integer/Name/Lambda cases. Complete Lambda recipes have Integer or resolved/parameter Name bodies; no Record/projection recipe is emitted. |
| Live term algebra | `crates/yu-solver/src/term.rs:170`, `:196`; leaves at `crates/yu-types/src/lib.rs:22` | Exhaustive `TermView`/`TermNode` variants are Leaf, Component, LiveVariable, positive Bottom, negative Top/Bottom and polarized Function. Exhaustive leaves are polarized Int and closed pure effect endpoints. There is no Record or rigid-atom variant. |
| Live endpoint/permission storage | `crates/yu-solver/src/lib.rs:704`, `:755`, `:9550`; `crates/yu-solver/src/term.rs:132` | Value endpoints are Bottom/Top/Int, ValueRow and polarized Function. Live views carry kind/polarity/ordinal; metadata carries origin/non-generic status. Fresh allocation records a level and that metadata, without a rigid permission set or explicit `A+` store. |
| Generalization algebra | `crates/yu-solver/src/f5c_generalization.rs:453`, `:480`; finalization at `crates/yu-solver/src/lib.rs:15217`, `:15267` | Exhaustive positive/negative drafts cover extrema, Int, variables, quantified/recursive/shared identities, Union/Intersection and Function. Finalization matches those cases. Quantified scheme identities do not provide a rigid-atom or permission-set representation for this fragment. |
| Closed observation algebra | `crates/yu-types/src/lib.rs:585`, `:599`, `:614`, `:618` | Positive/negative values cover extrema, Int, quantified/recursive identities, Function and Union/Intersection; effects are Bottom/Empty. Records and rigid permissions are absent from these exhaustive views. |
| Published compatibility observations | `crates/yu-solver/src/lib.rs:15419`, `:15693`, `:15708` | `finish` materializes occurrence compatibility observations; `projection_for` reads those observations; `root_value_for` returns Int/Never or Unknown, with Function/quantified/recursive/Union roots mapped to Unknown. These APIs do not implement existential hiding of a hidden Record variable. |

The observation APIs coexist with finalized closed schemes; the statement about
compatibility observations does not deny the existing Function scheme machinery.
The authoritative F5 scope is canonical one-parameter Function source/HIR,
live variables, polarized schemes and fresh instantiation
(`notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md:3–12`).
Its source completion requirement at `:28–34` does not authorize a Record or
rigid-permission extension.

## Existing fixtures and apparent contrary evidence

`crates/yu-hir/src/lib.rs:2328` contains
`associates_projection_tails_as_structural_continuations`, using
`f.(x).{y}.field::name` and checking retained projection-tail topology. This is
positive evidence for structural association, not semantic Record solving.
The internal fixture
`crates/yu-hir/tests/fixtures/simple_module_name_resolution.yu:1` contains only
`my x = 1; my y = x`.

Retained stable-core VM fixtures also exercise Record values, for example
`tests/contracts/stable-core/v0/run/vm/pass/record_field_named_like_str_method/main.yu`.
The separate negative fixture
`tests/contracts/stable-core/v0/check/fail/unsupported_record_type_annotation/main.yu`
has an explicit unsupported-record-annotation diagnostic contract. Those files
are not evidence that this pinned `ResolvedExpr`/collector path constructs the
hidden-variable package. No exact typed source package for the one-hidden
required-Record/rigid-permission fragment is available in the current internal
fixtures of the admitted path. No contrary representation was found in its
exhaustive downstream algebras.

## Authority boundary and next dependency

No extra language decision is needed to state or prove the conditional
mathematical lemma over its supplied structural and permission assumptions.
That lemma remains conditional research evidence. Production/source adoption
needs an approved Record/rigid-permission/projection gate specifying source
elaboration, required-field construction, rigid identities and lexical
permissions, retained public observations, and solution-preserving hiding.
The existing CST constructors and compatibility-query names do not select
those rules. Approval follows `rules/design-authority.md`; this note selects
none of them.

## Verification and omissions

Verification: baseline locator validation; comparison of the eight cited
production source files against current working source; whitespace check only
on this output. No tests, builds, measurements or Git mutations were performed.
Independent `regression_auditor` review found no substantive findings. It
checked the semantic admission boundary, downstream algebras, apparent CST/
stable-core Record evidence, and diagnostic fixture scope. The reviewer could
not itself compare every pinned source blob because of packed-object access;
the primary confirmed the eight cited production files, HIR test directory and
two cited fixtures have no differences from the baseline through the current
branch, and are clean in the worktree. Review did not run tests or prove a
source-generation theorem. Shared task/theory/index synchronization is
deferred to the primary; this artifact changes only its leased progress path.

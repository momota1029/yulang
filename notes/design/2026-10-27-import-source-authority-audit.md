# Import-to-Source authority audit

Status: reviewed bounded source-analysis checkpoint. No import semantics were
selected or changed. The original Yulang proof obligations remain open.

## Fixed instance

The audited fixture has provider `std::core::id`, explicit consumer exposure
`identity`, and an implicit prelude glob exposing the same provider. Its
provider declaration is `pub id x = x`. The existing Rust fixture confirms
that both names resolve to the same `SourceExportId`; it was inspected, not
executed in this audit.

The resolver establishes parse-owned source identity, declaration kind,
visibility, spelling, route, source key and range, then retains those facts in
`SourceExportId`. The ID contains no original `Name` or `Site`, installed
semantic certificate, or Source elaboration. `with_caller_evidence` associates
opaque evidence but does not interpret its payload.

## Binding authority

`OriginalSource.Binding` contains `name`, `owner`, `kind`, `component`,
`annotation`, `entry` and `singleUse`. Existing constructors determine these
fields from different source events:

| Field | Existing owner | Audit result |
| --- | --- | --- |
| `name` | Original lexical-name allocation; Alias changes only the copied Binding's name | Resolver exposure strings and common provider identity do not establish the original `Name` allocation or consumer lookup equations. |
| `owner` | Source introduction Site: binding, publication, pattern or formal registration | Provider key/range and HIR ordinal are not an original Site mapping. The importing construction must identify and authenticate the owning introduction. |
| `kind` | Recursive registration (`internal`), formal registration (`formal`), source publication (`published`); Name generation branches on `published`/`family` | Syntax `pub` means visibility. It is not a `Published(p, Σp)` receipt and does not select `.external`, `.published` or `.family`. |
| `component` | Recursive let registration supplies `some site`; ordinary records default to `none` | The ordinary fixture does not establish a recursive component. A `none` value is justified only after the corresponding ordinary Source-binding route is established. |
| `annotation` | Formal registration copies the source formal annotation; ordinary binding records default to `none` | The fixture has no written annotation, but the source annotation and final-target evidence remain owned by their formation/publication rules. The importer cannot invent an inferred annotation. |
| `entry` | Formal registration uses the formal's actual computation entry | An exported callable is not itself its formal. An imported callable's semantic entry belongs to the complete provider certificate; `some .value` cannot be inferred from “is a function.” |
| `singleUse` | Formal registration counts occurrences in that formal's body; ordinary records default to `false` | The provider formal's count follows its source body. Consumer uses of `id` do not determine a formal's `singleUse` flag. |

These are not seven arbitrary choices. If a faithful provider Source-binding
route is proved, `bindingRecords` itself supplies `.published` and the ordinary
defaults. The missing equation is the authenticated transport from the actual
provider source derivation and independently established semantic evidence to
the complete imported Binding and certificate, preserving lexical lookup.

The governing construction distinguishes:

* an installed immutable `Mono(h, Contract_h)` with all `Established` edges,
  whose aliases share the same complete certificate;
* a prior `Published(p, Σp)` and its source derivation, whose genuine
  instantiation retains its publication and instance event; and
* an independently typed `Family(d0, T0, R0)` with its original binder tree.

These routes are evidence-dependent. The concrete resolver ID does not classify
the provider as Mono, Published or Family. Rust's `use ... as identity` is an
exposure-name alias; it is not automatically SRC-J `Client.alias`, whose
premise is an already installed monomorphic handle. For a published or family
provider, separate lawful Name instantiations may remain separate; for an
already installed Mono, the alias must share its certificate.

## Ordered imports and complete Source

The CST/HIR inventory can authenticate every direct root, order, range and
whether each root is an import or declaration. `OriginalSource.Source` has no
raw `use` constructor. Its `moduleS` constructor accepts an already supplied
declaration and statement body; its generated rule adds a `sourceModuleLinking`
atom but does not consume Rust imports or construct an imported Context.

Therefore a complete root inventory does not yet yield a complete original
Source. A separate elaboration relation must account for explicit imports,
exposure aliases, public routes and implicit prelude installation, preserve
source order and scope, and exhibit the resulting Source, Context, root route,
ambient scope and linking premises. Replacing the imports with an empty Context,
dropping them, or wrapping an arbitrary body in `moduleS` does not establish
that relation.

## Scope and next evidence

This audit neither refutes the compiler nor adopts an import rule. The earlier
adapter's provider-artifact precondition failed before resolver joins executed;
that is an incomplete implementation attempt, not a semantic counterexample.
No Cargo, compiler, Lean/Lake, checker, tests or formatter ran here.

The next useful packet is a concrete import-elaboration construction that names
the provider's independently established derivation/certificate, its
installation and transport into the consumer, and the complete root-to-Source
correspondence. Review that construction before implementation. If the adopted
sources leave a genuine semantic choice, present its concrete alternatives and
consequences before asking for adoption. Preserve the original source domain,
Simple-sub A/B, soundness, effect hygiene, principality and termination claims.

Evidence: `tasks/agent-loop/inbox/import-source-authority-20261027-source.md`,
`tasks/agent-loop/inbox/import-source-authority-20261027-proof.md`, and the
independent review at
`tasks/agent-loop/inbox/import-source-authority-20261027-review.md`.

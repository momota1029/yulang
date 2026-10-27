# Import source authority: adopted rules and proof consumers

Sprint: `IMPORT-SOURCE-AUTHORITY-AUDIT-20261027/r1`.
Contract SHA-256: `747522aadee09038ded3897f83c0c939384590cf1a60de41fb6baab274f0b82f`.
Assignment: `/root/import_source_authority_proof`, handoff revision 1.
Outcome: source analysis identifying the remaining construction premises;
no theorem construction or certification.

Runtime identity is the collaboration task path above; session UUID is
unavailable. Actual start acknowledgement was sent to `/root` before reading.
Requested role: registered `lean_prover`; current runtime metadata reports
`gpt-6.1-sol`, effort UNKNOWN. No descendants.

## Authority, unchanged parent and pins

`notes/design/2026-10-08-source-generalize-definition.md` is Authoritative
only at its stated native source-definition scope. Section 2 selects
construction §§3–5 of
`notes/theory/2026-10-08-source-generalize-definition-and-proof.md`;
§3 retains local premises L1–L5 and §4 grants no production implementation.
The companion's §8, lines 955–980, explicitly retains resolver/evidence,
whole-source, principality and lifecycle obligations.

The original parent remains the universally quantified supported-source
claim at `2026-10-13-intrusion-source-preservation-proof.md:16–44`, with the
approved birth-level source-graph correction: source typing, principal
coverage, soundness, progress/termination, lexical/type/event scopes,
recursive sharing, generalization, complete Call and Effect hygiene. This
finite import audit does not narrow its source domain or shared witnesses.

Independently rehashed 68 governing, inherited, direct-artifact and handoff
entries; all matched. The two inherited manifest files themselves matched
their proof-handoff pins before use. Full receipt:
`/tmp/yulang-import-source-authority-20261027/proof/pins.json`, SHA-256
`993f2120a5e5577fec09018bede0d67d210af68d13738a0de9279bb168ae21a6`.
It includes the selected authority `46884ce3…d42a38`, companion
`e8ba4934…b2240`, and exact Syntax/Generation/Environment/Interpretation
modules. No Git command was run to authenticate baseline identity strings.

## What the adopted source rules already determine

Construction §3.1, line 138, requires Name to restrict the resolved binding's
existing joint certificate for the same actual value/provider. Section 3.3,
lines 219–268, makes classification an output of its owning source rule:

| Source construction | Required evidence and consequence |
| --- | --- |
| External immutable import/capture or monomorphic rebind, line 229 | `Mono(h,Contract_h)` and `Established` edges for the entire installed certificate, including free description, admission, future and dependent evidence fields. |
| Prior published polymorphic Name, line 230 | `Published(p,Sigma_p)` produced by a prior publication and its source derivation. A genuine source instantiation supplies `Instance(p,i,r)`. |
| Imported independently typed family, line 230 | `Family(d0,T0,R0)` with its independently typed declaration/derivation and original binder tree; bound parameters stay bound. |
| Alias/projection of a monomorphic value, line 231 | The same `h` and complete existing certificate, without another instantiation event. |

Section 3.4, lines 286–321, applies these distinctions to clients. A `new`
requires an independent source-definition/component derivation. For Family,
`d0` is an independent premise, not exporter success; a prior publication can
instead supply its independent derivation in source order. Alias and Name
retain the complete inference tuple. Section 5.1, lines 434–468, fixes the
whole free contract of Mono while retaining bound parameters of Published
and Family. Section 5.3, lines 617–624, explicitly prohibits classifying a
handle from provider identity.

These are adopted constraints on the required construction. They do not
supply the concrete provider derivation or module-linking construction for
the current Rust fixture.

## The actual Lean consumers expose the missing choice of construction

`YulangClosure.OriginalSource.sourceRules` at
`OriginalSourceGeneration.lean:95–110` looks up a complete `Binding`. For
`.published` or `.family` it adds an existential `.publishedInstance` binder
and an `exactWholeInstance` premise. Other kinds take the local Name path.
Thus changing the classification changes the generated rule tree before
checking; equal export IDs alone cannot justify either tree.

`OriginalSource.clientRules` at lines 420–438 realizes the finite-client
structure. `newUse` takes a raw `Definition` (Syntax lines 420–427), generates
its independent `sourceRules` under the retained source context, allocates
the instance and installs a `.local` handle. Alias copies the entire found
Binding, changing only its name, and requires `sameMonomorphicAlias` plus
`aliasPublication`. The syntax `use ... as ...` in Rust has not thereby been
identified with this monomorphic client Alias rule.

`OriginalSource.Environment.aliasPublication` at Generation lines 643–646
shares an already installed `PublicationId`. `Judgment.aliasPublication`
(784–787) requires the successful lookup and suffix proof.
`OriginalSourceEnvironment.alias_preserves_complete_publication`
(Environment lines 1343–1362) consequently preserves the whole publication
projection: identity, entry/completed actual states and captures. This is
useful transport once installation is established; it does not produce an
initial provider certificate from `SourceExportId`.

Publication installation itself has real premises: Generation lines 585–611
construct/check the initializer, Shared and Return/rebind prefixes;
`Judgment.publishGroup` (777–780) additionally requires the candidate and
stored record to agree. A declaration key supplies none of those premises.

`OriginalSource.Kernel.atom` remains the supplied local meaning
(Generation 670–685). `OriginalSource.SourceJudgment` (800–805) is indexed
by an already supplied Context and Source. Its finite reconstruction theorem
does not construct either input. The specialized `nameKernel`
(Interpretation 874–888) and `foldedNameKernel` (Environment 973–979) handle
the adopted ordinary value-formal case; their fallback preserves the
original kernel for published/imported-family cases. No concrete imported
certificate interpretation is obtained from those formal-Name consumers.

## Binding field audit

`OriginalSource.Binding` is Syntax lines 188–195; Context is its ordered list
and lookup selects the first matching name (198–205). Some fields have
defaults **after the owning construction is identified**. Those defaults
must not be confused with a proof that an import has that construction.

| Field | Existing constructor/consumer | Remaining fixture premise |
| --- | --- | --- |
| `name` | `bindNames` uses an explicit original Name; client Alias changes only this field. | Consistent source-name allocation and lexical lookup equations for `identity` and prelude `id`, joined to the provider identity. String equality or an export key is not the Nat allocation map. |
| `owner` | `bindingRecords` uses the actual source binding Site; Alias retains it. | SourceNodeKey/declaration-to-original-Site correspondence and the selected owning source rule. An ordinal alone does not establish it. |
| `kind` | Ordinary Source binding records are `.published`; recursive statement registration makes `.internal`; imported root Context may carry other kinds. Name generation branches on `.published/.family`. | Independently established Mono installation, prior publication, or typed Family derivation, followed by an import transport preserving that classification. |
| `component` | Defaults to `none`; recursive registration explicitly sets `some site` (Generation 329–334). Alias retains it. | The provider's genuine validating/recursive registration and its import correspondence. A proved ordinary nonrecursive Source.binding route would determine the lexical default. |
| `annotation` | Defaults to `none` in ordinary binding records. Formal construction instead copies `formal.annotation` (Generation 132–140). | Preserve the provider source annotation and actual final-root evidence at their owning rules. Syntax `bindingRecords` 225–226 ignores the binding's annotation; its default does not assert that the source has no annotation. |
| `entry` | Defaults to `none` for ordinary bindings; the formal constructor uses `some formal.entry`. | Identify the correct lexical Binding construction. This optional formal-entry metadata is not the imported callable's complete actual-role/entry certificate; that evidence still belongs to the provider derivation. |
| `singleUse` | Defaults to `false` for ordinary bindings; formal construction computes `body.nameCount formal.name == 1`. | Identify the owning construction; the two imported names/uses do not establish formal single-use metadata. |

In particular, constructing a complete ordinary Source.binding would already
determine its lexical `.published` record and defaults by Syntax 225–226;
the audit does not invent a need to choose each default independently. The
missing evidence is the source/reification/publication route that makes that
record the imported binding's original meaning, together with its semantic
certificate and all name/site correspondences.

## Concrete alias/prelude application and first remaining equation

The inspected fixture `module.rs:4817–4835` has provider `pub id x = x`, an
explicit import `use std::core::id as identity`, and a prelude glob. Its test
asserts that the two resolved names have the same exact provider identity.
The test was inspected, not executed. `source_exports.rs:1–4` explicitly
assigns no type-level meaning to these syntax/identity records.
`SemanticImports.with_caller_evidence` (module 903–924) associates an opaque
payload with a declaration while expressly leaving its meaning unchecked.

The first required equation is therefore an authenticated import transport:

```text
actual provider source derivation / publication or typed Family or Mono handle
  + exact consumer/provider lexical and declaration maps
  -> complete original imported Binding and installed certificate
     with each consumer Name selecting that same original construction
```

For the natural prior-publication route, one must reify/type the provider
definition in its actual Context, construct the prior publication in source
order, and transport its complete publication/certificate into the consumer.
For a Family route, supply `d0,T0,R0` independently. A Mono route requires an
actual previously instantiated/installed handle and shares its entire free
tuple. These are evidence-dependent routes, not interchangeable settings.
The name `id` and equality of its export IDs establish none of them. Treating
each imported use as independent or treating them as aliases of one Mono
changes description-frame sharing and can change lawful joint uses.

## Complete import roots remain a second equation

`OriginalSource.Source` (Syntax 79–148) has no raw `use` constructor.
`moduleS` takes an already supplied declaration and statement body.
Its generated rule (Generation 344–347) adds a `sourceModuleLinking` atom
and visits that existing body in the same input Context. It supplies no
rule translating complete ordered Rust import declarations into Context or
Source. In the inspected OriginalSource modules, `sourceModuleLinking` is
declared/generated and interpreted only through the supplied `Kernel.atom`.

The missing second construction must account for the complete ordered module
root, explicit imports, alias/glob/public routes and implicit prelude, while
preserving original scope, source occurrences and any actual initialization
order/effects. It must exhibit the resulting original Source tree and root
Context/route/ambient equations. A complete HIR/CST import inventory is a
necessary raw input but does not select this elaboration. Wrapping the body
in `moduleS`, discarding imports, or adding a new import constructor would
require its own justified construction; none was selected here.

## Parent application, resources and freeze

The accepted owner-table equations remain applicable universally over a
genuine incoming Context. This audit identifies why the current resolver
table cannot yet instantiate that Context: the first transport equation
above is unprovided; complete module-root elaboration follows separately.
The bounded source-owner trace, all runtime Frame premises and every original
parent gate remain OPEN. No semantic counterexample to the original language
is established by the prior adapter's failed artifact precondition.

The next useful evidence is a concrete reviewed import-elaboration candidate
that names the provider derivation/certificate, its installation/transport,
and complete root correspondence. Existing-rule implementation may suffice
if all those premises are independently supplied; this audit does not
establish that a new semantic choice is necessary. Any required new rule or
choice returns to the primary before adoption. Source annotations remain
optional under the accepted formation authority.

Only shell reads/searches and SHA-256 pin checks ran. Lean/Lake/checker,
Cargo, compiler builds, tests and formatter calls: **0**. Toolchain metadata
was read (`leanprover/lean4:v4.35.0`, no external packages); no executable
version or axiom result is claimed. No theorem types or axiom audits were
produced. The allocated source-analysis budget is 600 active seconds;
elapsed active time has no independent worker timer receipt.

Writes: this exact handoff and the assigned scratch `pins.json` only.
All writes stopped at submission; no verifier process, live shell session or
descendant remains. Independent review and primary adjudication are pending.

User-directive synchronization acknowledged: the nine UNKNOWN assignment
capacity reservations were already released idempotently. Their UNKNOWN
observations and quarantined paths remain; this exact leaf lease is unchanged.

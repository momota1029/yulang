# Value-owner introduction: source roots and the first native obstruction

Status: frozen bounded constructive derivation and constructor obstruction; unreviewed
Parent Value-reference / parent-copy SCC bridge: OPEN
Baseline supplied by primary: `afe402a7b`
Exclusive output lease: this file

## Statement, scope and authority

The parent statement retains its original quantifiers: every supported source
program `P`, every actual native inference history `h` for `P`, and every actual
retained Value extrusion pair `(c,p)`. Its required construction is an actual
owned-value interpretation `C_h(v)` on the relevant allocated Value identities,
with references jointly resolved to actual identities in that same history.
The selected intrusion test must qualify `(c,p)` by directed mutual
reachability in those references before the selected parent/copy equality.
Scopes, binders, distinct copies, shared captures and fresh-use independence
remain part of the claim. Complete Call, effects, soundness and required
principality remain independent required obligations.

Authority: the direct user decision in
`notes/design/2026-10-10-parent-copy-scc-intrusion.md`, **Value-reference SCC
clarification**, **Selected operation and compiler responsibility**, and
**Retained boundary**; the top-level inference principles §§1–5 and
**Evaluation**; and `rules/compiler-engineering.md`, **Natural compiler behavior
and proof-obligation economy** and **Deterministic Simple-sub inference**.
Vertices are actual Value variables. An edge means that the owning value
references another Value variable. Cross-level and uncle/nephew references are
allowed. Comparisons, bound orientation, lexical containment, parent metadata
and TypeDecl equality supply no reference edge by themselves.

This packet establishes the bounded original-root construction below and
locates the first native owner-transfer premise that those constructors do not
establish. It does not refute existence of every possible valid `C_h`, select a
new carrier, or establish the parent theorem. The bounded source discriminator
is not a restriction on the supported source domain:

```yulang
my f x = g;
my g y = f
```

Hypotheses for the bounded constructor result: successful lowering and
collection of this exact supported source; successful ordinary session
allocation; the same retained artifact and session throughout; original raw
rows before any subsequent justified equality. For the native prefix use the
ordinary candidate source schedule and its actual open recursive routing,
with successful finite admissions. No whole-program termination assumption,
checker transition assumption or type-consistency premise is used.

## 1. Actual original-root ownership is recoverable jointly

Let `d_f,d_g` be the constructed definition-order identities, `r_f,r_g` their
HIR roots, and `o_g,o_f` the Name occurrences in their Lambda bodies. Define
one map from the actual retained records:

```text
k(d) = batch.root_component_positions[batch.definitions[d.ordinal].root].component
beta(d) = session.live_components[k(d)].ordinal
Rf = beta(d_f), Rg = beta(d_g)
```

Collection registers a binding's own definition root before its body and
retains the root in its `CollectedDefinition` (`lib.rs:984–1092`,
`:1676–1696`, `:1897`). Session allocation assigns distinct dense Value rows
to distinct Value components (`:10047–10069`). Thus `Rf` and `Rg` are actual
distinct Value variables, not binders substituted for variables.

HIR forms the module namespace before lowering the owned binding bodies
(`module.rs:943`, `:1322`, `:1389`, `:1472`). LocalSource forms each Lambda with
its retained body index (`module/local_source.rs:286–325`) and resolves a Name
from the latest lexical binding, then the unique module definition
(`:636–656`). Here neither `x` nor `y` intercepts the other module name.
The actual owned source constructions, expressed as proof notation rather
than a new representation, are consequently

```text
C_source(Rf) = Lambda(x, Name(o_g, resolved-target Rg))
C_source(Rg) = Lambda(y, Name(o_f, resolved-target Rf)).
```

The endpoints are supplied jointly, not selected independently: the Name
arm appends the containing definition, resolved target and exact occurrence
(`candidate_source.rs:375–378`), and the endpoint pass freezes `parent`,
`target`, `occurrence`, `target_root_component` and `use_value_component`
from that same batch (`lib.rs:1275–1327`). Composing the parent root through
`k` and the target through its retained root component supplies

| Occurrence | Actual source owner | Actual resolved target |
| --- | --- | --- |
| `o_g` | `Rf` | `Rg` |
| `o_f` | `Rg` | `Rf` |

Since a reference in the owned Lambda body is a reference in its owning
binding value, `Rf -> Rg` and `Rg -> Rf` follow directly from these
constructions and the user-selected reference meaning. This is the already
independently reviewed original-root implication in
`notes/theory/2026-10-11-mutual-recursive-value-scc-proof.md`; this packet applies
it rather than reproving its broader exclusions. It supplies a real
nontrivial source-root SCC. It supplies no extrusion pair.

`C_source` is deliberately distinguished from the requested whole-history
`C_h`: it covers these original root owners, not every occurrence row,
parameter row, Apply result, fresh use or extrusion-created row. An abstract
owned-source construction may be recovered from retained HIR and maps; a
literal second AST field in the solver is not a necessary premise. The gap
below is the semantic correspondence of additional native Value owners,
not merely absence of an AST field.

## 2. Constructor crosswalk and separate initializer boundaries

The source constructors retain enough information to locate the relevant
source references. Their native endpoints are nevertheless different objects.

| Constructor | Retained source fact | Actual native introduction |
| --- | --- | --- |
| Module Name | resolved `DefId`, occurrence, containing module definition; final `DefinitionUse` retains both root and use components | allocates a distinct occurrence component; open recursive routing compares target-root row with use row |
| Parameter Name | resolved `HirParameterId` in the lexical environment | endpoint is the formal parameter recipe position, later the live formal row, instead of its allocated occurrence component |
| Local Name during a forming function initializer | resolved `HirLocalId`; active-initializer map selects that initializer endpoint | `Action::Link` compares initializer endpoint with the Name component |
| Published local Name | resolved local identity selects an installed `LocalScheme` | captures the scheme graph, prepares a joint fresh map, restores bounds and links the fresh root to the Name component |
| Lambda | exact parameter and body expression index | `LambdaRecipe` retains parameter position, root component, body endpoint and effects; native introduction constructs a four-port positive Function |
| Apply | exact callee/argument expression indices | recipe and Call input retain callee, argument, result and effect endpoints; native introduction builds a negative Function demand and compares the callee with it |
| Block | separate initializer indices and final expression | visits each initializer separately, installs its endpoint, then treats the final expression as the block result |

Owning locators: `module/local_source.rs:99–173`, `:332–371`, `:795–833`;
`candidate_source.rs:187–217`, `:253–336`, `:375–410`, `:441–460`;
`candidate_scheme.rs:1316–1336`, `:1354–1393`;
`lib.rs:719–727`, `:11233–11343`; `shadow_apply.rs:1304–1399`.

Two boundaries matter to the attempted construction.

First, the lexical `scope` field is not itself an owner edge. Lambda bodies
can carry `LocalSourceScope::Parameter`, and initializer Lambda bodies can
carry a parameter scope even though the initializer is owned by its local
binding. Owner recovery must follow the actual Lambda/body and initializer
links. The Block retains each `LocalSourceBinding.initializer` separately;
the enclosing block's owned reference walk follows its final expression and
does not absorb those initializer bodies. HIR separately schedules
`Work::Initializer` and the final expression; solver source scheduling
separately uses `Work::Initializer` / `Work::Install`. The local initializer
therefore supplies its own potential source owner. Install selects its actual
Value endpoint and retains `(local id, root row, boundary)`. Containment of
that initializer gives no outgoing reference from the enclosing value.

Second, reference targets and native computation endpoints cannot be exchanged
without proof. A parameter Name's native endpoint aliases its formal row
(`candidate_source.rs:211–217`); assigning the Name syntax to that endpoint
would not by itself establish that the formal's owned value is a self
reference. A published local use creates or shares actual rows using one
fresh map (`candidate_scheme.rs:973–1037`); the source local identity alone
does not choose which fresh row owns a copied construction. The retained map
is real, but its current graph nodes are rows, leaves, effect operands and
four-field Functions (`candidate_scheme.rs:36–79`). Its bounds are captured
typing evidence. No source-reference transport claim follows merely from
the fact that the map jointly transports those graph nodes.

For Apply, both source operands are retained, so the source-reference walk
can inspect both; a Lambda walk follows its actual body. The native negative
Function has argument and result Value fields, with argument and invocation
effect fields, and is a typing demand on the callee. Its stored Value ports
are not a proof that the Apply result's owned value references those fields.
The complete four-port Call is preserved in this crosswalk; no effect-erased
typing or complete Call theorem is claimed.

## 3. The earliest native owner-transfer obstruction is the recursive Name

Use `Ng` for the actual Name component of `o_g`, `Nf` for that of `o_f`,
`Lf,Lg` for the Lambda expression components, and `X,Y` for the formal rows.
All are distinct original Value rows at level 1, except that formal Name
endpoints would alias their formal rows if they occurred. These parameters
do not occur in the selected bodies.

The actual first owner-transfer seam for `g` is:

```text
retained resolved occurrence: (owner Rf, target Rg, occurrence o_g)
Name computation endpoint:   Ng
open-use admission:         Rg <: Ng
Lambda result endpoint:     Ng
Lambda native introduction: Function+(X, entry_f, return_f, Ng) <: Lf
definition-root link:       Lf <: Rf.
```

The module Name arm constructs the separate occurrence endpoint, not a native
`Ref(Rg)` owned-value constructor. `route_internal_inner`
(`lib.rs:15765–15784`) admits exactly the retained target/use comparison.
`admit_lambda_fact` reads `body_value_endpoint` (`:11233–11258`) and constructs
exactly the Function with result `Ng` (`:11342`). The reciprocal construction
uses `Nf`. The precise unsupplied constructor premise is

```text
This resolved Name introduction and its Lambda consumption supply the
actual owned construction on their native Value identities, jointly with
the references required by the retained source owner Rf / target Rg.
```

This is a premise at these exact introductions, not an assumption of this
derivation. It cannot be replaced by `Rg <: Ng`, `Ng`'s eventual inferred
Function bounds, or equality of their eventual exported type declarations.
Nor does the established `C_source(Rf)` prove it: that construction follows
the retained resolved Name directly to `Rg`, whereas the native Function
reads the distinct result row `Ng`. For example, factoring the source edge
through `Ng` would require an authentic ownership claim such as `Ng` owning
`Ref(Rg)`; no inspected constructor establishes it. Such a factorization is
not required or adopted here. An eventual interpretation may recover the
root reference directly, but must still establish its correspondence with
the native graph and later copies. This packet establishes neither route.

The obstruction is observed before freshening or extrusion. Default Value
allocation creates bounds, levels and origin metadata (`lib.rs:10047–10069`,
`:10156–10179`). Thus no later source-body interpretation is supplied by
allocation itself. The earliest native owner requiring a new correspondence
in the selected source is the module Name row used by the Lambda, rather
than a later parent/copy pair or generalization boundary.

## 4. Discriminator: source SCC, payload SCC and actual pair qualification

The independently reviewed operational audit
`notes/progress/2026-10-11-mutual-recursion-value-scc-source-audit.md` derives
the actual finite admissions and replay for this same source. Its projected
Value payload incidences give a native SCC `{Ng,Nf}`, while `Rf` and `Rg`
are not mutually reachable. The inspected constructors retain that mismatch:
equal-level `Rg <: Ng` stores `Ng` on `Rg`'s upper side
(`candidate_extrusion.rs:815–830`), and the Lambda Function result is `Ng`.
The scanner follows both stored bound sides and their structural payloads
(`candidate_intrusion.rs:358–422`); it does not read the resolved Name map.

Consequently the proposed direct, same-identity equation of the source-root
SCC with this scanner's payload SCC fails on these actual original root
identities, under the audit's stated successful native prefix. This is a
bounded constructor discrimination, not a new payload probe and not a
refutation of every possible graph interpretation.

The rows here all have level 1; this source creates no retained extrusion
pair. The copied-row branch requires an original level above the target
(`candidate_extrusion.rs:83–124`). Hence neither the source SCC nor this
payload mismatch proves or refutes the original all-retained-pairs intrusion
theorem. The actual recursive fixture in
`notes/progress/2026-10-11-source-qualified-value-parent-copy-scc.md` does
create a pair `(C,P)`, but its demonstrated `P`-to-`C` stored payload and
later cycles do not supply this missing semantic owner constructor. No
equivalent copy/SCC probe was repeated.

## 5. Proof-obligation economy and next owner

Two materially different existing methods now meet the same source supplier:
the constructive original-root map supplies authentic resolved references;
the operational replay trace supplies authentic native payloads. Their
discriminator exposes the exact Name/Lambda identity seam. Another abstract
SCC lemma or copied-payload experiment would leave it untouched.

The parent bridge remains an A/B correctness and natural-inference obligation
for the approved operation. Recovering already known resolved owner/target
information later from comparisons would incur D reconstruction debt; that
classification does not downgrade the parent theorem. HIR already knows the
source reference and its initializer/body ownership. Collection already
knows the target root and distinct occurrence endpoint. The owning native
introduction is `candidate_source::emit_candidate_source` together with
`route_internal_inner` and `admit_lambda_fact`; the consuming responsibility is
`settle_candidate_intrusion`. No carrier or semantic repair is adopted here.

One next action for the primary's source-construction/design owner: resolve
this exact original recursive Name introduction. Supply a justified
interpretation on `Rf,Rg,Ng,Nf,Lf,Lg` and the native Function introductions,
showing how their actual owned references recover `Rf -> Rg -> Rf`, or give
the concrete construction-level contradiction. Specify how that same owner
interpretation reaches the scanner. Only after that premise is established
should a copy/fresh-use transport proof apply the actual joint row maps.
No restriction of the parent source domain or removal of cross-level routes
is an admissible shortcut.

## Checks, dependencies and commit packet

Method: one bounded static source-constructor pass, application of the existing
reviewed root theorem and operational discriminator, and a constructional
economy audit. Read commands were bounded `rg`, `sed`, and `sha256sum`; the
single leased output was written with `apply_patch`. No Git command, compiler
edit, build, test, Oracle, instrumentation, executable probe or delegation ran
in this packet. A hash request initially used the wrong reference Scala path;
`rg --files` located the ordinary persistent baseline and its corrected hash
succeeded. Its `Typer.scala:62–72` Name/Lambda/Apply and `:223–230` Variable
constructors remain the ordinary Simple-sub baseline, not a source-Value
ownership theorem for Yulang's extensions.

At most three lightweight read subprocesses were concurrent. No measurement
budget was consumed; CPU/RAM and reasoning wall time were not measured.
Requested routing: one bounded Sol/high pass. Observed model/effort: unknown;
role/config prose is not runtime evidence. No Astra escalation. Fresh
independent review is required; the producer does not certify this note.

The primary supplied `afe402a7b`; no Git operation was used to re-read it.
These SHA-256 values pin the inspected live dependencies. Their solver and HIR
hashes match the supplied earlier frozen constructor snapshots. This leaf made
no dependency edits; baseline-content comparison and integration remain
primary-owned.

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/theory/2026-10-11-value-reference-scc-source-bridge.md` | `1bc8b29b7b1f3995bf3adedf604fe15db80be8e4bc8f1d0771644a449d086aef` |
| `notes/theory/2026-10-11-mutual-recursive-value-scc-proof.md` | `332f757481af278e533f0e5d7eda2b3aa004e75d54f1d3e48c77b8f76d5a786d` |
| `notes/progress/2026-10-11-mutual-recursion-value-scc-source-audit.md` | `04be51c44e2ead3805ffee59a4a9587eff64fe4952e3b5b74d29f6caf1bd55cc` |
| `notes/progress/2026-10-11-source-qualified-value-parent-copy-scc.md` | `88ce1aa652f8d289955b3088e683f1e8d6a8c5c3d4d49258d8f9c390ed9f3dbf` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-hir/src/module.rs` | `943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/shadow_apply.rs` | `230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `rules/compiler-engineering.md` | `4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9` |
| `/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| `/home/momota1029/rust/simple-sub-reference-paper.pdf` | `5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698` |

Commit packet: exact changed path
`notes/theory/2026-10-11-value-owner-introduction-proof.md`; supplied baseline
`afe402a7b`; changed dependency hashes: none caused by this leaf; independent
review: pending; checks: static reads, dependency hashes, output inspection;
proposed one-line checkpoint message:
`research: freeze Value-owner introduction and recursive Name obstruction`.
Proposed shared-record delta, left to the primary/curator: original parent
bridge OPEN; original-root owner mapping available; first native Name/Lambda
owner-transfer premise unresolved, with the source-construction/design owner
responsible. Earlier rejection-proof artifact remains frozen and unchanged.

# Original MemberEntry fields and the scoped eligibility boundary

Date: 2026-10-27. Producer: `/root/principality`, bounded `lean_prover` leaf.
Status: **checked source-owned MemberEntry constructor; complete dependency
schemas and eligibility remain OPEN**. Independent review is parent-owned
and pending. The selected SG operation is already defined. This packet
constructs its member-field owner at the original recursive-pair installation
and identifies the remaining input to the faithful fixed-closure walk.
It does not reopen the definition or refute principality.

## 1. Constructed MemberEntry and exact remaining frontier

The authoritative [Source-Generalize selection](../design/2026-10-08-source-generalize-definition.md)
adopts [SG §§3.3 and 5.1–5.2](2026-10-08-source-generalize-definition-and-proof.md).
Its eligibility test is exact: retain the whole source component and its
actual final root, perform the specified typed `retain`/`fix` walk, and select
precisely the retained ordinary `Desc(C,q,sort,sigma,Delta)` declarations
which the fix walk did not mark. The source already specifies that
`Internal(C,r)` retains the joint relation even when the raw provider was
reached through a fixed field. Established and executed dependent contracts
can still fix individual free Desc fields. Shared and event telescopes keep
their original ownership.

The new, independently reviewed
[OriginalScopedClosure](lean/YulangClosure/OriginalScopedClosure.lean)
supplies source-derived rule structure, declaration occurrence addresses,
the original binder tree and the actual publication endpoint. Its
`erase_allocate` theorem preserves every existing `RuleTree` constructor;
`source_residual` identifies the residual with the existing `Build`.
Neither theorem invents semantic fields that the erased source rule syntax
does not contain.

[OriginalMemberEntryFields.lean](lean/YulangClosure/OriginalMemberEntryFields.lean)
now constructs the SG `MemberEntry` split **at the existing actual
`WorldRegistry.pairRegistration`**. Its input type is:

```lean
register (position : Position) (outside : Context) (pair : SourcePair)
    (before : WorldRegistry s) (assignment : PairAssignment s)
    (guards : WorldGuards) (providers : Side → s.Provider)
    (parent : Nat → Option (CaptureData before.bindings before.count)) :
  Registration s
```

These are the original source and registration data. `CaptureData` contains
raw address/range/object readbacks, not semantic validity. `guards` is the
original guard data, with no new `guards.Valid` premise. `register` produces:

| Constructed field | Actual data and ownership |
| --- | --- |
| One `Component` | Original incoming `Position`, full outside `Context`, raw `SourcePair`, and `allocate position (sourceRules outside pair.statement)`. |
| `Operational.address : Nat` | The actual world binding address `before.count + side.offset`; it is not identified with a provider-store index. |
| `Operational.provider : s.Provider` | Exactly `providers side`, the provider argument used by the original world registration. |
| `Operational.value : s.Value` and `root : s.Root` | Exactly the original selected member's value and root. |
| `Internal s component` | The same source member `Side` and selected `s.Descriptor`, indexed by the one retained Component. Its program is that Component's whole program. |
| `Registration.world` | Exactly `before.pairRegistration assignment guards pair providers parent`. Every other original registry field remains in this same result. |

The constructor does not inspect a descriptor to decide its provenance.
Both member entries are emitted at this simultaneous owning rule. Other
installed objects are not relabeled by raw provider equality.

`registered_installed` proves that combining the Internal descriptor with
the Operational value/root gives **exactly `assignment.object side`**.
`registered_binding` proves the stronger actual consumer equation:

```lean
let built := register position outside pair before assignment guards providers parent
built.world.bindings (built.entries side).operational.address =
  some (built.entries side).installed
```

`registered_one_component` and `registered_whole_residual` show that both
Internal references retain the same complete `Build outside pair.statement`.
`component_source_reconstruction` applies that residual directly to the
existing independent source judgment, with its original arbitrary local
Kernel unchanged. It assumes no source derivation or complete semantic
certificate. `registered_whole_publications` retains the actual original
publication inventory, including its final-root incidences; this constructor
does not choose an older member root or invent a memberwise program.

`registered_provider_captures` gives each actual member provider the complete
original `pairEnvironment`. For other providers, `registered_old_capture_fields`
preserves both address and entire installed object under the original
provider-disequality premises. Prior bindings are preserved under the
original two fresh-address premises. `registered_shared_witnesses` preserves
the same witness-reference and witness-value maps. There is no new Shared
witness per member. Changing only the selected descriptions leaves all four
Operational fields unchanged; no equality of the changed whole semantic
world is asserted.

These are construction and readback equalities for the existing original
Lean registry. The supplied `PairAssignment` need not already satisfy the
source clauses: the new constructor does not prove that its selected opaque
member descriptors are valid source interfaces, that the world is meaningful,
or that a native heap/Rust execution has these readouts. The complete source
clauses remain active in the shared Program, and their original interpretation
and eventual satisfaction are separate obligations. This distinction also
applies to `component_source_reconstruction`, whose local Kernel has not been
replaced with a source-safety predicate.

**The missing datum is the declaration-time typed incidence of every free
semantic field, including its owning provenance and binding telescope.**
The current APIs, including this new partial owner, contain semantic values,
field-class payload constructors and source incidence IDs, but no
source-produced complete field schema on which the original fix walk can run.
An arbitrary adjacency list or a
function assigning dependencies to each Program node would supply this
missing owner as a new caller input. It would not derive the owner from the
original source construction.

The packet was renamed from the initial eligibility lease to
`OriginalMemberEntryFields` before the construction was frozen. No
`OriginalScopedEligibility.lean` placeholder was created. This packet does
not fix every Desc, identify lexical predecessors with free
semantic dependencies, assume an `eligible_preserves` law, or turn an opaque
primitive predicate into an enumerable field schema.

## 2. Existing owners and the absent fields

The following are actual current declarations, inspected in source; a
focused pinned-Lean inspection also records the central type interfaces.
This is a limitation of their current
representation; it is not a claim that the original semantic objects have
no dependencies.

| Original owner | Available current representation | Required missing information |
| --- | --- | --- |
| `Desc(C,q,sort,sigma,Delta)` | `OriginalSource.Binder` stores `site : Nat`, `kind : BinderKind`, `arity : Nat`. `OriginalScopedClosure.Occurrence` adds the original declaration, route, scope tree and incoming frame. The formal owner separately supplies value/computation entry. | A complete constructor-owned declaration schema, including its sort and actual free dependency telescope. A generic `.description` occurrence is not that schema. |
| Parameter introduction | `OriginalParameterWorld.FormalAssignment` has type `(parameter : Parameter) → Route → ScopeValues s View parameter.typeScope → Contract s parameter.formal.entry`. `Telescope` preserves all typed predecessor payloads. | The symbolic field incidence of the selected contract. An arbitrary function on the entire prior telescope does not expose which predecessor fields occur freely, or the dependent fields within its opaque descriptor/interface result. |
| Written annotation/hole introduction | `Annotation` is `Nat`; `Mark`, `Formal`, `Atom.annotation` and `Atom.annotations` retain those authentic IDs. `sourceRules` emits the real annotation boundary. | The referenced annotation declaration's typed syntax and owned hole declarations, scopes, guards and dependencies. The existing generic source builder does not enumerate those declarations from an annotation ID. |
| `MemberEntry`, `Live`, `Internal` | `Binding.kind = internal` and `Binding.component = some group` are computed at recursive registration. The new `register` emits a separate Operational object and Internal descriptor edge to the one complete source Program, with exact Installed reassembly and actual world readback proved. | Complete dependency schemas within the retained world, contract and evidence fields. The new field split does not interpret every opaque field or classify other installations as Established. |
| External `Mono` / `Established` | `Installed.value` carries `(descriptor, value, root)`; `Installed.carrier` carries `(interface, carrier, root)`. `Root.installed` and `WorldRegistry.bindings` map addresses to these objects. | The entire installed contract's declaration schema: free descriptive, admission, latent/future, provider and evidence fields, with their typed dependencies. The semantic descriptor/interface is an opaque value of the selected `Sorts`. |
| Actual `Executed` / `OneShot` | `Runtime.oneShot` carries `Outcome`: observation, optional value/carrier result, actual following history/configuration, endpoint objects and name/address bindings. | Declaration provenance and dependency telescopes for the selected executed arm's installed contract/evidence fields. These cannot be recovered from returned endpoint shape or raw identity. |
| `Shared` | `Shared` retains `bindings : List (Name × Nat)`, `installed : List (Nat × Installed s)` and `witness : s.WitnessValue`. Publication restoration retains the actual shared/replay frames. | The dependent contract of each installed field and witness, including free versus bound references at that **original** scope. Preserving one binder does not compute its semantic fixed closure. |
| `Event`, `EventField`, `EventProof`, `ViewLogic` | Runtime payload constructors distinguish invocation, receipt, Return/rebind, response, rigid opening and one-shot outcome. Logical payloads retain descriptors, interfaces, view meaning, assignment and joint witness. Actual event paths and proof-frame incidence already have distinct owners. | Field-level dependency telescopes for those complete payloads and their original local relations, with event-bound fields kept under their events. `RuntimeReadout` exposes arbitrary functions for assignment, witness, scope, authority, incidence and dictionary; their function arguments are not a declared free-variable inventory. |
| Authentic primitive / independently typed Family | `SourceSignatureConstruction.Catalogue` has `Port : Type`, `Packet : Joint → Port → Type`, `scope : List Binder`, `sharedSlot : Port → Nat`. `Introduction` retains an independent dependent license fiber. | Explicit typed field declarations inside the packet, their provenance, free anchors versus family-bound parameters, and original dependency incidences. A dependent semantic `Packet` type preserves the whole fiber but does not itself enumerate its syntax or free-field edges. |
| Local checking and permitted specialization | `Kernel.atom`, `primitiveCheck`, structural/function shape and conversion fields are independent local predicates. `Premise.checking` retains the actual goal endpoints. | The owning rule's actual operand/declaration telescope. No operation extracts it from a predicate, a successful check or a same-value semantic proof. |

`OriginalSourceInterpretation.Sorts.Dependencies` does not repair this gap:
it is an opaque `Type`, carried as `Fiber.D`. No declaration in the inspected
owner chain reads it as the SG publication-indexed field inventory. Likewise,
`Atom.operands : List Site` records source operands, not which semantic fields
of those operands are free, established, internal or locally bound.

The existing formal producer is useful and remains intact.
`OriginalFormalAdmission.Introduction.description` computes the selected
descriptor/interface payload from the authentic formal coordinate and typed
prior telescope. `ViewPacket` cannot overwrite that description. These
properties establish payload construction and scope separation; they do not
give the contract a finite symbolic dependency presentation. Reusing them
must preserve this distinction.

## 3. Why the allowed primitive-catalogue input is insufficient by itself

SG §2 L1 explicitly permits an authentic primitive's independently fixed
typed relation, full operand telescope, guard, effects, provider/future and
admission fields. SG §3.3 explicitly requires opaque primitive fields to have
the same external/shared/event classification. Such **declaration data** is
a legitimate input; its semantic local laws retain their separate owners.

That permission does not supply a per-Program replacement for source-owned
Parameter, recursive registration, publication, initializer, Return/rebind
or annotation formation. Those constructors must emit their own records.
It also does not authorize accepting arbitrary proposed edges together with
an assertion that they form the complete fixed closure. The dependency walk
must consume the real local fields, and its exactness must follow from the
constructor representation.

The distinction between an installed monomorphic contract and a bound family
cannot be reconstructed from a solved descriptor. Nor can a reference to an
own member's inferred interface be classified by raw provider equality: SG
§5.1 explicitly requires typed provenance and forbids relabeling an external
capture when traversal returns to a familiar provider. Adding a generic
reachability algorithm before these owners exist would leave precisely this
missing premise untouched.

## 4. Applications checked at the actual source owners

### Two annotations and the real publication

The existing `OriginalSourceRecordBoundary.Witness.original` is the actual
binding at site 20/name 30, with initializer record site 10, initializer
annotation 100 and outer binding annotation 101. Its original declaration
readout constructs both adapters. The already checked
`OriginalScopedClosure.actual_annotated_publication` yields exactly
`(30, 20, (20, writtenTarget), some 101, [10])`.

An eligibility operation for this publication must keep that outer target,
the earlier adapter and the actual initializer/Return/Shared fields. The
specialized record adapter's `Declarations.annotation : Annotation →
Option (Ty Atom depth)` supplies its record types and conversions. It does
not produce a complete original SG dependent contract, primitive catalogue,
or `Shared.installed`/witness field schema at this publication.

The generated rule syntax contains no explicit formal Desc introduction in
this fixture. Proving that this one syntactic list is empty would not prove
that the complete semantic field inventory has been reconstructed. No
“eligible = []” result is advertised as an application of SG eligibility.

### The original recursive pair

`OriginalRecursivePair.SourcePair.statement` constructs the genuine
recursive `let` from its two Lambda/formal/Name members. The generic source
builder puts their binding records in one component and emits the ordinary
formal Desc binders before their invocation challenges. The original
hygienic pair's peer Name uses are internal, so the source routing required
by SG §5.3 is available. The new constructor does not certify arbitrary raw
SourcePair names as hygienic.

`WorldRegistry.pairRegistration` constructs both installed raw member
objects and captures the full actual lexical environment. The new
`OriginalMemberEntryFields.register` now applies directly to that constructor
and computes the MemberEntry/Internal split from those same inputs. It
reassembles the exact existing `Installed.value` and proves the binding
readback, complete shared component residual and capture preservation.

The descriptor remains opaque: the new owner does not yet provide the
declaration-time dependencies within the retained world/evidence fields.

Fixing both installed member descriptors would contradict the selected
bare-pair eligibility result for `A_x,A_y`. Treating every descriptor reached
through the same raw members as Internal would miss a genuine established
dependency. The source already tells us which result is required. The new
owning constructor supplies the member-field distinction; the remaining
complete field schemas are needed before the walk can prove the required
eligibility result. No new semantic decision or convenient preorder is needed.

## 5. Exact next constructive owner

The next construction belongs **at source registration and typed declaration
formation, before the fix walk**:

1. Reuse the existing source origin, route, original scope and publication
   incidence. Add the complete typed declaration/operand schema emitted by
   each owning source constructor. Parameter data must retain its selected
   value/computation sort and pre-invocation telescope; annotation formation
   must expose its actual declared holes. This extends the representation;
   it does not change the original source or accepted semantics.
2. Extend the MemberEntry owner constructed here with the complete declared
   world/contract dependency fields, preserving its operational/Internal
   distinction and the whole registered relation. At external installation,
   construct the Established complete contract. At actual execution/installation, retain
   the OneShot fields and their declared evidence dependencies. Use the
   existing constructors and installation identities, not endpoint inspection.
3. Retain a typed term/telescope representation sufficient to read each
   field's actual free references and bound family/event variables. Genuine
   primitive declarations may supply their independently typed catalogue.
   Built-in source constructors must compute their own field records from
   their original rule inputs. No whole-program dependency-correctness law
   should become a caller premise.
4. Prove erasure and exact field coverage against the actual constructor
   outputs, including `Installed`, logical payloads, Shared evidence and all
   runtime/readout fields. Event fields stay at their event scope; ViewLogic
   and EventProof keep their description ownership. A field containing a
   contract must expose that contract's full dependency telescope.
5. Only then implement the already selected finite two-mode walk. Prove both
   closure and exactness of its fix marks; prove eligible iff retained
   ordinary own-component Desc and not fixed. Preserve the whole residual
   and actual exported endpoint. Apply it to the pair and the two-annotation
   publication without assuming their dependency result.

A record whose only new information is a caller-supplied `Delta` for every
Program node would not complete steps 1–4. Conversely, these steps do not
require changing the selected SG definition. They require faithfully
formalizing the remaining complete field-declaration schemas, which are
absent from the current source/payload representation. Endpoint graft action, original
instance interpretation, global all-valid-view `E_V` and
`SourceProblem.PrincipalCoverage` remain later independent obligations.

## 6. Verification, budget and frozen receipt

The new source has 241 lines and 16 authored theorems. It is frozen at SHA-256
`9c4833e323a649bc46bc5c18caa77115de86ddba2660a021a52f4aaf2ba57b9f`.
No original proof or runtime code was edited. A focused pinned-Lean
inspection of the actual imported declarations exited 0 with no warnings,
errors or elisions:

```text
timeout 120 env LEAN_NUM_THREADS=1 <pinned-lake> env lean -j1 -M1024
  --root=/tmp/yulang-scoped-eligibility
  /tmp/yulang-scoped-eligibility/InspectOwners.lean
```

The pinned toolchain is Lean 4.35.0. This initial script performs
`#print`/`#check` inspection only. The new module was then directly checked
with the same 120-second/1-GiB bound and no `.olean` output:

| Log in `/tmp/yulang-scoped-eligibility/` | Result |
| --- | --- |
| `inspect-01.log` | Declaration inspection, exit 0; no diagnostics or elisions. |
| `check-02.log` | First complete proof check, exit 0; two constructor-name linter warnings, repaired by renaming local Side variables. |
| `check-03.log` | Exit 1 after adding capture-field preservation: simplification left two definitional Option-map equalities. |
| `check-04.log` | Exit 0, no diagnostics; both remaining equalities discharged by kernel reduction. |

Every earlier log is retained. The parent built the exact frozen source:
19 jobs, exit 0, no diagnostics, receipt
`/tmp/yulang-member-entry-fields-build.log`. The subsequent full
originating-module type/transitive-axiom audit exits 0 at the authorized
audit-only `-M2048` limit, still without `.olean` output. It covers **all 123
originating declarations**: 68 definitions, five inductives, five
constructors, five recursors and 40 theorem constants. Of those theorem
constants, **16 are authored and 24 generated**. There are no warnings,
errors, elisions, `sorryAx` or unapproved axioms.

Every one of the 16 authored theorems has the exact transitive axiom set
`[propext, Classical.choice, Quot.sound]`, including the declarations proved
by reduction whose types reference the complete imported construction. All
generated declarations were checked as well; their union is the same three
approved logical axioms. No project axiom or semantic closure law is added.
The complete types and individual results are retained in the full log and
machine-readable census below.

Budget used: **four of 18 focused checker invocations and one of two
all-origin audits**. Three read-only executor calls encountered a transient
transport disconnect; bounded retry succeeded. That infrastructure event
supplies no mathematical evidence.

| Retained inspection artifact | SHA-256 |
| --- | --- |
| `/tmp/yulang-scoped-eligibility/InspectOwners.lean` | `1497abab866cb2889de583c0654fda7751745e56a210a3a7c614bb9b99b6bb07` |
| `/tmp/yulang-scoped-eligibility/inspect-01.log` | `6a74dea6e94ed39b4c3632af6f9481a64cc90f4220b28dceda13940410937bbb` |
| `/tmp/yulang-scoped-eligibility/owners.json` | `892fad65d661465650e4dc75f939d8dbda707530cc908bd3dd5d37955f144a91` |
| `/tmp/yulang-scoped-eligibility/AuditFull.lean` | `d6055e34f748e7dbbb83831efe4a154828fd7b55287cf7cc494c90647cad6aef` |
| `/tmp/yulang-scoped-eligibility/audit-01.log` | `996c72aba8f4acc53e9c2b95b641833139a099c506a116952c747d8b5a1a6ef5` |
| `/tmp/yulang-scoped-eligibility/census.json` | `1de7c5c03c3c52509c0747b9411064380181f1a0699dd1781a16b05bd8de6446` |

Read-only source revisions used for the representation finding:

| Path relative to repository | SHA-256 |
| --- | --- |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/theory/lean/YulangClosure/OriginalScopedClosure.lean` | `b316a5e18a14b4c9750cc97f294aea824ce6b0a704fc67929fa4a016e94ebeab` |
| `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean` | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |
| `notes/theory/lean/YulangClosure/OriginalSourceEvents.lean` | `cfd5f502a1e68a97e27e11a75400fae8789f167c92596aedb08ef7dfbb724342` |
| `notes/theory/lean/YulangClosure/OriginalParameterWorld.lean` | `7b5f849f744dbe56f374d8be6b11a5a218176abf6eeda2fb9da8180c7b1ff802` |
| `notes/theory/lean/YulangClosure/OriginalParameterSemantics.lean` | `733c5b05e0db226f95d14ff2161c46e9a389b43d86b365b000a9656ec4fd0bd2` |
| `notes/theory/lean/YulangClosure/OriginalFormalAdmission.lean` | `77230ab7984ee544db16fe4d9663b73f98b9afa9c5d2610fad59c26753d5ac7c` |
| `notes/theory/lean/YulangClosure/OriginalFormalShared.lean` | `abb9d69546e284fcb5fe6be9bb3c18269227e91da94e09eebf1a62e0b56e67f7` |
| `notes/theory/lean/YulangClosure/OriginalRecursivePair.lean` | `1069c185c6fa190c2a0dd776ebf4efc7bfab8ece7e36f2f4049d480e50fa65e7` |
| `notes/theory/lean/YulangClosure/SourceSignatureConstruction.lean` | `ed07890e29b4dcb38cabd18ec0e196efde9e95c64902942a9906a470b38c3311` |
| `notes/theory/lean/YulangClosure/OriginalSourceRecordBoundary.lean` | `c7889284745ebd23ec300cf3e4de0a8f7ffc4546a9af2eccf5df76d071a0dd1a` |

All original full goals remain OPEN. The only repository artifacts are this
note and its paired new Lean module; the initial unreferenced note-only draft
was moved to this authorized path. Parent retains builds, integration,
independent review and shared records. All checker processes have exited;
source and note writes stop at final handoff.

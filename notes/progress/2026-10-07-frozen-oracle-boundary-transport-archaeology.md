# Frozen Oracle shared-boundary transport: historical source/interface mechanism

Date: 2026-10-07
Status: bounded historical characterization; compiler-referee reviewed, pass
Yulang3 baseline: `21aceb0e4eacb0c09754a26f577f89d4180614fb`
Frozen Oracle: `/tmp/yulang2-oracle-rebuild`, `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this note only
Authority: historical implementation evidence only; no current semantic or production authority

## Question and result

The current `ORIGINAL_ASSOC` gap asks for a source producer that introduces one
original owner/view witness for the ordinary `f x` Call, including its static
`beta`/`Slots(beta)`, typed path, receiver-owned complete contribution and the
same original `xi=(nu,K,D)`. This bounded search looked for a distinct
historical source/interface mechanism beyond the already traced ordinary-App,
formal/frame, selection, occurrence, call-upper, SCC-use, declaration, and
typed-provenance paths.

It found a **compiled-unit boundary transport route**: generalized schemes
determine a dependency-closed boundary table; compiled import alpha-remaps that
table and its schemes together; session initialization substitutes each
boundary variable once; per-use scheme instantiation reuses that session
variable while freshening use-local binders. This is a concrete shared
interface/lifecycle mechanism. Its constructor starts from already-generalized
schemes. The inspected route does not derive an original Call contribution or
the current source owner/view judgment, so `ORIGINAL_ASSOC` and dependent gates
remain open.

## Authority and claim limits

The governing current sources are [inferred Function call views](../design/2026-10-05-inferred-function-call-views.md)
§§1–5 and [source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§§2–3, 10, together with `ORIGINAL_ASSOC` in the
[successor obligation ledger](../theory/successor-proof-obligations.md#original-assoc).
They require source-owned identities, typed formation, a complete receiver
contribution, preserved original scopes and one shared original assignment.
The current user explicitly keeps Frozen Oracle non-authoritative. No historical
field is assigned a current semantic meaning here.

Claim class: bounded static historical characterization plus a conditional
dataflow derivation from inspected field assignments and consumers. This is
not a current-language rule, source-adequacy result, source counterexample,
repository-wide absence theorem, or proof-gate closure. Blob equality verifies
the inspected historical revision only.

## Constructor → frozen boundary → import → use

All paths below are relative to the pinned Frozen Oracle checkout.

1. **Capture starts after generalization.**
   `crates/infer/src/analysis/cache_interface.rs:370–495` walks already
   generalized scheme roots to discover boundary variables and their
   transitive dependencies, then captures compact lower/upper intervals. It
   separates local quantifiers and recursive binders, and rejects conflicting
   binder classes, dependencies on local binders, and unclassified
   dependencies. It is boundary extraction from an existing interface, not
   source Call formation.
2. **The boundary table is frozen with the compiled schemes.**
   `analysis/cache_interface.rs:183–231` and
   `crates/infer/src/generalize/finalize.rs:29–41` convert retained schemes
   and each `CompiledBoundaryBound { var, bounds }` into the shared compiled
   type arena. The boundary variable remains explicit beside its neutral
   interval.
3. **Compiled import first performs importer-local alpha remapping.**
   `crates/infer/src/compiled_typed.rs:900–929,1245–1263,1536–1540` uses one
   `CompiledTypeImporter` mapping for the unit boundary table and imported
   schemes. This is the first shared mapping. It is local to that importer;
   separate unit prefixes receive disjoint mappings
   (`compiled_typed.rs:979–1008`, with a structural test at `:2024–2046`).
4. **Session initialization adds a second, longer-lived substitution.**
   `crates/infer/src/analysis/session/lifecycle.rs:36–42` and
   `crates/infer/src/instantiate.rs:39–56,1033–1059` allocate a root-level
   session mapping and install `lower <: mapped_var <: upper` constraints
   using an unknown internal origin. This mapping is distinct from the
   importer-local alpha map.
5. **Each use retains boundary variables while freshening its own binders.**
   `crates/infer/src/analysis/session/instantiate.rs:382–445` validates
   imported schemes before use. `crates/infer/src/instantiate.rs:104–113,
   571–588,620–641,750–760` seeds instantiation from the session boundary
   mapping and freshens quantified TypeVars, recursive-bound TypeVars, and
   stack quantifiers per use. `:1176–1213` rejects unmapped free variables
   and overlap between boundary and per-use TypeVars.

The conditional representation derivation is direct: if two validated scheme
uses refer to one retained boundary variable `b`, then after session seeding
both lookups use the same mapped `b_session`; a use-local quantified variable
is allocated through the freshening path instead. The contrast needs two uses
of a shared boundary variable. This is structural behavior under the inspected
mapping and validation branches, not an execution result or current semantic
claim. Allocator uniqueness is not separately established here.

## Exact stop against the current missing producer

The constructor consumes completed generalized interfaces. Its frozen record
contains a `TypeVar` and neutral interval, not an original static slot,
`beta`/`Slots(beta)`, typed `p0`, source Call owner, receiver incidence, or the
complete invocation contribution. Sharing a boundary variable through import
does not establish one original jointly scoped `(nu,K,D)` assignment. Session
subtyping is marked with an unknown internal origin; imported per-use
instantiation does not introduce the missing original generalized source
association.

Thus this route is an historical **shared-interface transport** analogue. The
inspected mechanism supplies no derivation of the current original owner/view
producer, and cannot discharge
`exists a in I_orig(X). forall z in F_C(X). Cover(a,z)`. Treating unit
boundary ownership, `TypeLevel`, a `TypeVar`, or successful imported use as the
missing source witness would add an unsupported bridge assumption.

## Review, source integrity and scope

An independent compiler-referee review passed the bounded historical claim.
The review specifically confirmed the pinned Oracle HEAD, clean Oracle tree,
the two distinct mappings (importer-local alpha remapping, then
session-lifetime boundary substitution), and all three per-use binder classes.
It did not certify current semantics or theorem closure.

The six decisive files matched their pinned commit blobs. SHA-256:

| Oracle source (under `crates/infer/src/`) | SHA-256 |
| --- | --- |
| `analysis/cache_interface.rs` | `e7c1b8da6cedfe55efe20257f9a69255e08fd25421dbead86d3bc04f2cf66ab5` |
| `analysis/session/lifecycle.rs` | `196b0f1eeef891e3547bf77e3d00f5f0574399e24bc59c4697219df6ff93d5ed` |
| `analysis/session/instantiate.rs` | `bf21175f47df78f35f2070fea51b3483d59a91ac4a606bace9e24f32878c2d19` |
| `compiled_typed.rs` | `871f3e80cad46024d39199f7613d79599b84fdd786d7b9ecb68c5dd9245dcc37` |
| `generalize/finalize.rs` | `a8e5a1c8e6ad57d1fac7e25a1ab6a329093e5c76e6d84c0625c124c349f07492` |
| `instantiate.rs` | `876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c` |

The producer used bounded static source reads and byte comparisons; the
reviewer independently reread the decisive windows. No Oracle execution,
tests, builds, mutations, seeds, enumeration, or executable model was used.
Broader export behavior and all other compiled-unit routes are outside this
bounded characterization.

Recommended next action: retain this transport mechanism as historical
crosswalk evidence, then derive original source owner/contribution formation
from current authoritative premises. Further boundary-import tracing would
not supply that missing introduction.

# Module registered root: source owner and implementation seam audit

Revision: 1; frozen research-only source/artifact evidence; independent review pending.
Worker: `/root/module_root_source_owner_audit`; current session; no descendants.
Baseline supplied by primary: `14820b4eec8688efa84cf76135694082ccf4f966`.
Sprint: `module-registered-root-embedding-20261017`, contract rev1 SHA-256
`198504dd9d648dd2eefc1dc565e0d2b1a5fb5f3fccfd33e7b9e788ec980d6ae7`.

## Objective, method and result

Identify the actual Application/module Name producers, retained typed fields,
consumers and ownership boundary. Method: bounded read-only source/authority
inspection with byte hashes, without compiler execution or a model checker.
Result: **NO_SAFE_CODE_SLICE**. No compiler/test write lease exists in this
sprint; the two source/call seams remain explicitly quarantined. The inspected
records also lack the authentic module typed-entry/root producer needed for a
complete source-to-generation-to-consumer implementation. Original theorem
conditions discharged: 0. Implementation/test behavior newly established: none.

This is a bounded source/artifact characterization, not a theorem of semantic
absence across the repository, a counterexample, or an implementation proposal.
It does not repeat the constructive root-embedding proof assigned to the prover.

## Governing meaning and exact premise

Read root AGENTS.md and AGENTS.pre-sprint.md, rules/research-lab.md and its
pre-sprint contract, rules/design-authority.md, rules/git-concurrency.md,
the current snapshot/README and the selected sprint contract. The sprint skill
was read for child packet boundaries; no new team or delegation was started.
The inference top-level principles §§1–3 retain construction/propagation and
source-owned evidence; they authorize no semantic shortcut here.

The adopted `module-environment-exposure-definition.md`, Decision and Limits,
forms actual typed Published/Family/Mono/Alias/Live environments and exact
lookup. Its accepted fixed source is `my id x = x; my answer = id 0`, with
`Instance(p_id,i_id*,d_id)` and separate occurrence `u_id`. Adoption supplies
neither the registered root nor a Rust representation. The reviewed local
`adopted-module-reference-application.md` §2 supplies declaration/publication,
`b_use` and whole `mu_id`; it is not registered-root formation.

`ordinary-call-original-generation.md` §7.2(2) explicitly separates the
proposed `ModuleContractRoot*(Decl*,b_use*,mu_id)` from its source-reference
leg `mu_id(r_id)`. That proposal remains conditional. Existing authority
`call-source-interface-definition.md` §§2–3 selects IF-Insert/IF-Use and
complete Call retention. Its underlying constructor text
`call-source-interface-construction.md` §3.2 requires original `reg_t` and an
actual independently typed clause or `Ref(t,m)` before constructing contextual
slots; §5 Call requires the actual Application constructor. These consumers do
not introduce the missing original registration. No language meaning was
reselected in this audit.

## Inspected owners and actual fields

| Owner / source locator | Actual observation | Required field still absent from this record |
| --- | --- | --- |
| `crates/yu-hir/src/module/local_source.rs:230`, `:239`, `:281`, identifier branch `:1004` | `LocalSourceExpr` retains occurrence, source key, range, scope, named-group identity and form. `Name` retains spelling/resolution; namespace singleton selects `ModuleDef(DefId)`. `Apply` retains callee/argument indices and syntax form. | Actual typed module entry constructor, its full dependencies/transport and registered original contract root. Namespace resolution establishes incidence only. |
| `crates/yu-hir/src/shadow.rs:1170`, `:2172` | `ApplicationSourceOccurrence` lazily exposes an existing structural Apply's expression/position/form/children; direct resolved-use incidence is filtered afterward. Its comment explicitly supplies no semantic Call view. | Typed Application registration, authentic `reg_t`, complete declaration telescope and original Gen-Call-0 derivation. |
| `crates/yu-solver/src/lib.rs:690` | `PendingDefinitionUse` contains exactly `parent: SourceReceiver`, `target: &DefId`, `occurrence: HirOccurrenceId`. | Published/Family/Mono/Alias/Live derivation, complete typed environment/scope transport, source `Sig`, whole source-reference map and registered contract-root derivation. |
| `crates/yu-solver/src/candidate_source.rs:962`, `:1040`, `:1370` | Module Name queues `PendingDefinitionUse` and `Action::Module`. Apply records `ApplySourceInput` and a candidate recipe. Execution constructs `DefinitionUseId`, then selects `route_candidate_open_use` or `route_incoming` by graph state. | Source typed-entry formation and the registered source root; native routing cannot supply them. |
| `crates/yu-solver/src/candidate_call.rs:19`, `:38`, `:294`, `:335`, `:388` | Formal registration retains owner/lambda/parameter/scope/recipe/native root. Apply input retains owner/expression/child indices/level/recipe, native ports, checking occurrence/cause, optional formal/native/introduction/receiver attachment. Module observer returns direct callee `DefId`; `native_registered_root()` uses only an authenticated formal's optional native root. Suppliers still request module source typing/admission and receiving/export correspondence, OriginalGenCall0 and complete downstream fields. | A module entry does not become a formal registration by having a Lambda definition. No module registered-root derivation or source/native field interpretation is retained by these records. |
| `crates/yu-solver/src/shadow_apply.rs:13`, `:28`, `:396` | Unresolved premise inventory retains ApplicationTypingRule and both module obligations; candidate source-call exposure invokes `candidate_call::observe`. | Complete source interpretation/discharge. Successful observation or solving would not authenticate those missing source premises. |

The concrete chain observed is HIR resolved Name/Apply incidence -> pending use
and native Apply inputs -> candidate module routing/native interfaces -> source
Call observer and explicitly pending suppliers. The authentic source chain
needed by §7.2(2) is typed module environment/lookup -> actual whole source map
-> registered `ModuleContractRoot*` with original-family embedding -> original
Data-Name/Result/Call construction. This audit establishes the first structural
chain only; the proof lane owns the missing registered-root construction.

## Ownership and implementation boundary

The current sprint contract, Lanes §§2 and 4, grants this worker only the two
paths in the commit packet. Both `candidate_source.rs` and `candidate_call.rs`
are QUARANTINED read-only under inherited UNKNOWN implementation ownership.
The immediately prior materialization sprint §4 says the same. Current.json
retains `/root/resident_dispatcher_loop_a`, `/root/resident_implementer_idle`
and `/root/runtime_source_supplier_proof` as inherited UNKNOWN assignments.
It does not enumerate a reliable current per-file writer mapping among them.
Historical board rows describe `/root/resident_implementer_idle` as a protected
legacy implementation identity, with no established current task/output lease;
those old rows do not establish cessation or release. Exact unknown per-file
writer identity remains UNKNOWN, rather than being guessed from the role name.

The HIR owners, solver lib.rs and shadow_apply.rs were inspected as alternative
seams. None has a new compiler write lease. Adding a source record there would
still need the missing semantic producer/field and the quarantined generation
and consumption seams. A new tag/container in another file cannot bypass either
boundary. No unquarantined complete source-to-generation-to-consumer slice was
identified in the inspected owners. This conclusion is conditional on the
primary's retained quarantine and current no-code contract; it is not a claim
that implementation can never be authorized.

## Evidence pins and coverage

SHA-256 of inspected current bytes (not Git object authentication):

```text
d5d03de8b80eb2792cc35690f3fc3c871f9704f4aee8df815bce40b1f49f9d4d notes/design/2026-10-17-module-environment-exposure-definition.md
44f33397a45f5d17a0302c6b1efbfe1f7bbdf018caed2ece2acc18176a746bd9 notes/design/2026-10-17-module-entry-provenance-contract.md
418055486f31ff7e3895a7f5ea1d86ce10a6ff83424f716a0203d4f276105765 notes/theory/2026-10-17-adopted-module-reference-application.md
bd2a690517118c8826dfe1a2fe9db53c829a1638bd2e6a1fd5aa01a252735aab notes/theory/2026-10-17-ordinary-call-original-generation.md
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c notes/design/2026-10-08-call-source-interface-definition.md
278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98 notes/theory/2026-10-08-call-source-interface-construction.md
ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5 crates/yu-hir/src/module/local_source.rs
460c813cb0d2e21565df011b1d816abbc2b180cef13797a1b7b453e9ee413f66 crates/yu-hir/src/shadow.rs
60e91c9a51394b04af42b3ec7c284062b34fcd9faa4ea79c35b4ae58aaf460ed crates/yu-hir/src/module.rs
2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f crates/yu-solver/src/lib.rs
efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38 crates/yu-solver/src/candidate_source.rs
2bcbab3d27e259fc4b22824980bd625014d4a19f4fa257cd74c69683c1be0359 crates/yu-solver/src/candidate_call.rs
bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf crates/yu-solver/src/shadow_apply.rs
```

The five sprint-pinned semantic dependencies and contract hash match the supplied
values. The construction note's current hash differs from the historical frozen
producer hash `0e159f...` quoted in the authority note; no equivalence to those
historical bytes is claimed. It is supporting current inspection, not a new
proof premise. Older sprint inventories also show a historical candidate_call
hash `cbad9cf...`; this audit pins the current observer bytes instead and makes
no historical equality claim. No dependencies were modified by this worker.
Git was not invoked, so baseline-to-working-file identity was not independently
authenticated here; primary must revalidate the pinned bytes before acceptance.

Commands: read-only `cat`, bounded `rg`/`head`, `sed -n` slices and `sha256sum`.
Two initial guessed source paths did not exist; searches resolved the actual
`module/local_source.rs` owner. Some large combined reads were output-truncated;
claims above use subsequent exact owner slices. No whole-repository absence
search was completed. No tests/builds/probes, mutations, seeds or ranges apply.
No independent executable oracle exists in this packet; source and design are
different evidence classes and neither derives semantic truth from native
success. Runtime wall/CPU/peak-memory measurement is UNKNOWN; charge the full
180 s grant, no carry. No heavyweight process, descendants or Git operation.

Recommended next action: the primary should consume the prover's exact root
constructor/embedding boundary and independently review it with this pinned
owner map, then resolve the inherited implementation writer identity/cessation
before granting any concrete compiler slice. Source `Sig/Phi_u`, admission /
observation equivalence, full Call, N-Transport, F1/FK1, soundness, principality,
termination and production remain unverified/open.

## Commit packet

Exact leased paths:
- `notes/progress/2026-10-17-module-root-source-owner-audit.md`
- `tasks/agent-loop/inbox/20261017-module-root-source-owner-audit.md`

Baseline: `14820b4eec8688efa84cf76135694082ccf4f966`.
Dependency hashes changed by this worker: none; inspected pins above.
Review status: frozen rev1, independent review pending; not self-certified.
Checks already run: read-only owner/authority inspection and SHA-256 inventory;
no compiler checks/tests/builds/probes.
Proposed commit: `research: pin module registered-root source owner blockers`.
Shared-record deltas left for primary/curator: record NO_SAFE_CODE_SLICE, audit
STOPPED/FROZEN, full180 charge and exact missing registered-root/source-native
fields; preserve quarantines and all original OPEN parent gates.

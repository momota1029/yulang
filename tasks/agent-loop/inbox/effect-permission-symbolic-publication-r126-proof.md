# R126 existing R39 publication application — revision 1

Status: **FROZEN / WRITES STOPPED / CONDITIONAL / independent review pending**.
Assignment: `R126-PROOF-1`, sprint
`EFFECT-PERMISSION-SYMBOLIC-PUBLICATION/20261102-R126`.
Worker: `/root/r126_symbolic_proof`, bounded lean_prover leaf, sole author,
no descendants. Primary NEW_TASK is the launch/activity receipt; effective
model/effort metadata was not supplied and is UNKNOWN. This handoff is the
only leased and changed path. No Lean declaration, model or axiom was added.

## Frozen inputs and authority

Baseline: `e4570173a19ed72f6257fa391032f153ca43943d`, branch `yulang3`.
Contract SHA-256:
`8a999995dca10358d9a8aaf9db8a5e7b473edc0e199e9b0de3e066157e86d8cb`.
Manifest SHA-256:
`7e47ad03d3e49f8cf711d1c46d52a106179b1c86b40cd18ce0f2fb8c172cf155`.
Admission SHA-256:
`564f4df5e1342a964baf282ff75dc32175da8f219b73ff51fcfbd6c1bfd92a9c`.
All three were recomputed and matched.

Existing R39 source:
`notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean` at
`1f5835c276143537ec58ed81db96c7c108cea8e7`, SHA-256
`748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e`.
Read in full using immutable `git show` and independently authenticated.
The primary explicitly clarified that this read-only Git operation and blob
hashing are allowed; no other Git operation was used.

Frozen R125 source handoff SHA-256:
`0fc58726d0db552c99714926533080d0238cb913f3d898f1b12430b3057e84a3`;
proof handoff SHA-256:
`23ac34427928c0f9e6a4060018391b0083de2da3c19381667950e763a9013387`;
reviewed outcome SHA-256:
`0cd54c5bcc0698657fdd6c16e00836dbdd35103f92fb2202ba0854d40dc7807e`.
All were read and independently rehashed successfully. R125 is the preceding
reviewed same-graph PRE bridge; it is not full symbolic publication closure.

Read root AGENTS and preserved map, goal-driven rules, handoff protocol,
design-authority, the Lean skill and both references, sprint skill, and exact
R126 contract/manifest/admission. Original parent/scope locators retained from
the contract and frozen R125 bridge are
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5,
the Value birth-level SCC correction
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6, and effect policy
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2.
The primary explicitly kept this packet at existing R39 plus frozen source
equations and declined a new parent-source reading. These locators are
inherited, not a claim of freshly reading those original documents. Original
quantifiers, accepted source features, full Call/effect evidence and one shared
lawful witness remain unchanged. Research drafts add no semantic authority.

## Exact existing declaration and definitions

All short names below have prefix
`YulangClosure.ComputationPermissionEntryR39.`. The actual source declaration
quantifies `{Id : Type} [DecidableEq Id]`:

```lean
theorem constructed_entry_publication (e : Inputs Id) (a : Action Id)
    (f : Registration Id) (r : Row Id) (port : Id) (s : State Id)
    (hf : e.formals[a.registration]? = some f) (hr : a.annotation.row = some r)
    (hp : f.entry = some port) (valid : Valid e a f r) (nonempty : r.concrete ≠ []) :
    ∃ p, prepare e a = some (f, r, port) ∧ permissionFor a f r port = some p ∧
      p.concrete = r.concrete ∧ p.entry = port ∧
      publish a f r port true s = some
        ⟨s.permissions ++ [p], s.links ++ symbolicLinks a r port, s.inflow⟩
```

This is a transcription of pinned source, not a fresh `#print` result.
`Valid e a f r` is exactly the conjunction:

```text
f.owner = a.annotation.owner ∧ f.role = .computation ∧ f.scope = a.scope ∧
e.recipes[f.recipe]? = some f.parameter ∧
ownerLookup e.owners a.occurrence = some f.owner ∧
sourceLambda e f = some (a.occurrence, f.parameter) ∧
f.recipe ∉ e.occupiedDomains ∧ a.registration ∉ e.retainedRegistrations ∧
r.variables.length ≤ 1
```

`sourceLambda` selects the authentic owner's LocalSource list and its
owner-local Lambda index; `.other` does not qualify. `build a f r port` copies
registration, recipe, formal identity, occurrence, owner, scope, annotation
position, row position, entry and the complete ordered concrete list.
`permissionFor` returns none exactly for an empty concrete list.
`State` has separate permission, generated-link and external-inflow lists.
`publish ... true s` is definitionally the three-field append/preserve result;
`publish ... false s = none`. Its readiness is a local point before final
resource sampling, not whole-call success or rollback.

For `r.variables = [name]`, the exact required list is:

```text
symbolicLinks a r port =
 [⟨a.occurrence,45,.entry port,.symbolic a.scope name⟩,
  ⟨a.occurrence,46,.symbolic a.scope name,.entry port⟩]
```

For no variable it is empty. The ≤1 guard excludes a longer row on the
successful preparation branch. Existing `symbolic_link_preserved` states the
same concrete two-link publication with hypothesis `r.variables = [name]`;
`empty_concrete_local_case` states the no-permission branch with the same
hf/hr/hp/Valid and `r.concrete = []`. No accepted empty or symbolic-only case
is removed by selecting the nonempty theorem's branch.

## Application and exact source dependencies

Keep R125's actual invocation, immutable batch B, graph G, action a, registration
f and outer annotation row r. Use its complete native tagged identities and
graph-relative entry `port = row_G(U)`. At the guard time t0, the same ordered
native permission Vec V0 supplies both
`e.retainedRegistrations = map registration V0` and
`s0.permissions = map P V0`. Therefore their shared-witness equation is
`e.retainedRegistrations = map (fun p => p.registration) s0.permissions`.
No independently chosen POST list replaces s0. R125's reviewed guard mapping
supplies hf/hr/hp/Valid at t0; the nonempty concrete branch supplies nonempty.

Consequently the existing theorem applies mathematically with that s0 and
returns the shared witness `p = build a f r port`, the prepare/retention facts,
full concrete-row equality, entry equality and its abstract State conclusion.
The theorem has **no** hypothesis or conclusion asserting that the real typed
drain preserves permissions, or that retained native provenance realizes links.
These are required source-to-State equations, not newly discharged R39 premises.

For the actual local transition, R125 gives
`map P V2 = map P V1 ++ [build a f r port]`, with t1 after successful symbolic
helpers and t2 just after the permission push. To identify this with R39's PRE
permission component still requires the authenticated equation `V1 = V0` (or
its exact P-projection consequence) for every successful helper path in this
invocation. Reserve relocation preserves a sequence but does not itself frame
transitive context/drain/extrusion/replay operations. The same graph and Vec
owner must be retained. Physical append index, action registration and recipe
index remain distinct.

The direct-request component requires an authenticated retained projection L,
with original term identity recoverable through each provenance edge's FactId,
such that `L2 = L0 ++ symbolicLinks a r port`. For a singleton name, this means
exactly the two records displayed above in order 45 then 46, with both retained
even when canonical fact deduplication reuses a FactId. It requires complete
occurrence/scope/name identity and graph-relative typed endpoints from the
original requested terms. Canonical representative endpoints, the facts Vec
alone, or a set of edges do not establish this list equation. Additional drain
constraints must be distinguished by an authenticated direct-request projection;
an unavailable retained original term cannot be treated as an empty projection.
No such projection is invented or assumed here.

At this handoff freeze the R126 source handoff had not been supplied as frozen
bytes with a revision/hash. Its live path was not read. Accordingly no R126
drain frame or direct-trace equation is asserted, and no actual-source symbolic
State conclusion is claimed. The result is the bounded conditional R39-side
map, not a failure of the existing theorem or a source-qualified counterexample.

First remaining dependencies, owned by Luna's R126 source/correspondence intake:

- `R126-SYMBOLIC-FRAME-1`: frozen successful symbolic-helper mutation/frame
  derivation proving V1 = V0, including reached context/replay owners. Falsifier:
  an actual successful source path changes the retained permission sequence.
- `R126-DIRECT-TRACE-1`: frozen original-term/FactId/provenance derivation of the
  exact ordered two-link delta, or the first actual identity/retention mismatch.
  Falsifier: changed endpoint, slot, occurrence, order or multiplicity on an
  authentic invocation; arbitrary malformed abstract states do not qualify.

If those equations are authenticated, substituting them and R125's local append
identifies the permission/link components of the abstract conclusion at t2.
The external inflow interpretation is still separate: an arbitrary unchanged
list I does not identify actual providers or solver lower bounds. Native inflow,
Catch/subtraction, later R121 indexed consumer correspondence, whole-call failure
and publication/reuse, full source/native soundness, principal coverage,
termination, R111's 6 GiB verification-resource gate and production remain OPEN.
The parent theorem and NO_SAFE_CODE_SLICE are unchanged.

## Evidence, coverage, resources and cessation

Actual commands: bounded `cat` reads; immutable
`git show 1f5835c276143537ec58ed81db96c7c108cea8e7:notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean`;
Python stdlib `hashlib` over that exact `git show` output, three R125 receipts
and three R126 governing files; one apply_patch for this handoff; final handoff
hash. All completed command exits were 0. Broad initial batched output was
truncated; focused full R39, R125-proof, contract and source-map reads followed.

Lean/Lake versions, actual goals/diagnostics, printed types, `#print axioms`,
skill checker, build and tests: **NOT RUN**, explicitly prohibited by this
packet. No theorem was delivered as newly kernel checked. R125 records
historical R39 axiom receipt `[propext, Quot.sound]` for the relevant existing
declarations; that is inherited evidence, not an R126 axiom audit or execution
receipt. No toolchain, dependency, configuration or source file was changed.

R39 covers finite exact identity tables, Lambda versus other source forms,
definition-backed empty schedules, copied ordered concrete lists with duplicates,
zero/one symbolic variable, empty permissions and local generated links. It
omits allocation, solver propagation, provider arrival, Catch/subtraction and
whole-language/native simulation. R126 source coverage remains pending the
frozen source handoff; this lane did not duplicate a Rust audit.

Resource grant: 300 seconds, no descendants or probes. CPU/RSS and exact active
elapsed time were not instrumented. This leaf stops at the frozen-source
dependency within the finite packet rather than expanding inputs or execution.
No scratch/copy/worktree/cache/generated output, background process, dirty or
quarantined source read, compiler edit, install, network access or Git mutation.
**All writes STOPPED at revision 1.** Independent review, source equation intake,
any renewed packet and integration remain with Luna.

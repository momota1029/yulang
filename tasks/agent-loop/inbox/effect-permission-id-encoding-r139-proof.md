# R139 proof handoff — checker evidence (construction scope only)

One direct module check; no build, dependency refresh, external checker scratch, or root imports.

```text
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --version
libc++abi: terminating due to uncaught exception of type lean::exception: failed to create thread: Resource temporarily unavailable

exit=-6; wall_seconds=1.492

$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake env lean --version
libc++abi: terminating due to uncaught exception of type lean::exception: failed to create thread: Resource temporarily unavailable

exit=-6; wall_seconds=1.553

$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake env lean -j1 -M1024 YulangClosure/FormalPermissionIdentityEncodingR139.lean
libc++abi: terminating due to uncaught exception of type lean::exception: failed to create thread: Resource temporarily unavailable

exit=-6; wall_seconds=1.245
```

Child max RSS KiB: 23940; user CPU seconds: 0.006924; system CPU seconds: 0.48628; total checker envelope wall seconds: 4.29.

Assignment-ID: /root/r139_proof; handoff revision 1; session R139.
Role: bounded Lean leaf; primary dispatch is the launch/active-work authority.
Requested role/effort: lean_prover/bounded; effective model/effort metadata UNKNOWN.
Author: /root/r139_proof only; descendants: none.
Baseline supplied by contract: 4c1d58a646a1101c080659ebfed6ae7862d8aded.
Outcome class: candidate, CONSTRUCTED_BUT_UNCHECKED. No theorem is claimed
kernel accepted, independently reviewed, source corresponding, or production ready.

## Source and original parent

Original source-preservation statement: notes/theory/2026-10-13-intrusion-source-preservation-proof.md
§1 (all supported original source programs, all lawful finite histories, each
retained extrusion occurrence, original scopes and a single joint witness),
with the current fixed birth-level induced-SCC correction in
notes/design/2026-10-24-birth-level-scc-intrusion.md §§2–6.
Whole-language scope: docs/yulang-whole-proof-closure-ja.md §§1–3.
The source manuscript docs/yulang-source-type-safety-ja.tex sec:owners explicitly
separates resumed execution owners from historical evidence and labels the
concrete corrected machine as a candidate; this packet adopts no draft semantics.

Exact original Lean parent: YulangClosure.SourceProblem.InferenceSoundness in
YulangClosure/Contracts.lean:
`∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
 ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a`.
The SourceProblem record remains uninstantiated; the proposition definition
supplies no concrete source law. This module imports Std only, so none of the
source/dependent proof modules or LocalLaws are assumed by these constructions.

Exact local prior seam: FormalPermissionSourceOrigin.Context has Nat-valued
parameter/occurrence/owner/scope; Context.metadata adds row position and ordered
concrete effect members. FormalPermissionConstructorR136.Row and record/inventory
still use those abstract numbers. R137 authenticates structural recursion but
leaves identity equations open. R138 supplies the audited production discard
envelope, without constructor-local rollback or early-consumer closure.

## Constructed declarations and quantifiers

Namespace: YulangClosure.FormalPermissionIdentityEncodingR139.
TaggedKey is a disjoint sum over seven arbitrary Type parameters: Owner,
Occurrence, Formal, Scope, Node, Effect, Symbol. Its derived DecidableEq uses
payload equality with variant tags. It encodes neither offsets nor hashes.
The generic table lemmas quantify over every K : Type with DecidableEq K;
instantiation with TaggedKey requires the seven payload DecidableEq instances.
These instances are ordinary decidable equality, with no injectivity law supplied
as a premise and no assumption equating source/native output.

Table K is List K. resolve returns some first-index exactly for members.
register reuses that first-index for members, otherwise appends one key and
returns the previous length. extend starts at [] for a complete local table.
No table well-formedness/injectivity premise is assumed: even arbitrary initial
lists satisfy the first-index uniqueness and extension properties.

The 19 named theorem targets are listed below. Every target has inline
`#check @<fully-qualified-name>` and `#print axioms <fully-qualified-name>` in
the artifact. Actual type prints: UNAVAILABLE for all 19. Actual transitive
axiom lists: UNAVAILABLE for all 19. The runtime aborted before elaboration;
absence of audit output is not an empty axiom list.

```lean
YulangClosure.FormalPermissionIdentityEncodingR139.equal_keys_resolve (table : Table K) (a b : K) (same : a = b) :
    resolve table a = resolve table b
```

```lean
YulangClosure.FormalPermissionIdentityEncodingR139.registered_index_injective (table : Table K) (a b : K)
    (ha : a ∈ table) (hb : b ∈ table)
    (same : table.idxOf a = table.idxOf b) : a = b
```

```lean
YulangClosure.FormalPermissionIdentityEncodingR139.distinct_registered_codes (table : Table K) (a b : K) (n : Nat)
    (ea : resolve table a = some n) (eb : resolve table b = some n) : a = b
```

```lean
YulangClosure.FormalPermissionIdentityEncodingR139.append_preserves (table suffix : Table K) (key : K) (n : Nat)
    (old : resolve table key = some n) : resolve (table ++ suffix) key = some n
```

```lean
YulangClosure.FormalPermissionIdentityEncodingR139.register_reuses (table : Table K) (key : K) (h : key ∈ table) :
    register table key = (table, table.idxOf key)
```

```lean
YulangClosure.FormalPermissionIdentityEncodingR139.register_fresh (table : Table K) (key : K) (h : key ∉ table) :
    register table key = (table ++ [key], table.length)
```

```lean
YulangClosure.FormalPermissionIdentityEncodingR139.register_resolves (table : Table K) (key : K) :
    resolve (register table key).1 key = some (register table key).2
```

```lean
YulangClosure.FormalPermissionIdentityEncodingR139.register_preserves (table : Table K) (key oldKey : K) (n : Nat)
    (old : resolve table oldKey = some n) :
    resolve (register table key).1 oldKey = some n
```

```lean
YulangClosure.FormalPermissionIdentityEncodingR139.extend_preserves (keys : List K) (table : Table K) (key : K) (n : Nat)
    (old : resolve table key = some n) : resolve (extend table keys) key = some n
```

```lean
YulangClosure.FormalPermissionIdentityEncodingR139.extend_registers (keys : List K) (table : Table K) (key : K)
    (member : key ∈ keys) : ∃ n, resolve (extend table keys) key = some n
```

```lean
YulangClosure.FormalPermissionIdentityEncodingR139.encode_length (table : Table K) (keys : List K) :
    (encode table keys).length = keys.length
```

```lean
YulangClosure.FormalPermissionIdentityEncodingR139.encode_position (table : Table K) (keys : List K) (i : Nat) :
    (encode table keys)[i]? = keys[i]?.map table.idxOf
```

```lean
YulangClosure.FormalPermissionIdentityEncodingR139.encode_append (table : Table K) (left right : List K) :
    encode table (left ++ right) = encode table left ++ encode table right
```

```lean
YulangClosure.FormalPermissionIdentityEncodingR139.encode_duplicates (table : Table K) (key : K) (count : Nat) :
    encode table (List.replicate count key) = List.replicate count (table.idxOf key)
```

```lean
YulangClosure.FormalPermissionIdentityEncodingR139.completed_sequence_resolves (keys : List K) (key : K) (member : key ∈ keys) :
    resolve (extend [] keys) key = some ((extend [] keys).idxOf key)
```

```lean
YulangClosure.FormalPermissionIdentityEncodingR139.failure_has_no_snapshot (reserve : K → Bool) (keys : List K) (error : Failure)
    (failed : construct reserve keys = .error error) :
    authenticated (construct reserve keys) = none
```

```lean
YulangClosure.FormalPermissionIdentityEncodingR139.failure_cannot_authenticate (error : Failure) (snapshot : Snapshot K) :
    authenticated (.error error) ≠ some snapshot
```

```lean
YulangClosure.FormalPermissionIdentityEncodingR139.reservation_failure (reserve : K → Bool) (table : Table K)
    (key : K) (keys : List K) (failed : reserve key = false) :
    constructFrom reserve table (key :: keys) = .error .reservation
```

```lean
YulangClosure.FormalPermissionIdentityEncodingR139.suffix_failure_discards_prefix (reserve : K → Bool) (table : Table K)
    (key : K) (keys : List K) (error : Failure) (allowed : reserve key = true)
    (failed : constructFrom reserve (register table key).1 keys = .error error) :
    constructFrom reserve table (key :: keys) = .error error
```


## Represented and omitted cases

Represented: all seven identity tags; arbitrary finite tables and registration
sequences; existing and fresh registration; any appended suffix; every position
and any number of repeated sequence members; reservation failure, lookup failure,
and recursive failure after a prefix was privately registered. encode_position
and encode_length preserve each ordered occurrence; encode_duplicates preserves
an arbitrary replicate count; encode_append preserves concatenation boundaries.
completed_sequence_resolves connects every input member to the completed table.
The failure sum is Except Failure (Snapshot K); its error branch contains only
Failure (reservation or lookup). authenticated projects only the ok branch.
suffix_failure_discards_prefix propagates a later error without returning a
snapshot. This is a result-type property, not a Rust rollback/termination receipt.

Omitted: Rust types and Eq/clone laws, scoped field key equations, actual same-table
use across source/native inventories, native inventory equality, integer capacity
or allocation failures, concrete source constructors/constraints/propagation,
arrival/capture/copy/Catch consumers, executable tests, independent review.
constructFrom is an abstract fallible constructor; no theorem connecting all its
successful results to R136, Rust execution, or source typing is claimed.
Cross-snapshot codes are not compared by any theorem. The namespace does not
supply a type-level prohibition against other clients comparing raw Nat codes.

## Parent application and first remaining premise

No application can currently be kernel checked because the single admitted
verification attempt failed before elaboration. If checked, register_fresh,
register_reuses, register_resolves, distinct_registered_codes and append_preserves
would discharge the local finite-table coding properties without postulating
injectivity. They cannot by themselves instantiate Context.metadata or the
original InferenceSoundness witness. The first local remaining obligation is
successful pinned elaboration and all 19 type/axiom audits. Verification owner:
primary Luna. The next source bridge is the reviewed equation assigning each
complete cloned Rust identity to its tagged key, Rust Eq agreement, and actual
reuse of ONE table by source and retained metadata. Source owner: R139 source
lane, followed by primary-assigned fresh review. Actual native inventory equality
and every original A/B, H, soundness and production premise remain OPEN.

Mutual TODO R139-VERIFY-1: primary verifies these exact frozen bytes with the
pinned toolchain and all inline audits under an authorized working resource
mechanism. Falsifier: any elaboration failure, changed theorem premise, sorryAx,
project axiom, or additional unapproved axiom. No retry, installation, resource
increase, or global-default change was attempted by this leaf. The thread error
occurred under RLIMIT_AS=1073741824 bytes; its cause was not diagnosed, so it is
not asserted to prove system-wide thread exhaustion or a mathematical failure.

Mutual TODO R139-EQ-1: source lane/primary supplies complete Rust key equations,
Eq/clone preservation and same-table use. Falsifiers: tag confusion, distinct
identity collision, source/native tables differ, or cloning changes equality.
This is a request for evidence, not a new lease or proof assumption.

## Execution, resources, and writes

Installed executable lookup `elan which lake` exited 0 and returned the absolute
native Lake path shown above. lean-toolchain pins leanprover/lean4:v4.35.0;
lakefile.toml sets -j1/-M1024; lake-manifest.json has no packages. Actual Lake/Lean
versions are UNOBSERVED because both version commands aborted. Commands were
run from notes/theory/lean with LEAN_NUM_THREADS=1, affinity restricted to one
available CPU, address space capped at 1 GiB, and one 120-second aggregate subprocess
timeout. Only one module-check command ran. No actual Lean goal or diagnostic
beyond the runtime thread failure was emitted. The resource values and all
nonzero exits above are preserved verbatim.

The skill checker was inspected but not invoked: it creates build/audit scratch
outside the exact two-file lease and would require more than the one direct
module check. Manual inline audits fit the assigned path constraint. No build,
tests, Rust source writes, dependency/toolchain changes, Git operations, nested
CLI, or delegation. No scratch files. No -o output requested; no shared cache
ownership acquired. The process aborted before elaboration; no before/after
cache inventory was taken, so a generated/cache delta is not certified.

Finite assignment envelope: 600 seconds. Checker subprocess envelope: 4.29 seconds;
one direct module check consumed. Work ends within the assignment bound.
Exact writes: the Lean artifact and this single handoff. No independent review
or integration milestone claimed. Pending: pinned verification and fresh review.

## Frozen inputs and artifact

The source/control hashes below record the read inputs; they do not elevate draft
semantic authority. All hashes SHA-256.

- `.agents/skills/yulang-lean-proofs/SKILL.md`: `05346b8c6e3d9cdd1715da1774bb26cf7bce313233782240b3493bd9ee8754a7` (7856 bytes).
- `.agents/skills/yulang-lean-proofs/references/sources.md`: `cb3f1009e80f0f9f7a1bf2575b4144e002a72f21e474c66b441e1f626a1e4d4a` (5330 bytes).
- `.agents/skills/yulang-lean-proofs/references/execution.md`: `a1d8c47550e8925220623e0401410556d92719aff5590c459ac4c2e88306800b` (5345 bytes).
- `rules/goal-driven-sprints.md`: `f2e01e3c33dc13d6c5cb77a66e7c5f0de15f08669f5a47fef0d6cb5c914da3a5` (20222 bytes).
- `AGENTS.md`: `4a6c910e12adb8f5ccc07b0921f2cc781ea7044994f99425d3c54c4e75837d3c` (11939 bytes).
- `AGENTS.pre-sprint.md`: `99ae7bbda0a8907a48f762420d996e145e9870ad9794ea0dc608770131182882` (24393 bytes).
- `tasks/agent-loop/sprints/effect-permission-id-encoding-20261102-r139.md`: `717acc2e9c3bd70f19a0b74854802952ab0eea6ccf62fab104c5075997ee4afb` (3375 bytes).
- `notes/theory/lean/lean-toolchain`: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` (25 bytes).
- `notes/theory/lean/lakefile.toml`: `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` (311 bytes).
- `notes/theory/lean/lake-manifest.json`: `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` (145 bytes).
- `notes/theory/lean/YulangClosure/Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` (7467 bytes).
- `notes/theory/lean/YulangClosure/FormalPermissionConstructorR136.lean`: `3289bccd2b85dd4576adb1c4a870e635985b60e2e87c459d9174c4a0477eab4f` (10356 bytes).
- `notes/theory/lean/YulangClosure/FormalPermissionSourceOrigin.lean`: `db37f9d83e450a450d689b9eed46311108e635eb846d268b7a3a567dcee624fd` (17918 bytes).
- `notes/theory/lean/YulangClosure/OriginalEffectHygiene.lean`: `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f` (20767 bytes).
- `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`: `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` (34671 bytes).
- `notes/design/2026-10-24-birth-level-scc-intrusion.md`: `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` (7812 bytes).
- `docs/yulang-whole-proof-closure-ja.md`: `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5` (57870 bytes).
- `docs/yulang-source-type-safety-ja.tex`: `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166` (184349 bytes).
- `tasks/agent-loop/history/effect-permission-hir-decoder-20261102-r137-outcome.md`: `82fd775010eb1b865928510bed1d34d282c0d46768f6ee93054ca0d670748231` (2122 bytes).
- `tasks/agent-loop/history/effect-permission-formal-publication-envelope-20261102-r138-outcome.md`: `2cfe94f5dd822c4df4619fa194186c2537393c1c3ed8340e244f56b6e93ac480` (2306 bytes).

Frozen Lean revision 1: `notes/theory/lean/YulangClosure/FormalPermissionIdentityEncodingR139.lean`, 11350 bytes, SHA-256 `5bf4e97160a6114c5ae320883fcfbd71045f0b2500c15de35df0def5366cb90b`.

STOPPED_WRITING: both leased outputs frozen at handoff revision 1. No children or outstanding writer/cache leases. Handoff byte size/hash are returned in the final authenticated message to avoid a self-referential hash.

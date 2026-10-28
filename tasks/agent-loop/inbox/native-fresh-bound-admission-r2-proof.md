# NATIVE-FRESH-BOUND-ADMISSION/r2 proof handoff

Assignment ID: NATIVE-FRESH-BOUND-ADMISSION/r2/proof; handoff revision 1.
Contract: `tasks/agent-loop/sprints/native-fresh-bound-admission-20261028-r2.md`, SHA-256 `415195c283db4b9c03dc9cac17e636507b9810261fa987dfc4ab36e514e900f0`.
Session: NATIVE-FRESH-BOUND-ADMISSION-20261028/r2.
Worker: `/root/native_fresh_bound_admission_proof_r2`; requested Sol/high;
observed model/effort UNKNOWN. Exact ACK sent to Luna before any body reads.
Grant: 700 seconds. No descendants, scheduling, Git, network, runtime/compiler
changes, dependency changes, scratch files, or generated/cache writes.

Outcome class: **candidate conditional construction, NOT_CHECKED**.
Independent review NOT_RUN. Source/native refinement OPEN. Production authority
unchanged. Phase-1 source review precedes every execution under this contract.

## Frozen artifact and exact leases

- `notes/theory/lean/YulangClosure/NativeFreshBoundAdmissionR2.lean`
  SHA-256 `d1bff386152537dc48b9ea107564114e4a90c3075b6dbe1478a5290be60c0780`.
- This handoff is the sole other write. Its frozen hash is sent separately,
  avoiding a self-referential byte hash.

Baseline supplied by Luna: `23a7028cf0b3eeef5e0d601f145fecc4112539e9`;
research base `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`. No Git command was run.
The module imports only admitted `Contracts` and `NativeFreshScopeTransport`;
no root import was changed. All authors: this worker only.

## Original statement and governing sources

`YulangClosure.SourceProblem.InferenceSoundness`, Contracts.lean:128:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

This proposition definition is not a concrete instance. The same scoped witness,
all supported source constructors, finite lawful histories, retained extrusion
occurrences and original Simple-sub A/B claims remain required and OPEN.

Read governing material: original preservation manuscript
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5
(its original parent, non-let paper boundary and first source-scope premise);
current immutable Value-birth/induced-SCC correction in
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6 and its theory
application; whole-proof closure document §§1,4; inference-soundness progress
record's original parent; inference top-level principles; selected annotation
policy §§1–1.2. Research prose is not treated as semantic authority. The original
external Simple-sub PDF is located by the manuscript, but is not an admitted new
dependency in this fixed packet and was not read or claimed as newly verified.
`OriginalEffectHygiene` opening and publication/consumer declarations were read
only for the shared-witness seam; they supply no missing native instance.

## Exact native path and represented cases

- `candidate_scheme.rs:4669–4715`: this bound ordinal, canonical target
  orientation, imported antecedent and context-use origin, optional mapped
  relation, then `candidate_begin_bound_restoration` with FreshUse cause.
- `candidate_effect.rs:714–777`: scoped FreshUse checks/reuses mapped ID;
  unscoped calls ordinary `candidate_context_bound`; duplicate origin keys still
  append an admission. Mapped and admitted IDs are distinct fields.
- `candidate_context.rs:4259–4276`: scoped snapshot source bound, parent,
  relation target pair, nonzero use and exact FreshUse transport guard.
- `candidate_context.rs:3888–3937,3043–3094`: ordinary payload compatibility,
  post-check context, key interning; nonidentity Effect self-relations reject.
- `candidate_extrusion.rs:648–875`: eight physical lanes, index before append,
  addressed readback, exact bound equality, emission naming admission.
- `candidate_context.rs:775–839`: append-only admission/emission IDs retain
  duplicate occurrence ownership independently of equal bound/cause keys.
- `candidate_extrusion.rs:966–1033`: insertion emission is saved in restoration;
  n=count returns this saved ID; completed child steps retain it.
- `candidate_context.rs:2789–2815,2880–2884`: relation row → scoped flow slot →
  transformer root → raw physical slot; root zero is logical identity and has
  no physical raw slot. Relation ID zero remains an ordinary physical row.

The construction computes key interning, admission, physical append, addressed
read, emission append and driver return. It does not insert desired attachments
into a publish function. `observeCompleted` reads the *current* inventory through
the admission reached by the returned emission, allowing its effective root/raw
to differ from preparation. Its required current read is explicit, not a temporal
preservation assumption. ConstructorAfterAppend's sole phase is represented by
the dedicated Readback construction rather than an extra singleton field.

The ordinary parent/context selection is an explicit cut: parent ID is the one
selected inside `candidate_context_bound_for`, and context is its computed
post-check context or the checked-boundary identity. The model computes the child
key/interner below this cut. The full source/processing-parent resolution,
checked-boundary semantics and executable Rust refinement are **not established**.
This limitation must not be reported as a complete native bridge.

Opaque atoms retain endpoint identities. Eight kind/side/row-or-atom lanes are
represented. Scoped and unscoped success, incompatibility checks, mapped/admitted
difference, logical identity, duplicate emissions and the completed driver handle
are represented. General allocation/resource failure, coverage bits, origins,
HashMap machinery/uniqueness refinement, journals, semantic bundle attachments,
canonicalization correctness, arbitrary interleaving, all FreshUse callers, and
all replay child success/termination remain omitted/open. `DriverReturns` records
only a completed history; it supplies no theorem that a history completes.

## Constructed declarations and intended application

All names below have prefix `YulangClosure.NativeFreshBoundAdmissionR2.`.
Every declared theorem's printed type and transitive axioms are **NOT_CHECKED**:

1. `at_append_new`: append stores the new row at the old vector length.
2. `intern_read`: the computed interner result indexes the supplied key.
3. `append_physical_read`: the calculated lane/index reads the exact appended bound.
4. `identity_has_no_physical_slot`: physicalRaw inventory 0 = none.
5. `insert_of_admission`: successful relation admission computes the complete
   insertion result, new admission/emission indices and addressed readback.
6. `driver_returns_saved`: DriverReturns saved next count returned → returned = saved.
7. `same_bound_from_returned_emission`: successful admission and insertion plus
   completed driver history give Corresponds after.state call returned relation,
   and the insertion inventory's relationRaw agrees with the admitted inventory.
   Corresponds includes exact emission/admission lookups, target bound, admitted
   relation, full FreshUse cause, addressed physical read, and retained readback.
8. `admitted_raw_readback`: exact relation-row/flow-row/raw-row reads compose to
   relationRaw inventory relation = some (flow.transformer, raw).
9. `completed_raw_readback`: Corresponds after call returned relation plus a
   current-inventory relationRaw result gives observeCompleted through that same
   emission/admission, retaining the cause, target bound and physical slot.
   Current inventory/root/raw are unrestricted; no prepared-root equality follows.
10. `duplicate_occurrences_get_distinct_emissions`: two successful sequential
    invocations have different returned emission IDs, even with duplicate bounds.
11. `scoped_admission_reuses`: the actual snapshot/pair/use/transport guards imply
    scoped admission returns the mapped relation without changing the inventory.
12. `unscoped_calculated_row`: resolved ordinary parent/payload/insertability
    derive admission via calculated key interning, including its physical row.
13. `scoped_nonidentity_branch`: explicit model reduction with mapped/admitted 1,
    physical flow/root 1, raw release 0; this is not a native execution receipt.
14. `unscoped_mapped_admitted_differ`: explicit model reduction with mapped 1,
    admitted 2 and logical root 0; this is not a native execution receipt.

Apply 11 or 12 to the actual admission branch; apply 5 and 7 to its insertion and
saved driver handle; apply 8 and 9 to the current inventory read. Apply 10 before
associating another duplicate ordinal. Ordinal is attached to its invocation and
returned handle, never recovered by endpoint-set equality or admission-cause
uniqueness. The native cause has no ordinal field.

Parent application: this supplies a candidate local evidence-association slice
inside native FreshUse. It constructs no sourceJudgment or sameScoped witness
for arbitrary s,x,d,a. First remaining local owner premise: authenticate actual
ordinary-parent/post-check-context inputs and actual completed inventory/evidence
history against candidate_context_bound_for and restoration's driver. Luna owns
the native recorder and independent source correspondence intake. The temporal
prepared-root theorem, all-route FreshUse correspondence and the complete source
clause/publication/use/shared-witness bridge stay OPEN with their existing owners.

## Actual commands, checks and resources

Actual read commands: bounded `cat`, `sed`, `rg`, `pwd`, `wc -l`, `sha256sum`;
Python was used solely to edit the leased Lean file. All returned exit 0. Initial
large reads truncated; decisive branch, guard, constructor and parent sections
were reread in bounded windows. No check failure or runtime receipt is hidden.

**No Lean/Lake/version/checker/test/build/Cargo/formatter command was run.**
Pinned configuration read: `leanprover/lean4:v4.35.0`; no external packages;
project lean options `-j1`, `-M1024`. Actual executable versions UNKNOWN.
Kernel acceptance NOT_CHECKED. Full printed theorem types NOT_CHECKED.
Axiom results for every declaration NOT_CHECKED. No self-certification.

After ACCEPT_FOR_BOUNDED_CHECKS, Luna is sole verification/cache owner. Within
its one 180-second Lean attempt, use the skill checker on module
`YulangClosure.NativeFreshBoundAdmissionR2`, explicitly requesting all fourteen
names above, an isolated project and resolved pinned Lake. The checker must print
each actual type and full axiom list; no default-build-only inference is valid.
If this frozen construction fails, preserve diagnostics and close incomplete per
the fixed contract; do not silently repair/run another attempt.

One reasoning lane; up to three independent lightweight read calls in a batch;
no heavy process. Exact CPU/RSS unmeasured. Last observed UTC during construction
08:11:24; 700-second grant was not enlarged. No caches/generated/scratch outputs.

## Dependency hashes and stop receipt

Verified against contract with sha256sum, all matched:

- scheme `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`
- context `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`
- extrusion `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`
- effect `1715046b29b760fe70b3c2fb05665dad23e7f95ad05883c39d06d4da37b925ab`
- source `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`
- shadow_apply `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`
- term `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`
- lib `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`
- Contracts `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- NativeFreshScopeTransport `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5`
- NativeScopeTransformer `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`
- OriginalEffectHygiene `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f`
- lean-toolchain `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`
- lakefile `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`
- lake-manifest `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`
- README `8d27e0b90fc04eb8a0a30606a857e564e5269e8e33e72fddbf1190cb6a7072e3`

All seven authority/manuscript/progress hashes also matched the exact contract
values in the retained command output. No alternate baseline or R1 proof was used.

STOP: both leased paths frozen; writes stopped on this handoff submission.
No descendants or unresolved generated-output leases. No permission to execute
was assumed. Next step is Luna's fresh phase-1 source review of these exact bytes.

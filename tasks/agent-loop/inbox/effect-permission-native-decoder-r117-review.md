# R117 independent frozen-artifact review

Verdict: **REJECT / BLOCKING**. The candidate adds checks at the intended private projection owner and consumes its fields in existing inventory assembly, but the frozen patch is malformed, contains a static Rust pointer-type error, and adds an invalid equality between two numeric namespaces. No production or proof gate is closed.

Assignment `/root/r117_review`; independent read-only compiler review, no descendants. Only this review receipt is written. The Rust handoff was read after inspecting patch hunks and their baseline suppliers; its explanations are not evidence for the findings.

## Frozen identity

Actually verified with `sha256sum`:

- Patch `tasks/agent-loop/artifacts/effect-permission-native-decoder-r117.patch`: `881a57716460266581d674eb9490908ea462a8840ba5b9923e6b37c8d5e04b13`.
- Rust handoff `tasks/agent-loop/inbox/effect-permission-native-decoder-r117-rust.md`: `da5bf1fbdb1c7e242a86f03eab3ecfc97476f68922294812d8b5e368b98cb9ae`.
- Proof map `tasks/agent-loop/inbox/effect-permission-native-decoder-r117-proof.md`: `0d5d17927a9b1cd2c7c72fb8b1ba0f7be44c146f7057cd1730b1b31dfcd32e53`.

Authority: `tasks/agent-loop/sprints/effect-permission-native-decoder-20261102-r117.md`, fixed outcome and immutable source pins. Baseline exact-path reads use commit `d177c46ec61fcadd70a3d587c2f8934f6bc91f46` exclusively: `candidate_receiver.rs` (contract SHA-256 `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2`), `candidate_effect.rs` (`1c80c55c62b724b9d2080bd2ddcdabfa35a5ba641c1bf45d9735dfd7fd05be41`), `candidate_source.rs` (`96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`), and `lib.rs` (`c43fcc4f39e4ba8bfea10aa39879c37973100d9f4b8bdef71fa5b3dc3fae01df`). These baseline hashes are contract pins, not independently rehashed here. No dirty Rust source was read.

## Findings

### BLOCKING R117-1: frozen bytes are not a valid unified diff

Exact location: patch line 4, first hunk `@@ -230,5 +230,9 @@`; its body at lines 5–12 contains four old/context lines and four additions, hence old count 4/new count 8. The next hunk begins at line 13 before the declared counts are satisfied. Independently, line 13 declares old 8/new 12 while its body at lines 14–24 contains old 7/new 11.

Concrete failure: an ordinary unified-diff consumer cannot consume these bytes as the declared hunks; the artifact cannot serve as the contract's exact patch candidate against the pinned baseline. This is a static count finding, not a patch-application receipt.

Violated clause: R117 fixed outcome requires a unified diff against the pinned `candidate_receiver.rs`.

Minimum closure: correct all hunk ranges/counts against the immutable baseline, freeze the resulting artifact and hashes, and obtain review of the corrected bytes. Merely describing the intended changes in the handoff does not repair the delivered patch.

### BLOCKING R117-2: permission pointer comparison has different indirection levels

Exact location: patch line 39, added `std::ptr::eq(permission, self.catch.permission)` in `InventoryPackage::internal_root_view_from`; baseline lookup at `candidate_receiver.rs:1860`. The package declaration at baseline line 1248 is `permissions: Vec<(usize, &'a FormalEntryPermission)>`. Destructuring `self.permissions.get(...)` yields `permission: &&FormalEntryPermission`, while the new catch field is `&FormalEntryPermission`.

Concrete failure: `std::ptr::eq` requires both arguments to coerce to the same `*const T`; the first argument addresses a stored reference while the second addresses the permission object. The added expression has a static type mismatch in the enabled `shadow-apply-candidate` configuration. Baseline inventory checks such as the provider emission comparison explicitly dereference the borrowed inventory payload before `ptr::eq`.

Violated invariant: the fixed outcome must authenticate the actual retained permission object and produce a concrete Rust patch candidate; a pointer to an inventory slot is not that object's identity.

Minimum closure: compare the actual borrowed payload, e.g. `std::ptr::eq(*permission, self.catch.permission)`, then freeze/review corrected bytes. Compilation remains unperformed and requires a separately authorized execution envelope; this review claims static type reasoning only.

### major R117-3: permission storage position is incorrectly equated with formal registration

Exact locations: patch lines 92–99 in `ProviderNativeContextProjection::capture`, especially `*index == retained.registration` and `*permission_index != retained.registration`. Related pre-existing downstream assumption: baseline `candidate_receiver.rs:1860–1862` indexes `permissions` by registration. Owning supplier: baseline `candidate_effect.rs:387–390` enumerates the separately packed `formal_entry_permissions` vector; lines 1785–1821 construct/push records only for nonempty concrete rows. Baseline `candidate_source.rs:1323–1327` schedules FormalEntry from the actual parameter registration. The authentic lookup at `candidate_effect.rs:462–474` selects by `permission.registration`, independently of storage position.

Counterexample trace: register an earlier formal that has no nonempty concrete entry permission, then the annotated computation formal at registration 1. Its first retained permission occupies storage position 0 and correctly carries `permission.registration == 1`. `internal_formal_entry_permission` and the baseline source projection's registration-based uniqueness lookup can authenticate it. The new provider-capture filter rejects it because `0 != 1`, returning `MissingInternalCertificate` despite genuine source/native evidence. Thus this change propagates a downstream inventory assumption into a projection that previously did not require it; checking more metadata does not repair the cause.

Violated clauses/invariants: R117 same formal registration/owner and prohibition on fabricated IDs; owner-qualified source identities must not be replaced with accidental equality of independently allocated ordinals. Availability of the private projection must not depend on unrelated preceding registrations or permission retention density.

Minimum closure: retain the real storage index separately, select uniquely by the record's registration, and authenticate the inventory consumer by that retained index plus actual record identity and registration. Remove the pre-existing registration-as-storage-index assumption at the touched consumer seam rather than copying it upstream. Supply a static trace or later focused authorized check with unequal registration/storage indices. This correction is within the exact join, not a request for unrelated refactoring.

## Attacks and evidence limits

- Different owner/state: added experiment/batch/live-context pointer checks match the intended R54 owner boundary. Existing capture also checks incidence use, Lambda origin/facts, Internal route and actual emission/admission pointers. Equal local indices alone do not bypass those reads.
- Same spelling/distinct operation: added complete `SourceOperationId` equalities connect origin declaration, provider and selected arm. The baseline same-spelling test `candidate_receiver.rs:5718` concerns ordinary Forward behavior; it does not exercise the new projection checks.
- Wrong endpoint/missing provenance: baseline provider capture requires `AnnotationMember`, exact view pointer/index, closed tail, selected member family, `ViewOrigin::Operation`, provider occurrence and declaration pointer. The new member/family fields flow into `InventoryCatchRequest` and are consumed by `internal_root_view_from`, whose successful result is required by `InventoryPackage::capture`. They are not disconnected metadata.
- Observer failure: the changed functions return only existing private `Option`/`CurrentEmissionGap` failures and read shared borrowed data. The pinned call structure routes inventory capture through the private observation accessor, not ordinary inference. No solver mutation, restoration change, new constraints or suppression branch is introduced by the shown hunks.
- Numeric namespaces: native member/view coordinates remain decoded through the actual view; the permission-index/registration conflation above is the demonstrated defect.
- Pinned receiver tests at lines 5703–5798 cover native suppression, same-spelling forwarding, grouped scrutinees and ordinary candidate admission controls. No test in that module exercises the new projection assembly or unequal permission-storage/formal-registration indices. No tests were added or run.

The proof map honestly labels its proposed fields/branches as not independently inspected frozen patch evidence. Its Lean supplier claims were not kernel-checked or independently re-proved here. The review's source evidence is the exact four permitted baseline blobs and frozen patch, with the sprint contract as the scoped governing authority; no broader authority or theorem closure is inferred. Source/native correspondence, R114 transport, R116 kernel acceptance, whole-language soundness/effect hygiene, principality, termination and production remain OPEN. No minor findings are asserted.

## STOPPED receipt

Review completed within the bounded 180-second assignment; exact resource telemetry unavailable. Commands were read-only `cat`, `sed`, `rg`, `nl`, `head`, exact-path `git show`, and `sha256sum`, plus writing this sole leased receipt. No patch application, source edits, tests, build/Cargo/compiler, Lean/Lake/checker, scratch/cache/worktree, environment exploration, Git mutation or descendants. Writes STOPPED at this receipt. Required next owner action: primary adjudication and a corrected frozen candidate; this reviewer has no integration or promotion authority.

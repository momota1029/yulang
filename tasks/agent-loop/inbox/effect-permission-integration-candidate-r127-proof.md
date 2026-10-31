# R127 source-to-proof premise audit — revision 2

Assignment `R127-PROOF-1`; sprint
`EFFECT-PERMISSION-INTEGRATION-CANDIDATE/20261102-R127`.
Outcome: **bounded frozen-target premise audit; conditional mathematics and
NO_AUTHENTICATED_LOCAL_TRACE unchanged**. The minor line-count receipt
discrepancy is resolved against authenticated implementation revision 2.
No theorem, model, axiom or source
artifact is constructed. Independent review and primary adjudication remain pending.

Worker `/root/r127_integration_proof`, sole author, no descendants. The primary's
NEW_TASK is the current-session assignment/activity receipt. Effective model
and effort metadata were not supplied and are UNKNOWN. Exact sole write lease:
`tasks/agent-loop/inbox/effect-permission-integration-candidate-r127-proof.md`.
Bound: 300 seconds. This packet explicitly prohibits the skill's normal Lean
execution workflow; NOT RUN below is a scope restriction, not a tool failure.

Revision 2 is the primary-authorized discrepancy-disposition update only.
Prior frozen proof revision 1 is retained by exact identity/SHA-256
`0b6930e8088c5a72c701833326f265314c41a271c1f56692dace0e3fc32ead51`.
Its original finding is preserved verbatim below. All target-specific proof
conclusions, source pins, theorem premises and execution limits are unchanged.

## Authority, original statement and authenticated inputs

Read root AGENTS, preserved map, goal-driven sprint rules, current assignment,
handoff protocol, the Lean proof skill and both references, sprint skill's leaf
boundary, design-authority, and R127 contract/manifest/admission. Relevant
original sources were actually read: effect-hygiene policy
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2;
top-level inference principles §1.1; original preservation manuscript
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5; and
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. The latter
replaces cross-level SCC qualification with the fixed Value-birth-level
induced graph. The old §5 cross-level helper is historical, not a current-rule
counterexample. No research draft adds semantic authority.

Original parent `YulangClosure.SourceProblem.InferenceSoundness`,
`notes/theory/lean/YulangClosure/Contracts.lean:128`, is a **definition**:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

`SourceScopedCoverage`, `PrincipalCoverage`, `NativeCorrespondence` and
`InferenceTermination` are separate roots at lines 133,138,147,152.
`docs/yulang-whole-proof-closure-ja.md` §§1,3–4 retains all accepted source
constructors, lexical scopes and one shared witness. Original A/B preservation
still ranges over every supported source program, lawful finite construction
history and actual retained extrusion occurrence, with complete Call, effects,
generalization/use and correlated evidence. No theorem here establishes these
concrete roots. Contravariant permission remains distinct from actual inflow
and residual: otherwise compatible `[signal,write]` inflow remains admitted
under `[signal]` permission and its write residual is preserved.

Fresh `sha256sum` commands exited 0 and authenticated these actual bytes:

| Input | SHA-256 |
| --- | --- |
| R127 contract | `aa6cb58fb8c728ff021a87b9e86ea9ce2251142bee283928816e97848317996a` |
| R127 manifest | `04566bb0f82e2d34bf4f6e843aa0534c193d37f1a87326066c298e2cabec9cce` |
| R127 admission | `3fcc4c15282ffb7b4ddfd9be9ced286ee03a8ed21db8eb8b19bfcf28d1c1787b` |
| R127 implementation handoff r1 | `fcf18bb16471edf61518905230599c554a1fb1c5c3d345c6164318d53d87e9ef` |
| R127 implementation handoff r2, discrepancy correction | `8f8765112bc5ca721053fdefaa66abf10919c5961315f4c6120fa8fd1f4d62c3` |
| R111 corrected handoff | `54a79a1b4f49d75b78bd3c3e96ff2c317941c57e24dfbad6e2c441309f131d9d` |
| R117 patch | `c3858b35433433806e7f8a01f27c12ab5491a8116e6e88c2b1e32a6ccf5beab1` |
| R119 patch | `5bc02af31d3c80ecae3848760b8723195dd568a7bf924cfc8b3b614b1227a18a` |
| R120 source / proof | `0c503338c144eab1feb2fce128227a7409f312b947876cd504f5b1af9fd1050e` / `2ce7eaba1483c4f9d5c190977421717125aa55b37c5764ee75b7b834d2da9415` |
| R121 source / proof / reviewed outcome | `b016a0249755607b698c20c0516821b1119d01dd44f7daf1c4d5d9cf18fb09f1` / `c9d331b6b4aa5f25892fe2041821a5c7eb9330241c955b2746a6858ca580b575` / `0e910bde2b5c3bc552a09a9c19172f3c9cf492628b673b9b50f72c09aab400b1` |
| R126 source r3 / proof / reviewed outcome | `a6bd6db65a2d3a2c92a8adad0d501e176b9a35bd646deb4e241c31faf66f7e27` / `36f18bb7b09e73451dce28497a83d8bb3b5ec5a951fcb4fec6a08e14b7fdca18` / `6d278bdbcf864d87a99f0b2f502754ea045f3ba4e2c197197166bd732499f1a9` |
| R39 module | `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e` |
| R119 module / proof handoff | `f0d3d9c51a270b19f24acaf6edecec0885dda1fd1b2718db88dd4105db6a343f` / `cd7f488faa9bc3ae5670fa3dfc3ab050a19e0ec8f772a5003f0125bf6b891c6d` |
| R118 / R45 / R116 modules | `2ebb7797c683b2bbf51d746f89d58d9abc4be66b5520fe6c0f4c6007a70d82ab` / `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f` / `2aed350468964d90d8d83714177fff77d477e3df0846ae23150194bd76270e3a` |
| Contracts | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| Effect policy / birth-level correction / original manuscript / whole-proof manuscript | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` / `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` / `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` / `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5` |

Baseline pins are inherited from the authenticated manifest, not fresh Rust
blob inspection: current `b5f4df2509ad9c8dba311a6139354bc3f7d33404`, original
Rust `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`, R126
`e4570173a19ed72f6257fa391032f153ca43943d`, R39
`1f5835c276143537ec58ed81db96c7c108cea8e7`. The manifest records identical
base lib/receiver/effect hashes across the first two baselines. No live or
dirty Rust source was read. Historical R120 receiver target
`108a50b5ed8aaa4813fa42ec4372d72dab4f67d4a158e7f551b8672ca3b9f470`
is explicitly **not** assumed to be R127's combined target.

## Constructor → borrow/capture → indexed consumer

These are frozen R120/R121/R126 source locators, not yet locators in R127:

1. Baseline `candidate_effect.rs::candidate_formal_entry_annotation`,
   1762–1828/1834, reads the exact annotation/registration/owner-local Lambda,
   enforces PRE absence, prepares the complete ordered concrete vector with
   duplicates, processes the optional symbolic helper and pushes the permission.
   Empty concrete and symbolic-only annotations remain admitted without a
   retained permission. At 462–487 internal lookup selects a unique registration
   and borrows `concrete: &permission.concrete`.
2. R126 source r3 authenticates successful helper frame `V1 = V0` and the
   invocation-scoped two-edge provenance suffix, slots 45 then 46, each FactId
   resolving to original typed terms before endpoint canonicalization. If
   `U=T`, the FactId and ordered term pair may coincide; the two distinct causes
   still retain two ordered edges. This is generated-link provenance, not inflow.
3. R120 virtual receiver `ProviderNativeContextProjection::capture`,
   5080–5207, checks owner/batch/live state, internal identities, native
   AnnotationMember view/member and full operation identities. It uniquely
   selects permission by registration, compares retained source fields and
   slice starting addresses, then at 5185–5199 searches that permission vector
   with `.position`, storing the optional member index and borrowed permission.
   Starting-address equality alone establishes neither slice length nor
   arbitrary slice provenance; the constructor's actual borrow is separate.
4. Request assembly at 4871–4887 copies both fields unchanged; borrowed inventory
   copying at 4893 preserves references. Consumer `internal_root_view_from`,
   1870–1901, uniquely selects by registration, checks packed slot and separate
   `std::ptr::eq`, then evaluates the captured optional index via
   `.and_then(|index| self.catch.permission.concrete.get(index))` against the
   captured family. Native/source/formal checks remain additional guards.

Registration, packed storage, native view/member, concrete member and complete
resolved family identity remain distinct. No displayed spelling substitutes
for `SourceEffectId` with resolved arguments.

## Exact existing theorem premises and parent application

The following are inspected **written source types**, not printed Lean types.
All R119 names below have prefix `YulangClosure.PermissionMemberWitnessR119`;
its candidate remains CONSTRUCTED / UNCHECKED.

```lean
-- :57, surrounding {Id : Type} [DecidableEq Id]
theorem indexed_read_member (xs : List Id) (member : Nat) (family : Id)
    (read : xs[member]? = some family) : family ∈ xs

-- :74
theorem same_record_search_read (permission : Permission Id)
    (searchedFamily consumedFamily : Id) (permissionMember : Nat)
    (searched : orderedSearch permission.concrete searchedFamily = some permissionMember)
    (read : permission.concrete[permissionMember]? = some consumedFamily) :
    consumedFamily = searchedFamily ∧ searchedFamily ∈ permission.concrete
```

`search_index_read` at :37 derives the indexed equation from orderedSearch;
`selected_retained_member` at :88 additionally requires successful R118 native
and registration/storage reads. `certificate_member_if_extracted` at :110
requires actual R45 `extract ... = some out` plus search/read on the same
probe permission. None derives Rust evaluation or heap/borrow identity.
R118 `decode` at :67 still uses recursive `contains`; it is not a trace model
of the later indexed guard. R45 `OwnerReads`/:118, `Identity`/:136 and
`extract`/:164 remain concrete extraction obligations.

`YulangClosure.ComputationPermissionEntryR39.constructed_entry_publication`
at :316 takes arbitrary decidable Id, `e,a,f,r,port,s`, and precisely:
`e.formals[a.registration]? = some f`, `a.annotation.row = some r`,
`f.entry = some port`, `Valid e a f r`, `r.concrete ≠ []`. It concludes an
existential shared permission p with successful prepare/permissionFor, full
concrete equality, entry equality and
`publish ... true s = some ⟨s.permissions ++ [p],
s.links ++ symbolicLinks a r port, s.inflow⟩`.
`Valid`/:116 retains exact owner/role/scope/recipe/source-Lambda equations,
recipe-domain and PRE registration absence, and at most one symbolic variable.
`build`/:128 copies the full ordered vector; `symbolicLinks`/:258 records
slots 45 and 46; `State`/:268 has separate permissions/links/inflow.

Applying R39 mathematically to R125's SAME PRE witness and R126's reviewed
frame/provenance equations preserves the local publication conclusion. The
R126 proof froze before its source r3; the reviewed R126 outcome subsequently
authenticates those source equations. They do not identify external inflow,
later consumers, whole-call success/rollback or all-language source judgment.
POST membership never reconstructs PRE registration absence.

R120 **NO_AUTHENTICATED_TRACE** remains exact: the first premise of the stronger
search/transport application is an authenticated interpretation of the actual
Rust vector, full equality and `.position` result into
`orderedSearch permission.concrete providerFamily = some permissionMember`.
Actual projection/request copying, integer conversion, successful get, stable
borrow/state/batch and same physical record require additional correspondence.
Equal Lean records cannot prove a Rust pointer relation.

R121 correctly reduces **local membership only** to the smaller first premise:
the actual successful guard's Rust get/equality must yield
`permission.concrete[k]? = some providerFamily` on that very interpreted record,
index and family. Then the existing `indexed_read_member` application yields
membership without orderedSearch. That interpretation is absent, so
**NO_AUTHENTICATED_LOCAL_TRACE** remains. It does not retire the stronger trace.
For `[4,9,9]`, reads at 1 and 2 both give 9; first search returns 1. Minimal
`[9,9]`, 0→1, disproves only deriving first-match from the local guard. It is
not an executed mutation or source-reachable attack. None/out-of-range/empty or
unequal reads cannot supply the premise. Equal payloads in different records
cannot replace the pointer check. These discriminators are unchanged abstract
arguments, not newly executed counterexamples.

`YulangClosure.SuppressionPermissionR116.selected_endpoint_member`/:110 still
requires SAME R39 prepare/permissionFor, SelectedSource, operationMatch and
provider-endpoint identity; membership alone does not instantiate it. R45
accepted_payload additionally requires successful extraction and identification
with the same probe permission. R114 admission transport, full source/native
soundness, principal coverage, termination and production remain OPEN.

## Frozen combined target comparison and STOP

R111's authenticated historical hunks are lib error-name/private-path repairs,
the effect RowKey import, receiver dereferences and `owns_source_root`.
The Member-root ownership repair reaches a real source-owner case and retains
its exact HIR/module/member ownership evidence; it is not blanket semantic
invariance. R117/R119 historical patches modify capture/selection/indexed-read
evidence. None of these patch texts establishes an operational interpretation
or kernel-checks R119.

The primary supplied implementation revision 1 and its hash; only then was it
read and freshly hash-authenticated. Its complete virtual target identities are:

| Candidate | SHA-256 |
| --- | --- |
| lib.rs | `6eb6b5df29bda1d1bd1fecabcbc2cc6e85e777dda2045f1d1ab86084f64cd84f` |
| candidate_receiver.rs | `335f5f2cd4841dd8288306623ee863606e355b9ceda6948ab6877d944bed3165` |
| candidate_effect.rs | `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01` |

These are authenticated source-lane result pins, not independent reconstruction
by this proof leaf. Its four R111 receiver replacements plus all six R117 and
six R119 hunks matched once under full-context ordered relocation. The R111
lib/effect targets are reused; this lane inspected the frozen exact replacement
hunks and patch bytes, without reconstructing source.

At this frozen target-description level the proof-premise comparison is:

- candidate_effect's only change is the RowKey import. No constructor, symbolic
  helper, retained-permission mutation or provenance expression changes.
  R126 source line locators shift by one from this import. The lib changes at
  11763,11770,18372 do not edit the R126 live-effect term, admission/provenance,
  typed drain or helper-dispatch bodies. Its other pinned source owners are
  untouched. Thus the reviewed successful-helper V1=V0 and ordered slot45/46
  equations, including U=T, retain the same textual dependencies; no extra
  R39 premise is introduced by these hunks. This is static dependency evidence,
  not compiled control-flow or whole-call acceptance.
- R111 receiver repairs occur outside the consumer/search/request expressions.
  The exact R117/R119 full-context payloads survive in the reported target.
  Capture still stores `.position`'s Option with the same borrowed permission;
  request copies both; the consumer uses `.get` on that captured permission
  with the separate selected-record pointer check. R121's short-circuit
  argument and minimal read premise therefore retain their expressions.
  R119's list theorem types and successful-search/read premises do not change.
  R111's Member-root ownership case remains actual owner evidence required
  for R45; the candidate does not establish its Lean interpretation.
- Relative to R120, R111 removes three receiver lines at its ownership match;
  the later capture/request chain shifts by three lines. R127's per-stage
  ranges authenticate R117 hunk6 at 5144–5186 and final R119 hunk5/hunk6 at
  5170–5188 / 5190–5197, rather than reusing R120's later line numbers.
  Consumer member payload ends at final R119 range 1881–1889. The exact
  constructor→borrow→capture→copy→get path above is preserved at these changed
  receiver coordinates; no new source behavior is inferred.

**RESOLVED / minor finding — line-count receipt discrepancy.** The primary
supplied implementation revision 2, whose complete handoff hash was freshly
verified as `8f8765112bc5ca721053fdefaa66abf10919c5961315f4c6120fa8fd1f4d62c3`.
It corrects only the reported receiver total to **5,872 lines**, so
`5875 − 3 = 5872` agrees with the R111 4→1 hunk. The receiver bytes/hash remain
296,602 / `335f5f2cd4841dd8288306623ee863606e355b9ceda6948ab6877d944bed3165`.
This resolves the receipt arithmetic; it adds no source execution, independent
review certification or proof correspondence. Actual update checks were
read-only `sha256sum` and focused `rg`, both exit 0, plus an edit to this sole
leased handoff. No source, execution or Git action occurred. Writes STOPPED
again at revision 2 freeze.

Exact revision-1 finding history, retained as historical text:

**UNRESOLVED / minor finding — line-count receipt discrepancy**, returned to
primary: R120 records 5875 final
receiver lines, while R127 records 5873. The R111 four receiver replacements
have net line delta −3 (the single 4→1 hunk), so those reported final counts
differ by one from that delta. The byte delta 296776→296602 is −174 and agrees
with the R111 byte delta 292001→291827. This proof leaf cannot reconcile the
line-count convention without authorized reconstruction; fresh independent
review must resolve the counts. It does not alter the literal patched guard
or establish a hash mismatch. No false source counterexample is asserted.

First substantive proof premise remains R121's same-record get/equality
interpretation (native decoder/projection correspondence owner through Luna);
the stronger R119-AUTHENTICATE-MEMBER-TRACE-1 additionally retains position and
field transport. A new authorized operational proof packet, not another list
membership lemma or assumed FaithfulDecoder law, is needed. R111's private
aggregate 6 GiB gate and unused compile allowance remain primary-owned and unmet.

Actual commands: read-only `cat`, `sed`, `rg`, `sha256sum`; all completed read
command exits were 0. Initial broad output truncations were followed by focused
relevant-source reads. One apply_patch update failed its exact text-context
check and made no change; a focused patch corrected it. `apply_patch` writes
only this handoff. On-disk metadata read:
`leanprover/lean4:v4.35.0`, library YulangClosure, `-j1 -M1024`, packages `[]`.
Actual executable versions, goals/diagnostics, printed theorem types, all
`#print axioms` outputs, kernel acceptance and skill checker: **NOT RUN /
UNKNOWN**, explicitly prohibited. No historical receipt is relabeled fresh.

No Lean declaration/model/axiom, build/test/compiler/checker/Lean/Lake command,
source/test edit, Rust blob reconstruction, filesystem patch application,
scratch/cache/copy/worktree/generated output, environment/storage probe, Git
operation, dirty/quarantined read, child or background process occurred.
CPU/RSS/exact elapsed telemetry were not instrumented; no measured spare budget
is claimed. Only this handoff changed. Writes STOPPED at final freeze; no
descendants or unresolved generated outputs. This is a proposed research
handoff, pending independent review and primary integration.

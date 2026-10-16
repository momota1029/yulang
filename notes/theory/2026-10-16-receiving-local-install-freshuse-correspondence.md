# Installed local g: native capture and FreshUse correspondence

Date: 2026-10-16
Packet: resident dispatcher P1; worker `/root/runtime_source_supplier_proof`.
Status: frozen bounded constructive native operational derivation; bounded
static `compiler_referee` review R2 was CLEAN. No source T, eligibility
theorem, implementation repair or parent promotion.
Baseline: `d7e85a25f90d5ea23ee1c64e805d66c612aaa6f9`.
Exact leases: this note and `tasks/agent-loop/inbox/20261016-loop-a-proof-001.md`.
Method: invert actual constructors and induct over successful owner transitions.

## 1. Frozen statement and exclusions

The original component is unchanged:

```text
receive(f:Unit->alpha+) = let g=f(Unit) in g(Unit)
alpha+ = ([ctrl]Unit)->[ctrl]Int.
```

The [preceding supplier note](2026-10-16-runtime-receiving-formal-source-supplier.md)
found that this exact annotation is rejected before candidate collection.
**This note does not claim that the rejected source reaches Install.** Its
claim is conditional on an authentic ordinary-mode schedule reaching the
actual unannotated Install / nonrecursive local Name / Apply owners.
That native premise supplies no missing source reachability or checked T.

Fix any well-formed exclusive candidate InferenceSession with feature
shadow-apply-candidate and scoped_experiment=false. Fix original source owner,
g's HirLocalId l/slot s, initializer endpoint e1, boundary b, Name occurrence
n_g/value component v/use level h, and later Apply c2 with that Name callee.
Keep c1/e1, n_g and c2 occurrences, causes, binder identities, result/effect
coordinates and source resolution distinct. Let r be the canonical native
ValueRow obtained from e1's positive endpoint at the actual successful Install.
Do not require later representative identity to keep the same numeral.

For EVERY such actual finite successful ordinary local route followed by
its Apply action, derive that the installed root is retained, one capture G
and one coherent FreshUse F provide all mapped operands, all captured-bound
restoration precedes the Name consumer link, and route publication follows
all final fallible steps. For returned mapping/restoration/link failures,
derive that no successful local route is published. For the private test-only
pause, derive retention without a successful route; no pause is executed here.
G/F are actual constructor outputs, not supplied source-validity certificates.
Quantifiers include all actual graph bounds, relation fibers, shared/fresh
rows and successful representative changes within this native scope.

Hypotheses are authentic state/inputs, exclusive session ownership and the
stated successful finite transitions. They do NOT include conflict absence,
source membership or solved unknowns. Native propagation can return with
retained diagnostics and symbolic constraints. No actual provider/world/
private-contract witness is chosen. Native operational hypotheses cannot
be used to claim source T for the original program.

Excluded: arbitrary process kill/panic or concurrent mutation, termination of
all routes, missing native generation, semantic duplicate redundancy, all future
replay, complete nonidentity-context meaning, source eligibility/generalization,
MODEL, source T, complete Call, runtime import, soundness/principality and F5.
No source scope, provider or residual lineage is merged to establish this claim.

## 2. Governing results and exact native entry

Top-level inference principles §§1,1.1,3–5 retain ordinary native accumulation,
propagation, levels/copying/intrusion and necessary abnormal safety. They do
not require full internal rollback. The selected [source ResultBind](../design/2026-10-16-source-result-bind-projection.md)
§2 and [its construction](2026-10-16-first-call-result-binding-projection.md)
§§2–4 govern the separate semantic fields in §7.

Reuse the independently reviewed [replay completion bridge](2026-10-16-extrusion-replay-capture-completion.md)
§§2–5 for queue-covered emitted work, typed-drain completion and actual replay
acknowledgement. Its missing-generation, semantic/context, source reachability
and full H2/U exclusions remain. The inspected current calls below use those
same actual drain/acknowledgement owners. This packet adds the installed-local
identity/map induction; it does not restart hygiene or promote that theorem.

`candidate_source.rs::emit_candidate_source` preallocates slots from authentic
bindings (:610–617). Block work order (:750–760) visits initializer, Install,
then the final expression; Apply visits callee/argument before Finish
(:709–712). Work::Install (:825–846) emits the original initializer-effect
link outside the generalized value and unannotated Action::Install(s,e1,b).
The later resolved local Name emits Action::Local(s,n_g,v,h) (:960–974), and
c2's Finish emits its Apply action (:1008–1049). This establishes the actual
source-schedule order, rather than assuming independent transitions.

The source driver (:1311–1354) changes Install to Stage::PublishLocal with
the actual positive exposed endpoint, invokes install_candidate_local_term,
and advances source.next only after success. The direct Action adapter
(:1377–1379) uses those same Install/Local owners.

## 3. Installed root and original ordinary-region facts

`candidate_scheme.rs:1476–1500` requires a ValueRow, obtains l from the
original locals[s], rejects an absent/already filled destination, and writes
LocalScheme{capture_region,id:l,root:r,boundary:b}. `value_endpoint`
(`lib.rs:11503–11532`) canonicalizes component/live rows. No alternate root
or provider is chosen. The local-use path reads this installed record and
does not rewrite it; capture occurs against current live bounds at USE time,
not a saved initializer snapshot. This is exactly native root retention.

Ordinary mode's actual region data is bounded more narrowly than source
scope preservation: candidate_source::region returns the sentinel usize::MAX,
computation_scope does not fill occurrence_regions (:58–84), and the local
initializer records local_regions only under scoped_experiment (:819–821).
Thus capture_region=None and caller=None; capture frontier and owned regions
are empty, F.scope_remap is default and F.scoped_relations is empty. No ordinary
source-region correspondence is supplied by those absences or the sentinel.
Original source binders remain required inputs of the separate semantic bridge.

## 4. Derive one capture and coherent reconstruction map

`route_candidate_local_run` (:1515–1570) starts the actual transaction. When
no LocalUse is retained, it reads the SAME (r,b,l,capture_region) from s,
captures G once, prepares F once and retains both together with
(s,l,n_g,v,h,cursor=default). Before stepping/resuming it checks s,n_g,v,h
against that parent. Every temporary pop pushes the SAME parent back before
error, pause or completion can return. Stepping borrows &frame.fresh;
it changes the cursor, without rerunning construction or replacing F.

Capture::intern canonicalizes and memoizes each polarized endpoint once
(:348–362); Capture::row memoizes representative RowKeys and records
local iff level>b && !non_generic (:364–392). capture_candidate_graph_inner
(:808–950) sets G.live_root=r, G.boundary=b and the positive root from r,
then closes pending structural nodes/local rows and contextual payload tails.
Nonlocal rows stop at their live shared anchors (:644–650); this says nothing
about absence of their mutable bounds. Captured bounds retain kind, side,
original BoundKey, relation and evidence index (:597–642). Relation is part
of the dedup key, so distinct relation fibers are not merged by equal endpoints.
Original relation attachments/bundles and payloads remain separately retained.

prepare_candidate_fresh_use (:1104–1378) creates ONE nonzero context_use u.
Its single canonical_rows dictionary maps each current source representative
q to q' exactly once: fresh at h iff captured local && current level>b &&
!non_generic, shared q otherwise. All F.rows entries and both polarities'
terms reuse that map. Function reconstruction uses the same F.terms and actual
four original children/polarities; cycles terminate through preallocated rows.
This establishes coherent native copying, without proving source eligibility.

One view_remap keyed by (old view ID,mapped tail) is shared between all
mapped effect operands and context payloads (:1158–1231;
candidate_effect.rs:917–933). Allowance/Support/AnnotationMember keep their
own constructors; Contribution keeps its original effect/origin with its
native instance. Original bundle occurrence/sets are copied once per original
bundle into F.bundle_remap. Those are native attachments, not provider proofs.
One weight_remap validates both payload views; one context_remap reconstructs
all original relation contexts. rename_contexts_impl (:1464–1580) validates
original handles and strictly earlier children, reconstructs each constructor
and requires every referenced substitution. Fresh rename has no certificate
substitution and rejects unsupported certificate cases rather than inventing
entry authorization. A failed rename removes its tentative map entries and
rolls back its own context checkpoint.

Each captured native evidence snapshot is imported once in original order
into F.evidence_remap. F is returned only after ALL construction succeeds,
then retained unchanged. Later canonicalization can follow new representatives;
it does not rerun F or choose new maps per bound. This is native coherence,
not a source substitution theorem over xi=(nu,K,D), worlds or private telescopes.

## 5. Ordered restoration and activated final link

Induct on LocalUseCursor(k,R,complete), initially (0,None,false), using
step_candidate_local_use (:1664–1703):

- R present: step that actual restoration, clear R/increment k only on
  Some(emission); otherwise retain both. Return without attempting root-link.
- R absent and k<G.bounds.len(): begin exactly bound k's restoration with
  the SAME G/F and save R. Do not increment k or link the root.
- Only R absent and k==G.bounds.len(): submit the Name consumer root-link.

begin_candidate_fresh_bound (:1380–1428) maps BOTH endpoints from F.terms/
F.effect_operands and keeps side orientation: Positive gives owner=upper,
item=lower; Negative gives owner=lower,item=upper. A captured relation uses
that SAME u, F.context_remap, original source BoundKey and source sets in
candidate_context_fresh_transport_scoped (:3658–3671), retaining an explicit
Transport/FreshUse witness. Its bundles use F.bundle_remap, and evidence uses
F.evidence_remap at the captured index, source_bound and u. Stored constraints
alone are not assumed activated: the actual next action is physical admission.

candidate_begin_bound_restoration (`candidate_extrusion.rs:695–717`) inserts
the mapped physical bound WITH evidence (:442–670), then retains its canonical
owner/item, original n_g occurrence/cause and saved opposite count m.
Restoration (:733–799) rereads the live canonical owner/opposite at each
saved index j<m and retains the ordered replay. It advances j only after
candidate_context_drive_replay(...,Some(original occurrence/cause)) returns
Complete. The actual child Idle/Running/Ready states validate operation,
ack, drain, occurrence and cause; they run the typed drain and deliver its
completion before advance (`candidate_context.rs:3498–3610`). At j=m the
restoration retires and returns Some(emission), enabling k to advance.

Hence every captured bound's SAVED restoration frontier and queue-covered
emitted children complete before linking. This does not prove all arbitrary
future opposite pairs or missing semantic work are generated or discharged.
Native conflicts/remaining symbolic bounds do not become source proofs.

The final link is exactly admit_candidate_value_link(n_g,0,
F.terms[G.root],component(v)) (:1680–1684). It records actual occurrence/cause
and calls constrain_live_value (:1501–1510). Candidate mode reaches the
actual typed drain (`lib.rs:12031–12088,12285–12305`), beyond merely storing a
constraint. Apply the existing emitted-work completion result within its scope.
No complete source Function/Value membership follows from this activation.

## 6. Commit, failure, pause and c2 consumer

After root-link, final route allocation and resource sampling succeed BEFORE
cursor.complete=true (:1685–1702). finish_route_transaction_with_candidate_accounting
(`lib.rs:9281–9331`) calls commit_local_use only on an Ok operation and a
complete parent. GraphState::commit_local_use (:267–292) transfers the SAME
G/F.rows, s/l/n_g into LocalFreshRoute. Temporary construction maps are
released; their actual transported native relations/evidence stay at their
owners. Map release creates no source certificate.

Preparation before LocalUse push is atomic with respect to owner steps.
Any returned preparation/restoration/link/final-allocation/sample error takes
the transaction Err branch, not commit_local_use. Rollback restores/clears
the parent cursor/frame, truncates local routes to their saved length and
uses native context/evidence/row/provenance journals
(`lib.rs:9206–9211,9461–9482`; candidate_context.rs:1785–1840).
Even failure after temporarily submitting root-link cannot publish that
successful LocalFreshRoute. If rollback/accounting itself errors, there is
still no successful route return. No full capacity restoration or arbitrary
retry claim is needed. Failed Install's post-write sample may leave a PRIVATE
slot outside a transaction, but cannot advance the source action; do not
mistake private partial state for a successful use.

Production route_candidate_local passes pause_after=None. The test-only
Paused branch occurs after a whole owner step with complete=false, retains
G/F/cursor and commits no LocalFreshRoute. It is not a production suspension
or source-admission certificate. No test/pause hook was run. execute_candidate_action
must return Ok before source.next advances (:1350–1354), and run_candidate
calls finish_candidate only after execute succeeds (`lib.rs:10441–10454`).

The later actual c2 Apply uses that original Name component v as its positive
callee (`candidate_source.rs:1008–1049`; shadow_apply.rs:1531–1650). Its recipe
authentication, fresh invocation effect/demand, NativeInterface, submitted
constraint/typed propagation and evaluation/invocation effect links are its
own actual constructors (:1650–1688). Thus the restored Name consumer link
and c2 meet at the SAME v. c2 does not reinstall g or choose another F. This
is an operational endpoint join; complete source Call meaning stays OPEN.

## 7. Source ResultBind fields without a native local counterpart

Compare the selected actual-return ResultBind against the inspected records:

| Original source field | Native local evidence and missing correspondence |
| --- | --- |
| g binding and Apply-owned checking endpoint | Authentic l/s, e1->r, b and actual Name/c2 component v. This is the bounded native join just derived. |
| Same actual return z, current world C2 and return/rebind witness | LocalScheme/FreshUse/LocalFreshRoute have no such fields. Install is a typing action, not executed source Return. |
| Whole J_z with tagged W_z and matching F_R,z plus both lawful maps | G's rows/bounds/evidence do not encode those source operands and their same-z binder. No J_z is constructed here. |
| Actual value/provider/private roots and genuine installed contracts with exact telescopes | Local IDs/native rows are not actual returned provider values or those telescopes. Shape cannot supply them. |
| Original source profiles, K/D, receipt/activity/continuation and compatible history | Native context/effect-view/evidence data is real retained data, but has no established decoding to these complete source fields. Ordinary mode has no retained region remap. |
| Hereditary p_i:ValueMem_A_i(J_z,C2,w), logical Env extension and complete actual/logical dependency classification | No such proof/classification field in this local interface. level>b && !non_generic is not the selected source fixed walk or eligibility. |
| Original alias versus independent-instance strategy and later restriction | One F per native occurrence, with older rows shared, is derived. Agreement with the source strategy/binders remains an independent bridge. |

These are statements about this actual local interface, not claims that all
source identities/evidence are absent from HIR or every compiler subsystem.
The first missing semantic owner/action is the independently typed actual
ResultBind supplier and its source-to-native interpretation BEFORE treating
this native map as a source instantiation. T/context/MODEL and fixed-dependency
evidence remain unprovided. A record with those field names, or native success,
cannot create that evidence. No native implementation defect or new metadata
requirement is inferred solely from the semantic gap.

## 8. Residuals, resources and frozen handoff

No mapping/restoration/publication defect was found within the bounded
successful-native path. The source supplier, T/context/MODEL, source ResultBind
and generalization/eligibility, runtime import, complete Call, soundness,
principality and F5 remain OPEN. Exact annotation noncoverage and scoped
Local-callee noncoverage remain separate; neither source domain is narrowed.

Economy audit: this packet supplies a new native constructor derivation,
not an equivalent attempt at the preceding source T premise. The remaining
source interpretation is A/B; missing retention could be D only where an
already proved fact exists. No reclassification closes the original gate.
Inbox P1-SOURCE-RESULTBIND-001 records the dependent source bridge with its
missing inputs, rather than requesting an invented implementation repair or
another unchanged supplier attempt. Luna/dispatcher select any successor.

Static checks: bounded rg/line reads, read-only git show/diff/status, dependency
hash/live-byte comparison and Markdown integrity. No code, tests/builds/probes,
network, measurements, Git mutation or children. At most three lightweight
read processes per batch; assigned 25-minute cap; elapsed wall/CPU/RAM
uninstrumented. Primary remains sole executable-verification/integration owner.
Same worker reused; requested Sol/high from original launch, observed runtime
model/effort unknown. Configuration reads establish no hot reload or model change.

One fail-fast preparatory command detected the preceding supplier note's
primary-owned review-status update and wrote no files. Its producer SHA was
`413c7639540d1fd5d4e0aa7643072d0014ffbb9ea855fdedf353d048403afd1e`;
current read-only dependency SHA is
`4528791a9020278623fe271c3616c7cec9156d2324f41b68bea37563b33eb90e`.
The prior semantic obstruction is preserved; this leaf never edits that note.
All tracked proof/code dependencies below match assigned baseline bytes at
freeze. Later unrelated HEAD movement is not treated as a baseline switch.
Shared task/board summaries are navigation only, not proof premises.

| Dependency | SHA-256 at assigned baseline |
| --- | --- |
| `notes/design/2026-10-16-resident-research-loop.md` | `3803cacfd8229a5196706783d1168a9dc774a519863ddaa6e595ee1c3c13f5e4` |
| `tasks/agent-loop/README.md` | `ac46d8e8a3e4a7e6181841218593108bf6ecc3b03433d9521419b00a5ec6adeb` |
| `.codex/agents/prover.toml` | `508d33aaa06bdef3d12f74143fb881017a12627c08567b10143ce4b45663c049` |
| `.codex/config.toml` | `7dc1e5d1814b41c87e3dfccc8663f035af0fd8fa3030c8c656725dfd2c98ebab` |
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` |
| `rules/agent-orchestration.md` | `8b418f8ed02606205ecdfedcf5da72dae074e1c799237b8cc034fdfbd71ab7a1` |
| `rules/research-lab.md` | `3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69` |
| `rules/compiler-engineering.md` | `4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9` |
| `rules/git-concurrency.md` | `2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/design/2026-10-16-source-result-bind-projection.md` | `f943e28a57e1a18cb22ec3e63a892f08711a3422293a240b168ea6dba5a082aa` |
| `notes/theory/2026-10-16-first-call-result-binding-projection.md` | `36592df8bc0d0315bbef836438391559ae6e23bfcd44074d7d542c9ea91912a2` |
| `notes/theory/2026-10-16-extrusion-replay-capture-completion.md` | `f286eb3d0280b614caf2a870aa36204ff766241033c9dc49b75f01cde9d87fd7` |
| `crates/yu-solver/src/candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| `crates/yu-solver/src/candidate_scheme.rs` | `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b` |
| `crates/yu-solver/src/candidate_context.rs` | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` |
| `crates/yu-solver/src/candidate_effect.rs` | `44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `7a57a93481095c6e7d4b8781810b1a5aa0d174e41ede29ac3f2b2b96bce10b0c` |
| `crates/yu-solver/src/shadow_apply.rs` | `357b274d0de509931bda3015a99b1a1cf2ac86d75a45d230d62ab456c56740ba` |
| `crates/yu-solver/src/lib.rs` | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |

## Commit packet

- Exact outputs: `notes/theory/2026-10-16-receiving-local-install-freshuse-correspondence.md`
  and `tasks/agent-loop/inbox/20261016-loop-a-proof-001.md`.
- Baseline: `d7e85a25f90d5ea23ee1c64e805d66c612aaa6f9`; no tracked dependency
  hash changes. Prior supplier note's primary-owned review delta is pinned above.
- Review: bounded static `compiler_referee` review R2 by
  `receiving_pair_referee` was CLEAN on this artifact at SHA-256
  `64c332c0bb931e9574f55efeedba36c942e16d2c84dce77363f04ad9a4860fd6` and its
  acknowledged request inbox at SHA-256
  `e01a7c477dfe9c70da102fb90cab9b2b2104aa068d82633da6842398f0ac9ae4`. All 23
  pinned dependencies matched. The review confirms only native Install,
  capture/FreshUse, restoration/link and publication correspondence; source T,
  J_z, context/MODEL, eligibility/generalization, runtime import and parent
  promotion remain open.
- Checks: constructor/restoration/commit/error trace, 23 pinned tracked hashes,
  prior-note hash and local link/fence/whitespace integrity. Zero executable checks.
- Proposed checkpoint: `research: derive installed local FreshUse owner correspondence`.
- Shared deltas left to primary/curator: preserve this one-map/native
  restore-before-link result separately from the original source ResultBind,
  context/MODEL, eligibility/generalization and runtime-import gates.
- Inbox: P1-SOURCE-RESULTBIND-001 revision 1, frozen before notification.
  Intake and successor selection belong to Luna/resident dispatcher.

Writing stops at this frozen handoff for both exact leased paths.

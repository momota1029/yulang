# Exact captured Call: source-base emission supplier audit

Status: independently reviewed bounded source/artifact correspondence audit;
non-authoritative research evidence. No semantic gate closure.
Objective: instantiate or falsify the supplied finite source-base emission certificate for the inner `call(result(name f), result(name x))` in `my apply f = { my step x = f x; step }`.
Method: derive the constructor/lexical rows from selected source authority, inspect the existing producer schemas, and stop at the first absent semantic supplier. No phase-composition probe or compiler behavior change.

## Result and claim class

The approved source supplies the exact constructor and lexical operands. The inspected current producers supply structural rows with pending semantic premises. They do not supply a genuine emitted source-base Call clause, initial independently typed source/descriptor/admission relation, or original joint witness. Therefore this packet cannot instantiate `FiniteSourceBaseEmissionConformanceCertificate` from these outputs.

This is bounded characterization of the inspected producer path plus a minimized omission witness. It does not falsify source-contracts §3.5, prove nonderivability, show that the source is invalid, or establish that no other future construction can supply the certificate. The source interpretation is established by the Authoritative addendum; semantic conformance is not established by this audit. No new language assumption is selected.

## Baseline, exact authority and dependencies

Observed HEAD, read directly from `.git/HEAD` and its loose ref without Git commands: `45fb91e069120f05741a0a4d488e80b38ca59ceb`, `research/simple-sub-intrusion`. This is the live source snapshot, not a claim that dirty inputs equal that commit. The supplied packet permits inspection of dirty source plumbing only as structure. No clean integration worktree was accessed.

Governing sources: `rules/design-authority.md`; Authoritative `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` §§1–4; Authoritative `notes/design/2026-10-05-inferred-function-call-views.md` §§1–5; Reviewed conditional `notes/design/2026-10-05-source-contracts-and-common-allowance.md` §§2.1–2.2, 3.2–3.5, 5.3; reviewed research `notes/progress/2026-10-08-call-type-closure-construction-attempt.md`. Rules `research-lab.md` and `git-concurrency.md` were also read. The initially read dirty `tasks/current.md:2350–2391` is coordination context only.

Accepted decisions retained: block sequentially binds `step`; returning `step` returns an inert captured function; inner `f` is the same outer formal and `x` the local formal; formation is independent of pending Q; source annotations, inferred public types and internal views are distinct; provisional Handler formal treatment does not determine actual supplied callable role/entry. No block reinterpretation, generic Value-entry-implies-Pure rule, or downstream-to-provider protection is introduced.

SHA-256 direct semantic/producer dependencies:

| Path | Hash |
| --- | --- |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/progress/2026-10-08-call-type-closure-construction-attempt.md` | `ab46864eb3639fb7dab81f42b756e94b2c0c6b958475e00bcdfa7a7264e6898e` |
| `crates/yu-hir/src/shadow.rs` | `5a3c61bf87a3f6147897816beea369df49059a49141607af9cca8c720c43386f` |
| `crates/yu-hir/src/module.rs` | `3bb488f9d9e13b43e79e472a65a35197ae4f2c76ae21a6f0f8f77195661f4363` |
| `crates/yu-core/src/lib.rs` | `3a2c2befd0dd38df3c06458a7fd918b8f32124a75d264ed51d859ec036c4ab5e` |
| `crates/yu-core/src/shadow.rs` | `f9d44ae357b0af86db2c17b93bc56d33dd150cb460fab612876f16909f3d9f43` |
| `crates/yu-core/src/shadow_derivation.rs` | `714fa4f53ee14f7a4d4e1d38ff0820157838de9c4b70a266bee1998eb2851dc2` |
| `crates/yu-core/src/shadow_call_formation.rs` | `394c763e5b4e2de6ae692ffacf22c07db8958f00129a47f1332f238c9a8eb5eb` |
| `crates/yu-solver/src/shadow_apply.rs` | `c5e437254f50cafddbd98ef37f2cfa541d1e9388c0d8a0c44c33d1332c2a36af` |
| `crates/yu-solver/src/shadow_candidate_source_crosswalk.rs` | `6e1278aea697f2aabebecbdac5cab62e1001fc1b28ba0046e06f7f6cfe90c60e` |

The full pre-read manifest is `/tmp/call-source-base-emission-inputs.sha256`: six document/context pins plus 101 candidate Rust/source-tool files pinned before the source searches. Only `tasks/current.md` changed at the first recheck: `ee06e32f389daf7e50dc1bbd7c6ba48900de78cf7dba961a08457b8a97228ae5` → `9d90899730d93ee7b0ce9a75d0409546cec3136758429a038727374ebd0896d1`. No inference depends on that moving task text. Final recheck is reported by the handoff.

## Constructed rows and exact preservation boundary

Let `b_f` be the outer `apply` formal, `b_x` the local `step` formal, and `b_step` the local sequential binding. Let `L_f` and `L_x` name their original lexical regions. These labels denote the already approved lexical positions, not new logical binder/evidence objects. The approved containing term is:

```text
lambda(b_f, bind(b_step,
  result(lambda(b_x, call(result(name b_f), result(name b_x)))),
  result(name b_step)))
```

The smallest inner constructor inventory is:

| Row | Ordered operands / lexical resolution | Current structural producer | Semantic emission still required by §§2–3 |
| --- | --- | --- | --- |
| `n_f = name b_f` | outer formal retained inside local closure | `Node::Name` with borrowed binder/use IDs, `shadow_derivation.rs:93–99` | original provider/dependent roots, independent typed read at original state/scope |
| `r_f = result(n_f)` | same `n_f`, no invocation | `Node::Result`, same lines | same returned descriptor/provider/configuration and witness |
| `n_x = name b_x` | local formal | same Name producer | original whole argument/provider relation and independent typing |
| `r_x = result(n_x)` | same `n_x` | same Result producer | same returned descriptor/provider/configuration and witness |
| `c = call(r_f,r_x)` | callee first, whole inert argument second, under the local body | `Node::PendingCall`, `shadow_derivation.rs:101–119` | actual receiver/receipt/entry/body/consumer/return clause, with shared `xi=(nu,K,D)` and original joint witness |

Lexical identity preservation is a conditional code-inspection result: assuming the validated retained skeleton exists, `captured_call_input` checks callee binder = outer formal, argument binder = local formal, returned binder = local `step`, and exact capture incidence (`yu-hir/src/shadow.rs:2229–2322`). `generate_captured_from_skeleton` then reborrows those very IDs and lambda/body references (`yu-core/src/shadow_call_formation.rs:309–377`); `IncompleteDerivation::project` passes the same borrowed IDs into Name and PendingCall nodes. No freshening occurs along those paths. The containing lexical capture is preserved as identity; these paths do not construct or prove preservation of logical binder scopes, descriptor/admission clauses, `xi`, or a semantic witness.

Actual HIR retention agrees only at this structural level: `module.rs:2471–2499` resolves callee to the outer parameter and argument to the local parameter, retains an Apply with its existing errors, and stores the outer capture. `ResolvedExpr::Apply` explicitly keeps semantic lowering pending (`module.rs:443–454`). No source acceptance is inferred.

## First absent supplier and minimal witness

The first unsupplied input is the finite **decorated, independently typed** source graph/kernel, starting at captured Name `f`'s original provider/view/descriptor and source-typed initial admission. Lexical resolution supplies `b_f`, but Authoritative call-view §5(1–2) still requires the exact shared formation and formal/use refinement judgments. Source-contracts §2.1 assumes independently typed primitive/owner/view kernels; §2.2 assumes active joint `M_E`, `A_E`, and independently interpreted `DescMem`; §3.3 requires initial source-typed context and joint dependencies. The scoped source-view locator explicitly retains these unresolved inputs (`shadow.rs:1295–1341`). This is the first semantic supplier boundary, before descriptor preservation can be proved through the Call.

At the implementation boundary, the Call-emission producer itself is also missing from the inspected outputs. `PendingSourceBaseStub` contains exactly three borrowed identities (`shadow_call_formation.rs:161–165`). `PendingSourceCallStub` adds the argument-expression identity and optional argument-use identity, still without a relation or witness (`:83–88`). Both return the same four unresolved categories (`:34–38`):

1. complete emitted original Call clause and joint witness;
2. initial source/descriptor relation;
3. finite source-base emission-conformance certificate;
4. complete invocation interpretation.

Minimal omission witness: restrict the approved program to the five rows above and its already fixed two-formal lexical context. The successful structural projection ends in `PendingCall` containing only `source`, two local child offsets, pending premise lists and capture incidence (`shadow_derivation.rs:158–166`). This value can be constructed by that function without constructing any emitted `E` clause, `A_E`, `DescMem` proof or `w`; its constructor takes none of them. This is a concrete schema-level witness that successful structural construction does not certify clause existence. It is not a competing source-semantic model or a runtime counterexample. Removing either Name/result branch no longer witnesses this exact two-operand Call cut.

The adjacent emission code does not fill the hole: `CandidateRelation::Apply` stores callee/argument endpoints and result index (`shadow_apply.rs:449–458`), and the captured emitter retains that recipe (`:493–521`). Its consumer submits an endpoint Function demand with experimental bottom/empty effect endpoints (`:832–865`). It does not emit the whole-tuple source-base Call inventory. Its API explicitly keeps source typing/admission, whole carrier compatibility, role/entry, complete invocation and scope transport unresolved (`:6–49`). This schema inspection is not an F5 result or semantic oracle.

The candidate crosswalk matcher compares exactly Call/use/argument identity fields (`shadow_candidate_source_crosswalk.rs:47–61`); its truth cannot establish an omitted emitted clause or witness.

## Why the reviewed theorem does not supply its own premise

Source-contracts §3.5, lines 243–246, assumes the local descriptor typing lemmas and finite conformance certificate before translating derivations in either direction. Starting from the approved constructor tree supplies only the source constructor index/operands. The reverse induction additionally needs the decorated source derivation and each matched emitted clause/typing lemma. Invoking that induction to obtain its own certificate is circular.

Section 5.3's Call congruence compares already fixed relations with the same non-child operands: actual entry/receiver/consumer, paths, providers and scopes. It neither constructs those operands nor proves a raw Call image satisfies independent `DescMem`. No additional conditional Call phase package was attempted.

## Checks, independence, coverage and limits

Commands performed: bounded `cat`, `sed`, `nl -ba`, `rg -n`, and `rg --files`; Python standard-library SHA-256 manifest creation/rechecks; direct reads of HEAD/ref; report write. The decisive source-contract §§2–3 and producer definitions were reread narrowly after initial combined output was truncated. No tests, builds, formatting, compiler execution, F5 output, Oracle execution, Git commands/mutations, child agents, interactive questions, or shared-file writes.

No executable semantic experiment ran: seeds/ranges, enumeration and mutation counts are zero/not applicable. Independence comes from the selected Authoritative source interpretation versus separately inspected implementation schemas. They share the selected core constructor vocabulary; matching that vocabulary is not independent validation of the source transition or typing rules. A checker assuming emitted Call/descriptor/admission clauses would check their consequences only.

Coverage: exact approved captured singleton, its direct Name/Name cut, inspected HIR/Core producers and adjacent candidate emitter/crosswalk. Filename discovery also inspected repository source-path names. This is not an exhaustive repository-wide absence proof. Recursive components, generalization/use, complete finite-prefix histories, requests/resumption/future-use admission, annotation/protection realization, source-world inhabitance, production-only Option 2 extras, principality and production conformance are unverified. Grouped/computed callees and annotated declarations are outside the partial stub generator's success envelope; an empty inventory says nothing about semantic absence.

Failure conditions for even the structural conclusion: changed pinned producer input, invalid/foreign branded IDs, unsupported topology, changed capture binder, changed ordered operand identity, or an unaccounted source wrapper. To promote the result to semantic conformance requires independently justified original scope/joint witness, descriptor/admission and exhaustive emitted-clause suppliers; inventing any from Q or endpoint shape invalidates that promotion.

Resource use: zero build/test/probe processes; lightweight read commands only, at most four concurrently in one read batch. No explicit numeric CPU/RAM/wall-time budget was supplied in this packet. Peak CPU/RAM and total wall time were not instrumented; displayed individual shell reads were subsecond. Scratch outputs are bounded to this report and its hash manifest.

## Independent review

One compiler-referee accepted the source/proof correspondence audit with no
findings. A separate spec-auditor accepted the exact-scope conformance with no
findings. Both confirmed the report hash and relevant source pins. The review
supports only that the inspected structural producers do not supply the
certificate; it does not establish source semantics, exhaustive absence,
production soundness, or certificate nonderivability.

Recommended next action: assign the source-generation/SEM_JOINT owner the exact captured-formal initial typed kernel and an authoritative-scope-conforming Call-emission constructor with retained original operands/witness. Obtain independent review of this missing-supplier audit first. Do not request another local CALL_TYPE composition attempt.

## Commit packet

- Exact leased/changed paths: `notes/theory/2026-10-08-captured-call-source-base-emission-audit.md`; source manifest remains at `/tmp/call-source-base-emission-inputs.sha256`.
- Observed source baseline SHA: `45fb91e069120f05741a0a4d488e80b38ca59ceb`; checkpoint base SHA: `4e6236623337bf0f54e324de4550d591123590a0`; dirty direct-source hashes above remain the operative pin.
- The inspected producer snapshot was uncommitted in the main worktree; this checkpoint contains the hash-pinned audit, not that source diff.
- Changed dependency hash: `tasks/current.md` changed from the initial hash to the first recheck hash above; semantic/producer inputs unchanged. Final recheck returned in handoff.
- Review status: accepted within scope by one compiler-referee and one spec-auditor; no semantic gate closure.
- Checks already run: scoped authority/producer reads, pre-read source pinning, dependency recheck; no executable semantic check.
- Proposed checkpoint message: `research: locate captured Call source-base emission supplier gap`.
- Shared-record deltas intentionally left for primary/curator: reference the first missing typed source kernel and actual Call-emission producer; retain the four source-base unresolved premises and current canonical DAG status. No shared authority, task, index, question-board, manifest or lockfile changes proposed.

No shared authority, task, index, question-board, manifest or lockfile changes
were included in this checkpoint.

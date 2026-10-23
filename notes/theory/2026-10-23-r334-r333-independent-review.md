# R334 — Independent review of R333 FieldTail transport

**Outcome: PASS as bounded implementation evidence.** The frozen R333 change was reviewed independently at `17e57af2c4605d7084c7d76792b115674776bbe2`, against baseline `85f41587e`. No BLOCKING, major, or minor compiler-correctness finding and no source-qualified falsifier were established. This review does not prove a general theorem or close any parent gate.

## Frozen inputs and provenance

- `crates/yu-solver/src/candidate_scheme.rs` SHA-256: `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5`.
- R333 contract SHA-256: `72937dff85d174d0abb0d9d318fe19ab6a1a1eaf7010cd943666828918993028`.
- R333 note SHA-256: `945964c75ba27c8ef6bc008e7cc4944d910e2eecd684355b976635fee4c64127`.
- Reviewer: `/root/r334_fieldtail_review`, fresh `compiler_referee`, no R333 authorship or descendants. Requested role `gpt-6.1-sol` / medium; effective model and effort remain UNKNOWN. Review was read-only; the reviewer reports work and writes stopped.

## Claim-by-claim disposition

1. **Merge before selection/removal — PASS.** Retained-state merge is at `candidate_scheme.rs:1427–1467`; pending/template coalescing at `3471–3478`; definition/local refresh at `3838–3846`, `3957`, and `3969–3975`. Selection sees merged requirements at `3525`. Capture removal requires the captured role set to cover active requirements at `2943–2946`. Immutable metadata conflicts return `ReceiptMismatch`.
2. **Exact provider and occurrence — PASS.** The refresh chooses the Definition, Member or Expression graph from typed source-owner identity (`3862–3871`) and joins by source owner, occurrence, operator origin, immutable source metadata and ordered source guards (`3873–3886`). External activation checks exact four-port representatives, guards, provider and role-source metadata (`4813–4846`).
3. **Transport across FreshUse row images — PASS.** All four provider ports must exist in the source graph (`3891–3893`). Imported role records need the authenticated subject/receiver relation in that graph (`3905–3918`), and every required identity needs a matching record (`3920–3923`). The code transports identities and records; it does not synthesize a bound. Role and four-port indices are made from one graph (`4212–4219`).
4. **External Definition evidence — PASS.** The fallback rejects local receiver/subject rows and requires both mapped keys to remain unchanged (`4795–4805`). It requires one exact provider field and exactly one reciprocal provider pair (`4812–4853`). Otherwise activation requires the relation in the same local graph (`1258–1269`, `1283–1293`).
5. **Fail-closed cases — PASS.** Missing graphs, ports, rows, identities or captures return errors (`3864–3898`, `3911–3923`, `3960`). Multiple exact fields are rejected (`4825`); fresh local rows cannot use the external fallback.

The source trace matched the repair's causal account: source body actions precede `WhereClause` registration (`candidate_source.rs:2168–2170`); admission begins with empty `required_roles` (`shadow_apply.rs:3989–3998`); completed Definition capture derives requirements from reciprocal role pairs (`candidate_scheme.rs:2716–2744`). Distinct FreshUse images may yield multiple descriptors for one source occurrence during refresh; this transports requirements and does not itself authorize a relation. Later activation still checks the relation.

## Evidence and limitation

The reviewer independently ran:

```text
cargo test -p yu-solver --features shadow-apply-candidate --lib local_initializer_fieldtail_keeps_late_where_role_requirement -- --nocapture
```

Result: **1 passed, 809 filtered out**; test time 0.10 s, Cargo wall time 0.21 s. One Cargo process ran; no broad suite, new test, output change, runtime/native certification or performance measurement was claimed.

The test's post-refresh path directly recaptures a local graph and invokes the activation helper (`candidate_scheme.rs:5655–5684`). It does not demonstrate a subsequent source-driven local use through source-instance/frontier readback, member selection and publication. The existing source-instance predicate requires the reciprocal pair in its retained graph (`2480–2503`), while the new activation helper can use the narrow unchanged-shared-row proof. This is an evidence limit, not an established source-valid compiler failure.

The next source/native question is to follow an admitted source program, if one naturally exists, from post-refresh local use through activation, source-instance/frontier readback, member selection and publication; otherwise prove that no such later use can occur in this phase. Owner: primary, with the source-scheduling and consumer-correspondence owners. No R333 code repair is justified by this review. For Button branch discharge, selector recorded `NO_SAFE_CODE_SLICE` while source-domain/dispatch preservation remains unresolved.

## Primary adjudication and remaining gates

I accept the R333 artifact as independently reviewed, bounded implementation evidence and leave its code unchanged. This is not a proof of complete source/native correspondence. The original Yulang2 catalog, Simple-sub A/B, receiving, principality, runtime/evaluation and production gates remain OPEN. No semantic authority changed and no expected output changed.

The review found no source-qualified counterexample: it considered repeated FreshUse images, multiple provider descriptors, different guard paths, changed local rows and stale empty local role sets. Hand-mutated internal records were not treated as a source refutation. The exact source-driven readback premise above remains OPEN and needs a fresh sprint decision.

R334 used a conservative 900-second charge inside its fresh 1,800-second envelope; no R333 time carried over. The reviewer stayed within the 1,200-second assignment bound and stopped with no descendants. This note and the frozen R333 contract retain the review snapshot; current active leases for R333 have been released after review.

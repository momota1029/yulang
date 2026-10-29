# R28 R2 source review

**Verdict: REJECT — pre-compile source gate.** Review was read-only. No compile, test, runtime, Lean, Lake, or checker command ran. The R2 candidate must remain uncompiled and unexecuted.

## Findings

### Major: Catch consumer identity still names a source occurrence

In `machine.rs:4110`, `catch_consumer.handler_id` is still serialized from `consumer.consumer_handler.occurrence`. The newly added `installation_occurrence` and owner fields follow it, but `handler_id` does not use the dynamic installation identity. Two installations of one Catch source therefore still emit the same handler ID. This violates the selected-handler identity rule in schema R1 and the R2 map's requirement that Lean `InstalledCatch.handle` denote the dynamic installation.

Closure requires deriving the projected handler identity from the captured `HandlerInstallation.occurrence`, keeping the Catch source site as a separate field, and validating the identity against the selected installation.

### Major: observation validation checks duplicated evidence rather than the request observation

`validate_callback_route_evidence` accepts no independently retained request observation. It reads `evidence.observation`, then compares that value with duplicate fields in the same evidence object. A cloned evidence record can change an older observation's bound from `observer + 1` to `observer + 2` after later observations exist; the current inequalities accept that pair even though `Receiving::observe` never created it. Coordinated changes to both observer copies can also pass when the new ordinal remains below the claimed bound.

The execution-table projection is correctly copied from its owning store and its selected row is checked. The remaining closure is to compare the candidate to an independently retained observation snapshot from the request, including observer, constructor-owned bound, event, and exact execution tuple.

### Major: `observer_bound` changes production observation storage

`receiving.rs:131` adds `observer_bound` to `Observation` without `#[cfg(test)]`; `Receiving::observe` initializes it in production at line 794. The field exists only for test evidence and changes production observation storage, contrary to the R1 test-only instrumentation boundary and the R2 map's scope.

Gate the field and initializer under `cfg(test)`, or retain the bound in a separate test-only observation store.

## Other review observations

- The `CallbackUseHandle` defect is repaired. The actual handle comes from `ViewKind::CallbackResult`, remains typed, and is passed to `callback_grant`.
- The actual observed execution occurrence replaces first-match lookup, and the execution table is copied from `Receiving.executions`.
- The unchanged Lean bridge remains constructed but unchecked. It proves generic implications from supplied record checks; native extraction and source correspondence remain open.
- Missing R2-specific mutations are an evidence gap, but not an independent source-gate rejection. The identity and observer-bound findings above show the substantive validator gaps that those mutations should exercise after closure.
- No additional blocking type defect was identified by source inspection. That is not a compile result.
- Tracked source changes remain limited to the two leased Rust runtime files; no language or solver decision change was found.

## Authenticated identities

| Input | SHA-256 |
|---|---|
| Contract R1 | `fa1a6f2e450169748e0696fb607963147a46cc4e6c464087cdefcacec383d89a` |
| Schema R1 | `fb46c1c031ee9132385c2170c22cbf8ea5eb27a8dc176ce0ba6356b7cf4a71ea` |
| Evidence map R2 | `37d36c35fce7988bc0387422f992f0dae81a1f97815fa768cb904a0d1801eacb` |
| R1 rejected archive | `b0d653c93772451b8868a34a0aee149cfaf1cfe3491f213b39bdf9e97fc85669` |
| R2 `machine.rs` | `c66d325fd14cf5d94094c9e09568950949405bf67b6924a513a2cceab3c90975` |
| R2 `receiving.rs` | `fbc664f166e2500208ba8e8598a078bbbcf2a3a72f620a5d40576750bca5bf81` |
| Rust handoff R2 | `e945e1a68c3f2d0ba8c69398f6fe265350162f65523c3effbcba39c32091bd36` |
| Lean candidate | `7089b047821ed82e715b4230c47e36f5fec231bf431ec6d26501137f8a358c18` |
| R26 overlay | `0621f43739c12ce1e7919a50de129414a4748d8359bf46740babd69f4854011e` |

The isolated worktree base is `c9e315208cb04bcc4fe8c3595d929fb76538f1cd`. Final source hashes remained unchanged through review. `receipts/owner-certificate.json` remains absent.

## Resource receipt

The reviewer observed 59 seconds from `23:00:28 UTC` to `23:01:27 UTC` and conservatively charged **120/1,200 seconds** for this review. Including the R1 review's 180 seconds, review total is **300/1,200 seconds**, leaving 900 seconds. The reviewer ran only reads, searches, hashes, archive comparison, and Git inspection; it wrote no files and stopped with no live processes or descendants.

The R2 author handoff reports approximately 298 seconds elapsed and acknowledges the 150-second repair cap overrun. Under the conservative Rust accounting carried from the prior handoff, Rust usage is at most **998/1,150 seconds**, leaving at most 152 seconds, below the planned 90-second compile + 60-second focused run + 30-second handoff reserve. No later execution gate is authorized by this review.

## Disposition

Source gate remains **REJECTED**. Compile, runtime JSON generation, Lean execution, parent application, source/native correspondence, and production remain **OPEN**. A source ACCEPT would still require separate primary authorization before compilation.

# R36 nested-helper native candidate

## Outcome and parent application

This is a frozen, test-only source/native candidate for `apply-scope-publication-20261018-r36` (revision 1, SHA-256 `4ea25fd1960e516eea35c877335b476cfa5f87238ff80cb169abc3403f612896`). The original parent remains `0 -> 0`. The candidate does not prove Apply-local type scope, dependency-telescope formation, publication, principality, N-Transport, soundness, or executor scope. No semantic adoption or production change is claimed.

The candidate now targets the contract's exact specimen:

```text
my outer = { my loop x = { my direct = loop x; my helper y = loop y; my first = helper x; my second = helper x; helper x }; loop }
```

The unit test distinguishes the two recursive Apply occurrences (`loop x` and nested `loop y`) and selects the latter's checking event. It checks that the selected signed Value pairs have both copy/parent identities, typed comparison endpoints, expected polarity, event membership, active group identity/occurrence/range, and captured coordinate in the installed `helper` root/boundary. One common typed join checks each selected signed coordinate against both selected helper `FreshUse` routes and their actual retained row/reconstruction map owners. Negative controls exercise wrong Apply occurrence, wrong signed coordinate, sibling route, wrong route maps, and a source-unrelated pair when present. Shared/unallocated images remain mapped to their existing representative; no final representative inequality follows from locality.

The source-level test separately counts all three literal helper Name uses and selects two concrete `FreshUse` routes. It checks component kinds and that direct and nested recursive `loop` Names remain open. It makes no claim that the third literal use is a selected route, and it does not compare final images for inequality.

## Source, propagation, and execution correspondence

Read-only owner path inspected:

- `candidate_source.rs::emit_candidate_source` retains each source Apply recipe/action, its `ApplySourceInput`, and exact checking occurrence.
- `candidate_call.rs::ApplySourceInput` retains owner, expression, argument/callee endpoints, result, checking and cause.
- `shadow_apply.rs::admit_candidate_fact` admits the existing candidate relation from that source input; no admission rule changes here.
- `candidate_extrusion.rs` retains signed parent/copy coordinates and polarity for the active comparison.
- `candidate_intrusion.rs` retains their source sets, comparison key, occurrence and active group.
- `candidate_scheme.rs` installs the local helper scheme, captures its root/boundary, and retains each local-use `FreshUse` row map. The test joins those extant records only.

This provides a concrete candidate over the existing source -> constraint -> propagation -> local capture/use path. Until the frozen candidate passes fresh compiler and spec review and Luna authorizes the one focused Cargo process, assertions remain unexecuted source-native evidence candidates, not observed execution evidence.

## Prior evidence reused and rejected

Reused R35's frozen native report and closeout only for the exact source fixture, owning record path, permitted test-only surface, and known compile failures. Repaired the reported unqualified `Parent` type and undefined `group_id` by using the owning `candidate_intrusion::Parent` record and the observed group tuple's actual ID.

Rejected R35's flat recursion specimen and its existential endpoint/event join: neither authenticated `loop y`, both signed C/D incidences, the exact active group, or both helper reconstruction maps. The old R35 candidate had no assertion execution and is not runtime evidence. No Simple-sub bypass was restored. R32 retention remains context only and does not close this native or mathematical gate.

## Exact remaining premises and boundary

- Fresh independent compiler and spec review of these frozen bytes is pending.
- The single focused Cargo invocation is unused and requires Luna's explicit launch receipt after both reviews are CLEAN.
- The candidate may expose missing native incidence. The precise required incidence is: within one active group carrying the exact `loop y` checking event, a positive signed parent/copy pair rooted at the Apply argument Value row and a negative signed pair rooted at its result Value row must each be captured at the installed helper root/boundary and joined through both selected helper `FreshUse` maps. If either does not exist, report that specific side and first failed edge (`PairOutsideSourceGroup`, `PairNotInHelperCapture`, or reconstruction-map mismatch); do not substitute another event-associated endpoint.
- R35's separate source-owner gap remains: the adopted source rule has not yet supplied the original logical type scope, complete dependency telescope, validating component, and active-root/helper-publication action for Apply-local C/D. This packet does not close it or the unchanged all-frame Call lift.

## Frozen evidence and resources

Sprint baseline/contract: R36 contract SHA above. Direct code dependencies were rechecked unchanged: `candidate_source.rs` `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c`; `candidate_call.rs` `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479`; `shadow_apply.rs` `5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb`; `candidate_extrusion.rs` `fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d`; `candidate_intrusion.rs` `7a57a93481095c6e7d4b8781810b1a5aa0d174e41ede29ac3f2b2b96bce10b0c`; `candidate_value_graph.rs` `8738c1b1699228b1a4dfd30af7e03d0afb100ca6124d23037c645246d888dc50`.

Governing source/design reads: Source Generalize definition SHA `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` §§2–4; local self-recursive binding SHA `38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895` §§1–3; intrusion value/type association SHA `531a9efae0ab7e03bfbd2f41cd7da86078e2fc8e67675d2c5c941972409f4e89` §§2–3. These retain their existing meanings and do not approve this candidate rule.

No Cargo, build, test, or probe has run. Manual source/type-path inspection only; no compiler result is claimed. Requested model/effort: Luna/high. Observed model/effort: UNKNOWN/UNKNOWN. Charge the full 1,200-second grant because actual duration metadata is absent; remaining assignment budget 0. No descendants and no scratch paths. Exact writes stop after freezing the leased test module, integration test, this report, and its single handoff. Independent review and Luna's launch receipt remain mandatory before the one authorized Cargo invocation.

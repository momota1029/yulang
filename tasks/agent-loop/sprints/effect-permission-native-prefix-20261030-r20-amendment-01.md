# R20 amendment 01 — phase-indexed native observations

Parent contract: `EFFECT-PERMISSION-NATIVE-PREFIX/20261030-r20`, revision 1, SHA-256 `49dc3bacbff9a536deaee6a45c0fe808ee7010c3eef4a73bb4b1a7d3019b822e`. This is the sequential R20 revision 2 clarification. It preserves the objective, source domain, parent quantifiers, semantics, production authority, leases and resource envelope.

## Corrected interpretation

R18's `TupleInput` is a completed observation record. It contains both entry-side data and results that arise later in the same invocation: five reserve receipts, page allocation and claim results, intern result, and snapshots. Interpret R20 observations by phase: the complete SCC/member/provider prefix; selected source occurrence and action; state at `intern_structure` entry; then each reached reserve, allocation/claim, return or snapshot point through the invocation's return or first failure. Link every field that is observed to its actual same-call owner and event.

Record branch-skipped and unreached operations explicitly. Do not invent receipts for them or turn absent observations into successful/default values. Keep an explicit observed / skipped / unavailable status for every R18 field. No assumptions about `Conditions` may be inserted.

The minimum source-to-Lean result is an authenticated selected invocation and complete preceding plan/journal trace that derives the actual arena journal state at that exact call from initialization. Prove R18 `Conditions` impossible for **every completion** of the unobserved `TupleInput` fields when the authenticated actual entry journal is absent; R19 `selected_call_excludes_R18` can then consume arbitrary completions because its contradiction is the `activeJournal` field. Preserve the association between the selected occurrence, arena identity and completion set.

Do not claim full native `TupleInput` equality, downstream outcome coverage, or complete source/native correspondence where any field remains unavailable. Report the exact unavailable field and first missing source edge. If entry journal presence is true, mismatched, or unauthenticated, R20 cannot exclude the R18 condition for that call. The original full source/native obligation remains OPEN wherever this partial interpretation does not establish it.

Falsifiers include a missing or reordered plan action, uncovered provider/member, unclassified journal writer, unmatched transaction token, wrong source occurrence/arena, incorrect reached/skipped classification, or any observed field not matching its owning native operation.

## Exact scratch resources

- Rust Cargo target: `isolated/ep-native-r20/project/build-target`.
- Lean 4.35 isolated project/cache/logs: `isolated/ep-native-r20/lean-scratch`.
- Pinned Lake: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake` (Lake 5.0.0-src+eb6cafb, Lean 4.35.0).

These exact paths are primary-recorded resource leases. All original R20 active-time, process, audit, reviewer, concurrency and Git controls remain unchanged. The first Lean audit was launched before this amendment and is retained as one of the two authorized audits; its roots are the general trace transition model, not a call-specific application.

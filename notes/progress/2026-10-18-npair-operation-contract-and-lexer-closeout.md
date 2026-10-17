# Operation contract and lexer identity sprint closeout

Sprint: `npair-operation-contract-and-lexer-identity-20261018`, contract rev1 SHA-256 `67ff7aefe2b696db00433305f42774aca02c53253d877ac1ffc6035c81dbc631`.
Baseline: `b3a9b1739b59d8c7991b5f798e98f71f96904b19`. Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`.

## Outcome

Original parent conditions closed: **0 → 0**. No source domain, theorem quantifier, or original NPAIR obligation was weakened. No compiler code or test changed.

The frozen Operation candidate (`notes/design/2026-10-18-npair-operation-self-effect-contract-candidate.md`, SHA-256 `c8c9854c32cdb3dc5e9fe8e1be15293e3b05bb0b393daff3632f9ba516df1455`) adds a field-indexed presentation and distinguishes `Self(req)`, direct consumer, written rows, shared tail, nested/returned fields and original alternatives. It keeps the same reference and `theta`. It does not recover the unavailable original Operation `Prim/T` specialization or establish field projections.

Fresh independent spec review found no major defect in retaining it as a candidate, and explicitly identified universal original-domain lift/forgetting, authentic consumer field introduction and complete W/Z/domain evidence as **blocking for proof/application**. A minor notes that the illustrative `eta` binder is unspecified. The reviewer confirmed later user authorization can support selecting this interpretation, but cannot prove compatibility or waive source evidence.

The frozen lexer result (`notes/theory/2026-10-18-npair-lexer-bracket-identity.md`, SHA-256 `7e6b99f764ffc32f1bab3935a1035be1b4861a84a9fd69cd6a43093891bf98b9`) conditionally derives one-byte `[` payload under lexer-input/transaction and authentic callback premises. It does not establish row-start/key separation or any parent condition. Fresh spec and compiler/source reviewers returned related minor findings: `scan_type_payload` has no split argument, and the actual Type callback's absence of payload splits remains unverified. Both review receipts confirm no major finding within the stated conditional claim. This artifact remains research-only and is excluded from successor proof premises.

All authors and reviewers STOPPED. Full 900-second cap charged: candidate 300, lexer 180, Luna 60, independent spec review 120, compiler/source review 120, reserve 120 spent on the candidate's fresh spec review. Astra0. Static source/hashes only; no tests, builds, probes, Cargo or compiler edits. One reviewer wrote a temporary `/tmp/npair-review-authority-read`; repository files were unaffected.

## Adjudication and next work

Following the user's instruction to adopt proposed interpretations by default and roll back on concrete conflict, the successor contract adopts C1/C2 as a **working semantic rule for proof and private evidence work**. This is not a claim that it matches all original semantics. The successor must preserve every original tuple and prove the universal compatibility lift; a source-qualified mismatch triggers revision or rollback, never source/theorem narrowing.

Next sprint `npair-operation-self-source-realization-20261018` (contract rev1) has a single integrated result: construct the actual self contribution at the same reference/`theta`, and trace an existing accepted Operation source through native emission to formal Permission. It has a Sol proof lane and Luna implementation lane; the latter may create only reversible private evidence in two pinned owners and cannot alter production semantics, public API or fixtures. Fresh proof/source and compiler reviews are reserved. Parent remains OPEN, closure 0.

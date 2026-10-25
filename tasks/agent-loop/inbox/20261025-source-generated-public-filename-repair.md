# Public filename repair — primary revision 4

Author: primary parent01a17247, after original author and independent reviewer
STOP. Contract r4 SHA7503d09945b31a065c9747be0761af8c93b319d2798ff1fda6984d16414db193.

Old example SHA d65f979a94001ee393e6075b227c793368231bb9d98c12373db1a758673a0c09.
New example SHA aea1caf0b88bbce6479050ebff4989cbc3afb784e50dad228a4af70bfa3df005.
Original eight-row ledger SHA132cab00236c36c7072d5fdf11eccb86681fc6ebc2c34a6351887e89282a0b43
and original native report SHAffb247950c6111a022883cbec8af545cac1dc71f7a848cd0a6d6d13aac765f6d
remain frozen. The original native handoff describes the earlier source hash;
this exact delta is primary-authored and requires independent delta review.

The complete file equals its original build-row source_text after this single
replacement; source(), run_low(), target44, source-language programs and all
production files are byte-identical. Previous public StructuralProjection is
an invalid-filename preparation failure. Valid-filename public outcome is not
predetermined. Native cell-republication correspondence remains OPEN.

```diff
--- frozen-r2-example
+++ primary-r4-example
@@ -36,7 +36,7 @@
             // Ordinary execution prepares its own world and source schedule.
             // An unavailable public route is evidence of a boundary, not permission
             // to treat RuntimeEvidence::default() as a production certificate.
-            match yu_playground::execute(&source, case, "main", STEP_LIMIT, false) {
+            match yu_playground::execute(&source, &format!("{case}.yu"), "main", STEP_LIMIT, false) {
                 Ok(actual) if actual == format!("{expected}\n") => {
                     println!("CASE={case} public_status=MATCH result={actual:?} steps=NOT_EXPOSED");
                 }
```

No old failures or counters were reset. One newly granted build and two
public-only attempts use a separate r4 ledger; no low-route execution is repeated.

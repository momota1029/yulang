# R343 — scoped primitive arms and carrier continuation

Baseline `944dff732`. `OriginalFullIFArmInterpretationR343.lean` constructs
finite scoped primitive-arm contributions from independently supplied primitive
data, fields and licenses, retaining the supplied R310 Arm record, dependent
telescope and distinct Fin positions. Its `Legacy.arm_registered` computes
the child and catalogue and applies unchanged R306. Independent review
confirmed this conditional application; the legacy specialization explicitly
requires identity whole action and a parameter-independent endpoint interface.
Its supplied `special.slot` is unused, and actual original arm registration,
binder/source-action authentication, nonidentity legacy transport and the full
Bind/Delay/Call original semantics are not established. Original R159
admission, Checking and source children remain open.

The initial `OriginalContinuationEliminationR343.lean` model builds the
selected outer `(make 1) value` continuation on R342's direct-request
operation. Independent review found this differs from the carrier/force order
in `OriginalHigherOrderCorrespondenceR343.lean`. The subsequent
`OriginalCarrierContinuationR343.lean` uses the latter consistently: ten
candidate steps to publication and seven steps to deliver a response through
the pending outer caller, preserving the same suffix and every represented
typed response through arbitrary finite protocol developments. The earlier
direct-request theorem remains a separate candidate, not evidence of native
execution. The carrier proof still uses a formal operation lambda and arbitrary
receipts, and does not establish native owner/world/receipt simulation, original
resumed CalleeInputs or an R159 parent premise.

Before commit, trailing blank lines were removed from the two continuation
files. Their final SHA-256 values are respectively
`113f6bdae913b17135081062f326ab4b63ab72646c7b41e6cbc15f526ef1d420` and
`a3c29d34d217e46b0bfd0828301742876f2d5bd22c68deb55bfa22e7dbab09ac`.
An independent repeat compile and full audit verified that each change removed
exactly one final LF; the type/axiom reports were unchanged. Delta receipt
SHA-256 `89f7aee0c475784a33faba12644543e7da359c2cff5779652c14bdedf1afd344`.

Fresh independent pinned Lean 4.35 checking at `-j1 -M2048` compiled all 94
HigherOrder dependency/target modules from source and audited all 45 originating
theorems. It separately compiled the R318 and scoped-arm target and audited all
342 originating constants including 155 theorems. Only standard Lean axioms
occurred. Independent receipts:
`eefdad416fd857d49bac778146bfadb0cc62eda012b1ed46b277acb0a31873d0` and
`efab7fca81922bd2fd9da5f4f070df338e0da331adfec1a4e92236d1b2e2317e`.

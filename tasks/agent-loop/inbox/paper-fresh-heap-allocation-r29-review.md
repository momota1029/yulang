# R29 independent M1 review

Disposition: **CLEAN for the bounded intermediate claim**. No BLOCKING, major, or minor findings.

Reviewed frozen inputs:

- Module SHA-256: `7cd87b8e5fd43eea0206401de6ed91e817755f3d1ad2c5aeee1caf0dd1732925`
- Contract SHA-256: `1859d9a005b9bfbff2fd98de5bf7e2d984b48f890cd42ca37b5909f5439d8c70`
- Handoff SHA-256: `ea88664ab5f3a70864a713a47e19036df8b097fa7adc77775a2978f8a8f02846`
- Primary verification SHA-256: `1301b818fd5d3f68c3162ab468112ad50b7a0af1436e2bb582827083a51d2899`

Authority: `rules/design-authority.md`, `notes/design/INDEX.md`, R29 contract §§“Fixed goal and theorem boundary,” “Required falsifiers and open guard boundary,” and “Exact leases and checks”; manuscript `docs/yulang-operational-type-safety-ja.tex:324–326,981–990`. Applied `yulang-lean-proofs` as a source-only reviewer under the contract’s explicit checker prohibition.

Verified obligations:

- `PaperFreshHeapAllocation.lean:13–35,216–238`: one block supplies identities, types, RHSs and allocated nodes. Pairwise uniqueness and both graph/heap freshness premises are explicit. No independent result vector or allocation zip.
- `:37–80,133–189`: graph and heap lookup use first-match semantics. Freshness excludes shadowing of old successful lookups; new entries retain exact identity/type/payload associations. R27’s identity-membership lemma supports graph freshness reasoning.
- `:82–125`: every RHS uses its matching block type and shared formal context. The same R28 substitution is applied throughout. Both actual public whole-list Option success and individual RHS success/type preservation are proved.
- `:127–131,191–238`: length and exact prefix/original suffix are explicit. Old payloads retain their values and type witnesses through R27 weakening. Entire updated payload typing follows.
- `:240–283`: duplicate graph identities, old heap collision, zip truncation, formal order, swapped replacements and sequential substitution have concrete discriminators.
- `:285–305`: self-alias payload typing and an actual heap lookup self-edge are established. This correctly exposes the auxiliary relation’s guard limitation.

The primary receipt contains matching complete BEGIN/END records, printed types and axiom results for **all 31 public declarations**: 10 definitions/abbreviations and 21 theorems. Printed types agree with the reviewed source. Seven declarations report no axioms, two report only `propext`, and 22 report `propext, Quot.sound`. No omitted public declaration or disallowed axiom was found.

Scope remains explicit at `:3–6,214–215,285`: no source-formal order, guardedness, full paper heap judgment, full `rec` preservation, source/native correspondence or production closure is claimed. These remain unresolved parent obligations rather than defects in this authorized intermediate.

No existing expectation, snapshot, fixture, diagnostic or semantic test name was changed or proposed for change. No semantic approval decision is introduced.

Reviewer activity: **zero Lean/Lake/checker invocations, zero cache access, zero Git activity, zero file writes**. Review used source and supplied verification evidence; it did not independently rerun the checker. Report returned to the primary for persistence because the governing read-only instruction prohibits edits.

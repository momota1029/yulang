# Receipt: nested extrusion origin Value

Question ID/revision: `2026-10-12-nested-extrusion-origin-value`, revision 1
Draft ID/revision: `2026-10-12-nested-extrusion-origin-value-answer`, revision 1
Approved answer: matching revision 1
Original worktree/branch: `/home/momota1029/rust/yulang`, `research/simple-sub-intrusion`

## Validation and integration

- The question, current draft, and approved answer identities and revisions
  match. The approved answer embeds the draft exactly.
- The approved answer records the explicit user approval `OKです` and states
  that the external message locator is unavailable.
- The question's Yulang source revision `06430602372f7c94ca8cba362fd360a728388ffa`
  is an ancestor of the integration baseline. The current governing Value
  ownership and extrusion-qualification sections were reread and remain
  consistent with the selected origin rule. The pinned Simple-sub revision is
  not present in this Yulang Git object database; it was not treated as fresh
  evidence for changing that reference.
- A fresh independent `spec_auditor` review at baseline `c0b67771d` found no
  content mismatch or conflict. It confirmed the answer resolves the missing
  origin choice without changing Apply-result edges or assigning every type
  occurrence a permanent Value owner. No proof of equality preservation follows.
- The exact three-file answer bundle was committed at
  `c0b67771df12d599a0574d09c22dd46284178b26` and pushed to
  `origin/research/simple-sub-intrusion`. Current files match the committed
  versions.

## Outcome and affected scope

Accepted and consumed for the scoped decision: call-demand extrusion
occurrences use the root of the definition whose source-owned initializer/body
contains the call, even under expression wrappers; a nested definition owns
calls in its own initializer/body. For the inner `odd(n - 1)` call inside
`even`, origin `E` and receiver `O` qualify that occurrence's retained pairs
for `C=T` and `D=R` under the approved Value-SCC rule.

The decision is recorded in
[`2026-10-12-intrusion-value-type-association.md`](../../notes/design/2026-10-12-intrusion-value-type-association.md)
and synchronized in `tasks/current.md`. Source construction/transport,
equality-preservation proofs, soundness, required principality, complete Call,
effect hygiene and F5 cutover remain open. No implementation is authorized by
this answer.

# Computed Call Union R293: independent review

`/root/r293_parent_audit` and `/root/r293_lean_review` independently reviewed
revision 2. Frozen module SHA-256
`50b1ce82dbd81d8c17a99461a78b77a9066094896f38e046d70fb4dd69365543`;
handoff SHA-256
`d145d32dd4bbd444dc267b4e38570de2c06fa19112e27d89f3ba123a2aa0af61`.
All 21 dependency pins matched. Lean reviewer independently ran the pinned
Lean 4.35.0 checker in a separate cache: eight theorem audits passed.
`evidence_sound` has no axioms; the other seven use `propext` and `Quot.sound`.
Supplemental `retainContribution` audit also passed with `propext` and
`Quot.sound`. Full types and original producer audit are in the handoff.

Revision 1 replaced all alternatives at a selected site, potentially losing
original witnesses. Revision 2 uses `Sum.inl` to retain every old relation
witness, including shared-site nodes, and `Sum.inr` for new tagged cases.
`retainContribution` structurally preserves all existing contribution forms.
This is monotone witness retention, not equivalence of the extended relation
with original source semantics.

The checked construction forms typed packets from existing `clause` trace
interpretations and decoded interfaces, preserves raw event/history/world and
witness, and applies the existing alternative contribution constructors. It is
conditional: `Inputs.traceForm`, `observationFields`, decoded interfaces,
scopes and arm inventory are still supplied; authentic EI registration, source
arm inventory and field/owner formation have not been constructed.

`app_result_pair` assumes original callableImage-to-synthesis Checking and
image membership, and preserves that same-extension check in its conclusion.
It does not invoke `app_admission_iff`, derive checking, identify callableImage
with EvalInvoke, or supply original admission, formation, other locals and both
children. GR5's original target check remains independent. Parent-edge delta is
zero. No source/native correspondence, original Union closure or production
authority follows. Both reviewers stopped without repository or Git writes.

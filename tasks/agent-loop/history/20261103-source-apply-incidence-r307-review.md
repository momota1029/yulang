# R307 independent review and outcome

The frozen source extractor has SHA-256
`0f55c2afff3a491585326b34e27d36ba6bf4c750cfb4e62d33fba5f0bcf01f20`;
its revision-2 handoff has SHA-256
`d41497fbcfc4ec8ae728f0b7439277366359037d69a73e4f80002bc6c30fc711`.
Independent review checked the branded HIR child indices, owner and source-key
identity, Group paths, and regenerated owner/nested/empty outputs byte-for-byte.
An isolated offline locked build and ten tests passed on revision 1; revision 2
adds only two regression tests, independently inspected and run: 12 passed.
The supported top-level binding carriers are the scope, not all source forms.
Legacy signature references remain intact, although new owner keys may append.

The Lean artifact has SHA-256
`c3f63a454831d4193ee708f754d4d1194ececfa5a21d777624556eacb0898a07`;
its handoff has SHA-256
`07a7cde9577ffdeb192a8262fd5605437e6e86429190eae695bbe12f817f3670`.
Independent Lean 4.35.0 verification built the isolated cone, audited the
printed types and transitive axioms of all 18 declarations, and directly
checked the three extractor-generated Lean files. A separate parent-edge audit
confirmed that the finite authentic owner fixture joins Apply and both child
roots, applies the original `TableToSource.app`, and specializes unchanged
R159 with one shared extension. Child swaps, a dropped Group and conflated
same-position occurrences are rejected.

This is finite occurrence/root incidence, not authentication of complete child
syntax: the latter still needs the separate `TableToSource` child premises.
The fixed owner fixture is unannotated and does not establish general source
coverage or Rust–Lean equivalence. R159 decoding, actual logical admission,
all original locals and both child judgments remain premises; authentic EI-All
interpretation, original independent arm laws and q_c registration remain open.
The semantic parent theorem is therefore conditional, not closed.

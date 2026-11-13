# Executable request checking to local named-spine dictionaries

Status: Draft proof implementation, 2026-11-13.

Input structural facts are explicit: a finite input nominal spine, declaration
visibility/checkedness, actual root argument location, normalized input query,
root output definition and no where children. The checker searches the current
finite carrier slots by exact output source identity, then inspects the actual
normalized request queries. Success constructs the observed request proof and
therefore a NamedSpine.Shape, a local Node and the same terminal Evidence in all
current models. No caller-provided output Tree or semantic Evidence is needed.
`discover` returns `Option Node`; successful return is equivalent to checker
true. This does not make Input discovery or general coverage automatic.

The existing cycle170 nominal-input/named-output fixture evaluates true. The
existing reserved-output fixture evaluates false. Its InitialSource and Linked
hold, yet output identity2 is reserved rather than attached to a physical slot.
`GeneralNominalState.sources` includes carrier slots, row sources, reserved
identities and identifiers in ordinary atoms. Membership in that list must not
be used to invent a physical target locator. The checker's failure is not
language rejection: a future installation or a separate semantic evidence path
may constrain a reserved output. Soundness is proved; general completeness is
not claimed, including for aliases or nonpoint descriptors.

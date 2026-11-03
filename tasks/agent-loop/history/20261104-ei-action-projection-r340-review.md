# R340 — primitive action and receiver projection

Baseline `bcd119715`. `OriginalEIContractRealizationR340.lean` recursively
constructs actions for the existing Guard syntax from independently lawful
atomic actions, and reconstructs the transformed declaration lookup,
PrimitiveLeaf and PrimitiveInput. Its R311 application replaces separately
supplied changed-world request/resume primitive evidence with those actions.
Independent source review confirmed this conditional reduction. Authentic
nonidentity atomic/lookup/resolver action instances and their compatibility
with the same source request remain independent; changed-world callee evidence
and full EI transport are not established.

Forward response mapping covers its images, not necessarily every admitted
response at the changed world. The independent reviewer supplied a constant
Boolean-map counterexample to unconditional coverage. The subsequent owner
investigation found IF forward naturality and R295's contravariant IF-Use
pullback, but no equation connecting actual `ResponseAt` domains to that
pullback; source-authorized admission cannot be silently redefined as the
image. This does not rule out a separately established original domain law.
Independent specification review clarified that two-way correspondence is
sufficient for exact domain identification, but need not be imposed as a
new prerequisite for forward universal typing: an authenticated pullback of
every admitted use-domain response to its original declaration can suffice.

`OriginalReceiverProjectionR340.lean` extracts the actual checked observation
at the same receiver and constructs an abstract-Inputs discriminator where
all Function challenges execute yet a different target trace fails. Its
ReturnInputs argument field is vacuous due to missing reify registration, and
the registry lacks source-key authentication. Independent review therefore
accepts it only as an abstract-interface counterexample, not a source or EI
counterexample. It does not construct the original checked-observation→trace
projection or discharge R339/R306/R159.

The independent review used frozen source SHA `b4cca04240d289972dd1bbb3f000d816b695f5c220aa7114e72403e87d920eca`.
One trailing space was removed before commit; final source SHA-256 is
`ecd7e02c1e67a3408862fb433624e496adb25268d848fd9354616fb81d6ae624`.
Independent checking verified the one-byte difference and recompiled both
final modules with identical type/axiom results. Updated receipt SHA-256:
`7a2137e9fa294d6ffad7499f20caeff22e08e2c6b3cae8aad5788a532deca6e2`.

Fresh independent pinned Lean 4.35 checking with `-j1 -M2048` compiled both
modules together and audited 151 originating constants, including 80 theorem
declarations and 18 authored roots. Only standard Lean axioms occurred. The
source, configuration and reused artifacts were hash authenticated. Receipt
SHA-256:
`2b27a32611a293eafdc0ff3407edcbe3f4d719bc828627a9a5e81968b3b8dd19`.

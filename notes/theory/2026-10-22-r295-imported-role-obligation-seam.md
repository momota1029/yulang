# R295 — imported `say` role-obligation seam

## Exact starting point

R294 committed `8dc8fbf4b`'s predecessor, which admits the exact pinned
parenthesized typed formal in ordinary HIR and joins the public `say` export to
its provider binding. The declaration-local carrier retains the source-owned
`where 'a: Display` clause with a `SourceNodeKey` owned by the pinned console
parse. This is source ownership evidence only.

## Candidate inference boundary

The current `candidate_source::preflight` returns `Unsupported` immediately
when `LocalSource::where_clauses()` is nonempty. Its focused unit test builds
`my display(value: 'a) = where 'a: Display; value`, verifies the two retained
names, and asserts that rejection. The implementation comment states that no
identity-bound role constraint consumer exists.

Imported values are independently outside the candidate path. Preflight rejects
`LocalSourceResolution::Imported`, and the Name collector returns unavailable
for that resolution. `FieldTail` similarly returns unavailable because member
typing requires an authentic imported role/field resolver. This covers the
essential `say` body `value.show` as well as the Console and Types sample uses.

The type annotation machinery already interns a named annotation variable by
`(AnnotationScope, name)`. A declaration prerequisite on `'a` must reference the
same solver row created for the formal's annotation. The HIR's where carrier
currently has only text, spans and source-node keys; it has no resolved
variable or role identity. The role/implementation index likewise keeps exact
source declarations but explicitly makes no conformance or selection judgment.

Finally, `CandidateInference` solves one HIR. `export` accepts only roots from
that HIR's solved artifact; no API supplies provider HIRs or imported schemes.
Authentic import resolution in HIR therefore does not yet imply a type scheme
is available at an imported use.

## Required shape of the next bridge

The first reusable object should be a source-qualified role obligation whose
subject is the exact candidate type row for the annotation variable, whose role
is a resolved `SourceRoleId`, and whose origin remains the exact where-clause
key. It must travel with the generalized scheme through one coherent FreshUse
map. Role implementation selection must wait for the inferred receiver type and
produce an identity-bearing member/provider path. Imported scheme use must join
the same finite authenticated source world without turning spelling into a
special case. These records are premises to implement, not a completed design
proof; full payload coverage and consumer correspondence remain open.

The next sprint should couple that record with a provider-scheme import edge in
the existing candidate source/session path. A disconnected class-constraint
solver would leave both the source route and the proof companion's same-map
Capture/FreshUse obligations unsatisfied.

## Verification and limits

Passed:

- the focused candidate preflight prerequisite test;
- the implicit-prelude source identity/local-shadowing test;
- the pinned public-export owner/carrier test.

No code changed in R295. The tests establish the current source identities and
the exact fail-closed boundaries; they do not establish source acceptance,
typing, runtime behavior, theorem closure or Oracle parity. The `[io]`
contravariant annotation continues to denote an open row `[io,'e]`, so a
`[state]` callback is not itself an effect violation.

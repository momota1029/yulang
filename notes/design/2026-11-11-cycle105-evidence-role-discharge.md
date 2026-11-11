# Cycle105: computed evidence discharges retained source roles

Status: Implemented finite fragment, not a language-semantics authority. Date: 2026-11-11.

## Boundary and target

Use the existing checked finite grouped source and named ordinary inequalities.
After its actual mixed saturation, compute each retained role's possible scalar
heads by searching the allocated slots with the same source name and reading
paired scalar evidence. Run the existing structural role solver for these heads.
There is no caller-provided head map, successful checker result, slot map, state,
fuel or derivation witness at the outer entry.

For any registry env/roles with WellFormed env.cores and AssocWellFormed env roles,
and any finite src, prove outer success iff ValidSource src.clauses, independent
Models src, and, for every original clause c, some scalar b has an independent
source Derives src c.receiver b and existing declarative Discharges env.cores
(fun _ => b) c. Discharges uses structural Fills and RoleConstraints.Resolves;
it does not inspect the executed resolver or allocated evidence.

Return two Boolean observations, ordinary consistency and role discharge, in
Option. None is fragment-invalid input. Neither Boolean false is assigned a
language-visible pending/selected/ambiguous/rejected tag. A source-name domain
support lemma closes the reverse direction even when bare obligations add no
slots. Missing/unseeded bare roles cannot disappear. Source conjunction order
and duplication should preserve both observations.

## Authority and exclusions

spec/06-roles.md 6.3: unknown receivers are not chosen from a unique impl;
associated equalities carry ordinary type information; where is conjunction.
Read the current audit branch x-oracle X13–X16 and C3-PARENT/C3-PARENT-NEG. These
are compatibility context, not an oracle for this finite adapter. No new
Yulang2 run or new language-semantic decision is required here.

Only the existing int/str structural encoder is supported. A bool/unit evidence
fact may be ordinary-consistent but does not discharge a role through this
encoder. Arbitrary ordinary semantic knownness, parser/expression lowering,
new generated children, dynamic allocation, general saturation termination,
four-way final diagnostics and canonical dictionaries remain open. This closes
a finite computed-evidence-to-retained-role bridge, not a full B4 package.

## Review precision

Order congruence is whole-clause and ordinary-inequality membership equivalence;
it does not change equations inside a clause. Ground templates still require a
derived scalar receiver in this evidence-backed adapter. This restriction is
not asserted to be a new source-language rejection rule.

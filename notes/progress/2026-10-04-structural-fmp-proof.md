# Structural FMP: finite fence completion

Date: 2026-10-04
Branch: `research/simple-sub-intrusion`
Base inspected: `76e7715f77ae0bdf4926cc494b8c496cc2f6afd8`
Integration base: `00e317226966827b42a14bef125bd088e60f83d5`
Mode: M3 mathematical certification; two independent review domains
Status: reviewed classification A; normalized pure structural FMP and BR proved
Implementation authority: none

## Request and exact target

After the prior classification C at `76e7715f`, the user asked to prove the
remaining statement. The target remains one fixed normalized package `P`:

```text
Sat_I*(Gamma_P) => exists finite surjective mu. Sat_mu(Gamma_P).
```

Equivalently, if every finite surjective monoid quotient is inconsistent,
the free least Horn closure has a finite conflict. Neither a changing
package nor a family of failed quotient constructions meets that target.

The earlier [finite-feedback/rank result](2026-10-04-structural-fmp-feedback-rank.md)
is retained. Its finite-horizon theorem and exact BR equivalence are not
retracted. The present attack constructs a complete regular model directly.

## Proved result and discharged obligations

The complete argument is
[Structural FMP by finite fence profiles](../design/2026-10-04-structural-fmp-fence-completion.md).
It constructs at most `8^N` states on the original finite flat-term universe.
It has no Structural S, two-sided-anchor, or common-rigid-permission premise.

The mathematical connection is Sequeira's 1998 finite distance-state method
for native Record subtyping. The exact source locators and attribution are
in the design note. The paper's regular-type setting was not treated as a
proof of arbitrary-to-regular completion. The added bridge consists of:

1. simultaneous guarded three-edge up/down fences for any connected pair
   of arbitrary proper trees, including negative and invariant coordinates;
2. arbitrary-tree soundness of all seven-value closure and decomposition
   rules, giving a consistent finite distance matrix from an arbitrary model;
3. complete Record successor consistency and comparison cases, including
   the landmark argument and unequal raw domains;
4. exact successor/start-state equality, preserving shared recursive
   descriptor equations;
5. a separate same-address shadow of the original arbitrary model for every
   constructed root/path occurrence, preserving arbitrary rigid permissions.

Proof-level distances and the empty Record default stay within the existing
proper structural carrier. No global extrema, source rejection rule,
production comparison-transitivity rule, or compiler implementation is added.

## Production and independent review boundaries

Read-only producer investigations covered constructor completion, the Horn
bridge, and the exact primary literature. Their reports helped construct
the argument and do not count as independent certification.

Fresh independent reviewers inspect the complete candidate as untrusted:

| Review | Assigned scope | Status |
|---|---|---|
| `review_fmp_arbitrary_scope` | arbitrary-tree diameter and closure soundness; descriptor and permission transfer; fixed-package quantifiers | PASS; no BLOCKING, major or minor findings |
| `review_fmp_finite_profiles` | finite algebra/state construction; native Record cases; invariant coordinates; exact shared successors; source theorem conformance | PASS; no BLOCKING, major or minor findings |

The root owns all edits, finding adjudication, navigation updates and Git
integration. Reviewers are read-only and have no child agents. Convergence
requires no accepted BLOCKING or major mathematical finding; minor text
repairs do not expand the panel. No new semantic decision is being adopted.

The arbitrary/scope reviewer independently reconstructed the guarded
three-edge fences and their signed simulations. It checked that truncation
is used only for an already finite distance, Record common-lower bounds
project to actual child common lowers, and the closure induction does not
assume regularity. It also checked exact child/start-profile equality and
both domain inclusions, then verified the shadow for every root/path
occurrence rather than for a representative of a shared state. It confirmed
the complete quotient bridge and fixed-package contrapositive. It did not
claim the detailed finite-algebra/source review assigned to the other lane.

The finite-profile reviewer independently exhausted the distance algebra and
all 25 active Record parent pairs. It checked that the nine parent instances
of the four exceptional projected cases use the selected-field landmark.
For comparison descent it verified raw-S inclusion in raw-T, recovery of
raw-T entries through expansion of S, and domain equality before applying
the successor relation. It checked invariant child equality, exact recursive
descriptor sharing, finite state count and the direct original-bound
simulation. It read the primary Sequeira source and confirmed the native
Record transfer without a hidden Helly/extrema assumption. It did not
independently re-prove the already reviewed free-Horn characterization or
the prior BR equivalence.

Together these reviews cover all new mathematical obligations. No repair
round was needed. Post-review changes to the proof are status/navigation
and a worked explanation of the already reviewed one-sided Record/Function
obstruction; the theorem construction is unchanged.

## Focused verification

The research-only
[finite algebra check](evidence/2026-10-04-fence-completion-algebra.py)
exhausts the seven distance values and their pairs/triples. It checks the
displayed capped concatenation table, associativity, meet distributivity,
reversal/variance identities, and all Record local cases including both
parent values mapping to child `L`. It is not a package solver or a proof
assistant certification of arbitrary trees.

The command
`python notes/progress/evidence/2026-10-04-fence-completion-algebra.py`
passes with:

| Exhausted dimension | Count |
|---|---:|
| finite distance values | 7 |
| algebra pairs | 49 |
| algebra triples | 343 |
| active Record parent pairs | 25 |
| direct Record parent cases | 16 |
| landmark Record parent cases | 9 |
| scalar related-profile value pairs | 19 |

The independent finite-profile reviewer also ran its own inline algebra
check. These checks certify finite tables and case coverage only; the
arbitrary-tree construction, model transfer and scopes are established by
the written proofs and reviews.
The focused diff whitespace check passes. A repository-local link check on
the nine changed Markdown files resolves all 106 relative file-link
occurrences, with no missing target. Status navigation explicitly marks the
earlier open FMP/BR claims as historical.
Compiler, Cargo, Oracle and performance runs are outside this proof-only
change. No production implementation or runtime claim is made.

## Integration and remaining scope

`tasks/current.md`, `notes/design/INDEX.md`, the direct-main-gate progress
record, and the old finite-feedback note/record now distinguish the proved
FMP from the historical classification C. Their closed theorems and
construction-specific counterexamples remain intact. The open-residual
design and research-playground direction have matching status cross-links;
their semantic and implementation authority is unchanged.

During review, upstream advanced through `fc07a95a` and `00e31722`. Their
test-only transport and restricted feedback playground changes were read
and fast-forwarded before navigation integration. This proof change neither
modifies those programs nor relies on their bounded enumeration as evidence
for FMP. The user-requested compiler-implementation exclusion remains in
force for this task.

The FMP gate is closed. Whole-production source correspondence,
Function/effect compatibility, joint predicates, principality and lifecycle
remain distinct gates. No premise that production belongs to a newly
restricted source fragment is added.

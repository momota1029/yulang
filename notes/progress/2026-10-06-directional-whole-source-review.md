# Directional whole-source research: independent review and integration

Date: 2026-10-06
Research baseline: `e12738d4f1452d87883516dfa5b709a4a5c38230`
Branch: `research/simple-sub-intrusion`
Mode: M3 research correctness/conformance; M0 status integration
Status: new independent reviews complete for the bounded package below
Semantic/implementation authority: none

## 1. Review isolation and exact targets

Three separate producers used constructive source judgments, adversarial
finite models, and source/typed/implementation correspondence. The primary
produced the whole-active-relation specialization. Two additional agents
reviewed frozen artifacts without producer reports or each other's verdicts:

- `compiler_review`: compiler-referee correctness review, in two disjoint
  target batches;
- `spec_review`: exact current-user/Authority conformance review of the five
  target files.

Both review agents were launched with `fork_turns=none`. Neither was a
producer or repaired its own findings. The current repository role settings
requested `gpt-6.1-sol` medium for the compiler referee and low for the spec
auditor. No runtime-reconfiguration claim is made.

| Frozen artifact | SHA-256 at review input | Review scope |
| --- | --- | --- |
| [Joint source judgment](2026-10-06-directional-joint-source-judgment.md) | `14d06fd9667a9eaa829da7026033395c148094a68be3e3546e28dc19858b8e2c` | Source-instance S1, compliant-refinement retention S2, certified saturation S3, original scopes and remaining source rules |
| [Full relation and gate delta](2026-10-06-directional-full-relation-and-gate-delta.md) | `2c4bacf9ce80f1f8fad857b8363bacf5d953e7a003d48c57a72f45992b7d967c` | Active-predicate DREL-1, full-source DREL-2 obligation, recursive operator/quantifier conditions and downstream implications |
| [Typed contribution bridge](2026-10-06-directional-typed-contribution-bridge.md) | `29e70812e7b87b6f96ae1f1f8c35f3db61e7dc44d842a8359b7cca3cef6692f8` | Static fragment, conditional original receiver schema, typed capture/read images and event/lifetime conditions |
| [Falsification note](2026-10-06-directional-source-relation-falsification.md) | `78305fe64d188b70d168482c29d936e672e000e2ebc32e98b33e59f628407398` | Supplied certificates, finite closure, stage-erasure and joint/active-predicate countermodels, exact scope |
| [Research checker](../../tools/research_directional_source_relation.py) | `768e600edd3b13aed779a6be2bfd39b2ba1be1dd13d8ad468476f92c145b0277` | Rule matching, coherent transport, physical-order coverage and shortcut discriminators |

The compiler referee additionally inspected the earlier
[Apply output bridge](2026-10-06-directional-apply-output-bridge-attempt.md)
within its narrow Name/Call-to-upper-occurrence dependency. This is a new
review of that dependency, not retroactive reuse of older E/R or local-rule
reviews. The two previous source-event notes arriving upstream at
`51e61b4f` and `4be72ac1` remain their own independently reviewed artifacts;
their reviewer verdicts were not supplied as evidence for this package.

## 2. Findings and adjudication

**Compiler-referee batch 1:** no blocking, major or minor findings on the
joint judgment, full-relation note, or narrow Apply dependency. In particular:

- S1 is restricted to the selected source registration/upper-use instance
  and reviewed ordinary constructors, not generic seed formation.
- S2 assumes a compliant refinement; protection retention is not refinement
  existence, role aggregation or full solution coverage.
- DREL-1 preserves active predicates by passing them the same independently
  interpreted incidence. It does not define an unknown source semantics into
  existence. DREL-2 remains an actual semantic leaf obligation.
- Recursion uses pointwise defining-operator equality, not bare equations or
  equality of projected solutions on different recursive carriers.
- Admission/all-world, common-allowance and production consequences retain
  their hypotheses and quantifier order. Option 2 extras are allowed without
  reference source constructors.

**Compiler-referee batch 2:** no blocking or major findings on the typed
bridge, falsification note or checker. One minor finding was accepted:

> The loop labeled as four endpoint-valuation checks constructs an unused
> `Xi`; each iteration repeats the same symbolic closure check.

The primary removed that loop and the `endpoint_valuations` output field,
and corrected the note's coverage description. The explicit global-equality
mutation still consumes equal effect values and rejects merging their
origin-tagged protection. No generation or transport rule changed. This was
a minor verification/reporting correction, closed by primary diff inspection
and one focused final run under the repository's minor-only convergence
rule; no additional review panel or broader experiment was needed.

**Spec auditor:** no blocking, major or minor authority-conformance findings
on the five frozen targets. The audit specifically checked the conditional
`r_A` receiver schema, stage versus delivery order, conditional role refinement,
one original `xi`, actual role/entry preservation, no Q-created evidence,
and the unaltered callback B / Option A / Option 2 boundaries.

No accepted blocking or major finding remains. Review/status metadata and
links to this record were added after review; the only executable correction
is the deletion described above. Such metadata does not certify a stronger
statement than the reviewed targets.

## 3. Precisely reviewed results

The reviewed package supports:

1. The selected binder-registration/Name/Call composition can produce its
   local seed-at-exposure witness and upper output mark before solving.
2. Already justified lower information remains an active constraint and
   receives no backward mark. Certified multi-use/freshening preserves source
   occurrences, scope, shared roots and inherited evidence.
3. Fair replay of fixed certified source facts is independent of physical
   delivery order. Genuine late semantic applicability is a separate source
   premise, not supplied by saturation.
4. Directional inlining versus materialization preserves an independently
   interpreted whole relation even when its active predicates read protection.
   Full independent seed/refined source normalization still requires DREL-2.
5. A realized upper fragment and a supplied typed capture/read association
   compose by the common indexed image, with original provider evidence and
   receiver identity retained. They do not create the initial realization.
6. Finite countermodels distinguish cross-use witness stitching, active lower
   evidence deletion, and the gap between old-predicate graph extension and
   protection-sensitive semantic preservation.

The pointwise/conditional transport supports every already admitted world or
production alternative in its stated interface. It does not construct the
all-world domain, prove new production containment, or enlarge `V_alloc`
to all independently valid source views.

## 4. Verification and exclusions

Focused commands used on the research package:

```sh
python3 tools/research_directional_protection.py
timeout 60s python3 tools/research_directional_source_relation.py
git diff --check
```

The old local checker passed its existing 32,768 joins, 32,768 record-order
checks, 18 focused equalities, one invalid-identity rejection, 256 joint
relations, 768 query filters, coherent renaming and seven total mutations.
That existing scope is unchanged.

The new checker passed after the minor correction: 5,040 permutations of
seven delivered inputs with the second use delivered last; one additional
opposite-use-order schedule; one stage/applicability-erasure pair; two
anti-correlated original joint rows; eight lower candidates and four
lower-constrained observation candidates; ten shortcut mutations; and one
invalid captured-root transport. These are **not** all eight-input
permutations or a parsed-source inference test. Symbolic denotation independence
is a property of the rule interface, with a separate explicit equal-value
mutation; no four-valuation coverage is reported.

One bounded single-process checker ran per invocation, with a 256 MiB
address-space limit, 55-second CPU limit and 60-second external wall limit.
The primary checked local references, whitespace and changed-path scope.
No Cargo build, broad test suite, parser/source acceptance, production effect
solver, runtime handler trace, Oracle run or performance benchmark was used.
The typed note's implementation/Oracle table is a direct producer audit;
the compiler referee did not independently certify that table as production
correspondence.

The source-origin supplier for arbitrary recursive/generalized uses,
genuinely late source-seed applicability, source-to-received-view realization,
typed capture attachment, full semantic refinement coverage, initial/world
admission, all-view principality, finite effective presentation and production
conformance remain open. No implementation authority follows from review.

## 5. Integration discipline

The research started from the fetched actual origin `e12738d4`, which already
contained independent review of the previous local directional rule. New
review was performed for this package. Upstream `51e61b4f` and `4be72ac1`
were incorporated without altering them; the governing rule files were
unchanged in that interval. Further origin movement must be checked before
publication. Only exact research/status paths belong in this change.

The primary retains task/theory synchronization and Git integration. Pending
question bundles, frozen historical ledgers, production/shadow code and test
expectations are outside this change. No force push or other-worker rollback
is authorized. The actual published SHA belongs in the final report after
remote verification, not as a predicted self-referential commit in this file.

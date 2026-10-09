# Builtin `any`: descriptor-introduction package obstruction

Date: 2026-10-10
Status: frozen, independently reviewed exploratory research; no semantic or implementation authority
Baseline: `c3cb59dfabf2410dba3b76946540027f663e6677`
Branch: `research/simple-sub-intrusion`
Exclusive write lease: this file only
Review: `compiler_referee` and `spec_auditor`; no findings within the selected scope; prior-decision delta review by `compiler_referee`, no findings
Objective: construct the builtin descriptor package needed by `my widened = 0 as any`
Method: invert the selected descriptor/registry constructors after approved builtin lookup
Claim class: bounded constructor characterization and minimized missing premise; no new theorem closure

## 1. Result and fixed decisions

Approved lookup selects lowercase `any` as the builtin Type name at this
written occurrence. The next required input is an independently specified,
complete **builtin Any descriptor declaration**, with its ordinary Value
interpretation and typed membership/guard/evidence signature. Within the
selected supplier envelope below, no constructor introduces that declaration.
The selected leaf and proof registries consume independently supplied meanings.
Thus this attempt stops before attaching the declaration to an ordinary root.
It does not assert that a source-owned package is impossible under some later
selected definition, or that the program is rejected by the language.

The [name decision](../design/2026-10-10-source-annotation-any-name-design.md),
lines 7–19, is the current narrow authority: builtin precedence, no shadowing,
no uppercase builtin alias, and name introduction/lookup only. In this note
`Any` names the semantic target mentioned in existing documents; the exact
source spelling is `any`. No question-board file was read. The primary supplied
the accepted decisions, including that semantic root/guards/Top/implementation
remain open and that the complete Call contract stays fixed.

One related user-accepted criterion is bounded to a different position:
[`zero`'s principal-scheme criterion](../progress/2026-10-04-principal-scheme-acceptance-criteria.md),
§§1–2 and “Clarification,” accepts `Top -> int` with surface spelling
`any -> int` for `my zero x = 0`. The same record expressly limits this to
that negative Function argument and says it establishes no general
interpretation of `Any` or polarized `Top`. It therefore records a required
practical inference presentation, but supplies neither the ordinary
`Value(Any)` root nor its complete membership and hereditary evidence for the
separate written-target case analyzed here.

The [one-case owner design](2026-10-10-source-owned-annotation-any-design.md),
§§1–4, lines 27–32, 36–60, 69–87 and 91–107, selects source-owned,
proof-only annotation formation and conditional Direct consumption. Its
reviewed owner plan does not furnish the missing semantic declaration. Its
header remains Draft. This note changes neither that status nor its authority.

The [prior attempt](2026-10-10-source-annotation-any-root-construction-attempt.md),
§§2–4, locates H2: written-Type formation must supply the complete root and
interpretation. That result remains conditional. This attempt factors H2 at
its **builtin semantic declaration input**, now that name lookup has been
selected. It does not repeat the prior H0–H4 boundary proof or treat the name
approval as semantic approval.

## 2. Exact supplier envelope

Navigation used `notes/design/INDEX.md`, active annotation entries at lines
114–143; actual source sections govern:

| Source / exact section and lines | Selected consequence | Unsupplied input |
| --- | --- | --- |
| [Source Generalize selection](../design/2026-10-08-source-generalize-definition.md), §2, lines 35–65 | Selects SRC §§3–5; final annotation target survives Generalize. | An annotation target's genuine meaning. |
| [SRC](2026-10-08-source-generalize-definition-and-proof.md), L3/L4, lines 87–96; §3.1 line 137; §3.2 lines 167–173 and 193–203 | Literal needs its actual declaration; Top uses existing membership; annotation checks its written target. | Neither schema elaborates builtin `any` into a descriptor declaration. |
| SRC §3.3, lines 219–237 | Typed records are owner outputs; written constants are Intrinsic; logical checking keeps its original binders. | Classifying a field does not give its semantic contents. |
| [Contextual Function selection](../design/2026-10-08-contextual-function-membership-definition.md), §3, lines 80–86 and 101–114 | Selects hereditary immutable interpretation and positive simultaneous construction. | Does not select an exhaustive descriptor model. |
| [Original semantic input](2026-10-08-call-semantic-input-realization.md), §4.1, lines 286–294 | Ground facts and Function/carrier cases retain their proper meanings; other descriptor interpretations remain parameters. | A supplied complete interpretation for this builtin descriptor. |
| [Immutable construction](2026-10-08-simultaneous-immutable-root-introduction.md), §3, lines 160–177 and 214–224 | Ground/fixed external clauses retain independent relation, original root/incidence/witness/event fields. Kernel-governed fields cannot be hidden in a leaf. | The independent relation is a premise, not produced by `PhiV`. |
| [CE](2026-10-08-native-projection-certificate-constructors.md), §2.1, lines 77–97; §3, lines 110–138 and 147–155 | Evidence has independent typing; Top retains membership witness, independent law, same value/provider and guards. | The full local law and complete evidence signature are supplied declarations. |
| [PE selection](../design/2026-10-08-native-projection-public-export-definition.md), §§2–3, lines 44–49 and 60–77 | Actual annotation roots survive; native consumer validates finite independent proofs; Any receives no fictitious Function equations. | No Any descriptor introduction. |
| [PE construction](2026-10-08-projection-public-export-construction.md), §4.2, lines 232–248; §6.1, lines 347–358 and 391–396; §6.2, lines 428–440 | Decode introduces a Function root; Direct retrieves complete interpreted roots; whole-value Any example supplies `v_Any` as an operand. | Complete Any descriptor/root, and unknown primitive laws, cannot arise from a bare registered name. |

The construction envelope is these selected schemas and the owner design.
This is not an exhaustive repository or legacy search. No production code,
parser, compiler test, executable checker, or question-board bundle was read
or changed for this attempt. Prior code observations are not re-certified here.

## 3. Required fields versus introduction laws

Let `q_type` be the actual written `any` occurrence under original scope
`sigma_q`. This is a hypothetical authentic source occurrence; parsing the
exact program remains unverified. Use the existing full membership indices
`(v,p,e,xi)` and original binder tree. The following rows are required-data
slots from the selected interfaces, **not** a proposed new semantic relation,
Rust record, runtime object, or exhaustive Any signature.

| Required slot | What is known | What still needs a genuine supplier |
| --- | --- | --- |
| Resolved Type identity and route | Source spelling `any`, builtin lookup/precedence and no import prerequisite are selected. | Authentic occurrence/scope linkage in source formation; executable resolver not claimed. |
| Completed descriptor interpretation | Owner design selects ordinary Value(Any), with no Function inlet/receiver/invocation equations. | Exact membership definition at the full indices and its complete typed operands. A Value head does not fill these fields. |
| Membership evidence telescope | CE requires independently typed witnesses and preserves distinct proof objects at the same tuple. | Actual Any witness fields, dependent binders and lawful introductions. Their contents and arity are unspecified here. |
| Guards and hereditary restrictions | Owner design requires genuine Any guards, original scopes and compatible-future obligations; CE preserves required guards. | Exact Any guard signature and its laws. This note neither sets it empty nor imports Function guards as Any fields. |
| Declaration/registration incidence | Builtin introduction requires no user declaration/import. Direct requires an actual registered interpretation. | Semantic builtin declaration and authentic registration route. A fixed-external *import* constructor is not automatically the selected builtin route. |
| Occurrence/root linkage | Source owner must bind this written Type to a complete ordinary root with scope maps. | Construction from the genuine builtin declaration into this occurrence's root. Fresh allocation versus authentic reuse is unselected. |
| Local Top law | Existing checking catalogue retains same-value/provider Top/Any checks with full independent law and evidence. | Actual independently typed law at the descriptor/root signature. A registry row or name is not this law. |

Only the first row's lookup policy is newly supplied by the name decision.
Rows requiring authentic records remain proof obligations even when their
retention shape is specified. In particular, **required fields are not
constructors**, and a constructor with an independent premise cannot fabricate
that premise. No exact complete Any evidence signature can be enumerated from
these sources without making an additional semantic assumption.

## 4. Minimized construction obstruction

Explicit hypotheses for the bounded analysis:

- **P0 (source instance, unverified):** authentic `q_type/sigma_q` exists for
  the assigned program. This isolates semantics from the earlier operational
  parse/lowering seam; it does not claim executable acceptance.
- **P1 (established selected lookup):** the name decision applies to that
  Type occurrence and selects the builtin target identity.
- **P2 (selected completeness obligation):** written-Type/root formation must
  supply the complete interpreted ordinary Value target before Direct,
  as owner design §3 and PE §6.1 require.
- **P3 (bounded supplier set):** candidates are only the selected schemas in
  §2. This is a coverage bound, not an axiom that the repository contains
  no other useful result.

Construction inversion under P0–P3 gives:

1. Lookup yields the selected builtin Type identity. By the name decision's
   lines 13–19, lookup supplies no membership, evidence, guard or Top meaning.
2. The ordinary target must already have a complete registered interpretation
   when PE's consumer retrieves it. Therefore its semantic declaration is an
   antecedent of consuming the boundary proof.
3. `PhiV`'s ground/fixed-external branch can incorporate an independently
   supplied relation. Substituting the target identity for its descriptor
   parameter leaves exactly that relation, original incidence and witnesses
   as premises. Choosing a branch does not instantiate their contents.
4. CE's Top row and `Apply_L` interpret a genuine independently typed law.
   Choosing a Top tag leaves that law and its dependent signature as premises.
   PE explicitly refuses certificates obtained by registering an unknown law's
   bare name. A proof that preserves a completed membership certificate cannot
   serve as the missing definition of that membership.
5. PE decode's actual head is Function. Changing its result field to Any
   leaves a Function descriptor and cannot yield the required ordinary Any
   declaration. Annotation's final-root rule requires its written target.

The first unfilled input is therefore:

> the genuine semantic declaration of the builtin Any Value descriptor,
> including its complete independent membership/guard/evidence interpretation
> and registration signature.

This is a minimized **open premise**, not a semantic counterexample. It is
already exposed by the one written Type occurrence; the literal supplies an
operand value, not the declaration of its written target. Removing the
annotation removes the assigned question. Adding Call, projection frames,
solver models or more input values does not supply a descriptor declaration.

This partial input diagram localizes the gap more finely than prior H2:

```text
q_type = written `any`, sigma_q
    -- selected builtin lookup --> builtin Type identity
    -- [MISSING: semantic descriptor declaration/signature] --> completed contract
    -- source-owned occurrence/root formation --> actual ordinary target root
```

There is no new conditional Top theorem in this note. Even assuming a
membership certificate specifically for `0` would leave the independent
complete descriptor record absent; PE retrieves that record separately from
the submitted finite boundary proof. Assuming a completed contract would
permit examining occurrence/root packaging, but would bypass the exact premise
this assignment asks to construct.

The prior owner attempt and this builtin declaration inversion leave the same
semantic supplier open. Under compiler-engineering's proof-economy rules,
lines 23–71, this is an A/B formation prerequisite for any future authorized
acceptance of the selected ordinary annotation case. It is not a stronger C
characterization and is not yet D reconstruction debt: no inspected owner has
first constructed and then discarded the missing declaration. Retaining
syntax, scope or an identity can prevent later provenance debt, but cannot
retain a membership meaning that was never supplied. Another assumed-Any
checker would leave the same premise untouched. This classification grants
no implementation permission and changes no canonical gate status.

## 5. Evidence quality, failures and limits

This is constructor inversion grounded in the selected sources. There is no
independent executable oracle. The analysis shares the source documents'
interface and genuine-local-law assumptions; it does not prove those laws or
validate their omitted semantic definitions. A checker supplied a candidate Any
relation or transition rules would provide consistency evidence about that
candidate and could not establish that the source selected it.

No candidate Any interpretation is introduced. In particular, universal
membership, guard-free truth, a negative-bound Top node, and endpoint-derived
meaning are not used as assumptions. No model enumeration or mutation was
run; seeds/ranges, mutation coverage and performance samples are inapplicable.
The absence claim is bounded to the enumerated constructor sections. A
previously selected exact builtin semantic supplier outside that envelope
would invalidate the obstruction's coverage conclusion and require a focused
source bridge, not a silent extension of this note.

Failure conditions for eventual packaging include wrong source occurrence or
scope; unresolved/mismatched semantic target; missing complete declaration,
guards, typed witnesses or registration; hiding kernel-dependent obligations
inside a fixed leaf; substituting a Function root; or binding Top to different
roots/full indices. No source rejection rule follows from these conditions.
Source parse acceptance, resolver implementation, complete builtin semantic
selection, full Top construction, root allocation/reuse, runtime/production
routing, failure/resources, arbitrary annotations and complete Call remain
unverified or outside scope.

Recommended next action: the primary should obtain or select the exact builtin
Any semantic declaration and its genuine full signature in a separate narrow
semantic gate, preserving the existing Value/Top intent and complete Call
contract. If an already selected source supplies it, return that exact section
instead. Resume package construction only once that supplier is available.

## 6. Commands, resource budget and frozen dependencies

Checks were read-only branch/SHA/status, bounded `cat`, `rg`, numbered narrow
source reads, `sha256sum`, and `git diff --name-only <baseline> -- <dependency
paths>`. The dependency diff was empty when drafting. The sole write was this
leased note. One lightweight shell command invocation ran at a time; no
heavyweight computation, tests, builds, parser/probe, scratch output, Git
mutation, delegation or question-board operation occurred. Locator output was
truncated once and followed by exact narrow source reads. CPU time, peak RAM
and total wall time were not instrumented; tool-reported read commands each
completed in under one second. No measurement budget was consumed.

Direct semantic dependency SHA-256 snapshot:

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-source-annotation-any-name-design.md` | `3cb57799e423f7c5036aa02e77e232b1924ecf3d8487c2649bb669d70da0e238` |
| `notes/theory/2026-10-10-source-owned-annotation-any-design.md` | `bfff9fdfa6e5aa9258949992d0711fa674b91fdde501e0a658e02b3712999a3e` |
| `notes/theory/2026-10-10-source-annotation-any-root-construction-attempt.md` | `f336a0d8081607debe27ffd0c9d46716b39e55ce8ec14fb05c25ab28bf77e9b5` |
| `notes/progress/2026-10-04-principal-scheme-acceptance-criteria.md` | `13c6feb02727d8cc735dcb19843b337dee9126cd7afc519f3d18c6e1cdf95337` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| `notes/theory/2026-10-08-call-semantic-input-realization.md` | `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a` |
| `notes/theory/2026-10-08-simultaneous-immutable-root-introduction.md` | `a5efa7056b12f931892548ecf3366d66156627ec44577c99d20ca48596438ae6` |
| `notes/design/2026-10-08-native-projection-public-export-definition.md` | `aed6ef63b01f555a5f2804f87a599167c1a30fa999afc0b9d9f11b8ae974a919` |
| `notes/theory/2026-10-08-projection-public-export-construction.md` | `4cf84e7a38153b893f1d339780598e2b79084c747ecb883acf0e4fdaa49cf631` |
| `notes/theory/2026-10-08-native-projection-certificate-constructors.md` | `04c5699dfaaf5f98ee9db54df5bd124f25e7131abb6bc3104e1675a5490f74a8` |

Policy snapshot: `rules/research-lab.md`
`5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6`;
`rules/design-authority.md`
`925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5`;
`rules/git-concurrency.md`
`e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e`;
`rules/compiler-engineering.md`
`1ff144d376052d2e01d2e97ba3290e6942f126765067fbf11dfeffc06f89b442`.
Navigation/task records were read as locators only; their content is not a
semantic premise. The primary must revalidate dependencies before integration.

## 7. Commit packet

- Exact leased path: `notes/theory/2026-10-10-builtin-any-descriptor-package-attempt.md`.
- Baseline SHA: `c3cb59dfabf2410dba3b76946540027f663e6677`.
- Changed dependency hashes: none observed against the pinned baseline.
- Review status: frozen, independently reviewed exploratory bounded obstruction;
  the added `zero` criterion clarification also received focused delta review;
  no semantic approval, theorem closure or implementation authority.
- Checks already run: bounded source/constructor inversion, exact supplier
  lines, read-only identity/status, dependency hashes and baseline-path diff;
  no executable verification.
- Proposed research-checkpoint commit message:
  `research: isolate builtin Any descriptor declaration prerequisite`.
- Shared-record deltas intentionally left for primary/curator: record that
  builtin lookup is selected while the complete builtin semantic declaration
  is the first open input inside prior H2; keep root/Top/implementation gates
  open and avoid scheduling another assumed-Any checker. No shared task,
  index, authority, theory map, manifest, lockfile or question bundle was changed.

Producer writes stop at handoff; review is against this frozen artifact and
its recorded dependencies.

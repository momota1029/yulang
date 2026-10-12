# Contextual live PUSH: bounded source-conformance audit

Date: 2026-10-12
Status: bounded source-conformance obstruction, independently reviewed
Claim class: static constructor obstruction, not a source typing counterexample
Baseline: `7aeeb477257e030c218fbba23ed1e60c32d541cb`
Branch: `research/simple-sub-intrusion`
Lease: this file only; leaf source audit, no delegation or implementation

The assigned question is whether the two approved paired-ascription circuits
produce an authentic live contextual PUSH and matching output POP, with actual
shared attachments and per-constructor residual lineage. The audit stops at the
first missing premise: the inspected Y3 ascription route retains a unit-PUSH
marker but does not construct an executable PUSH payload. Matching output POP,
residual lineage, complete replay and publication therefore remain unverified.
This independently grounded source obstruction does not review or certify the
mathematical proof, and does not refute the approved annotation meaning.

## Authority and exact premise

The governing sources are contextual attachment/admission §§3–6, including
§3.1's one attachment identity per exact annotation's concrete set; annotation
effect hygiene §§1–4; the residual-lineage selection's Selected policy and
Preserved contract; and top-level inference principles §§1–5. The latter
supersedes unconditional full abnormal-route restoration requirements. The
current user scope permits proof/source work and excludes compiler edits.

The reviewed finite-observer result is
`notes/theory/2026-10-12-contextual-cycle-summary-proof.md`, particularly
§§1–2 and §6. Its two source circuits come from
`notes/progress/2026-10-10-recursive-push-source-invariant.md`, “Minimal
nonrecursive source”, “Nested actual source”, and “Complete recursive grammar”.
Their Oracle construction result is not current Y3 source conformance.

The missing construction premise is:

> For the actual covariant concrete return-row occurrence of either approved
> paired expression ascription, its selected attachment instance and resolved
> family produce a live unit left-PUSH relation on the actual Effect owners,
> reachable by ordinary source constraint replay.

No assumption that this premise holds is admitted into the audit. The callback
example's corrected former output supplies no expected scheme. There is no
runtime oracle, source-domain restriction, or newly selected semantic law.

## Constructor evidence and minimized obstruction

All locators below refer to the baseline. Source association here means the
ordinary ascription endpoint and annotation occurrence; it does not establish
the separately open type-occurrence/Value-reference association law.

| Layer | Exact owner and observed construction | Boundary |
| --- | --- | --- |
| HIR source | `yu-hir/src/module/local_source.rs:508–522` parses an expression annotation tail and retains `LocalSourceForm::Ascription { inner, annotation }`. | No execution or exact source preflight is claimed. |
| Shared actual endpoint | `yu-solver/src/candidate_source.rs:222–235` peels nested ascriptions/groups and aliases their positions/endpoints to the underlying child; `:413–437` retains `Action::Ascription`; `:662` dispatches it. | Both ascriptions constrain the shared provider endpoint; no inference theorem follows from aliasing alone. |
| Paired annotation | `candidate_effect.rs:1194–1271` calls `candidate_annotation_pair` with identical source/target endpoints. It constructs negative and positive Function views using common variable/view maps, then admits provider-to-upper and exposed-to-provider Value links. | Written annotation interfaces do not authorize inferred-entry `both`. |
| Effect row | `candidate_effect.rs:1405–1439` composes argument/result polarity; `:1551–1576` reuses a view keyed by exact row position and creates fresh Support/Allowance ports for the two polarities. | The fresh ports and written tail are not by themselves Oracle's `r --PUSH_i--> e`. Concrete composed-negative rows are separately rejected at `:1507–1509`. |
| Attachment metadata | `candidate_effect.rs:755–769` retains `source_weight` even for an annotation with a symbolic tail, but exposes `closed_weight` only without a tail. `candidate_context.rs:2174–2195` retains owner, exact position, resolved allowed operands, lexical scope and member ordinals; a positive nonempty set gets `SourceUnitPush`. | Reusing the row's view shares its weight/attachment handle within that pair. This is source metadata, not a live operation or a proof of fresh-use identity. |
| Live payload | `candidate_context.rs:115–135` declares `LocalWeight.left_word: [(); 0]` and `right_pops: [(); 0]`; `:2193` initializes both to `[]`. | **First missing premise:** this payload cannot contain even one PUSH or POP. |
| Context admission | `candidate_context.rs:2483–2494` chooses only `Allowance.closed_weight` and creates `PrefixLeft { weight, input: IDENTITY }`. | A ContextExpr prefix node is not evidence of a PUSH: its live weight is a zero-word filter. A symbolic-tail source weight is not selected here. |
| Detached preparation | `candidate_context.rs:2200–2215` materializes one detached PUSH from `SourceUnitPush`; `:1487` evaluates supplied detached weights. | Neither function has a non-test call site in the inspected solver tree. The adapter returns `DetachedWeight` and constructs no live relation, bound, registration or executable word. |

The smallest obstruction needs only the first annotation's concrete covariant
return row `[io; 't]`, which is common to both approved examples. Even granting
successful HIR construction and admission, that row's `source_weight` has empty
live words and, with its tail present, no `closed_weight`. Thus neither dormant
`SourceUnitPush` nor `PrefixLeft` supplies the required live unit operation.
The paired Function/value links can be retained while this premise remains
absent. The argument is a static representation/constructor derivation, not a
claim that an exact program parses, executes, terminates or obtains a scheme.

The live zero-word consumer corroborates the distinction:
`candidate_zero_word_filters` at `candidate_context.rs:2644–2667` validates
empty words and an exact closed view, and `candidate_context_execute_relation`
at `:2744–2812` discharges retained Allowance checks. Its existence establishes
a zero-word check consumer, not an attachment-local PUSH/POP subtraction
consumer. No semantic rule is inferred from that implementation behavior.

## Stop boundary and unverified owners

Inspection stops at the absent live constructor; no downstream workaround is
designed. The following remain unverified for the approved paired circuits:

- Matching returned-value/output POP with the same actual attachment, and the
  nested source's left POP into its inner return-Effect owner.
- Exact Y3-to-Oracle owner correspondence, concrete Act seed admission, source
  preflight/acceptance, complete Call and actual output contribution preservation.
- Attachment-qualified residual recipes, distinct constructor lineage,
  current/future lower fan-out, gamma feedback and outgoing projections.
  The existing `ReplayRecipe` evidence records are not certification of this
  required residual-constructor premise.
- Context-sensitive bound/replay completeness, capture/freshening, extrusion,
  qualifying intrusion, finite certificate generation/invalidation, suspension
  and public publication of consistent results.

The already inspected ContextExpr/function-port constructors retain inherited
contexts and dependency records (`candidate_function_port_admit:2557–2607`).
This does not manufacture the missing payload. Replay and local check
publication are distinct from source operation generation and public scheme
publication; none is used to close the original source/output gate.

Independent `spec_auditor` review found no blocking, major, or minor issues.
It confirmed the zero-length live word fields, symbolic-tail exclusion from
`closed_weight`, closed-weight-only context admission, and detached adapter
boundary. Review scope did not include exact program acceptance/execution,
matching POP, residual-lineage consumers, generalization, lifecycle, or public
output; this note makes no claim on those obligations.

## Checks, independence and resources

Commands: read-only `git status --short`, `git branch --show-current`,
`git rev-parse HEAD`; bounded `rg` and `sed` source/authority reads;
`git diff <baseline> -- <ten dependency paths>`; dependency `sha256sum`.
The dependency diff was empty. Non-test search for `materialize_unit_push`,
`evaluate_context`, `SourceUnitPush`, and `LocalWeight {` found only their
definitions/construction in `candidate_context.rs`; no non-test adapter caller.
This is bounded solver-tree evidence, not a compiler-wide absence theorem.

The authority and source files are separate evidence: neither an executable
reference nor an assumed transition checker is used as an oracle. Shared
premises are the primary's pinned authority and source-domain locators. No
build, test, probe, mutation, seed/range search, benchmark or Git mutation ran.
One lightweight process per read/hash command; no heavyweight processes or
measurement samples. Wall time and peak RAM were not measured. No numeric
CPU/RAM/wall limit was supplied beyond the no-build/test/probe assignment.
Only the leased note was written; pre-existing dirty artifacts were preserved.

Recommended next action: the primary should assign the exact authentic
annotation-to-live-PUSH construction premise to its responsible proof/source
owner under the existing approved semantics; keep implementation and complete
source/output gates OPEN until that premise is grounded and reviewed.

## Commit packet

- Exact leased path: `notes/progress/2026-10-12-contextual-live-push-source-audit.md`.
- Baseline: `7aeeb477257e030c218fbba23ed1e60c32d541cb`.
- Status: bounded source-conformance obstruction, independently reviewed; no
  theorem or production gate closure.
- Checks already run: documentary/source reads, baseline dependency diff and
  SHA-256 capture; no builds/tests/probes. Final note whitespace and dependency
  revalidation are recorded in the handoff.
- Proposed subject: `research: audit missing live contextual PUSH constructor`.
- Changed dependency hashes: none. Direct dependency SHA-256:

```text
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  notes/design/2026-10-10-contextual-attachment-admission-design.md
503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98  notes/design/2026-10-10-contextual-residual-lineage-selection.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
6e5561c8614148a8c19c72231cecb9706a64757c58d8fae7a23199591cc387c1  notes/theory/2026-10-12-contextual-cycle-summary-proof.md
fb7793967fd9e5aa1610c4b1bca5686247c1744c04bff149c107afb36e343790  notes/progress/2026-10-10-recursive-push-source-invariant.md
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df  crates/yu-solver/src/candidate_effect.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
```

Shared-record deltas intentionally left for the primary/curator: cite the exact
missing live constructor and its source owner if accepted; retain matching
POP, attachment/lineage consumers, publication and the parent contextual
source/output theorem as OPEN. No shared task/index/authority/question changes
are proposed as part of this checkpoint.

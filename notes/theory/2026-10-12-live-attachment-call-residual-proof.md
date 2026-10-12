# Live attachment through direct and aliased Call: exact constructor boundary

Date: 2026-10-12
Status: frozen research handoff; bounded fresh-map claim independently reviewed; original effect-hygiene gate OPEN
Claim class: unsupplied source premise, with a bounded constructor-local fresh-map derivation
Primary baseline: `b4c46cf05bc62a53b61141605686be2177b82358`
Exclusive lease: this file only; proof leaf, no further delegation

## 1. Frozen statement and authority

Keep [H](2026-10-11-oracle-global-effect-hygiene-proof.md) §1 unchanged:
for every Oracle program P in its original successfully lowered domain, every
successfully lowered composed-negative concrete annotation a with its original
scope sigma and binders, every actual copy/instantiation u, and every actual
function Call/output route k involving a, a's subtraction removes only its
attached contribution on that route. An independent same-family contribution
survives. Symbolic tails remain connected; every current/future concrete lower
reaching the relevant receiver encounters the retained check. Occurrence,
attachment, scope, actual provider/call binder and correlated residual lineage
remain identified through copying/generalization under the consistent fresh-use
renaming. Incorrect lowers require an authentic check/error and safe
nonpublication, rather than acceptance. This note does not prove H or narrow
its domain to the current Y3 carrier.

The assigned Y3 bridge fixes each actual supported source occurrence a, original
owner o, exact row position p, scope sigma, resolved concrete set C and original
symbolic binder x when present. For every actual direct or alias Call k and
fresh use u, derive one jointly owned attachment route from source construction
through its live PUSH/POP/filter operations into the actual output and every
selected residual consumer. Each residual creation retains its own lineage,
source, heads, gamma, feedback and exact gamma-to-original-tail projection.
Receiver/provider, attachment and residual witnesses must belong to this same
construction; they cannot be selected independently after endpoint equality.

Authority: [annotation hygiene](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5; [residual lineage](../design/2026-10-10-contextual-residual-lineage-selection.md),
“Selected policy”; [attachment/admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§§3–6, including one identity per exact annotation set and member ordinals in
§3.1; and [inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. [Complete Call](../design/2026-10-07-complete-call-contribution-definition.md)
§2 retains callee computation, whole argument, actual returned provider/entry,
return/future interfaces and independent alternatives with their evidence.
A four-port demand alone does not establish that meaning.

Local hypotheses below: actual source bytes listed in §6; valid retained graph
handles; normal completion of the named constructors in one live session before
allocation exhaustion. These supply neither source admission nor complete
capture, consumer activation, typed-view transport, complete replay or Call.
The withdrawn callback output, arbitrary concrete-negative admission, new
semantics/restrictions and global soundness/principality/F5 closure are excluded.
Necessary safe nonpublication remains; exhaustive abnormal restoration is not
introduced as a general premise.

## 2. Established inputs and stopping point

Use the existing [source map](2026-10-12-effect-hygiene-source-construction-proof.md)
§§2–4 and [negative constructor bridge](2026-10-12-y3-negative-effect-construction-bridge-proof.md)
§§3–5 for source occurrence/binder retention and the negative guards. Use the
independently reviewed [coupled obstruction](2026-10-12-y3-effect-call-output-coupled-proof.md)
§3 for its empty executable-word carrier lemma. Its five directly used solver
files are byte-identical to its recorded fingerprints at this inspection.
These results are dependencies, not repeated proofs or new parent progress.

The first missing constructor remains the live operation emission at
`candidate_effect.rs::candidate_signature_view:733–774` and
`candidate_context.rs::source_weight:2174–2196`. The successful annotation view
retains a payload identity, owner, p, sigma, C and ordinals. The selected source
marker at `candidate_context.rs:2187` is explicitly dormant. Its adapter at
2200–2215 returns a detached weight and installs no live relation, bound,
registration or executable operation. Thus the implication

```text
actual annotation-owned payload -> its executable source attachment operation
```

has no current supplying constructor. `PrefixLeft(weight, input)` cannot be
renamed to a live PUSH merely because it names this payload. Closed Allowance
seeding at `candidate_context_source:2483–2501` creates a zero-word filter;
open-tail source metadata creates no such filter. Neither is the missing
attachment operation. The negative source guards remain as established in the
input notes; bypassing them is outside this lease and supplies no emission.

No live source-owned attachment satisfying the requested antecedent was
constructed. Quantifying only over existing live instances would hide the
missing source bridge in an empty domain. This is an implementation premise
obstruction, not semantic infeasibility or a source-qualified counterexample.

## 3. Bounded direct/alias and fresh-map derivation

The direct formal source owner allocates `FormalRegistrationInput` from the
actual Lambda parameter (`candidate_source.rs:189–201`) and assigns
`FormalNameInput` only to resolved parameter Names (239–246). Apply at 394–412
retains the actual callee/argument endpoints, evaluation effects, result,
application effect, occurrence and optional formal-name index. Group,
Ascription and Block forward that optional index from their actual child;
a resolved local alias Name instead schedules `Action::Local` at 381–389.
The alias is not given the direct parameter-name record by matching rows.

`route_candidate_local_run:1354–1399` reads the actual installed local root and
boundary, calls `capture_candidate_graph(root,boundary)`, constructs one
`FreshUse`, and retains it with this local, occurrence, destination and level.
`step_candidate_local_use:1500–1520` restores captured bounds in order, then
links that use's reconstructed root to that Name's actual Value component.
This is a real alias-to-native-Call producer route, not provider completeness.

**Local map conclusion.** For every successfully completed
`prepare_candidate_fresh_use` and every fixed key `(v,t)` it actually passes
to `candidate_remapped_effect_view`, all endpoint uses of that key obtain the
same fresh view. If the captured state also contains a source `LocalWeight`
payload for that original view, each context-payload use of the same key
obtains the same copied payload. That copied payload retains its owner, row
position, resolved members, stored scope and composed polarity; different
completed fresh-use allocations obtain distinct copies for such payloads.
Operation-owned Support/Allowance views can have no source payload, so this
conditional theorem asserts no attachment payload or metadata for them. This
constructor-local property is not the requested attachment theorem.

Derivation: `candidate_scheme.rs:1037–1071` creates one `view_remap` and uses it
for Support, Allowance and AnnotationMember endpoints. The context-payload
loop at 1089–1107 runs only for retained payload references; it uses that same
map, validates the original payload/view, and stores the copied payload in
`weight_remap`. At
`candidate_effect.rs:832–847`, an existing `(v,t)` returns its stored copy;
a miss copies once and inserts that exact key. The copy at 806–830 validates
the source payload, copies the source metadata and members, and returns to
the single source-weight allocator. Arena append yields distinct payload IDs
for different successful allocations in the retained state. Same-key reuse
therefore relates endpoint and context copies through an actual shared map,
rather than independently chosen witnesses. The statement does not assert
that unequal `(v,t)` keys identify one attachment.

Context reconstruction at `candidate_context.rs:1266–1379` replaces each
payload through `weight_remap` and each child through one `context_remap`;
Replay keeps its ordered children, Swap its child, and Prefix/Suffix their
operator. Shared source children use the same map entry. Capture discovers
payloads only from retained reachable bound relations and their post-check
context roots (`candidate_scheme.rs:747–789`). Moreover `context_payloads`
explicitly rejects `BothFromRight` at `candidate_context.rs:1413`.
Neither this discovery nor successful reconstruction proves capture of all
source obligations, authorized `both`, or retention of a residual graph.
The latter has no constructor in this attachment route.

## 4. Actual consumers and exact unverified join

The actual Apply owner validates source-input/recipe incidence before building
its native interface (`shadow_apply.rs:1312–1397`), and emits its callee
evaluation and invocation effects to the actual application effect at
1425–1444. `candidate_call.rs:26–55` stores these source/native endpoints;
its optional formal-name field is not attachment or returned-provider evidence.
These consumers do not receive a live source attachment from §2.

Function-port admission swaps argument Value/Effect and preserves result
Value/Effect, using the actual parent's post-check context
(`candidate_context.rs:2557–2608`). Reached zero-word filter execution uses
the task's actual lower endpoint, registers/replays its Allowance and only
then records discharge (`:2744–2814`). Concrete Support/Allowance comparison
enumerates members/tail or checks/forwards the same concrete endpoint
(`candidate_effect.rs:888–958`). These are specific real consumers, without
an attachment-local operation or lineage-owned gamma supplied by their calls.
`discharge_residuals` is a relation-to-context map, not the selected residual
recipe. No operation or lineage identity is inferred from that name.

The unsupplied joint premise is: the owning source constructor emits its live
attachment on the actual contribution/Call route, with the correlated output
operation and checks, followed by each authentic residual creation and its
two live obligations. §2 is the first failure. The downstream output,
independent same-family survival, actual provider, current/future fan-out and
reverse gamma feedback remain unproved, rather than conditional conclusions
obtained by assuming this premise.

## 5. Economy audit and one next action

The previous negative-constructor and coupled-carrier attempts already leave
this same source emission premise untouched. This pass stops there and does
not repeat detached arithmetic or the empty-word induction. Under
[proof-obligation economy](../../rules/compiler-engineering.md), source hygiene
and ordinary inference are A/B obligations. Reconstructing the occurrence,
scope or identity later from equal rows would be D debt: signature formation
already owns those inputs. The fresh-map derivation locates retained metadata;
it neither creates the missing operation nor changes the original gate status.

One next action: the primary supplies a bounded construction packet at the
source view/payload seam with its actual executable operation and source/Call
incidence as the decisive evidence, then returns that frozen construction to
the continuation proof and independent review. Keep the approved §6 source
slice, negative preflight, and dependent production gate unchanged. Original
H, complete Call, soundness, required principality and F5 gates remain OPEN.

## 6. Checks, runtime and frozen dependency snapshot

Static commands only: `cat`, bounded `sed`, `rg`, and Python SHA-256/relative-link/
whitespace checks. No code/test/build/probe/Oracle execution, Git operation,
delegation, shared-record edit or external contact. Initial independent reads
used at most three concurrent lightweight commands; subsequent reads were
foreground and sequential. No heavy process or measurement sample ran.
CPU/RSS and elapsed wall time were not instrumented. Initial combined output
was truncated; governing clauses and relied-on constructors were reread in
bounded output. Primary retains verification and integration ownership.

Requested routing: `gpt-6.1-sol` / high. The callable schema exposes `prover`;
`.codex/config.toml` registers it and its role file omits model/effort pins.
Observed effective runtime model/effort: unknown. No override, Astra execution
or hot reload is claimed. Independent review of this note is pending.

Hashes below identify the exact bytes read, not an independently verified
baseline equality claim. No dependency was written. The primary must compare
them with the assigned baseline before integration; the current task's gate
paragraph in `tasks/current.md:12295` is a scheduling locator, not a proof
premise. Shared records can move independently of this source cone.

```text
ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df  crates/yu-solver/src/candidate_effect.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35  crates/yu-solver/src/candidate_call.rs
cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411  crates/yu-solver/src/shadow_apply.rs
503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98  notes/design/2026-10-10-contextual-residual-lineage-selection.md
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  notes/design/2026-10-10-contextual-attachment-admission-design.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e  notes/design/2026-10-07-complete-call-contribution-definition.md
6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1  notes/theory/2026-10-11-oracle-global-effect-hygiene-proof.md
9ef17e83908d31d2483a65e23317f84fdd8176102dafb038903477bcfcd4f268  notes/theory/2026-10-12-effect-hygiene-source-construction-proof.md
1a58d1134091e0b91acaf8014baca3a43f72b7764889ff15bbb3c382cd6245e6  notes/theory/2026-10-12-y3-negative-effect-construction-bridge-proof.md
7e0bcc467391a052e834bfa40343af845ba74788d1d74a00ae4e20c686d69192  notes/theory/2026-10-12-y3-effect-call-output-coupled-proof.md
9b17e2b4116ff265e0a218daf799e01d8a76f61de2a8e7fa17be869b991b459d  rules/agent-orchestration.md
3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69  rules/research-lab.md
e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1  rules/design-authority.md
4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9  rules/compiler-engineering.md
2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6  rules/git-concurrency.md
dae388e4e811c346727ec6688472c7fcf6341ddc5466168cfaa03fdcc0b8e17a  .codex/config.toml
485a26c7409e16c692ad10095031ab0e7084726ec5da5666082b3bbc4a5daf98  .codex/agents/prover.toml
```

## Commit packet

- Exact frozen lease: `notes/theory/2026-10-12-live-attachment-call-residual-proof.md`.
- Baseline: `b4c46cf05bc62a53b61141605686be2177b82358`.
- Changed dependencies: none written; frozen read hashes above; baseline equality awaits primary validation.
- Claim/review: unsupplied first source emission premise and bounded fresh-map
  derivation. Fresh independent `compiler_referee` worker
  `/root/live_attachment_call_review` initially found a major quantifier issue
  concerning payload-less views. The primary repaired §3 to state unconditional
  same-key view reuse and conditional payload/metadata reuse only when a source
  `LocalWeight` exists; the same reviewer delta-reviewed that repair and
  reported PASS with no remaining findings. Effective review model/effort are
  unknown. This is research-only and constructor-local; parent OPEN.
- Checks: owner reads, dependency hash stability, local links and whitespace; no executable verification.
- Proposed message: `research: pin live attachment constructor gap and alias fresh-map seam`.
- Shared-record deltas left for primary/curator: retain the same OPEN gate and owning source seam; record the within-use `(view, mapped tail)` map fact without promoting it to live attachment, full capture or Call preservation. No shared record was edited.

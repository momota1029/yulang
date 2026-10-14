# Native handler residual cut: existing Allowance feasibility

Status: independently reviewed primitive P, conditional on its explicit native
processing premises; primary acceptance below. Original shallow Catch residual,
effect hygiene, soundness and required principality parent gates remain OPEN.
Baseline: `21d5a9773e577bf9b49b5d978bc60bedf8d72a42`.
Lease: this file only. Leaf; no children, compiler changes or Git mutations.

## 1. Frozen claims and exclusions

Original parent, unchanged: for every ordinary admitted shallow Catch H under
one original scoped assignment sigma, retain its scrutinee, operation/value
arm binders, raw resumptions, complete provider and dependent future interfaces.
Remove exactly H-eligible scrutinee contributions actually consumed there;
preserve protected, independent, unmatched and future contributions, including
same-family survivors and effects of raw resumption outside H. Preserve each
residual constructor lineage through levels, capture, freshening and qualifying
parent/copy intrusion. No independently chosen marginal witness is allowed.

Narrow primitive P: fix a source row s, resolved concrete head set J, one new
view v with `allowed=J`, `tail=Some(gamma)`, and one fresh gamma. Install
`s <= Allowance(v)` through actual constraint admission. For plain identity
contexts, successful eventual processing of all generated work, and all exact
concrete lowers q reaching s, characterize the generated residual constraints
and the effect of current/future gamma uppers. Distinct constructions have
distinct v and initial gamma, even if later row equality is required.

P hypotheses are explicit: valid live handles; ordinary insertion/replay and
worklist consumers complete without exhaustion/suspension; concrete equality
is the resolved SourceEffectId comparison actually implemented; no unrelated
lower constraints enter gamma for the least-residual readout. Identity context
means no outstanding protection/PUSH/POP obligation, not merely that an
allocated payload currently has empty words. Additional zero-word checks, when
present, retain their own obligations; P does not discard them. Symbolic rows
retain their constraints rather than being declared empty.

Required P conclusion: q with effect in J emits no q-to-gamma task at this
consumer; every other q emits the same endpoint to gamma; gamma's current and
future upper obligations check those forwarded lowers. No new source watcher
is needed for this primitive. This is not a theorem that arbitrary gamma
valuations equal the residual, nor that Catch source admission satisfies P.

Exclusions: no negative-formal enabling, direct-call-only source restriction,
new request token, global Call reproof, full hygiene claim, unsupported source
counterexample, semantics adoption or production promotion.

Authority: top-level inference principles §§1–5 and §1.1; annotation-effect
hygiene integration §§1,3–5 (its §6 callback result is withdrawn); contextual
residual lineage selection, Selected policy/Preserved contract; contextual
attachment/admission §§2–4; SCC intrusion charter §§13–15. The previous
handler-residual-owner-correspondence note §1 fixes the original parent and
§2 establishes authentic Apply/invocation support. This packet reuses that
flow rather than repeating its absent-owner inventory or requesting tokens.

## 2. Constructive constraint elimination

Let S be the nominal concrete support of s and G that of gamma. The native
headed upper relation means `S subseteq J union G`. Hence:

```text
S subseteq J union G  iff  S minus J subseteq G.
```

With gamma upper bounds G subseteq T_i, existence of gamma is equivalent to
`S minus J subseteq T_i` for every i, and the least witness is `G=S minus J`.
This witness is chosen jointly from S and J under the same assignment, not
independently for each bound. The constraints allow larger G: e.g. S={E},
J={E}, G={E} satisfies the headed relation. Thus the relation realizes the
least residual and its upper feedback; it does not axiomatize gamma equality
in every model. Other source-justified gamma lowers or required equality can
enlarge G and must remain; the least-witness statement does not suppress them.

For multiple distinct constructions v_i, keep every
`s <= Allowance(J_i,gamma_i)` separately. The same argument gives the least
residual `S minus J_i` for each independent gamma, before other obligations.
No congruence or lineage merging follows from equal S, J or gamma values.

## 3. Actual native generation and activation

`candidate_effect.rs:888–958`, `candidate_check_effect_operand`, directly
implements P's atomic elimination. Support(v) expands every
AnnotationMember(v,k) and its symbolic tail. Against Allowance(v_i), a concrete
Contribution or AnnotationMember uses its resolved effect identity; membership
returns successfully, while nonmembership enqueues that exact lower endpoint
against canonical EffectRow(gamma_i). Neither origin nor a survivor at the
same nominal point is rewritten by this forwarding operation.

`candidate_extrusion.rs:843–867`, `candidate_apply_effect`, makes
`s <= Allowance(v_i)` a negative exact upper on s and calls
`candidate_replay_bound`. Concrete-to-gamma admission makes an exact lower
on gamma; row-to-row admission retains the existing level-selected orientation.
The replay owner at 765–809 enumerates the opposite bounds. Installing the
Allowance after source lowers therefore checks existing lowers; installing a
new source lower later checks the retained Allowance. Installing a gamma
upper before or after a forwarded lower produces the corresponding comparison.
Reverse feedback is this constraint composition; it does not require eagerly
writing a second synthesized `s <= Allowance(J,T_i)` bound.

Activation is not inferred just from storage. `candidate_context.rs:3007–3093`
forms replay children from the new/old Cartesian fiber quadrants and retains
both relation parents and ordered context; two identity inputs remain identity.
At 3157–3203 it transfers the owned child into `enqueue_item`, or drives an
incoming-use typed drain with its original provenance. `lib.rs:12853–12883`
retains child evidence and queues the typed item; `dispatch_live_item` at
12348–12378 reaches `apply_effect_task`, whose candidate branch at 11717
calls the above actual effect consumer. `candidate_context_execute_relation`
at 2840–2905 returns ordinary dispatch for identity context and separately
executes retained zero-word checks.

`candidate_context_drive_replay` can return Queued while the outer worklist
owns completion. This packet proves the reached transition correspondence and
the P conclusion conditional on successful drain; it does not prove all-history
memo validity, termination of arbitrary context graphs, complete publication
barriers or suspension resumption. Calling only candidate_insert_bound would
not establish current replay. A provisional constructor must use the owning
constraint/drain path or explicitly perform the corresponding replay.

The view constructor at `candidate_effect.rs:758–768` gives an open view
(`tail=Some(gamma)`) no closed_weight. `candidate_context_source` at
`candidate_context.rs:2574–2589` seeds an Allowance relation with identity
unless it has a closed_weight. Thus the proposed open native cut really can
start plain without adding a new context interpreter. This says nothing about
whether incoming source paths have all their semantic protection represented.

## 4. Existing lifecycle keeps this primitive reachable

The headed relation is also retained when gamma is the exported coordinate:

| Owner | Relevant established source operation | Limit |
| --- | --- | --- |
| candidate_effect.rs:554–560 | Registers source/view incidence keyed by the Allowance tail. | Capture incidence is not a solver edge or a new propagation watcher. |
| candidate_scheme.rs:647–656 | Expanding a captured gamma follows incoming incidence and captures source-to-Allowance. | Depends on the relation having been authentically admitted and capture completing. |
| candidate_extrusion.rs:165–179,295–309 | Positive gamma extrusion rebuilds the incoming Allowance with the mapped source/tail and transfers origins. | Copied-bound initialization is not, by itself, proof that every worklist obligation finishes. |
| candidate_effect.rs:808–842; candidate_scheme.rs:1077–1108 | Copies each original view through one per-operation/per-use `(view,tail)` map; freshens generic rows under the existing boundary rule. | Different original view IDs remain different even with equal mapped tails; local authority still needs correct source formation. |
| candidate_intrusion.rs:525–607 | Qualifying parent/copy equality transfers both bound sides and origins, splices incidence, canonicalizes contexts and replays every lower against the merged uppers. | Equality selection is the existing actual occurrence/SCC rule, not row-endpoint SCC membership. |

These paths already preserve the ordinary Allowance construction; they make
adding another watcher mechanism unnecessary for P. They do not turn an
Allowance view into the full contextual ResidualRecipe, or establish protection
transport that its source constructor never emitted. Separate constructor view
IDs survive canonical row equality; if gamma's actual recorded pair qualifies,
its equality still applies. Capture/genericity rules must not be overridden
merely to keep a convenient fresh gamma.

## 5. Exact sufficient source invariant and unsupported premise

The sufficient boundary invariant U is contribution-local under the original
assignment and current receiver activation:

1. Every scrutinee contribution delivered to this cut has its authentic Apply,
   typed path, original origin and complete future interface retained.
2. For each delivered contribution q, `effect(q) in J` is equivalent to
   eligibility and guaranteed consumption at this H boundary. Every protected
   or independent same-family survivor reaches a distinct live bypass
   projection. P's plain membership consumer cannot distinguish two delivered
   contributions with the same resolved effect. A contextual alternative would
   require a separately established consumer law and is not justified by P.
   A shared nominal head alone does not prove this equivalence.
3. Only H's original scrutinee is the source of the cut. Pattern/default/guard,
   selected arms and raw-resumption computations contribute to the outer output
   independently, as required by charter §§14–15. Exhausted ordered matching
   forwards the original request/suffix. Heads cannot assert removal of such a
   forwarded request without a coverage argument.
4. Future lowers, capture/freshening and qualifying intrusion preserve these
   statements and the actual relation parents; they cannot retroactively give
   H authority over a protected future typed path.

Under U and P's successful native processing, the nominal cut removes exactly
the contributions U licenses, and the preserved bypass/outer projections
retain the other effects. Existing one-color hygiene and typed-boundary
transport can be applied once their authentic profiles/owners are supplied;
another proof of those conditional lemmas is unnecessary.

Current carrier does not establish U. Operation views have no source-weight
protection word, while source annotation weights have empty executable words
and only detached unit-PUSH preparation. This is an absence of constructed
protection, not a proof that all arriving source effects are unguarded.
The retained actual Apply provenance and invocation row already establish
operation support flow; no extra per-request token is required for that fact.
They do not prove U's typed-path eligibility or ordered arm coverage.

The semantic discriminator is source-owned: charter §13 requires the protected
callback's argument/environment/returned-value path to survive an inner handler
without the matching contract. Its resolved concrete E may equal E from an
eligible local operation. Passing both through an ordinary headed Allowance
without a protected bypass makes the concrete membership branch treat both
identically. This refutes family membership as sufficient evidence for U;
it is not a new current-Y3 source-qualified Catch counterexample. At the pinned
baseline Y3 has no Catch constructor, and this leaf ran no source program. No invented
source spelling or unverified inferred scheme supplies that missing witness.

Therefore the useful result is **positive algebraic feasibility with an exact
source admission condition**, not a proof that a generic current-carrier Catch
can safely filter its whole scrutinee row. A provisional coupled constructor
can expose this cut and U's actual typed-path/coverage evidence at formation;
it must keep the original ordinary source domain and all dependent production,
hygiene and principality gates OPEN. No blanket direct-operation source
restriction or declaration that empty stored words certify U follows.

Proof-obligation economy: primitive P is a native constraint-elimination result;
U is required A/B source correspondence. Reconstructing eligibility from family
IDs after dropping the boundary facts is D debt. The relevant formation/typed
transport/selection owner should retain and consume facts it actually knows.
Do not add an equivalent family-match proof, repeated missing-nonzero audit or
new reconstruction layer. This packet changes the evidence by establishing the
useful existing primitive, while leaving that precise U premise untouched.

## 6. Producer freeze, checks and handoff (before independent review)

Checks: bounded rg/range reads, read-only baseline comparison and SHA-256
snapshot. All dependency paths below matched the pinned baseline; no dependency
hash changed. No Cargo, tests, executable probe, measurements, build, Git
mutation or child launch. One leaf, lightweight sequential source commands,
within the assigned ten-minute work budget; CPU/peak RAM not measured.
Requested runtime: normal Sol/high leaf. Observed effective model/effort:
unknown, no runtime metadata exposed here. Inspected prover role is registered
and unpinned; this does not establish runtime inheritance or hot reload.
No Astra escalation. Independent review pending; producer does not certify P.

Dependency SHA-256 (paths relative to repository):

```text
2539188fc293e476a38b489132b01f05d8c8de636f0cf435ace26c8a52ed92d3 crates/yu-solver/src/candidate_effect.rs
ed3e213e943a553943784e409194723f64acb810a0bcf06607ee95b0eb4e4ed1 crates/yu-solver/src/candidate_extrusion.rs
c8ef7cc472f0dcb60d793c6f9b4f6ba1aefb76f919ff2a3ce9310f85eb647dcd crates/yu-solver/src/candidate_scheme.rs
77b145ed8a8bf2fae30a07ed74d11a29f38d18930f92e3c1c10456244fe9402e crates/yu-solver/src/candidate_intrusion.rs
ed2981e436e94353411b4a976c09872edd345e381a5847941a7908ffe04005e0 crates/yu-solver/src/candidate_context.rs
4060efb4177b26d5afc395a138fb24c7ef2a641a64f547755775b2c9bd801fd7 crates/yu-solver/src/candidate_source.rs
cd55eb486a17f5a2d487cfd3ef016a6334a625229f15784c88d6237aaafd87f7 crates/yu-solver/src/shadow_apply.rs
91938447f78b6ca6b252a67641f30c2e20f05193d112aa7f0019a87caf6f93e3 crates/yu-solver/src/lib.rs
fab5436a6f37b795c7fb6553c320e2ed942d2ab850d3a446c1fa3e2e3c6ceeaa crates/yu-hir/src/module/local_source.rs
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81 notes/design/2026-10-11-yulang-inference-top-level-principles.md
503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a notes/design/2026-10-10-annotation-effect-hygiene-integration.md
d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98 notes/design/2026-10-10-contextual-residual-lineage-selection.md
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc notes/design/2026-10-10-contextual-attachment-admission-design.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed notes/design/2026-09-29-scc-intrusion-redesign-charter.md
f7e2e99ead9c82d4e163c5ab4d13c36fa022329593da2f8fd52bfe5650f81f1c notes/theory/2026-10-14-handler-residual-owner-correspondence.md
```

One next action: primary expose the smallest reversible source-owned Catch cut
with actual U eligibility/coverage evidence and the outside effect projections;
reuse native Allowance/replay for its certified plain operation. Review U's
protected same-family and forward/raw-resumption cases before production use.

Commit packet: exact leased path
`notes/theory/2026-10-14-native-handler-residual-cut.md`; baseline
`21d5a9773e577bf9b49b5d978bc60bedf8d72a42`; changed dependency hashes: none.
Review: research-only, unreviewed, original parent OPEN. Checks already run:
source trace, dependency equality/hash reads, note trailing-whitespace and
terminal-newline check (passed); no implementation verification.
Proposed message: `research: derive native Allowance residual cut and admission premise`.
Shared-record delta for primary/curator: record existing plain residual primitive
and lifecycle reachability; retain U at formation/typed transport/selection and
successful drain as exact open bridges; keep parent and production gates OPEN.
No shared record was edited. Writes stopped for review at handoff.

## 7. Independent review and primary acceptance

Fresh `compiler_referee` review inspected frozen artifact
`f0cf7df587eef2d156f1496adf57eee36cb5cff3af53c3ba0eb09360fbfbd511`
and the exact baseline code. No blocking or major finding applies to P.
The primary accepts its algebraic elimination, actual native activation and
bounded lifecycle-retention conclusions under the stated successful-processing
premise. The review also identified existing focused tests for mixed Allowance
capture/extrusion, late unmatched lowers, view sharing and independent uses;
it ran none and those assertions do not prove the theorem.

One minor qualification is repaired in §5: P's plain consumer cannot distinguish
protected contributions with the same concrete effect. Its application requires
those survivors to bypass the filtered input; any contextual alternative needs
its own established consumer law. This clarifies the existing premise without
claiming to establish U. The primary inspected this textual repair.

The frozen dependency table and producer handoff above remain historical.
Concurrent normal-return Catch implementation changes separate source/observer
owners; this review certifies the pinned native primitive, not those new source
paths. Reuse this primitive in the next constructor rather than adding a watcher
engine. U, handler coverage, protected future paths, full contextual recipes,
soundness/principality and production admission remain OPEN.

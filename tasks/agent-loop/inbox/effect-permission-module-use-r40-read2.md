# R40 READ2: module-use structural mapping and registration provenance

Status: frozen reader output; independent source validation pending. Claim class:
bounded source characterization with a conditional analytic falsifier. No compiler
change, theorem closure, production promotion, or repository-wide absence claim.

## Objective, baseline, and scope

Determine whether the five admitted bodies construct an association from an
original computation-formal registration to the argument-effect child produced
for one module use. Baseline is `720eacd38118a1fb408c5886525f3af241f5307d`, pinned
by the admission receipt; this reader did not independently resolve Git refs.

Contract: `tasks/agent-loop/sprints/effect-permission-module-use-20261031-r40-read2.md`.
Admission receipt: `tasks/agent-loop/history/effect-permission-module-use-20261031-r40-read2-admission.md`,
observed SHA-256 `7b34672c009635602a007c5e8a3d7e612f4aa30dab4c4aa2887b83d3f17245c4`.
The prior intake was an admitted dependency, not reread or independently validated.
Required process rules were read. Compiler source inspection was restricted to
the five exact contract slices of `crates/yu-solver/src/candidate_scheme.rs`.

Observed full-file SHA-256:
`31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`.
All five contract hashes match SHA-256 of the indicated byte-line slice after
Python `slice.strip()`. They are not hashes of raw inclusive lines with their
leading indentation and final newline. No source mismatch was observed.

| Function / inclusive lines | Normalized SHA-256 |
|---|---|
| `freshen_candidate_graph_retained`, 4242–4258 | `6605d0d4c346af9f274d9d8c07256a5e77690886ad942c30f19f75923f9f1e1a` |
| `freshen_candidate_graph_core`, 4260–4280 | `5920a3b8c85d3e37f9c1c4af1c46f11b491f3d46a0acef195101dbc70ae4018d` |
| `prepare_candidate_fresh_use`, 4281–4668 | `d0d7994e00e877d39e1da3f610b4209614bb39788181cafd1d7b42c393666584` |
| `begin_candidate_fresh_bound`, 4669–4716 | `f3752551c4cdc01e2529c4aed22932467e189b0e74c84a99bd772d0aa58f0c7a` |
| `instantiate_candidate_graph`, 4717–4800 | `c3c628ace48cc3c5e7c4a93314f86f3a5a6b80c394999ea6b12a6071028d40bd` |

## Observed derivation

1. `instantiate_candidate_graph` receives `id: &DefinitionUseId`, a `DefinitionUse`
   record, and a `Graph` (4717–4723). It constructs the current use occurrence from
   `record.occurrence` at slot zero, derives its cause, and calls retained freshening
   (4724–4726). `freshen_candidate_graph_retained` returns `(root, fresh)` while
   accounting for its retained bytes (4246–4257).
2. `freshen_candidate_graph_core` looks up the caller region using that occurrence,
   invokes `prepare_candidate_fresh_use`, restores every captured bound using the
   same occurrence/cause and `fresh`, then selects `fresh.terms[graph.root]`
   (4265–4278). The explicit occurrence-to-`context_use` census at 4271–4275 is
   `cfg(test)`; it is not production provenance evidence.
3. `prepare_candidate_fresh_use` obtains one `context_use` through `begin_use()`
   (4284), optionally freshens owned regions against the caller (4285–4287), then
   maps each graph row by its current representative (4330–4362). For one call,
   equal representatives share `canonical_rows[source]`; otherwise eligible local
   generic rows receive a fresh row at `use_level`, while other rows reuse the
   representative (4333–4344). Direction: captured graph row index to image row.
   A shared image is structural alias information, not registration identity.
4. Effect operands are reconstructed by graph node index (4388–4414): allowance,
   support and annotation-member views use the mapped optional tail and a view
   remapper; contributions are recreated from cloned `effect` and `origin`
   (4390–4409). Those call sites retain distinctions in operand kind, annotation
   member index, and contribution origin. Callee helper internals were not read.
5. A row node uses its mapped row to produce a live term (4483–4486). A Function
   node reconstructs all four children in order and destructures them as
   `[a, ae, re, r]`; the positive or negative function constructor receives that
   exact tuple (4487–4503). Every reconstructed node is placed in `terms[index]`
   (4578). Therefore, **if** an original registration has already been certified
   to refer to graph Function node `n` and its argument-effect child `children[1]`,
   this body supplies the structural image `terms[children[1]]` in the resulting
   function. That registration-to-node premise is not constructed in these bodies.
6. Existing scoped-flow provenance is preserved conditionally: when the scoped
   experiment is enabled, each captured relation's flow is obtained; scope and
   input identifiers are remapped; `demand.root` is looked up in
   `graph.negative_formal_roots` and replaced by `terms[index]`; a local demand
   receives this `context_use` (4581–4605). This is an observed source-root-term
   mapping and local use stamp. No inspected statement equates that demand/root
   association with the particular computation-formal registration or with a
   Function argument-effect child. Such an association could exist in inputs or
   helpers outside this lease; it is not established here.
7. Bound restoration maps captured lower/upper indices to fresh terms or effect
   operands (4675–4689), preserves owner orientation (4691–4695), and constructs
   transport carrying the parent relation, mapped bound endpoints,
   `fresh.context_use`, remapped context, `bound.source_bound`, and optional scoped
   flow (4696–4709). The bound admission cause is explicitly
   `BoundAdmissionCause::FreshUse { antecedent, use_origin: fresh.context_use,
   source_bound: bound.source_bound, mapped_relation }` (4712–4715).
   Imported evidence snapshots are prepared at 4640–4643. These are actual bound
   provenance constructors, but the inspected call sites do not attach a
   computation-formal registration-to-argument-effect-child certificate.
8. `instantiate_candidate_graph` computes `receiving_owner` from `record.parent`
   (4727–4733), activates source obligations using the graph, mapped rows, and that
   owner (4734–4737), and calls `fresh.into_retained_parts()` (4738). The helper
   implementation and returned retained-map type are outside this read scope;
   whether they contain further certificates is unverified.
9. The incoming route is published for the exact `id` and `record`, reconstructed
   `lower`, and `upper = component_term_at(record.use_value_component)`
   (4740–4745, 4765–4772). A `DispatchRoute::Module(state.routes.len())` is formed
   immediately before the push (4774). The pushed `FreshRoute` has exactly these
   observed fields (4775–4783): `use_id: id.clone()`,
   `source_owner: receiving_owner.clone()`, `provider: definitions[record.target].root`,
   `graph`, `rows`, and `retained: retained_maps`. This binds the stored structural
   route to a particular definition use, receiving source root, and provider root.
   Activated source roles are retained per receiving owner (4784–4787), and field
   tails receive the module dispatch context (4789–4794). The inspected bodies
   establish those associations; their helper contracts were not inspected.

## First unestablished provenance link

The five bodies do **not construct** the association

`original computation-formal registration -> captured Function node / its argument-effect child index`.

Given such an association, their structural reconstruction provides its image
for this FreshUse, and the module route supplies exact use identity. They do not
themselves supply the association's premise. A retained certificate with the
original registration identity, its original Function/argument-effect coordinate,
and the exact use/image would make the desired consumer premise explicit. This
is a statement of the evidence needed, not an approved design or implementation.

The scoped demand root mapping, imported bound evidence, source obligations,
and retained maps must not be dismissed as mere copied terms. Each carries
some provenance in the inspected call sites. Conversely, those call sites do
not establish the particular registration-to-child association. The declaration
or construction of that association may exist outside the five bodies. This
report makes no repository-wide absence claim.

## Analytic `{signal | e}` / `{write | e}` falsifier

Take distinct registrations `R_signal` and `R_write`, with permissions
`{signal | e}` and `{write | e}`, sharing the same tail representative `e`.
Within a single FreshUse, the loop at 4333–4344 maps that representative to one
image `e'` (or reuses it if nongeneric). Thus the candidate identifier
`image(e)` cannot distinguish the two registrations. In the same graph, different
annotation-member endpoints or reconstructed view heads can still distinguish
`signal` from `write`; the inspected code does not itself interchange them.

A proposed consumer that treats shared tail-image equality as sufficient
registration authority admits this witness: a `signal` contribution associated
with the `R_write` use retrieves `R_signal`'s subtraction permission through
`e'`, and wrongly authorizes subtraction of that contribution. Required
hypotheses are (i) two distinct registrations, (ii) shared representative tail,
(iii) permission lookup using only the image tail, and (iv) actual contribution
arriving on the other registration's path. The failure is conditional on (iii);
these five bodies do not implement that consumer. Permission does not restrict
the actual input to the named effect. Even within one module use, use identity
alone cannot separate two formal registrations sharing `e`.

This is a minimized information-loss witness for a row-only provenance claim,
not an observed Rust runtime failure or a complete source-language program.
Preserving distinct heads and checking registration-specific incidence would
reject that alleged identification. A certificate for an exact registration
and child image is the discriminating missing premise for the proposed consumer.

## Evidence, limits, resources, and recommendation

Commands: `cat` of the contract and required three rules; Python byte reads,
inclusive line extraction, SHA-256, and UTC timestamp; `apply_patch` of this sole
output. The initial `python` invocation failed because that executable is absent;
`python3` succeeded. One tool response truncated part of Variant reconstruction;
the omitted lines 4517–4538 were reread inside the permitted function slice.
No compiler execution, tests, builds, Cargo/Lake, environments, worktrees,
scratch files, or caches were created. Coverage is the five pinned bodies only.
No oracle or randomized experiment was used; there are no seeds or sampled
ranges. The argument shares the code's existing Graph invariants and does not
prove the helper implementations or their inputs. No source, manifest, lockfile,
shared record, or Git mutation was made.

First measured source observation: `2026-10-30T20:02:49Z`. Full dispatch-to-stop
wall time was not instrumented; do not recover unused budget from this report.
Conservatively charge the reader's full 300-second allowance. CPU and memory
were not separately measured. The sole new path is this report.

Recommended next action: independently validate this frozen characterization,
then inspect only the owning constructor/type that associates source-role or
scoped-demand identity with the original registration and Function child before
admitting any residual consumer. The concrete helper/type selection remains the
primary's decision; this packet does not enlarge its read or write scope.

## Commit packet

- Exact leased path: `tasks/agent-loop/inbox/effect-permission-module-use-r40-read2.md`.
- Baseline: `720eacd38118a1fb408c5886525f3af241f5307d` (admission-pinned).
- Dependency changes: none observed; source and normalized function hashes above.
- Review: frozen, independent source validation pending; no self-certification.
- Checks already run: byte/hash verification and bounded static source derivation;
  no executable behavior check.
- Proposed checkpoint message: `research: trace R40 module-use provenance boundary`.
- Shared-record deltas left to primary: record the structural mapping and exact
  use fields; retain the open registration-to-child premise and conditional
  shared-tail falsifier; preserve all broader theorem and production gates.

Reader writing has stopped after this artifact; no further edits are authorized.

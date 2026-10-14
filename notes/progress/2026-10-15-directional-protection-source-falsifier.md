# Directional protection: source-qualified falsification pass

Date: 2026-10-15
Status: frozen unreviewed research checkpoint; no implementation authority
Method: one bounded static source/fixture pass; no execution or constructive proof
Primary baseline: `5781fe30e711cb1aac2f7b3a97f4484cd0f278e2`
Production source baseline: `427d1ff5daab866fa7d89cb513a077063cc6454d`
Gate: the selected local omitted-formal directional-protection source bridge; H1/H2/U remain open

## Objective and governing premise

Attack whether current constructors establish the actual premises of the selected
rule: actual binder annotation absence, original scope and variable, an original
source upper Function demand, and exactly its ResultEffect occurrence, preserved
without backflow into a provider lower Function. Authority is the direct user
decision in directional addendum §§1–4, the source-generation note §§1–3, and
top-level inference principles §1.1. `tasks/effects-handler-next.md` §§1–4 is read
at the pinned primary baseline. Its historical pending-profile language is not a
new semantic premise and does not reopen the selected local rule.

**Result class:** bounded source correspondence and a missing-transition witness.
This is neither a runtime misprotection counterexample nor proof of the rule.
The exact unsupported premise is a source-owned semantic witness that omitted
formal `f` is protected **at its original upper exposure**, followed by an
introduction at that demand's original ResultEffect. Current omission evidence
does not itself authorize that step.

## Small authentic discriminator

Use the existing fixture, without changing its spelling or expectations:

```text
my apply f = f 1; my id x = x; pub out = apply id
```

Owner: `crates/yu-solver/tests/shadow_apply_candidate.rs:425`,
`parameter_apply_retains_premises_and_ordinary_routes`. This fixture contains the
two required directions: the omitted formal's original body demand at `f 1`,
and a known module callable `id` supplied at `apply id`. `id` is a known local
module provider, not a claim about imported external-callable support.

The following trace is determined by current source constructors, not observed
by executing this fixture:

1. `candidate_source.rs:258` forms local binder-to-scope mappings;
   `:387` records `OmittedFormal` only under `parameter.annotation.is_none()`.
   The record contains owner, original Lambda, formal identity, source position,
   and original Definition/Local scope (`:21`). A Name use cannot create it.
2. Parameter Name endpoints directly select the parameter recipe (`:295`),
   and source formal Name registrations retain the binder correspondence
   (`:324`). Module Names instead schedule `Action::Module` (`:584`). Thus
   unannotated use-site syntax does not turn the known `id` Name into a newly
   omitted formal. `id`'s own omitted `x` is a different binder.
3. `candidate_source.rs:603` retains an Apply source input and checking occurrence
   before solving. `shadow_apply.rs:1428` authenticates that input against the
   recipe; `:1485` constructs a negative Function demand directly from source
   endpoints. Its return effect is a fresh invocation row, not the combined
   application row. The `NativeInterface` is retained before
   `constrain_live_value` (`:1524`). `candidate_call.rs:331` checks that the raw
   demand's ResultEffect is exactly `native.invocation_effect`, and `:375`
   checks its original row ordinal. These fields are useful source evidence;
   none is a protection seed or grant.
4. The body's Apply action precedes the owning Lambda action: Visit pushes
   `Work::Finish` before descending into the Lambda body (`candidate_source.rs:363`,
   `:406`), and Finish appends `Action::Lambda` only after body traversal
   (`:659`). Sequential execution dispatches Candidate and Lambda separately
   (`:889`). Consequently the original `f 1` demand is admitted before
   `admit_lambda_fact` creates `FormalConstruction` for `apply`.
5. `lib.rs:11385` authenticates the Lambda's original raw Argument child and
   retains `FormalConstruction`. `candidate_context.rs:2740` attaches it to the
   owning origin. Its declaration (`:275`) explicitly has no semantic consumer.
   It identifies the omitted formal's domain, not the upper demand's output
   effect. The source omission record was already available in the collection
   plan at step 1, so the ordering is not an impossibility result: a constructor
   can use that earlier source evidence. It does refute treating the existing
   post-body `FormalConstruction` as a seed already supplied at step 3.

The selected law calls for new protection on the `f 1` upper demand's invocation
ResultEffect, without newly painting `id`'s provider ResultEffect from the same
seed. No such local semantic producer exists in the inspected route. The
known-provider pair therefore exposes a missing construction step; it does not
demonstrate that the implementation currently introduces protection backwards.

## First absent constructor and consumer

The first absent semantic constructor is between the source-owned omission
record and `ProtectedVarAt(k,f,original_scope,upper_use)`. `OmittedFormal` is
declared construction-only (`candidate_source.rs:18`); `FormalConstruction` is
declared an owning Lambda fact rather than a callback contract or receipt
(`candidate_context.rs:274`). There is no inspected producer joining that
evidence to the original demand and producing exactly its ResultEffect mark.

The live consumer confirms the limit. `candidate_context_source` (`:2688`)
creates context from a closed allowance filter, otherwise IDENTITY;
`candidate_context_seed_with_formal` stores the formal in origin metadata.
`candidate_function_port_admit` (`:2777`) swaps Argument/ArgumentEffect and
preserves ResultEffect/Result from the inherited context. It does not inspect
omission evidence or distinguish the selected newly protected ResultEffect
from the ordinary preserved Result child. `candidate_context_execute_relation`
(`:2964`) discharges filters already present in context; it does not consult
omission/formal metadata. Thus ordinary Function field transport is not the
missing introduction rule.

`candidate_effect.rs:1099` recursively constructs **explicitly annotated**
formal Function pairs; `:1121` allocates a shared fresh effect row for an omitted
effect annotation within that explicit type. This is a separate absence from
the whole binder's `parameter.annotation.is_none()`. `candidate_signature_view`
(`:733`) constructs annotation/operation views and their source/closed weights.
Neither constructor supplies the missing seed for the wholly unannotated `f`.
An empty allowance or a successful type comparison cannot substitute for it.

## Capture, typed fields, and fresh use

The existing authentic captured fixture is:

```text
my outer cb = { my inner x = cb x; inner }
```

It occurs in `candidate_context_tests.rs:489`,
`omitted_formal_source_domains_correlate_with_retained_extrusion_pairs`.
The receiving extension is already present at `:576`:

```text
my root = { my outer cb = { my inner x = cb x; inner }; my identity z = z; outer identity }
```

These are coverage locators only; their existing assertions were read, not run.
`candidate_formal_argument_incidence` (`candidate_context.rs:302`) recognizes a
bounded chain of Argument FunctionPort, Replay, FreshUse transport, and an
optional source Name handoff. Its source comment explicitly excludes earlier
extrusion/derived routes. It authenticates the receiving Argument of the
owning Lambda. It does not authenticate a directional protection mark at
`cb x`'s original upper ResultEffect.

The ordinary structural decomposition retains field identity:
`lib.rs:12567` compares lower ResultEffect to upper ResultEffect, independently
of the other three fields. `candidate_scheme.rs:526` captures the four fields
with their variances; `:548` captures oriented bounds and their relation/evidence
snapshot. `prepare_candidate_fresh_use` (`:1009`) remaps shared canonical rows
per use, and `begin_candidate_fresh_bound` (`:1253`) restores owner orientation,
FreshUse transport, context, and evidence snapshots. These are existing carriers
to investigate once the seed/exposure incidence exists. They cannot preserve a
directional protection witness that has not been generated. No claim is made
that they drop all provenance or cannot be extended. Equal remapped row values
and four-field preservation alone do not establish original occurrence authority.

## Independence, coverage, and failure conditions

The oracle for the desired distinction is the already selected user rule, not
candidate code or a checker assuming its transitions. The source trace is an
independent static method relative to the constructive proof lane; this artifact
has not received independent review. Shared assumptions are authentic HIR
resolution, ordinary execution of the emitted source schedule, and the pinned
candidate route. No invented surface program, executable model, mutation,
enumeration, seed/range, Cargo command, build, test, or measurement was used.

Coverage is the named omitted binder, original upper demand, known module
provider, and bounded captured/FreshUse constructors. Imports, arbitrary aliases,
recursive SCCs, late-seed replay, every extrusion path, failed-demand runtime
behavior, nested result exposures, independent inherited protection, dynamic
Receive/Observe, and handler removal were not verified. In particular this pass
does not establish whole-source absence of all protection machinery, general
no-backflow, hygiene, or the constructive theorem.

The missing-transition finding would need revision if a dependency adds a real
consumer of OmittedFormal/FormalConstruction that retains original protected
scope at exposure and marks the exact original upper ResultEffect. Adding only
a source registry, a successful query, or a field-copy observation would leave
that premise untouched.

**One recommended next action:** assign the source constructor owner a bounded
handoff connecting the already available binder omission/scope evidence to the
original demand at `admit_candidate_fact`, before its solver admission, and
identify the exact witness consumed by the constructive lane. Keep implementation
authorization and captured/late-demand preservation gates explicit. The later
Lambda Argument certificate cannot alone discharge this exposure-time premise.

## Checks, dependencies, and commit packet

Read-only checks: `git rev-parse HEAD`, scoped `git status --short`, `rg`, `sed`,
`git show` of frozen task sections, SHA-256 hashes, and scoped
`git diff 427d1ff5daab866fa7d89cb513a077063cc6454d 5781fe30e --stat`.
The five named production files plus `shadow_apply.rs` and `candidate_call.rs`
are unchanged between the production and primary baselines. The test dependency
`candidate_context_tests.rs` differs: production blob
`0a182c16665a5acd8f887eb8ce989fb5a7e73581`, primary blob
`fca4eb0b7c95eb29a051751993cda41ad8ae06ca` (422 added lines).
No dependency was changed by this worker. Live task-file edits were excluded
from authority consumption. At freeze, HEAD had advanced to
`8aad0a1ac423e98d261be91b2d575456e7507293`; a scoped diff against the primary
baseline showed no change to the listed source, authority, or fixture
dependencies. The task sections remain intentionally pinned to the assignment
baseline.

Frozen authority SHA-256:

- Directional addendum: `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7`.
- Source-generation note: `3702eb2ea5108eba1adc8ab7a557542abb9993cee09f70b738e2999a05a2d185`.
- Top-level inference principles: `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
- Pinned task file: `72a25f14a43275ea489df3da4a99c17de8ad06dea549c7fd96d810d16a6b3799`.

Resource budget: one static pass, under 15 minutes; sequential lightweight
read commands, no local compute wave. CPU time and peak memory were not measured.
Checks on the note: `git diff --no-index --check /dev/null` against this note
passed; no compiler verification.

- Exact lease/changed path: `notes/progress/2026-10-15-directional-protection-source-falsifier.md`.
- Baseline: `5781fe30e711cb1aac2f7b3a97f4484cd0f278e2`; production baseline as above.
- Changed dependency hashes: none during the pass; baseline test difference recorded above.
- Review: unreviewed, frozen for primary-assigned independent review; no self-certification.
- Proposed commit: `research: trace missing directional protection exposure bridge`.
- Shared deltas left to primary/curator: record the exposure-time seed-to-demand
  bridge as missing, retain H1/H2/U OPEN, and distinguish existing Argument
  correspondence from ResultEffect introduction. No shared record was edited.

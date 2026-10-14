# Directional introduction to live context: bounded source audit

Date: 2026-10-15
Baseline supplied by primary: `2b95123d644990352ca0a0e4c28c58680c9ffed3`
Branch supplied by primary: `research/simple-sub-intrusion`
Status: reviewed bounded research characterization; no theorem or implementation closure.
Lease: this file only. No compiler/test/shared-record edits or Git commands.

Review: a fresh independent `compiler_referee` found no blocking or major
issue. Two minor source-locator drifts were corrected and closed by delta
review. The audit identifies the missing record-to-live-context edge but found
no executed wrong-subtraction counterexample; late demand and complete source
coverage remain unverified.

## Objective, authority and result

Method: static independent falsification/source-consumer tracing of the proposed
bridge from an omitted formal's authenticated `DirectionalIntroduction` to live
protection at that original upper Function's `ResultEffect`. This is a
complementary source audit; the primary's prover lane owns construction of the
main theorem. No additional workers were launched.

Governing scope: directional addendum §§1–4 (selected direction and no-backflow),
handler-boundary construction §§1,3,6, native residual-cut §§3–5, annotation-effect
hygiene integration §§1,3–5, contextual attachment/admission §§2–4, typed-boundary
realization §6, and top-level inference principles §1.1. The retracted callback
result and older unconditional rollback clauses are not premises.

**Result:** the symbolic source certificate is traceable to the exact original
upper demand, but no inspected live context constructor/consumer reads it.
Consequently it does not yet discharge the `ProtectedVarAt`/live protection
premise of the directional rule or supply the profile premise of the existing
hygiene results. This agrees with the playground record's explicitly symbolic
scope; it is not a contradiction to that record. No currently executing
wrong-subtraction counterexample was established. H1/H2/U remain OPEN and this
note supplies no permission to activate residual P.

Claim class: bounded source characterization, conditional on successful ordinary
formation/admission of the source shapes below. Source identity validation and
the consumer disconnect are actual inspected implementation facts. Parser/solver
execution, all-source reachability, hygiene and runtime claims are unverified.

## Exact source-to-record path

Locators below refer to the dependency hashes in the final section.

1. `candidate_source.rs:258–285,323–334` creates a formal registration with its
   original owner, lambda index, parameter ID, recipe position and retained
   scope; only actual `Name(Parameter)` expressions receive `formal_names`.
   `:386–395` creates `OmittedFormal` only when `parameter.annotation.is_none()`.
   A known module/local callable lookup or operation declaration is not this
   premise. A missing annotation on a Name expression is insufficient.
2. `candidate_source.rs:605–622` retains an Apply recipe and source input.
   For original Apply occurrence `u`, the checking ID is precisely
   `ConstraintOccurrenceId(u,0)` and its cause is `CauseId::for_occurrence` of
   that ID. The recipe has an index and a back-reference `source_input`; those
   indices are storage identities, not grant/eligibility evidence.
3. `shadow_apply.rs:1440–1535` checks that recipe/input/occurrence/endpoints
   agree. It allocates a fresh invocation effect row `r_u`, constructs
   `U_u = negative_function(argument, argument_effect, return_effect, result)`,
   where `return_effect = live_effect_term(Negative,r_u)`, and joins the exact
   original omitted formal through `formal_name -> registration -> lambda`.
   The record stores `(registration,name,omitted,checking,cause,U_u,
   ResultEffect,return_effect,r_u)` **before** `constrain_live_value` at `:1544`.
   The application effect is a separate coordinate. The callee evaluation,
   argument evaluation and result Value coordinates are also separate fields.
4. `candidate_call.rs:355–525` validates the source Apply children and owner,
   complete negative Function fields, live row kinds/polarities, and raw
   invocation ordinal. It validates the routed original formal and its
   omission/scope, checking/cause/demand, exact `ResultEffect` enum and raw row.
   This validation does not reconstruct the original occurrence from canonical
   row equality. Numeric recipe/row IDs were not obtained by executing a solver;
   `u`, `U_u`, and `r_u` here denote their exact constructor identities.

## Discriminator traces and their bounds

The existing fixture literals below were inspected, not run. New combinations
are explicitly constructor-supported source candidates, not observed solves.
Every Apply follows the recipe/checking/raw-field path above.

### Omitted callback inside Catch and known provider

Minimal constructor-supported combination:

```yulang
act signal:
    our ping: () -> int
my relay cb = catch cb() { signal::ping(), _ -> 1, v -> v }
my answer = relay signal::ping
```

`cb()` has a `Name(Parameter)` callee and its original omitted `cb` registration,
so its source input carries an introduction at `ResultEffect(U_cb) = r_cb`.
The outer `relay signal::ping` has a known module callee and receives no new
omitted-formal introduction. The operation reference is immediately pure and
its actual declaration's latent support comes from `candidate_operation` /
`candidate_signature_value` (`candidate_effect.rs:779–804`). The operation
family support is not a callback protection seed and cannot transfer protection
back into the provider's lower Function output.

The constituent source shapes are authenticated by
`candidate_operation_catch.rs:26–67` and `shadow_apply.rs:1736–1767`; this combined
literal has not been parsed/solved. Catch construction at
`candidate_source.rs:517–534` forwards the scrutinee effect with slot 51 and
independently joins every arm body's effect. It installs no cut or callback
protection. Therefore this is a source-qualified missing-bridge discriminator,
not evidence of a current incorrect Catch removal. Plain family removal would
need U's independent consumption/protected-bypass premise first.

### Separate Apply uses

Existing literal `my apply f = f (f 1)` in `shadow_apply.rs:1739` has two source
Apply occurrences for the same formal. The inspected test expects two distinct
checking occurrences and demand Terms, each introduction equal to its own raw
invocation effect and unequal to its own application/argument/result fields.
The corresponding CLI fixture is at
`tools/inference-playground/tests/cli.rs:333–351`.

This distinguishes a per-Apply witness from one solved-row protection bit. It
does not show separate semantic slots, distinct canonical rows after intrusion,
or live protection at either use. No nominal equality is used as a grant.

### Captured, returned and wrapped callback

Existing literals at `shadow_apply.rs:1740–1743`:

```yulang
my outer cb = { my inner x = cb x; inner }
my apply f = { my first = f 1; my second = (f) 1; my step x = ({ f }) x; step }
```

The first records the source call to the original captured `cb`; returning
`inner` creates no new Apply exposure. The second has three source upper uses
of the original formal, including Group/Block callee wrappers. Wrapper routing
retains `formal_names` at `candidate_source.rs:624,654,678`; the observer checks
that route rather than identifying nearby solved endpoints
(`candidate_call.rs:450–478`). The registered root is checked across those uses
by the existing test at `shadow_apply.rs:1805–1855`.

An Apply through an arbitrary returned/local alias is not automatically a new
direct formal introduction: `formal_names` starts only at `Name(Parameter)`
and traverses the listed wrappers. This is a boundary of this certificate, not
a rejection of such source or proof that inherited protection disappears.
Transport must establish the corresponding typed path independently.

The existing operation-Catch fixture
`monomorphic_callback_response_preserves_original_returned_callback`
(`candidate_operation_catch.rs:108–112`) separately authenticates the source
shape `catch (signal::ping())(1) { signal::ping(), k -> k id, v -> v }` with a
returned callback. `k` is a Catch binder, not an omitted lambda formal.
`candidate_catch_operation` constructs its paired response/original-result
ports with shared declaration environments and E/R rows
(`candidate_effect.rs:806–863`); slots 64/65 retain `E <= R` and `S <= R`.
Neither that pairing nor the operation support manufactures a directional seed
for `k` or proves profile transport through the returned callback.

### Two operations in one family, one matching arm

Constructor-supported source candidate:

```yulang
act signal:
    our ping: () -> int
    our pong: () -> int
my result = catch signal::pong() { signal::ping(), _ -> 1, v -> v }
```

HIR resolves expression and pattern operations using `(resolved family, member)`
at `yu-hir/src/module/local_source.rs:798–810,853–873`. Thus `ping` and `pong`
have different operation declarations while sharing a family. Source formation
retains the actual arm declaration; current Catch simply joins effects.
No matching `pong` operation arm exists. A value arm is not coverage of that
request. Family equality cannot establish guaranteed request consumption.

No existing literal with this precise pair was found in the selected Catch
fixtures, and this source candidate was not executed. The operation-support
tests (`candidate_operation_source.rs:43–55,86–113`) authenticate retention of
the actual operation declaration and its family/interface members. They do not
prove ordered handler coverage. This trace independently identifies U.2/U.3's
coverage premise even after a future protection bridge succeeds.

### Late Function demand

The selected source fixtures do not authenticate a delayed Function demand
arising after live protection installation: live installation is itself absent.
No late-demand witness or source schedule was fabricated. Existing local/raw-k
alias fixtures at `candidate_operation_catch.rs:87–103` authenticate multiple
uses and response-entry forwarding, not that temporal property. Future-lower
support in existing replay is an implementation mechanism; it cannot establish
the missing source/profile constructor by itself. This discriminator remains
unverified within the static-only packet.

## Exact first missing owner/consumer premise

At `candidate_context.rs:2688–2745`, context seeding uses the task endpoints,
source checking provenance, closed allowance weight and optional inferred-entry
origin. `candidate_context_seed_with_formal` adds formal construction provenance,
but neither entry reads `ApplySourceInput.introduction` or `DirectionalIntroduction`.
`candidate_context_source` returns identity unless the actual upper Allowance
owns a closed checking weight. This does **not** mean the source is unprotected.

The actual Function decomposition (`lib.rs:12547–12580`) compares lower and
upper result-effect fields. `candidate_function_port_admit`
(`candidate_context.rs:2776–2830`) preserves the parent context for Result and
ResultEffect, swaps Argument/ArgumentEffect, and prefixes any child-local
checking context. It introduces no omitted-formal protection. The ResultEffect
child is the correct scalar position but the required source protection
operation has not been installed on its parent/child lineage.

`LocalWeight.left_word/right_pops` have zero-sized array types
(`candidate_context.rs:114–135`). Detached `materialize_unit_push` at `:2368`
explicitly creates no live relation/bound/registration/context word. Actual
execution at `:2960–3020` dispatches identity contexts normally and executes
retained zero-word allowance checks; it does not read directional introductions.
`lib.rs:11254–11345` retains lambda entry origins at slot 3, but the origin type
is expressly distinct from a context-operation certificate
(`candidate_context.rs:155–175`). No `both` authority follows from that metadata.

The first missing premise is therefore:

> The original omitted formal's source protection, at the authentic upper-use
> checking occurrence and scope, constructs executable protection at precisely
> `ResultEffect(U_u)`, and the actual Function-port/context consumer preserves
> and executes it under the same source owner and assignment without marking
> provider lower outputs or sibling coordinates.

Owner: the coupled original formal/Apply admission and typed context consumer
(`candidate_source`, `shadow_apply::admit_candidate_fact`,
`candidate_context::{candidate_context_seed,candidate_function_port_admit,
candidate_context_execute_relation}`). The source/profile/lifetime premise is
still needed to apply the existing hygiene theorem. Neither the scalar
decomposition nor metadata-only provenance supplies it.

Capture/freshening (`candidate_scheme.rs:800–823,1094–1141`) remaps reachable
context/view roots with per-use maps; qualifying intrusion
(`candidate_intrusion.rs:518–610`) transfers both bound sides, origins,
canonical contexts and opposite-bound replay. These paths preserve their
constructed inputs and cannot create the missing live protection. This audit
does not prove all-path preservation once the constructor exists.

## Independence, checks, omissions and next action

The source implementation and existing fixture expectations are the evidence;
no supplied toy transition system or independent executable oracle was used.
The tests share compiler owners with the candidate and were only read. Existing
observer mutation tests (`shadow_apply.rs:1769–1803`) corrupt field, checking ID,
formal record, effect and scopes; they discriminate certificate authentication,
not live protection execution. No mutations were executed in this packet.

Commands: bounded `rg`, `sed`, `cat` reads; `sha256sum` of direct dependencies;
one patch writing this note. No Cargo/test/build, executable probe, benchmark,
Git command, child agent, or broad formatter. Seeds/ranges: none. Budget: one
static leaf, at most 15 minutes; no measurement samples or heavyweight processes.
CPU peak/RAM and exact elapsed wall time were not measured. Two attempted
locator reads reported nonexistent paths (`contextual-effect-typing-design.md`
and `crates/yu-playground`); relevant actual context design and
`tools/inference-playground` paths were located and read. This was not a complete
repository/source or historical Oracle search.

Recommended next action: primary assigns the smallest separately authorized
constructor/consumer slice that materializes this original occurrence's
protection and demonstrates the omitted/provider/repeated-use distinctions
through actual live contexts, with its needed lifecycle invariant established
by the constructive lane. Keep residual activation and parent proof gates OPEN.
Another conditional theorem assuming this same absent constructor cannot close
the bridge. This recommendation selects no new language meaning or carrier.

## Frozen dependencies (SHA-256)

These are filesystem content hashes, not Git object IDs. The baseline commit
was supplied by the primary; no Git commands were allowed to compare it with
the live tree. No dependency was modified by this leaf. The primary must compare
this dependency snapshot with its pinned revision before integration.

```text
397db1bd4e9df20cb120ffda45a88c45a6da594f3cc9516d3de4cefb494568c3 notes/progress/2026-10-15-directional-introduction-playground.md
6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7 notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md
81eed00aefed2948768290c6066d95463bac0fd2340b7e33d56227d7368ec59f notes/theory/2026-10-14-handler-boundary-construction.md
469677cc50b1dfd5327fa330e85bb83124c9e17cec391866dbf71ee23c40d50b notes/theory/2026-10-14-native-handler-residual-cut.md
503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a notes/design/2026-10-10-annotation-effect-hygiene-integration.md
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc notes/design/2026-10-10-contextual-attachment-admission-design.md
1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb notes/design/2026-10-02-typed-boundary-realization-draft.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81 notes/design/2026-10-11-yulang-inference-top-level-principles.md
32a6d875b9e89af8192cf017fbeccc95e9648223490d72de64a6957c97aa6e1b crates/yu-solver/src/candidate_source.rs
cc5778b936a5495182c08d4853ab9ef006d079df5e169dd94df629c2d82f3199 crates/yu-solver/src/candidate_call.rs
831dc28b977a5e01e6f0ef0faa795495d78ecb2cc01678db48e9cf7ea5132eac crates/yu-solver/src/shadow_apply.rs
6301ca80eec137df3f2c2c44e2edaa7dbdf1ed7a78c69617228888e63654e461 crates/yu-solver/src/candidate_context.rs
f414efa7efdb17644f4dfa6b0bba621c1bb7cccd0f83735c33a0acb875da6b91 crates/yu-solver/src/candidate_effect.rs
c8ef7cc472f0dcb60d793c6f9b4f6ba1aefb76f919ff2a3ce9310f85eb647dcd crates/yu-solver/src/candidate_scheme.rs
4a2b87ebf6e5e219c06763bc4e589517fd48c575c89038f2a11fc1e6494fe90e crates/yu-solver/src/candidate_intrusion.rs
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5 crates/yu-solver/src/lib.rs
8c580da56de25c76146073919840f6d15dec3b11a53c0787309a082dc59e5484 crates/yu-solver/tests/candidate_operation_catch.rs
7e438b91ed03dbb52b644f78bc082232efd5164fd8d095d10373d826d2d7d0cb crates/yu-solver/tests/candidate_operation_source.rs
afc91346af535529f973421bdbe2a43520c98946097cae545e4ae1a665146074 crates/yu-hir/src/module/local_source.rs
a5afa505708e5f68e0d77af532ff718ad15221d953e3b78247dd3142aa3098cf tools/inference-playground/tests/cli.rs
```

## Commit packet

- Exact leased path: `notes/progress/2026-10-15-directional-introduction-context-falsifier.md`.
- Baseline: `2b95123d644990352ca0a0e4c28c58680c9ffed3`.
- Dependency changes: none by this worker; primary comparison with pinned Git
  revision remains required. Direct content hashes are recorded above.
- Claim/review status: frozen, independently reviewed bounded characterization;
  no theorem, implementation, or production closure.
- Checks already run: static locator/content inspection, dependency SHA-256,
  independent review and two-locator delta review; no tests/builds/probes/
  measurements. The primary owns whitespace checks and integration.
- Proposed message: `research: trace directional introduction to missing live context consumer`.
- Shared-record deltas left to primary/curator: link this evidence and identify
  the coupled constructor/consumer owner in the active lane; retain H1/H2/U and
  residual activation OPEN. No task/index/authority/question file was edited.

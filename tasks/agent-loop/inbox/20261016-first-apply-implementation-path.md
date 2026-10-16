# First-Apply implementation lane handoff

- Sprint / contract: `first-apply-owner-elimination-20261016`, revision 1,
  SHA-256 `9b5fe6ab1bf847bcc4b93d1b43c013b9e2b337e4894022992597b1c3b5eebb5b`.
- Assignment / handoff revision: `LUNA-FIRST-APPLY-IMPLEMENTATION`, revision 1.
- Parent: `FIRST-RESULT-ADEQUACY`, unchanged original claim for
  `my receive (f: () -> 'a) = { my g = f(); g() }`, quantified over every
  original `xi=(nu,K,D)` and complete first-Call witness `z`, with the same
  provider, captures, scopes/binders, whole Unit carrier, entry/current
  configuration, pending Bind/future obligations and both tagged images
  `M_W* W_z union_tagged M_res* F_R,z`.
- Baseline: `eeb7826a238848d219058f4f14e0948c115ae6ac`.
- Worker: `/root/luna_first_apply_implementation`; session ID and actual
  runtime launch receipt unavailable in this worker context. Requested role /
  model / effort: `implementer` / `gpt-6-luna` / `high`. Observed model / effort:
  UNKNOWN / UNKNOWN. No model or configuration was changed.
- Exact write lease: this inbox file only. No source, test, contract, state,
  theory, generated or scratch path was written. No descendants or background
  processes were started. Writer state: STOPPED WRITING after freezing this
  handoff; no separate cancellation receipt exists for this foreground task.
- Outcome class: `NO_SAFE_CODE_SLICE`.

## Owner audit and result

The four source owners were read at the exact pinned bytes. Candidate source
planning and native propagation are present, but no independently approved
implementation change can bridge the original source premise to the actual
native children. The current sprint grants no compiler or test write lease;
the inspected source paths are also FROZEN under the preceding implementation
continuation. A new test or instrumentation would exceed the exact output lease
and would not establish the missing implication.

| Owner and inspected locus | What the owner currently does | Owner-specific blocker and evidence needed to unblock |
| --- | --- | --- |
| `crates/yu-solver/src/candidate_source.rs:980-1011` | For a parsed `LocalSourceForm::Apply`, retains a candidate `Apply` relation from its child positions and creates a source-call input keyed by the occurrence. | This is candidate source planning, not the original complete Apply/check/ExecuteCallable elimination. It supplies neither the original `xi,z` telescope nor the same-provider, whole-carrier and parent-context derivation. Need the original owning source rule with its complete telescope and maps, or a source-qualified original `(xi,z)` counterexample. |
| `crates/yu-solver/src/shadow_apply.rs:1558-1696` | Checks candidate recipe/source-input alignment, creates a negative Function demand from candidate argument/result endpoints, allocates an invocation effect, retains a `NativeInterface`, and admits value/effect constraints. | Its antecedent is the generated candidate recipe. Using its emitted children as evidence for the original source antecedent would assume the comparison/constraints that FIRST-RESULT-ADEQUACY forbids in the antecedent. Need an independently governing source elimination deriving each corresponding actual native child at the original `xi,z`, including both tagged packet inputs and retained parent contexts. |
| `crates/yu-solver/src/candidate_call.rs:250-385,437-535` | Exposes candidate Call ports and validates LocalSource occurrence/cause identity, generated demand shape, endpoint kinds/polarities, and retained row identity. | This observer validates artifact/source alignment and native representation; it does not establish original Gen-Call-0 formation, contextual Function membership, or source adequacy. It cannot safely synthesize missing semantic children from generated fields. Need the original source supplier/inversion and the independently derived child maps above. |
| `crates/yu-solver/src/lib.rs:12455-12814` (Function dispatch at `12635-12675`) | Propagates an already admitted native Function pair by dispatching Argument, ArgumentEffect, ResultEffect and Result child pairs. | This consumes an existing native pair; it does not derive that pair from the original first Apply obligations. Adding a source-specific dispatch would reverse the needed implication or change inference without its premise. Need the original first-Apply elimination and a checked mapping from its children to these exact dispatch inputs. |

These loci show an existing candidate `source -> constraint admission ->
propagation` route. The previous test-only handoff observes one contextual-effect
conflict along that route. Neither is an independently approved path to change
compiler behavior: the original Call/first-result adequacy gate remains open,
production authority is absent, and this assignment leases no code/test path.
No withdrawn Simple-sub bypass is restored or proposed. Therefore there is no
safe code slice within this contract.

## Prior evidence reused and rejected

Reused the prior Luna implementation handoff
`tasks/agent-loop/inbox/20261016-call-contextual-effects-implementation.md`
and primary reconciliation
`notes/progress/2026-10-16-call-contextual-effects-implementation-reconciliation.md`.
That handoff's test `source_call_native_interface_reaches_its_root_effect_consumer`
is provisional, test-only evidence for one authentic `tick::next()` Apply,
retained candidate Call and root annotation conflict. The reconciliation records
independent acceptance of the repaired test's operand attribution; it explicitly
does not establish the intervening propagation route, original Gen-Call-0
formation, first-Apply adequacy or public execution correspondence. The earlier
ordinary `id 7` runtime check is unrelated contextual-effect evidence.

Rejected as a premise: candidate-generated native constraints as antecedents;
test success as original source elimination; declaration or source occurrence
identity alone as complete original typing; and the candidate negative Function
as proof that the same original provider/result/future contract was derived.
The exact governing Authoritative Call formation, contextual Function
membership, complete Call contribution and source-interface definitions were
read. Their constructors retain the relevant contracts but do not grant
production implementation authority or supply this missing actual Apply
eliminator.

## Frozen inputs, resources and next step

The sprint contract's 14 direct dependency hashes all matched their pinned
values at audit. Exact inspected source pins:

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| `crates/yu-solver/src/candidate_call.rs` | `cbad9cf51a05343eb7a29ab77aac520891467a8aa4edc3201ea3d91f978984a1` |
| `crates/yu-solver/src/shadow_apply.rs` | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` |
| `crates/yu-solver/src/lib.rs` | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` |

Contract-dependency verification covered the governing sprint rule/design,
inference principles, four original Call/interface definitions, both pinned
theory notes, source-attack progress evidence and all four source files above;
all 14 matched. No test/build, formatter, benchmark, executable probe, Git
command, or network action ran. Heavy processes: 0. Lightweight probes: 0.
Within the 600-second / four-stage assignment bound, approximately 150 active
seconds and four stages were used (contract/rule intake; prior implementation
history; four-owner source audit; dependency-pin verification and handoff).
No budget renewal requested. No disposable scratch or generated output exists.

Next authorized step: the original Call/effect proof owner must supply the
independent complete Apply/check/ExecuteCallable elimination rule and its
actual maps from the original obligation at each fixed `xi,z` to Argument,
ArgumentEffect, ResultEffect and Result at the exact native dispatch positions,
preserving both source packet inputs, provider, parent contexts, and pending
Bind/future obligations; alternatively provide a source-qualified original
`(xi,z)` falsifier. Luna can then issue a new exact implementation lease for a
reviewed end-to-end source-to-constraints-to-propagation-to-execution slice if
the premise permits one. Until then, no owner-local code change is justified.

No production theorem, semantic gate, source domain, inference behavior,
diagnostic or cutover status is changed. This handoff is not independent review
or self-certification.

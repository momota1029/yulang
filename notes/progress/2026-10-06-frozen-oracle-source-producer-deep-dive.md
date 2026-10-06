# Frozen Oracle: local effect-view ledger and Catch correspondence boundary

Date: 2026-10-06
Status: frozen, independently compiler-referee-reviewed bounded historical characterization (no findings); research-only
Yulang3 baseline: `91c8d7be6ee15ad47bba069a2bbc4e86f0ea7729`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`, `/tmp/yulang2-oracle-rebuild`
Exclusive lease: this note only
Semantic and implementation authority: none

## Objective, selected cone, and novelty

Trace a source-owned view candidate to its first missing correspondence with
the current original signature/owner/view producer. The distinct cone is
`LocalBinding.effect -> local Name -> EffectViewId -> Catch row submission`.
The prior producer/falsification notes already mention separate ordinary and
stack effects and ordinary Apply's use of the ordinary endpoint. This pass
does not repeat that attack: it follows the separate Catch consumer, its two
comparison channels, and the scope of the view ID's inverse.

Result: a local Name can allocate a fresh view handle for an unchanged stored
stack tuple. Catch consumes that tuple to submit both the ordinary and weighted
inner effect against the handled row. These submissions receive
`UnknownInternal`, and the resulting Catch computation carries no view handle.
The original scrutinee expression is retained in `Expr::Catch`; this result
does **not** claim that source identity is globally erased or unrecoverable.
Neither the view ledger nor these Catch submissions constructs a complete
original signature/owner/contribution table or its exhaustive inverse.

Governing current sections: inferred call views §§1.1–5; nested-block source
interpretation §§1–3; directional protection §§2–4; current task's missing
source producer frontier; theorem-dependency lines 400–432; original-signature
licensing construction, “Explicit hypotheses and sorts”, “Conditional
constructor and both coverage directions”, and “First unclosed leaf”.
The selected nested block returns its captured closure. Protected-variable
upper introduction retains original upper/lower identities without backflow.
The pending E/R choice is superseded. Frozen Oracle supplies historical
implementation evidence only; no selected language meaning is reopened.

## Hypotheses and claim class

H1: the twelve historical and fifteen current files inventoried below equal
their pinned blobs. Verified byte-for-byte.

H2: one live `ExprLowerer` receives a valid supplied `LocalBinding` with
`effect=Some(Stack { effect:e, inner:i, weight:w })`; local Name lowering
completes twice without another view insertion between the two calls.
The vector length and both successor lengths fit in `u32`, all referenced IDs
are valid, and allocation does not fail. This is a local state premise,
not a claim that an accepted surface program realizes this state.

H3: a Catch reaches the nonempty handled-row branch with one of the two
computations returned by the consecutive H2 reads as its scrutinee, and
comparison submission completes. Thus its view handle resolves to H2's
unchanged stack tuple L and its ordinary endpoint is L.effect. The row and its
completeness decision are supplied; their semantic correctness is not proved
here.

Established results are H1 and the cited frozen field assignments/branches.
The derivation under H2/H3 is a bounded historical characterization. It is
neither a current conditional theorem nor an admitted-source counterexample,
and it proves no complete-profile existence, licensing, admission, soundness,
principality, source adequacy or production conformance.

## Exact source chain and stop boundary

All source locators below are relative to the frozen Oracle checkout.

1. `crates/infer/src/lowering/local.rs:6–23,43–53` distinguishes a local's
   `DefId` and value from its optional effect. The stack effect contains only
   `effect`, `inner`, and `weight`. Its comment explicitly separates ordinary
   forwarding from the stack view used by Catch. Neither the tuple nor
   `EffectViewId(pub u32)` (`typing.rs:55–56`) includes a formal/occurrence,
   static signature slot, receiver, or contribution coordinate.
2. There is an annotation-side input to this tuple, rather than a newly found
   unannotated producer: `lowering/expr/lambda.rs:1316–1326` maps a supplied
   annotation connection's `effect_stack` to `LocalEffect::Stack`; the defined
   parameter path passes the cloned effect into pattern lowering at
   `:707–714`. Annotation absence sets `local_effect=None` (`:1252–1264`).
   The annotation connection itself and pattern installation are not audited
   here. H2 starts at the actual supplied local record, so this contextual
   producer locator supplies neither that missing installation proof nor
   accepted-source coverage.
3. `lowering/name_ref.rs:146–173` clones the local effect, creates a reference
   resolved to `local.def`, records parent/value/span, creates `Expr::Var`,
   and attaches the optional effect-view handle to its returned computation.
   `:176–198` allocates a handle **on every stack-effect Name read** by appending
   the tuple to `self.effect_views`. The ledger entry contains no reference
   ID; the returned computation separately retains both expression and view.
   Thus the whole returned record offers a structural join that its tuple
   alone does not supply.
4. The ledger is a field of `ExprLowerer`, not a demonstrated exported profile
   table (`lowering/expr/mod.rs:36–40`); both inspected constructors initialize
   it empty (`:88–92,134–138`). `typing.rs:18–39` defaults new computations to
   `effect_view=None` and attaches one only through `with_effect_view`.
5. For nonempty handled effects, `lowering/control.rs:957–974` forms a row and
   passes the scrutinee's ordinary endpoint and view to
   `subtype_scrutinee_effect_to_row`. In its Stack branch (`:995–1020`), it
   submits `Pos::Var(effect) <: row`, then constructs
   `Pos::Stack { inner:Pos::Var(inner), weight } <: row`. Both calls pass
   `OriginId::unknown_internal()`. The None branch submits only the ordinary
   variable comparison. This is a source-lowering consumer requesting solver
   comparisons; no solver conclusion is used as evidence here.
6. The immediate result retains `Expr::Catch(scrutinee.expr, arms)` and uses
   `Computation::new(..., Evaluation::Computation)` (`control.rs:983–992`),
   hence has `effect_view=None`. This is the selected stop boundary. The
   requested comparison arguments have no source-owned attachment certificate;
   the Catch result has no inherited view handle. The retained expression may
   support additional structural or downstream provenance, which is outside
   this cone and is not excluded.

These are facts during source lowering, before final signature projection.
They are **not** a claim that the ledger exists before every solver operation:
annotation connection or earlier lowering may already have submitted and
processed constraints. No solver or post-solve output was traced in this pass.

## Smallest handle discriminator and conditional derivation

Let the initial ledger length be n under H2 and let `L=(e,i,w)` be unchanged.
Two Name reads produce:

```text
first read:  view v1=n;   ledger[n]=L;   Expr::Var(r1), resolved to d
second read: view v2=n+1; ledger[n+1]=L; Expr::Var(r2), resolved to d
v1 != v2; ledger[v1]=ledger[v2]=L; same supplied local d
```

The inequality follows from the append indices and explicit no-overflow
premise, not from a generic “fresh” helper name. The distinct fresh reference
allocation calls are visible; uniqueness of returned RefIds is not needed for
the view inequality and is not separately proved. Two reads are the minimum
needed to discriminate per-read view allocation from a canonical handle for
this one unchanged tuple. This does not select current static-slot sharing.

For a supplied handled row R under H3, the requested terms are:

```text
Stack view L:  Var(e) <: R ; Stack(Var(i),w) <: R
No view:       Var(e) <: R
```

These are submission sequences, not counts of distinct final constraints:
the machine may intern, deduplicate, or fail. Replacing the handle with None
is an analytical mutation that removes the second requested channel while
holding e and R fixed. No executable mutation or final acceptance difference
was measured. Equal e and i or identity w may also collapse semantic/structural
distinctions, so no solver-outcome discriminator is claimed.

The ledger inverse recovers L from v; by itself it does not recover the local
definition, reference, annotation source or licensed contribution. The full
Computation/Expr/ref chain can retain definition/use identity, but retaining
that identity still supplies no original `Attach_C(X,e,t)` judgment. A complete
signature table is not an inverse of this three-field ledger lookup.

## Coverage, independence, and exact missing current clause

Current licensing requires a source-owned attachment from the original upper
introduction witness to tagged `t=(beta,s,p,c)` and exhaustive inversion of
the independently interpreted original licensing rules on one X/original
`xi=(nu,K,D)`. This cone supplies a local stack tuple and a specialized row
consumer. It does not supply original beta/slot/position/contribution coverage,
typed owner/receiver incidence, or the soundness and completeness implications
for `Attach_C`/`Lic_C`. It also does not manufacture the unannotated formal's
selected protection seed: the inspected annotation-absence path has no local
effect view. No mapping from historical stack hygiene to the selected current
protection meaning is asserted.

Oracle source is grounded independently of current stipulated-transition
checkers. The lowerer, ledger and Catch consumer share one implementation's
assumptions and are not independent semantic oracles. Byte equality establishes
artifact provenance; reading these assignments establishes only their local
consequences. No checker assumes and then claims to prove source rules.

Omitted: pattern installation, complete annotation lowering, accepted CST
realization, other ledger consumers, complete solver/projection behavior,
methods/recursion/imports, global provenance reconstruction, complete original
licensing/profile/nonemptiness/admission, and current proof/production gates.
Failure conditions include changed blobs, invalid/local-crossed view indices,
`u32` index truncation, local effect mutation, intervening insertions (for the
consecutive-index formula), allocation/submission failure, and not reaching
the nonempty handled-row branch. No global Oracle absence is claimed.

Stop: the Catch submission/result boundary is the first missing typed
attachment boundary in this selected cone. The twelve-file source budget is
exhausted. Recommended next action: derive current `Attach_C` construction and
exhaustive inversion directly; this ledger may serve only as a check against
equating ephemeral read views with original static signature slots.

## Commands, resources, and frozen hashes

Read-only commands: bounded `rg -n`, `rg -l`, `rg --files`, `sed -n`, `nl -ba`,
`cat`, revision reads, and a sequential Python SHA-256/byte comparison against
`git show <pin>:<path>`. All twelve source and fifteen current dependencies
matched. Initial aggregate context output truncated; decisive prior-note and
source windows were reread. No build/test/Oracle execution, formatter, Git
mutation, random seed, enumeration range or scratch output. Only this leased
note was written. One sequential lightweight source/hash job; heavyweight
process count zero. CPU, peak RSS and total wall time were not instrumented;
captured commands completed in about 0.2 seconds or less individually.

Historical files below are under `crates/infer/src/`. Locator-only alternatives
were investigated but furnish no positive claim: `uses.rs`,
`lowering/expr/projection.rs`, `lowering/mod.rs`,
`role_impl_conformance/view.rs`, and `lowering/expr/block_local.rs`.

| Historical path | SHA-256 |
| --- | --- |
| `typing.rs` | `b6ade453931d288c03332770fa76022abf90f1276466faeefa3d647be63bcef6` |
| `uses.rs` | `e3492318c6cb788097b350f1cd692023ffa7454b8a7c2f8fc448a0293520fdf3` |
| `lowering/name_ref.rs` | `699c7dc84a2b4889355ffe9cd23b3e871c295957dbcb3fbad96ee9ee36470ede` |
| `lowering/expr/projection.rs` | `cd7a7c78f013e4f8e20dd3d0f3b979660b6168ab72e7867cf8d15f3f82e848fd` |
| `lowering/control.rs` | `4253ea5e94b671271fe64b5d1956bb961215e2e5c1278c56d88f0c67caaa7963` |
| `lowering/mod.rs` | `244e5f8ea339d2e24aa1f8456e99072e4a491b97da58348a4e79eed188ce61a1` |
| `lowering/expr/mod.rs` | `bbece8eddeba93cff358f4d14eeb9d818f4ac9170b327668457340f166e08c6b` |
| `role_impl_conformance/view.rs` | `94130ef703f4775f10a46d9706f165a9b588195bff280242d1da66ec49aec835` |
| `lowering/local.rs` | `300bc2b12d8f13aed0ae5f65cdec93683e7de2719be38bb33724f51730e52f81` |
| `lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `lowering/expr/block_local.rs` | `661386fe559d8e207a9597962cfee3c11f05f21aa2888e22b2c0143825051898` |
| `lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |

| Current dependency | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `tasks/current.md` | `7893e5f7bb9482c9a0d95c533460722b314a2d2562a9874eba230359bb3af6ba` |
| `notes/theory/inference-theorem-dependencies.md` | `cb32b2450d45904e7518f807eb5cc3ca1ce8ea2f512b35a3f7b3c150d50ef94b` |
| `notes/design/INDEX.md` | `222eb6613c51e175de81be32172017e4f5fddcac18119716bdf675f841f3bbd2` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/progress/2026-10-06-original-signature-licensing-construction.md` | `f5032a91781706551dcd01474f6024eb34fcb0cb110fa6157f7ec577ccfc5cff` |
| `notes/progress/2026-10-06-frozen-oracle-whole-tuple-source-producer-correspondence.md` | `fcc23c134001e25f02a28a251c38ef083872b51458e39948fcfb3dc0c8652dae` |
| `notes/progress/2026-10-06-frozen-oracle-signature-applicability-archaeology.md` | `1621abe333739b475222953ec52adfd5a67d54727c2b612bdee160186ede8b30` |
| `notes/progress/2026-10-06-frozen-oracle-missing-producer-followup.md` | `d211a365acca703b782e2fc936864b9c0c189a5861ce34729326c3f3b642d6ee` |
| `notes/progress/2026-10-06-frozen-oracle-remaining-licensing-producer-archaeology.md` | `03adcceed74bb8a08290e748989fd0af1e8eb417a19a7a7ba6303c29191d70d7` |
| `notes/progress/2026-10-06-frozen-oracle-missing-producer-falsification.md` | `868435a99720a49752312f20fa7c51886ead5e0f9371f29a47bc759c9885a7fc` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-frozen-oracle-source-producer-deep-dive.md`.
- Baseline SHA: Yulang3 `91c8d7be6ee15ad47bba069a2bbc4e86f0ea7729`;
  Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; all inventoried dependencies matched pins.
- Review status: frozen, independently compiler-referee-reviewed historical
  characterization with no remaining finding; the inspected chain stops at
  comparison submission. No semantic authority is claimed.
- Checks already run: bounded source/record reads and locator searches,
  revision checks, twelve-source/fifteen-current byte and SHA-256 checks;
  no execution/build/test or Git mutation. Primary owns lease/diff inspection.
- Proposed one-line research-checkpoint commit message:
  `research: trace Oracle local effect-view Catch correspondence boundary`.
- Shared-record deltas intentionally left for primary/curator: optionally
  record the ephemeral view ledger and dual Catch comparison mechanism with
  the retained expression recovery qualification. Keep original attachment,
  exhaustive inversion, complete profile/admission and every theorem/production
  gate open. No shared record or question-board bundle was changed.

## Independent review

A compiler referee reviewed this note against the exact frozen Oracle source
and the cited current-theory frontier. The initial review found no blocking or
major issue and one nonblocking H3 precision observation: the Catch scrutinee
needed to be explicitly tied to one of H2's two returned computations. The
repair now states that link, so its view resolves to H2's tuple `L` and its
ordinary endpoint is `L.effect`. Delta review passed with no remaining
finding. Review scope remains this bounded historical chain; it does not
certify Oracle semantics or any current source/proof gate.

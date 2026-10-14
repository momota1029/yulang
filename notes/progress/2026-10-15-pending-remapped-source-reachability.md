# Pending/remapped cuts: authentic source reachability

Status: reviewed bounded static source characterization. A fresh M2
`compiler_referee` found no findings in this artifact. No executed source
witness, source-qualified counterexample, H2/U closure or implementation
authority follows.

## Objective, baseline and unchanged parent

Investigate only the combined premise of the reviewed pending/remapped native
discriminator: structural Value extrusion overtakes the original queued
`x <= Allowance(v)`, genuinely copies x to x', and a later unmatched atom is
admitted directly to x' before upper admission, merging, qualified equality or
fresh restoration supplies a checking route.

Primary-supplied checkpoint: `9675907dfb1d37ab46e31573f0470e2f29de3fc5`,
branch `research/simple-sub-intrusion`. Native source baseline:
`d8a6209c1dc181858948c4d811259aa20683d64e`. No Git command was used to
independently establish branch identity. The five native owner hashes shared
with the reviewed audit match exactly; additional source/HIR inputs are frozen
below. The primary subsequently reported fresh M2 compiler-referee review of
the pending pair with no findings, within its conditional scope.

The original parent remains every originally admitted shallow Catch H under
one original scoped sigma, with full scrutinee, operation/value-arm binders,
provider, raw resumptions and dependent interfaces. Eligible actually consumed,
protected/independent, unmatched, outside-arm and raw-resumption contributions
keep their original categories. The original upper Function demand's Eout is
the selected local introduction. No marginal witness, source restriction,
new protection law or residual identity is selected. H1/H2/U remain OPEN;
H3/P remain disabled; production/F5 remains separate.

Governing sections: top-level principles §1.1 and §§1–5; residual-lineage
selection, Selected policy and Preserved contract; attachment/admission §4;
design-authority's authority order and natural compiler behavior; and
compiler-engineering's proof-obligation economy. Later top-level principles
govern the older unconditional rollback row. The `yulang-proofs` skill is
applied only to the source/evidence boundary; the main constructive lane
remains primary-owned.

## Decisive bounded result

The literal native discriminator's **fresh `Contribution` constructor is not
seeded by ordinary source-only candidate execution** at this baseline.
Authentic operation effects instead reach the same nominal consumer as
`AnnotationMember(view,member)`. Therefore that literal native trace cannot
itself be promoted to a source witness. This is a constructor distinction,
not permission to drop semantic source contributions or the analogous
AnnotationMember obligation.

Independently, the suggested nested positive Result Function is insufficient
to authenticate the later consumer: its positive x' field decomposes as an
Effect lower. A negative occurrence of the original x selects another
polarity-map entry. These facts eliminate two proposed shortcuts to source
reachability. They do **not** prove the combined premise impossible for all
source-generated AnnotationMember histories.

### Constructor invariant and derivation

Hypotheses: begin with the ordinary candidate graph created from source/HIR;
do not inject a native operand or captured graph through a test/helper; use
the current source actions, solver transitions and scheme capture/freshening.
These hypotheses describe the execution whose correspondence is being
investigated. They do not define a narrower admitted language.

1. `start_candidate_graph` constructs `GraphState::default()` and initializes
   its effect algebra (`candidate_scheme.rs:703–718`). The effect state is
   `Default` with an empty `Vec<Contribution>` (`candidate_effect.rs:109–118`).
2. A crate-wide search of `candidate_effect_contribution`, `Contribution(`
   and contribution storage finds the only append/allocation at
   `candidate_effect.rs:929–951`. It returns `Contribution(id)` after pushing
   one entry. Other storage mutations retain/truncate an existing prefix;
   they supply no first entry.
3. Every direct caller outside the scheme reconstruction branch is under a
   test module: `candidate_context_tests.rs`, `candidate_effect.rs`'s
   `#[cfg(test)] mod tests` (from 1653), `shadow_apply.rs`'s tests (including
   1720), and `lib.rs`'s tests (including 33365). Test-built handles are not
   source producers.
4. The remaining non-test caller is `candidate_scheme.rs:1092–1095`. It first
   obtains an existing `Contribution(id)` from a captured node and indexes
   `state.contributions[id]`, then copies its effect/origin through that same
   allocator. Capture forms such a node only from an existing Contribution
   endpoint (`candidate_scheme.rs:473`). It cannot create the first operand
   from an initially empty source-only state.
5. Induction over these mutation/constructor sites gives zero native
   Contribution operands for that source-only execution. Freshening preserves
   this invariant because its Contribution branch requires a prior seed.

This is static correspondence for the present native tag, unreviewed here.
It is not a claim that source programs lack effects, or that a future authorized
source constructor could not produce that tag.

Authentic route: HIR records resolved operation syntax as
`LocalSourceForm::Operation` (`yu-hir/src/module/local_source.rs:694–709`),
and source planning creates `Action::Operation` (`candidate_source.rs:573`).
`candidate_operation` constructs the signature's positive Value at level+1
and admits its Value link (`candidate_effect.rs:786–804`). At the outer
operation Function only, `candidate_signature_value` adds the declaration's
family to ResultEffect (`1494–1509`). `candidate_signature_effect` builds a
view and installs `Support(view)` on the appropriate fresh port
(`1516–1536`, `1634–1646`). Ordinary comparison of Support emits its members
as `AnnotationMember(id,member)` and its tail as a row
(`candidate_effect.rs:960–982`). Both native atom variants share the
Allowance membership/unmatched-tail branch (`985–1019`), but member identity
also contains the actual view ID. Copying that ID must use the actual shared
view-map key; replacing it by a fabricated Contribution loses this premise.

## Source order and the real overtaking seam

Source actions do not run concurrently with a previous action's typed drain.
`step_candidate_source` executes one action and advances `next` after its
return (`candidate_source.rs:819–873`). `admit_candidate_fact` builds an Apply
demand, runs `constrain_live_value`, and only then admits application-effect
joins (`shadow_apply.rs:1428–1570`). Annotation pairs likewise check the
initializer, computation effect and exposed signature by successive calls
(`candidate_effect.rs:1269–1344`). A source action boundary therefore cannot
retain an ordinary pending cut while the next source action begins copying.
Synthetic source support changes only at completed action/construction
boundaries; its supply hook is test-only (`candidate_source.rs:807–818`).
`start_typed_drain` requires an empty worklist (`lib.rs:12192–12206`), and
normal completion checks worklist exhaustion before acknowledgement/return
(`12347–12364`). Thus splitting the native setup over completed constrain
calls cannot authenticate the pending order.

There is nevertheless a genuine **intra-drain** scheduling seam. For a
Function/Function comparison, children are Argument Value, ArgumentEffect,
ResultEffect, Result Value (`lib.rs:12551–12581`). The retained dispatcher
iterates them in reverse and inserts each at the front (`12701–12724`), so
they are popped in that stated order. Ordinary effect-bound replay creates
children and drives them with no provenance (`candidate_extrusion.rs:766–806`);
that owner transfers them to the queue back (`candidate_context.rs:3281–3344`,
`lib.rs:12913–12914`).

For example, the following queue evolution is a conditional schedule
derivation, **not an authenticated HIR fixture**:

```text
front [ArgumentValue, ArgumentEffect, ResultEffect, ResultValue] back
after an Effect child emits x<=Allowance(v):
front [remaining Function siblings, x<=Allowance(v)] back
```

If a remaining Value sibling is structural against a lower-level row, its
dispatch calls `candidate_extrude` synchronously and queues the rewritten
Value (`lib.rs:12469–12516`) before the pending Effect child is popped.
Extrusion's local Work loop does not drain the typed queue. This establishes
that FIFO alone supplies no universal pre-copy cut-registration barrier.
It does not establish that one source-derived set of sibling interfaces has
all the required row equalities, levels, incidence and nonqualification.

## Why the proposed copied-Result consumer does not follow

For the discriminator's x, positive Visit creates the map entry
`Key(EffectRow(x), Positive, l)` and x-to-x' link
(`candidate_extrusion.rs:5,89–125`). Rebuilding a Function uses polarity p on
Result/ResultEffect and the opposite polarity on Argument/ArgumentEffect
(`223–252`). `Work::Function` creates a live term with the child's recorded
polarity (`330–356,371–386`).

For a directly exposed positive ResultEffect field, Function decomposition
uses that field as its Effect **lower**, with the receiving Function's field
as upper (`lib.rs:12569–12574`). Nesting positive Result Functions repeats
this orientation; it does not turn x' into a receiver of a fresh atom.
`effect_endpoint` also asserts the polarity of a live variable
(`lib.rs:11466–11484`). A negative occurrence of x is a distinct
`Key(x,Negative,l)`; it is not the positive x' merely because the original row
ordinal is shared. One map does not identify those entries.

Bounded conclusion: the suggested nested positive Result carrier, followed
only by ordinary Function field decomposition, cannot be the required direct
`q <= x'` consumer. It may install an upper on x', which is an actual
transition to include and can activate existing lowers; the discriminator
explicitly excludes such intervening upper admission. No semantic source
rule is inferred from this local conclusion.

The following seams prevent promotion to a universal source impossibility
theorem in this packet:

| Attempted route | Static disposition / remaining premise |
| --- | --- |
| Separate source actions / public constrain calls | Refuted as a way to leave the original ordinary queue pending across the boundary. Each call completes its emitted drain. |
| Sibling Function Value after an Effect replay | Native scheduling permits overtaking. One authentic complete source/HIR interface satisfying the combined levels/incidence is not derived. |
| Nested positive Result Function exposes x' | Exposes x' as a lower, and supplies no direct fresh-atom receiver. Negative copy is distinct. |
| Operation creates the literal fresh Contribution | Refuted for source-only current constructors by the zero-seed induction. Semantic contributions still exist as AnnotationMember. |
| Incoming Allowance tail is x' | Real exception to a naive polarity-only global argument: IncomingAllowance reconstructs a negative cut whose tail is a positive copied gamma (`extrusion:165–179,295–309`); unmatched atom checking can admit directly to that tail (`effect:1008–1013`). One must track its original cut, source, actual member/view identity, pending receipts and old gamma link. No full disposition is established here. |
| Support or AnnotationMember carrying a copied view | Support expands members and a tail. Per-operation view-map identity matters; native Contribution substitution is insufficient. Full source ancestry through every copied/fresh member remains open. |
| Source effect component addresses x' directly | Source components are initially allocated into `live_components` (`lib.rs:10099–10105`); the inspected mapping is not assigned an extrusion copy. Structural fields and canonical representatives remain other access routes. This observation alone is not an all-lifecycle ownership theorem. |
| Actual upper admission, merge, qualified equality, fresh restore | Preserve these positive alternatives. No source proof excludes them in the combined history, and none may be suppressed just to realize the candidate. |
| Catch constructs this residual state | Current source Catch joins scrutinee and arm effects separately (`candidate_source.rs:517–534`). H3/P is disabled. A native open cut from an annotation is not evidence of authentic Catch consumption or complete operation coverage. |

The precise remaining premise is an **authentic incoming-atom owner** for a
positive copied row, after the pending original cut scan, whose original
source/cut/tail and view-map counterparts do not already emit the required
consequence. Local Function polarity rules do not discharge this because
incoming Allowance tails cross that simple signed-term boundary. This is the
owning constructor/consumer problem to resolve; repeating the native
Contribution trace or a direct-Replay census does not address it.

## Checks, budget, omissions and next action

Method: static constructor census and direct source/queue/consumer derivation.
There is no independent executable oracle. The code is the operational
subject; the argument does not assume that its transitions implement the
accepted language meaning. Valid handles, successful processing and untouched
source-only initialization are explicit premises. No seed/range, mutation,
probe, measurement, Cargo/build/test, Git command, compiler edit, child launch
or interactive question was used. Initial combined reads exceeded capture
limits; cited source-owner ranges were reread in bounded chunks. The search
was complete for the named Contribution allocator/call sites under
`crates/yu-solver/src`; full semantic source reachability was not completed.

One static leaf; twenty-minute wall cap. Exact elapsed time, CPU and peak RAM
were not measured. Only lightweight read commands and the leased note write
ran. Source hashes shared with the supplied reviewed audit are unchanged.
Task records changed under the primary while this lane ran and are locators,
not frozen proof premises. The pending pair's live hashes reflect the supplied
review-status update. No production dependency change was observed.

Smallest future executable seam, if required: use an ordinary source/HIR
candidate schedule and observe the existing retained typed-drain steps around
`candidate_apply_effect`'s replay, `dispatch_live_item`'s structural extrusion,
and `candidate_check_effect_operand`'s AnnotationMember-to-tail admission.
Require the same operation's parent/copy and view-map IDs, actual source
checking occurrence, exact queue order and rescue events; do not inject a
native atom or hand-built effect graph. A harness must first identify the
source expression producing the receiver of the late member. No such fixture
or harness was written or run; the Cargo allocation is exhausted.

Recommended next action: give the constructive/source lane the positive-copy
incoming-atom lineage obligation, beginning with IncomingAllowance's copied
tail and the source-generated AnnotationMember's exact view-map ancestry.
Prove the original/link counterpart consequence or exhibit the authentic
source receiver that escapes it. This changes the method from assumed native
input to its actual producer without changing the original H2/U scope.

SHA-256 frozen dependencies (bare `.rs` names are under
`crates/yu-solver/src/`):

```text
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5 lib.rs
ed3e213e943a553943784e409194723f64acb810a0bcf06607ee95b0eb4e4ed1 candidate_extrusion.rs
f414efa7efdb17644f4dfa6b0bba621c1bb7cccd0f83735c33a0acb875da6b91 candidate_effect.rs
6301ca80eec137df3f2c2c44e2edaa7dbdf1ed7a78c69617228888e63654e461 candidate_context.rs
c8ef7cc472f0dcb60d793c6f9b4f6ba1aefb76f919ff2a3ce9310f85eb647dcd candidate_scheme.rs
32a6d875b9e89af8192cf017fbeccc95e9648223490d72de64a6957c97aa6e1b candidate_source.rs
831dc28b977a5e01e6f0ef0faa795495d78ecb2cc01678db48e9cf7ea5132eac shadow_apply.rs
afc91346af535529f973421bdbe2a43520c98946097cae545e4ae1a665146074 crates/yu-hir/src/module/local_source.rs
00e9691a3ecb92029f15fc6bb0a0c79f906287d2c6517e672e33ab7c7f1c6cd5 notes/theory/2026-10-15-pending-symbolic-cut-continuation-application.md
bd377f5a891d94f40bb026408fbf1ca824695b6fd6a08aa3a08f667d3aa177ae notes/progress/2026-10-15-pending-symbolic-cut-continuation-falsifier.md
1e6d42dc59ca4e82c62fa78fd4bcb6188f72b35aac964095883fcf03bb5beaf6 notes/progress/2026-10-15-copied-symbolic-cut-continuation-owner-audit.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81 notes/design/2026-10-11-yulang-inference-top-level-principles.md
d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98 notes/design/2026-10-10-contextual-residual-lineage-selection.md
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc notes/design/2026-10-10-contextual-attachment-admission-design.md
```

## Commit packet

- Exact leased path: `notes/progress/2026-10-15-pending-remapped-source-reachability.md`.
- Baseline SHA: `9675907dfb1d37ab46e31573f0470e2f29de3fc5`; native baseline
  `d8a6209c1dc181858948c4d811259aa20683d64e`.
- Changed dependency hashes: five shared native owner hashes unchanged;
  pending pair now has the reviewed-status hashes above. Primary-owned task
  text moved and supplies no theorem premise. Additional source inputs are
  frozen above, without claiming a Git-baseline diff check.
- Review status: fresh M2 `compiler_referee` found no findings in this bounded
  characterization. The combined semantic source reachability remains OPEN;
  no accepted-source witness or impossibility theorem is established.
- Checks already run: focused constructor/call-site census, queue and signed
  Function-field derivation, dependency hashes, leased artifact whitespace and
  terminal-newline check. No executable verification.
- Proposed checkpoint message: `research: distinguish pending cut source constructors and copied-row consumers`.
- Shared deltas left for primary/curator: record the literal Contribution
  zero-seed result, real sibling-overtaking seam, bounded Result-carrier
  exclusion, and incoming-Allowance/AnnotationMember ownership premise.
  Preserve H1/H2/U OPEN, H3/P disabled and every source category. No shared
  task/index/authority/theory file was edited. Primary owns fresh review,
  adjudication and Git integration.

Writes stop at handoff.

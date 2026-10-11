# Same-family handler-arm contribution: Oracle source-to-output derivation

Date: 2026-10-12
Status: producer research note; no independent review or gate promotion
Claim class: bounded source-to-handler derivation; output bridge remains unproved
Yulang3 baseline: `0ef6b49ef401df9fa24e94007869d0c03fc80cc2`, branch `research/simple-sub-intrusion`
Oracle source: immutable `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this file only; leaf, no delegation

## 1. Frozen statement, quantifiers, binders, and exclusions

The parent statement remains original **H**, verbatim from
[original H attempt](2026-10-12-oracle-effect-hygiene-original-H-proof-attempt.md)
§1 and [global H](2026-10-11-oracle-global-effect-hygiene-proof.md) §1:

> For every Oracle source program P in the original successfully lowered source
> domain, every successfully lowered composed-negative concrete annotation
> occurrence a, its original lexical scope sigma and binders, every actual
> copy/instantiation u of that occurrence, and every actual function call/output
> route k involving that occurrence, subtraction authorized by a removes only
> the contribution attached to that exact instance on that route. An independent
> contribution at the same resolved family survives that subtraction. Symbolic
> annotation tails remain connected; every current and future concrete lower
> reaching the relevant receiver encounters the actual retained check. The
> occurrence, attachment, scope, provider/call binder and correlated residual
> lineage remain appropriately identified through actual copying and
> generalization, up to the actual consistent renaming of a fresh use.

The assigned discriminator fixes one candidate source P+ derived from the
captured int fixture in [constructor derivation](2026-10-12-native-negative-residual-constructor-derivation.md)
§11:

```yulang
act ev:
    pub send: (int, int) -> ()

my run(action: [ev] 'a): 'a = catch action:
    ev::send (s, n), k ->
        ev::send (s, n)
        run (k ())
    v -> v

run: ev::send (1, 42)
```

Freeze the actual lexical annotation occurrence `[ev]` on `action`, its
function scope, Value binder `'a`, payload binders `s,n`, continuation binder
`k`, value-arm binder `v`, operation declaration, recursive `run` reference,
and final `run`/`send` Calls. The emitted arm application and final argument
application are distinct source occurrences even though both resolve to
nullary effect family E = ev. The handler pattern is a third occurrence;
the declaration is a fourth. No arena-local numeric ID is an origin witness.

Required bounded conclusion: for every normal successful publication/use of
this source, the arm application's independent E contribution has a
source-derived route through its actual branch result and the selected `run`
return Effect, survives actual projection/generalization, and reaches the
actual later/current outer Call output. Its preservation must be justified
jointly with the input occurrence's subtraction, not by independently choosing
an output witness. This bounded conclusion is a discriminator inside H; even
a proof of it does not establish universal H. Its acceptance is not assumed
from the control fixture, and no Oracle execution is allocated.

Shared operational assumptions: inspected immutable bytes, completed normal
constructor calls, valid fresh allocation before exhaustion. These assumptions
do not supply actual scheme selection, source activation, projection support,
replay completeness, attachment-to-Call adequacy, or successful acceptance.
Incorrect attempts must not publish an inconsistent result. No domain
restriction, semantic weakening, new inferred scheme, authority adoption,
complete Call theorem, soundness/principality theorem, or universal H closure
is claimed. Parameterized families, nested higher-order cases, arbitrary
copies, and future consumers stay in the original parent statement.

Authority: [annotation hygiene](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–4; [attachment/admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§§3–6; [residual lineage](../design/2026-10-10-contextual-residual-lineage-selection.md);
[complete Call](../design/2026-10-07-complete-call-contribution-definition.md)
§§2–5; [top-level inference](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. Complete Call retains callee computation, whole argument, actual
provider/entry, return, and future interface. The former callback output is
withdrawn. The existing [run contribution proof](2026-10-12-run-effect-contribution-proof.md)
is reused only within its reviewed conditional scope.

## 2. Grammar and source occurrence inventory

All Oracle locators below are relative to `crates/` at the immutable revision;
reads used `git -C /home/momota1029/rust/yulang2-oracle-capture show
a58eefc31e:<path>`. The live capture checkout's instrumentation is not evidence
for this candidate.

The block spelling is supported by the owning parser, rather than guessed:
`parser/src/expr/control.rs:917–926::parse_arm` passes the Arrow's trailing
trivia to `parse_inline_or_indent`; that helper at 22–34 selects an indented
statement block when its indentation exceeds the arm indentation.
`parser/src/stmt/block.rs:242–283` consumes the two statements and stops at
the dedented value arm. The handler accessor
`infer/src/lowering/control/syntax.rs:91–100::arm_body_expr` accepts the
resulting `IndentBlock`; `expr/block_local.rs:69–86,130–140` lowers its first
expression as a statement and its final expression as the block result.
This is a static grammar/constructor characterization, not a parse or acceptance
result for P+.

Use origin labels A (final argument `send`), B (added arm `send`), and C
(recursive `run (k ())`). Preserve these expressions, their actual parent
`run` definition, and their argument spans. The formal annotation view is
attached to the `action` binder. Reading the payload tuple for B reads `s,n`,
not `action`, and B calls the resolved operation declaration. In the inspected
owners, B does not obtain A's formal effect view from equal family spelling.
This establishes different construction occurrences and different Effect
slots. It does not establish the complete semantic attachment/Call theorem.

The control P0 omits B and uses the original one-expression arm. Only P0 has
the existing successful int capture. Its selected scheme cannot be substituted
for P+'s scheme, and this note transfers none of its numeric root/bound IDs.

## 3. Native constraints emitted at the handler boundary

Names below are constructor coordinates, not source names or numeric IDs:

| Coordinate | Actual owner |
| --- | --- |
| V | full Effect slot of annotated `action` |
| U, alpha | inner coordinate and subtraction ID of that same annotation instance |
| K_B, C_B | B's call-return and complete application result Effects |
| C_C | recursive arm application's complete result Effect |
| B_eff | joined arm block Effect |
| T | `lower_catch_with_scrutinee`'s result Effect |
| R | final defined body Effect, after recursive-skeleton forwarding |
| O | final outer application result Effect |

The original concrete parameter constructor, reused within
constructor-derivation §9's exact scope, emits
`Push_alpha(U) <: V`; its public argument port is
`Var(V) intersect Row({E},Top)`. The annotation `[ev]` has no symbolic Effect
tail; Value `'a` remains a separate binder. The handler is complete: the one
operation, total tuple payload pattern, and unguarded arm satisfy
`control/syntax.rs:133–146` and `control.rs:1723–1758`.

The actual B application is constructed by
`expr/tail.rs:535–627::make_app_with_origins`. It allocates fresh K_B and C_B,
emits its actual four-port demand, and emits these two empty-context roots:

```text
callee_evaluation_B <: C_B
K_B                 <: C_B                       [F0]
```

For this resolved global operation callee, the return projection is the bare
call Effect slot (`tail.rs:740–755`); no local unannotated-parameter return
wrapper is justified. Both forwarding roots have Internal origins, separate
from the source-origin Call demand. The unchanged operation signature owner
`body/act.rs:112–125,147–194`, `body/signature_helpers.rs:217–255`,
`lowering/mod.rs:599–615`, and `signature_effect.rs:78–106` constructs a
positive Function with return Effect `Row([Con(E,[])])`. This is the actual
declaration constructor, not yet an observation of B's selected provider.

`expr/block_local.rs:1284–1306::prepend_block` emits

```text
C_B <: B_eff                                     [F1]
C_C <: B_eff
tail_value_C <: block_value
```

`control.rs:1164–1168::lower_catch_arm` then emits

```text
B_eff <: T                                       [F2]
block_value <: catch_value
```

After lowering the arms, `control.rs:957–974,995–1021` emits the separate
scrutinee constraints

```text
V             <: Row({E},T)
Push_alpha(U) <: Row({E},T).
```

Only the actual scrutinee and its effect view are arguments to this row owner.
Neither K_B, C_B nor B_eff is substituted as the scrutinee. The weighted row
owner may create/reuse its own gamma and emits both source feedback and
gamma-to-T projection (`constraints/row_effect.rs:151–233`). These residual
derivations retain their actual parents; they are not the independent B path.
Oracle residual-key reuse does not authorize successor lineage merging.

The defined-lambda owner emits `T <: R` when forwarding to a recursive
skeleton (`expr/lambda.rs:788–808`), then constructs the actual Function
return Effect from R at 946–974 and `expr/tail.rs:1084–1109`. This coordinate
is not U or V. The root formal stack alone does not create an output POP;
the exclusions in constructor-derivation §9.1 still apply. Any further
predicates from actual Value/result/latent constructors must be computed from
those constructors; their absence is not assumed from family equality.

Thus the source emits a distinct arm-output path F0/F1/F2, followed by the
real R owner. It emits no arm-wide family deletion at `lower_catch_arm`.
Emitted roots alone are insufficient for the required published-output claim.

## 4. A source-derived projection fact for F0/F1/F2

This is an unreviewed local derivation at the actual source constructors.
Its hypotheses are completed normal admissions of P+'s F0/F1/F2, with the
actual fresh coordinates above. It concludes projectability of their alias
lower bounds while those admitted records are queried. It does not assume an
Independent carrier, an E lower at K_B, or an exported R row.

1. Each root first exposes a fresh result receiver. C_B is fresh at B's
   application; its first callee-evaluation forwarding supplies no use of C_B
   as a source. B_eff is fresh at `prepend_block` after both computations
   have been lowered. T is allocated by `lower_catch_with_scrutinee` before
   this first, unguarded effect arm; continuation formation uses V, not T
   (`control.rs:1128–1133,1596–1629`), and the scrutinee row is installed only
   after the arm body. No earlier owner in this source prefix exposes these
   exact forwarding keys as derived results. Internal origin IDs themselves
   are shared constants and are not used as freshness evidence.
2. `constraints/machine/entry.rs:1357–1424` admits a new canonical root with
   its root origin and empty structural/replay/row parent lists, then queues
   it. The fresh receiver rules out a preexisting equivalent key. The endpoints
   are distinct Vars, so `canonical_subtype_constraint` at 1092–1118 does not
   omit it as a self edge. `subtype` at 493–499 actually drains the queue.
3. `machine/propagate.rs:104–129` installs both the alias lower on the
   receiver and the alias upper on the source. These three computations are
   at the same body level; no level crossing is used to infer identity.
   The fresh receiver has no upper before its first exposure, so its initial
   lower insertion does not manufacture a qualified replay of the same root
   before that root's upper registration.
4. `machine/bounds.rs:962–1029::register_constraint_upper_replay_claims`
   finds no qualified parents for that initial root and actually admits a
   Direct original claim q_i. `constraints/mod.rs:1717–1813` registers its
   claimed Standalone clause on the associated alias lower. The original
   claim constructor has `coverage_root = claim` and records its exact
   producer (`proof/mod.rs:7118–7136,7240–7260`). This is registration at the
   source root, not an assumed semantic-independent support.
5. In production, activation of live row-reduction coverage comes from
   `row_effect.rs:490–540`, with the producer of an actual Var-to-Row
   constraint. Its original-claim lookup is keyed by that producer and
   record. F0/F1/F2 have immutable Var-to-Var producer keys and cannot be
   those row producers. Distinct original claims get fresh roots; derived
   claims retain their parent's root, and claim moves preserve producer,
   coverage root and lineage (`proof/mod.rs:7401–7514`). The production
   activation caller search finds no source path that activates a reduction
   state under these three original roots. Test-only raw live-state writers
   are outside this source derivation. Therefore these q_i roots have empty
   live coverage; sharing a bound with another claim does not identify roots.
6. `CpkProjectionEvaluator::eval_root_coverage` at
   `proof/mod.rs:11879–11915` returns IncludedExact for each q_i. The alias
   lower's actual Standalone Claimed(q_i) clause therefore succeeds in
   `eval_record_uncached` at 11669–11732. A valid scoped query includes that
   record (`structural_kernel/access.rs:862–895`). Extra excluded clauses
   do not remove this successful clause.

The proved distinction is concrete: **a source-owned surviving route can be
projectable through an uncovered Claimed Direct root**. An Independent enum
tag is not necessary. Conversely, a root Internal origin does not itself make
the alias Independent: `projection_carrier_is_independent` at
`machine/bounds.rs:2692–2706` rejects that root's ConstraintOrigin carrier when
the bound has a claim produced by the very same constraint. The actual
Standalone clause, rather than a guessed carrier classification, supplies
inclusion here.

This conclusion is about the three alias bounds and their original coverage
roots. It neither proves arbitrary bound-retention/subsumption across future
lifecycle changes nor proves that the concrete arm contribution is among the
selected R lowers. The recursive body forwarding and root selection have not
been folded into the fresh-receiver argument.

## 5. The actual source constructor supplies the concrete seed

There is a more direct owner than module/SCC scheme selection for B.
`lowering/name_ref.rs:7–37::lower_path_name_at` resolves the qualified
`ev::send` path and calls
`expr/block_local.rs:990–1020::lower_resolved_value_ref_at`. After allocating
the fresh use Value Z_B and queuing ApplyRefResolution, that owner calls
`constrain_act_operation_ref(target,Z_B)` at 1015–1017. P+ is an ordinary
defined lambda, with no current sub-return target that can disable this call.

`constrain_act_operation_ref` at 1029–1048 looks up the actual operation
declaration and its stored signature, builds its operation signature at
1066–1091, lowers it positively, and directly admits

```text
F_B <: Z_B
F_B = Fun(declared_payload_upper, Row([],Top),
          Row([Con(E,[])]), declared_return_lower).
```

Here the two declared Value ports are the positive/negative lowering of the
actual `(int,int)` payload and `()` return, not independently chosen ports.
The exact retained signature is the unchanged declaration from P0; this source
case has no act type parameters or copied-act aliases. The stored-signature
builder and positive lowerer must complete normally, as required by the
source-constructor hypotheses. Their failure-return branches are not asserted
to emit F_B. E is the resolved family of that very declaration, not a family
chosen after inspecting an output. The no-argument-effect signature branch
is `Row([],Top)`, not Neg::Bot (`signature_effect.rs:19–26`); thus no
pure-argument passthrough is used to supply the emitted E.

Z_B is fresh and the direct constructor's predicate is closed, so this initial
Function lower is unclaimed. The subsequently emitted B demand is
`Var(Z_B) <: Fun(actual_tuple_value,actual_tuple_effect,Var(K_B),actual_result)`.
It is a fresh source-origin demand, with a Direct original upper root q_B.
Its immutable negative Function key cannot be a Var-to-Row coverage producer,
by the same actual production-owner argument as §4. The native planner
therefore produces the Function comparison with both actual bound parents;
its qualified replay constraint is projectable because the direct Function
lower and q_B upper are included.

`propagate.rs:257–263` then emits
`Row([Con(E,[])]) <: Var(K_B)` as FunctionReturnEffect, retaining that very
Function comparison as its structural parent. `entry.rs:1507–1508,1564–1589`
registers the structural qualified parent; `bounds.rs:1204–1213,2332–2370`
registers its DerivedUnary clause. Evaluation uses the actual parent
constraint, whose replay has the two included premises, rather than assuming
an Independent tag on the row. It returns IncludedExact. `subtype` drains
these admitted tasks before returning, subject to the stated normal-completion
qualification. Thus the positive E row seed at K_B is derived at B's actual
reference/application constructors; no generalized `send` provider, separate
per-use witness, or observed SCC event is required for this bounded seed.

This closes the formerly possible seed ambiguity by a source owner, not by
another reconstruction. P+ acceptance and the selected `run` scheme are
still not established. Resource-terminal admissions, absent/invalid stored
signatures, other sub-return contexts and parameterized/copied-act cases are
omitted from this local constructor derivation and remain in universal H.

## 6. Native replay from the seed to the branch result

The local continuation first has the following explicit implication:

```text
an actual, projectable Row([Con(E,[])]) lower at K_B
+ active F0/F1/F2 upper records and completed normal replay admissions
---------------------------------------------------------------
an included row lower along K_B -> C_B -> B_eff -> T,
with its actual seed and forwarding parents retained.
```

The seed and its projectability are inputs to this implication, independently
derived for B in §5. Applying it proves the source-to-T slice under the
completed normal constructor hypotheses. It does not independently choose a
row-output witness or assume the desired published output.

The owning replay planner makes the operational step explicit. For each
admitted row lower and forwarding upper, `proof/mod.rs:9448–9515` sees an
uncovered q_i, selects Generic with a real pair replay, and retains both
parent blocks. This avoids `SkipAlreadyCovered` without presuming global
replay completeness. Both bound arrival orders use this owner
(`machine/bounds.rs:3450–3473,3582–3645`). The generated replay is the same
positive row against the exact next negative Var, with the actual ordered
weights. On the empty-context path those weights remain empty.

The concrete row is neither Bot nor an equal-Var self pair
(`entry.rs:1092–1118`); evidence-only replay is guarded by a Var-to-Var
shape at `bounds.rs:3814–3829` and cannot apply to this row replay. A new
result is queued and stepped; an existing canonical result receives the
actual replay derivation and eager claim-parent consequences
(`entry.rs:1165–1259`; `bounds.rs:3033–3053,3832–3848`). A completed
normal replay/admission remains an explicit qualification: resource-terminal
or discarded evidence is not treated as successful propagation.

`propagate.rs:150–160` installs the row at the target. Positive extrusion
visits the Row and its nullary constructor but has no variable to rename or
level to lower (`bounds.rs:4523–4532,4547–4593`). It does not turn this row
into an annotation stack or gamma. Projection parent registration supplies
the actual `ReplayConjunction(lower_premise,upper_premise)` clause
(`bounds.rs:1179–1243,2332–2370`). Its lower premise is the supplied included
seed, and its upper premise is included through q_i; the evaluator at
`proof/mod.rs:11735–11763` includes that conjunction. Induct over the three
actual forwarding edges. This is a proof about native producers and consumers,
not a checker that assumes forwarding transitions.

The combined §§4–6 result is an unreviewed bounded constructor derivation:
B's positive E row reaches the actual handler result T with a projectable
parent tree. Its route does not use the scrutinee row's matched-E transition.
It establishes no published `run` port. Unconditional inclusion of every derived row
does not follow from inclusion of an alias alone: its actual clause is a
conjunction, and its seed can be excluded.

## 7. Exact first unproved source operation and downstream exclusions

The first unproved operation after this derived source-to-handler slice is
**T-to-R forwarding into the recursive defined skeleton, followed by selection
of the actual Function/root return port**. `expr/lambda.rs:788–808` forwards
the actual completed body to `skeleton.body_effect`; R is not a fresh block
receiver. Prior self-call skeleton constraints are already present. The
fresh-receiver proof of §4 cannot be reapplied without deriving this operation's
actual canonical producer, upper record, qualified parents, projection clauses
and resulting row at R. Merely writing `T <: R`, or applying transitivity to
the stored constraints, leaves that operational step unproved. No recursive
projection/activation invariant is assumed to discharge it.

For the later outer `run` reference, the actual named-reference owner queues
the resolved use with its parent, target and use Value
(`lowering/name_ref.rs:83–115`; lifecycle consumer
`analysis/session/lifecycle.rs:1092–1101`). SCC selection chooses
InstantiateUse for a quantified target and otherwise the appropriate open
route (`scc.rs:266–288`). `analysis/session/instantiate.rs:342–519`
reads the target's actual installed scheme and installs its cloned predicate.
The Function consumer `machine/propagate.rs:212–269` emits the return-effect
constraint from **that** provider with **that** replay context. There is no
license to replace this provider with an independently selected declaration
shape, or to infer an Independent support merely because this is a distinct
source application. This later `run` consumer is separate from the direct
operation-reference seed construction in §5.

Remaining necessary work includes the actual T-to-R
forwarding/extrusion and recursive Function/root selection, the selected
scheme image, and the outer reference/use and Call consumer. This note proves
none of those by the captured P0 scheme. For the actual generalized root:

- Module compaction is consumed at
  `analysis/session/generalize.rs:580–602,478–549`; local generalization uses
  `expr/tail.rs:944–1011`. Both need their own actual selected dependency state.
- `compact/collect/mod.rs:848–879` queries projectable lowers and passes only
  their bounds onward. At 1099–1128, a Var lower becomes a secondary occurrence;
  it does not recursively collect that Var's E lower. Thus the alias lemma
  cannot by itself prove concrete inclusion in the compact return Effect.
- `compact/collect/type_nodes.rs:13–22,196–225,261–286,404–445` carries a
  selected positive Function's actual return port into positive Effect
  collection. A selected concrete nullary E row item survives this constructor
  for every carried weight. This known row-item fact supplies no selection
  premise and is not counted as a new universal hygiene proof.
- Variable rewriting retains already materialized row keys
  (`generalize/simplification.rs:100–152`), and finalization materializes
  concrete row entries (`compact/finalize.rs:415–426,542–549,641–689`). These
  facts do not establish the full recursive merge/simplification, pruning,
  quantifier and filter-cleanup equivalence for P+'s unknown compact root.
- `instantiate.rs:788–808,832–845` clones actual Function/Row/Con structure
  with one map; root POPs at 770–785 are an additional operation. Freshening
  cannot restore a missing compact row. No stack-free P+ scheme is assumed.
- The outer Call actually forwards its callee-evaluation and call-return
  Effects to O (`expr/tail.rs:615–627`). Its FunctionReturnEffect child must
  come from the real published provider's return Effect. An input E matching
  `Row({E},tail)` need not flow to that tail (`propagate.rs:1007–1042`);
  that handled A path supplies no substitute for independent B output.

No output loss or rejection of P+ was observed; no accepted counterexample was
constructed. There is no theorem that P+ is accepted, and no displayed target
scheme is proposed. The new local result derives the direct operation seed
and its projectable native forwarding into the actual handler result. It
discharges the source-to-claim registration/exclusion question for these fresh
forwarding aliases and their concrete parent tree. The T-to-R/selected-port
and seed-to-published-output bridges stay OPEN,
as do original H, complete Call, soundness and required principality.

## 8. Economy audit and one next action

The earlier isolated residual countermodel, row-head/tail partition and P0
selected-root capture did not establish an independent arm source-to-output
route. This method changes the input to a distinct actual source occurrence
and derives original forwarding claims at their construction points. That
registers a useful local proof; it does not turn a changed discriminator or
obligation label into end-to-end proof progress.

The unmet output preservation is A/B. Recovering the ephemeral Call result
Effect and its source parent from later compact aliases is D reconstruction
debt: `tail.rs:615–624` already knows the forwarding endpoints, but uses
Internal origins without a structural parent to the Call demand; the returned
Computation holds the result slot. ExpressionActual at `expr/chain.rs:17–26`
registers Value alone. A source-owner certificate/capture can retain these
existing facts without a new semantic edge. The fresh-claim derivation also
shows why another abstract rule identifying semantic independence with the
Independent enum would be both unnecessary and unsupported.

One next action: primary assign one bounded owner capture or corresponding
source proof of P+'s T-to-R skeleton forwarding and actual selected R return
query, consuming §§4–6's source-to-T derivation, then joining that exact
return image to the outer Call output. The capture
must retain the same source boundary, provider, per-use map, bound parents,
weights and projection formula; stop at the first authentic excluded/missing
body/return route or at the published output. Existing P0 observations are a
control only.
This is a proposed handoff; no capture job was launched or resource permission
extended by this leaf.

## 9. Checks, dependencies, resources, and runtime

Static checks only: immutable `git show`/`git grep`/`git ls-tree` owner reads,
bounded `cat`/`sed`/`rg` note/rule reads, read-only baseline/diff/blob queries,
SHA-256 dependency snapshot, and final leased-document whitespace/local-link
inspection. No Oracle invocation, Cargo/build/test, executable inference
probe, measurement, network request, Git mutation, shared-record edit,
configuration change, specialist contact or child delegation occurred.
Primary remains the sole integration and verification owner. No independent
review is claimed.

The producer used one lightweight shell tool call at a time after the initial
parallel read batches (at most three lightweight shell reads concurrently).
No CPU-intensive job or inference process ran; sample count is zero.
CPU/RAM usage was not instrumented. Wall-time ceiling was 45 minutes;
the lane stopped at the localized T-to-R/selected-port seam within that bound.
Initial large read captures were truncated; decisive sections were reread
narrowly. Two guessed Oracle source filenames were absent, and a Git glob
search returned no match; the actual owners were subsequently located and
read. One document patch failed to match its context and made no change;
the correction was applied in smaller exact patches. These events supply no
proof or acceptance evidence.

Requested runtime: `gpt-6.1-sol` / `high`, leaf-only. `.codex/config.toml`
registers `prover`; `.codex/agents/prover.toml` omits model/effort pins.
Observed runtime model and effort: unknown, because this leaf received no
effective runtime metadata. No Astra launch, override success, hot reload,
or additional job is claimed.

The direct dependency check `git diff --name-only 0ef6b49ef -- <exact
rules/config/governing/input-note paths>` returned no paths. No dependency
was edited by this leaf. Oracle identity is pinned by immutable object reads,
not by the dirty capture worktree's contents. The following critical source
blob IDs additionally freeze the actual constructor/consumer bridge:

| Oracle source at a58eefc31e | Git blob ID |
| --- | --- |
| `crates/infer/src/lowering/expr/block_local.rs` | `a406f4f9b7bc8e7e976014f2b348978e002a1191` |
| `crates/infer/src/lowering/expr/tail.rs` | `8289bfdc6a17b2469ae168ac7939d34813fda474` |
| `crates/infer/src/lowering/control.rs` | `2ae09cdd9abd3f4ce4a39f0091f3f98556de04bd` |
| `crates/infer/src/constraints/machine/bounds.rs` | `365ed25a8b3b7e468a7a4e57159125be53209708` |
| `crates/infer/src/constraints/proof/mod.rs` | `3410858a5bfa0bc0073ab4988b2541738807abf5` |
| `crates/infer/src/compact/collect/mod.rs` | `2e0e8ac841e7240ee3b6b8db23915233f7ab832e` |
| `crates/infer/src/lowering/expr/lambda.rs` | `724b103cda8b4e2c457aacf0a674372fb191e3d6` |

| Yulang3 frozen input | SHA-256 |
| --- | --- |
| `notes/theory/2026-10-12-oracle-effect-hygiene-original-H-proof-attempt.md` | `686d0970affd4c16aa82d87156fdae96ee6a48548a886212059d824e53651a48` |
| `notes/theory/2026-10-11-oracle-global-effect-hygiene-proof.md` | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| `notes/theory/2026-10-12-run-effect-contribution-proof.md` | `6605bbac7dbc26f30edbb67ba356fca528313708be24651a76f828925cc9a138` |
| `notes/theory/2026-10-12-native-negative-residual-constructor-derivation.md` | `d4dff22c2d5f171d8236e9a7e8a9e144ee3e12dc9a1e8642cc9f89f8740eb2d3` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/design/2026-10-10-contextual-residual-lineage-selection.md` | `d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98` |
| `notes/design/2026-10-07-complete-call-contribution-definition.md` | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |

## Commit packet

- Exact leased/change path:
  `notes/theory/2026-10-12-same-family-handler-output-proof.md` only;
  writes stop at handoff.
- Baseline: `0ef6b49ef401df9fa24e94007869d0c03fc80cc2`;
  Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none in the inspected pinned dependency cone;
  Oracle source blob IDs and Yulang3 note/design hashes are recorded above.
- Claim/review status: unreviewed bounded source-to-T constructor derivation,
  actual Direct-root projection derivation, and precise T-to-R/selected-output
  obstruction. No accepted source counterexample, whole-output theorem,
  universal H, complete Call, soundness/principality or production closure.
- Checks already run: immutable owner/activation/claim/evaluator/collector
  reads; baseline and dependency comparison; hashes/blob IDs; final local
  document whitespace and link inspection. Zero builds/tests/Oracle calls.
- Proposed checkpoint message:
  `research: derive same-family arm contribution through Oracle handler result`.
- Shared-record deltas left for primary/curator: record the direct qualified
  operation-reference signature constructor and the actual seed-to-T claim
  tree as producer evidence pending fresh independent review; keep original H
  OPEN and move this bounded route's next evidence to T-to-R recursive body
  activation, actual selected Function/root return and outer Call output.
  `tasks/current.md`, `tasks/research-lab.md`, theory maps and design/index
  records remain primary/curator-owned and were not edited.

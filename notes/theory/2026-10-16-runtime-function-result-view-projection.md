# Function-valued computation results: projection and missing runtime owners

Date: 2026-10-16
Status: independently reviewed bounded source/consumer obstruction.
The original Function-valued receiving gate remains OPEN.
Baseline: `e26437142a0821aeaeeb7e30cacbd87493543ac0`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this new note only; no implementation authority.

Review provenance: independent semantic/source-runtime reviewer
`checked_result_semantics` reports CLEAN at producer SHA-256
`354ddb7d0995cf91716370a27f31c66434f74110297976cdc7659f587417b4d5`.
The primary accepts only the obstruction and exact producer/consumer handoff;
no Function-schema widening or representation design is selected.
Mode M1, one relevant reviewer; static checks only, zero executable checks
and zero benchmark samples/processes. The two source/consumer obligations
are now assigned together to a bounded constructive source-output packet.

## 1. Frozen original obligation

Fix an authentic source program in the assigned LocalSource domain, its
original declarations, lexical scopes, formal/annotation occurrences and
symbolic binders. Fix one compatible source typing and one joint assignment
`xi=(nu,K,D)`. Consider each actual retained entry of an original formal with
explicit outer interface `Computation(E,A)`, where `A` is Function-valued,
including higher-order results and compatible instances at symbolic leaves.
The outer row remains open as selected by annotation policy. An annotation
permission does not assert an effect inflow or a closed upper bound.

For every finite legal execution/reuse history in which that computation
returns the actual callable packet `W`, construct its result view from that
same consumption and actual return. Preserve the full actual latent paths,
inherited profiles, original receiver identities, joint predicates and
dependent incidences, actual contracts and coverage dependencies. Remove the
consumed computation effect position from the *result correspondence*;
preserve any independently sourced incidence of the same boundary witness
already on `W`. Later complete Calls must observe the transported callable
position, with current activity and genuine same-view receipts. Forwarding,
captured suffixes, recapture and repeated template use retain this meaning.

Exclusions: no exhaustive profile inference, prior execution of the provider,
runtime-tag inference of typed paths, fresh marginal witnesses, new source
restrictions, weakened ordinary inference or automatic erasure of an unknown
profile. No new attachment, permission or boundary may be invented by return.
This is an A/B parent obligation; this note neither reclassifies nor closes it.

**Result of this packet:** the source determines a two-input result
correspondence without enumerating the eventual shape of `A`. The pinned
runtime does not construct or consume the corresponding Function packet.
There is a concrete missing *later complete-Call observation consumer* in
addition to the known ground-result rewrite. A result-return patch alone
cannot establish the original conclusion. This is a bounded obstruction,
not a source-qualified behavioral counterexample or a new projection theorem.

## 2. Exact governing sources and reused results

- [Top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
  §§1–4: generate/accumulate constraints naturally, retain unknowns and reuse
  hygiene results. No solve-at-generation or exhaustive search is required.
- [Annotation integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
  §§1–1.2,3: composed polarity, position-local concrete permission, no
  declaration-only inflow, shared variables and existing transport hypotheses.
- [Receiver-relative protection](../design/2026-10-15-callback-identity-forwarding.md),
  “Direct clarification: protection relative to the receiving boundary”:
  original receiver scope controls protection; outward movement does not
  authorize globally deleting retained evidence.
- [Typed computation core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §§2–3,6,9: consuming `Comp(E,A)` returns `A` once; source result/consumer
  skeletons and producer-specific complete `J_call`. Sections 2–3 do assume
  typed-path evidence; the document does not prove arbitrary raw inference.
- [Typed-boundary transport](../design/2026-10-02-typed-boundary-realization-draft.md)
  §6, lines 665–832 at the baseline: two indexed result sources, matching
  result-prefix removal, joint `chi,K,D,L`, same-view receipts and later
  latent observation. Its profile-supply premise is explicitly retained.
- [Primitive receiving](2026-10-16-primitive-computation-root-receiving.md)
  §§1,3–5 and actual matcher §8: four rigid result leaves justify `ground`;
  Function results were explicitly excluded.
- [Receiving construction](2026-10-15-runtime-receiving-view-construction.md)
  §5, lines 291–305: actual returned view and matching result paths must
  survive; a runtime tag cannot supply that map.
- [Returned exposure classification](2026-10-15-callback-result-exposure-classification.md)
  §§3–4: prefix removal with symbolic `alpha`, two inputs of the same return,
  no new seed from ordinary return/bind/Name, private captures stay private.
- [Function construction](2026-10-15-function-callback-profile-construction.md)
  §§1,3: the original explicit annotation coordinates have a forward
  construction/zip; this does not supply all profile applicability, unknown
  symbolic shapes or higher-order result coverage.
- [Raw-template correspondence](2026-10-16-runtime-resume-template-correspondence.md)
  §§10–12: actual local control, original View evidence and fresh execution;
  general Function transport and full-domain visibility remain excluded.

The distinction between reviewed finite/decorated results and unproved raw
source applicability is material here. Neither a historical fixed-shape
adapter model nor a native constraint's satisfiability supplies the missing
current-runtime packet. No live explicit-alpha/raw-Contract lane output was
read or assumed.

## 3. The source map, without discovering future latent paths

At the original source elimination of `Computation(E,A)`, distinguish its
effect position `C.effect` and its result edge `C.result`. For every *actual
typed* path `q` of `A` under the fixed `xi`, source result consumption generates

```text
M_C(C.result.q, q)
M_C(C.effect, _) = absent
```

This rule is generated by the outer computation constructor and the exact
designated elimination, before any particular Function assignment to `A`.
It tests/removes one original result prefix. It does not enumerate suffixes,
turn a symbolic leaf into Function syntax, or select a path by family equality.
Recursive descriptors retain their original graph edge and binder; the rule
does not unfold an infinite signature. For an actual Function path, including
its complete call and further result paths, the same original edge is removed
and the remainder is retained. This is the existing source rule, applied at
the owning elimination, rather than a premise that an arbitrary map is lawful.

That is only one input. Let `V_C` be the executed computation's source view
and `W` the actual returned value view of this same execution. The return rule
also retains `W` through its actual whole-value correspondence `M_W`. With
source tags retained, the required object is

```text
ReturnView(C,W) = M_W* W union_tagged M_C* V_C
```

For direct value return and ordinary binding/read, `M_W` is identity in its
original value coordinates. For an admitted typed adaptation it is that
adaptation's actual map, not identity guessed from pointer equality. The
LocalSource runtime currently registers no such effect-upcast adapter
(`program.rs:365–374`); that bounded erasure fact does not settle general
source conversion.

Both indexed images act on `chi` and `D`; `K` remains the shared ledger under
the same `nu`, and origins/receivers/lineage stay original. Unrelated pending
request, residual and continuation incidences keep their original graph
locations. Restricting a target map does not delete the source evidence graph.
In particular:

1. `C.effect` cannot become `q=call.effect` on the returned callable merely
   because both mention the same family.
2. If `W` independently carries `chi_W(q,b)`, discarding the consumed root's
   image does not remove that incidence, even if its boundary identity is `b`.
3. If a matching callee/result contract independently supplies
   `chi_C(C.result.q,b)`, actual-value identity alone is insufficient; that
   second tagged input must survive as well.
4. Unknown coverage must retain its *indexed dependency*. The source rule
   permits an unresolved result dependency; it does not prove that an
   unknown root dependency contributes to every result path, or to none.

These are consequences of the already reviewed result rule. They do not
establish that current constructors supply both packets or that a later Call
activates their paths. Proving those premises is precisely the assigned
source/runtime bridge; the next sections inspect its real owners.

## 4. Actual source constructors and transports at the baseline

| Owner | Established constructor/consumer fact | Remaining Function obligation |
| --- | --- | --- |
| HIR `source_annotation.rs:69–100` | Retains annotation owner/position, separate outer row, explicit Function argument/result trees, concrete IDs and symbolic references. | The tree is genuine source input, not a complete profile/typed-path derivation for arbitrary instances. The coordinates have not all been discarded. |
| `program.rs:132–141,375–401` | Lambda retains actual formal ID, source site, parameter role, body and optional root schema. Outer effects choose Computation independently of result value. | No result-path/Function packet descriptor is exported to the runtime. `RootCompSchema::from_parameter` at `receiving.rs:22–36` authenticates only Unit/Int/Bool/Str. |
| Lambda evaluation, `machine.rs:483–499,1635–1647` | Constructs the actual closure with its original lexical environment, then `data` constructs `opaque(value)`. | No public Function profile/port is constructed. Captured cell views remain private; scanning or unioning that environment cannot replace the missing public packet. |
| Comp entry, `machine.rs:651–735` | Delays the whole argument, creates a fresh invocation, and binds the inert Comp. `receiving.enter` prepends one original-receiver boundary only when schema exists. | A Function result gets no authenticated local root schema. Extending this predicate alone would reach a result consumer proved only for rigid leaves. |
| Direct formal forwarding, `machine.rs:1171–1181`; `receiving.rs:116–129` | Exact resolved Execute-Name delays retain the original bound view's image and unknown flag. Other argument code remains unknown. | This is the root-only dependency already proved. It exports no separate `C.result` dependency or actual Function path; group/ascription is not silently equated with exact Name by this helper. |
| Name read/force, `machine.rs:1497–1525` | Validates same value/view, creates an actual receipt; an imaged Comp opens one execution and `RootCompReturn` before executing one layer. | The opened view has no path descriptor beyond RootComp. Name/read identity does not construct a missing result packet. |
| Return, `machine.rs:601–605`; `receiving.rs:105–112` | Ends the exact execution triple, replaces the actual return view with `ground(value)`, hence `image=None, unknown=false`. | The source two-input image is absent. The old view remains in the arena, but this result record no longer references it. A closure's prior unknown dependency would be asserted complete-empty by this proposed extension. |
| Value entry, local/root/GlobalRead caches, receiver return and value-arm binder, `machine.rs:625–632,798–839,903–924` | Copy the whole actual returned view handle while changing the source role to Value where required. | These preserve the handle they receive; none repairs the earlier incorrect or absent Function packet. |
| Forward/If/Block, `machine.rs:438–443,512–531,854–895,1528–1563` | Evaluate actual source child/selected branch/final expression; non-discarded returned records pass onward. | Runtime branch choice is not inference of branch types. Both branches' constraints remain required in ordinary inference; these routes do not authenticate profile completeness. |
| Operation result/response, `machine.rs:645–649,739–793,930–939,1268–1290` | Retains declaration-selected result consumption after native return, but payload checks and bound raw responses currently match only four primitives. | Function operation responses are unavailable on these consumers; no full-domain Resume/operation result theorem is inferred. A primitive response can still have a suffix returning a callable. |

The primitive ground theorem applies its latent-empty premise at the final
whole-computation return, independently of intermediate operation response
type. There is no analogous premise for Function. This audit does not exhibit
a currently accepted typed Function schema returning a closure through that
delimiter: the schema guard prevents that source entry. Accordingly the
prospective overwrite is a demonstrated failed repair strategy, not an
executed soundness counterexample in the pinned runtime.

## 5. The additional missing consumer: later complete Call

Even grant a correct returned Function packet provisionally to isolate the
consumer. Its next source Name read records a genuine receipt and preserves
the view. The real `Frame::Callee` branch at `machine.rs:651–797` then looks up
`self.executables[received.value]` or the operation's value tag. It neither
calls `receiving.execution(received.view, ...)` nor retains that view in a
complete callable execution delimiter. Closure invocation retains body and
environment; the invocation descriptor retains Call/provider source sites.
Those are actual control/provenance facts, not the missing executing port.

The complete runtime execution-entry census has exactly two relevant owners:
Name's Comp path at `1515–1521`, and saved RootComp View entry at `1153–1159`.
Fresh event construction at `1566–1589` calls `observe` only on that current
`executing_views` list. `ExecutionView` and `Observation` have no typed-port
field (`receiving.rs:48–58`). Thus an event produced by calling the returned
function has no newly opened observation of that callable's own full
`J_call` position. Any ambient Comp observation is a different source view;
equal receiver, family or underlying closure cannot substitute for it.

This is a concrete missing source/operational edge, independent of how an
event's final eligibility is decided. The actual selector at
`machine.rs:1254–1266` uses only closed-primitive nonprotection or positive
RootComp `local_grant`. That query follows one unpositioned image chain and
checks the boundary's *outer* annotation row (`receiving.rs:258–265,305–320`).
It does not interpret a returned Function's independently placed contract.
The current unknown flag is never promoted to a negative certificate. No
later query can recover an observation which this Call never constructed.

The source owner is already precise: typed-core §§3,9 makes `J_call` cover
actual entry, forced argument, body and designated producer result consumer.
For operation callables, ending at native ReceiverReturn is too early because
`OperationResultConsumer` is outside it. For closures, observing only body
code omits Value entry force. Merely activating a Function view somewhere
inside the callee would therefore not establish complete Call meaning.

## 6. Capture, reuse, constraints and the retained first premise

Current capture stores `RootCompReturn.execution` as `TemplateNode::View`
(`machine.rs:1016–1019`; `continuation.rs:40–43`). Re-entry authenticates the
original view/receipt and creates a fresh execution; it does not use the
executable-owner remap to rewrite boundary identities (`1153–1159`). Unwind
ends exactly that execution and saves it (`1359–1362`). These are the already
reviewed primitive control facts. There is no result projection descriptor
on either the frame or saved View node. Reusing the current node repeats
the same ground completion, not the source Function result map. A required
future Call view would also need its full result recipe and port to survive
this same capture/re-entry seam; fresh control owner does not create Receive.

Native constraints were checked separately from runtime shape. At this
baseline, `shadow_apply.rs:1553–1625` constructs the actual source Call's
negative Function demand, with distinct invocation-effect and result-value
endpoints. `lib.rs:12643–12672` creates separate AE/RE/Argument/Result children;
the Result child is the actual covariant value inequality.
`candidate_context.rs:3020–3063` preserves the parent's post-check context
and original source references and records a FunctionPort dependency; clearing
one scoped demand at Result is not evidence of deleting all inherited data.
`candidate_call.rs:267–359` retains the authentic source/native join and
`375–395` still reports complete-result/future-interface suppliers.

These are real native mechanisms, not proof that the runtime receives their
source interpretation. `RuntimeProgram::from_hir(hir, RuntimeEvidence)`
accepts no native constraint graph, joint assignment, typed result packet or
Function-path certificate. `RuntimeEvidence` has only the Name-consumption
map (`program.rs:54–57`); the program retains HIR. Neither native constraint
storage nor historical exact-interface simulation therefore supplies the
absent runtime export. This audit does not assert native information loss,
absence of source witnesses in its evidence graph, incomplete replay, or
soundness failure of native inference. Those require their owning proofs.

**Precise first missing bridge:** original Function-valued computation
elimination/return construction must deliver the actual returned packet and
the same execution's result-indexed dependency/contract packet to the runtime,
with authentic original path and receiver references. Current source syntax
and native constraints retain useful original operands, but their API does
not establish that delivery. The next missing consumer is the complete-Call
view just identified. Neither is discharged by the existing conditional
transport theorem. No universal profile reconstruction is necessary merely
to describe this edge.

## 7. Construction handoff and obligation economy

Proposed retained output, for independent design/proof review only:

```text
ResultProjection(original elimination, original result edge,
                 indexed computation packet/dependency)
ReturnPacket(actual returned view, ResultProjection)
```

This names the canonical source result edge and both source inputs. It is
not a new ledger, snapshot, profile inferred from support, or a requirement
to enumerate every future shape. An unknown source dependency remains
unresolved through that exact edge. The actual returned view supplies its
independent lineage. Existing source annotations and native result relations
must be joined at their authentic construction, before this output can be
treated as established evidence. Retention format and implementation authority
belong to the primary's existing review/approval path.

The owning runtime handoff is consequently:

1. Construct/export that source result edge and the actual Function view;
   authenticate annotation/instance/binder associations under one `xi`.
2. Complete the consumed Comp using the two inputs; retain unknown coverage
   and original receiver IDs. The projection targets matching latent paths,
   and preserves old request/residual/continuation evidence separately.
3. At a later Call, open the source-selected complete callable port over the
   entire producer-specific invocation, and project its result on completion.
   Preserve its port and result recipe in crossed template View nodes without
   making another boundary or receipt during restoration.
4. Let actual same-view receipts, fresh event observations, matching contract
   positions and *current* activity discharge eligibility. Extending the
   current RootComp-only `local_grant` by outer-row membership is insufficient.

The existing scalar-return and direct-Name proofs leave this producer/consumer
bridge untouched; another given-a-valid-map preservation proof would leave it
untouched again. The economy audit classifies the required Function execution
as A/B. Missing export of the canonical source result edge is D with an A/B
consequence; the full profile-applicability premise remains genuinely semantic
where its source construction is unproved. Retain known construction evidence
where available; do not assert every missing profile was previously known.
No gate is weakened, retired or promoted by this classification.

One next action: primary assigns the original source elimination/return owner
a bounded construction/export packet for the two inputs above, with a later
complete-Call observation consumer included in its acceptance contract. Review
this frozen obstruction before authorizing Function schema widening. Do not
spend another packet proving only result-prefix image algebra.

## 8. Pins, checks, resources and commit packet

All source reads used `git show e26437142:<path>`; concurrent live outputs
were excluded. Exact direct SHA-256 pins:

| Path | SHA-256 |
| --- | --- |
| runtime/program.rs | `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748` |
| runtime/receiving.rs | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| runtime/machine.rs | `04024174d88223e252e1d093eaee96c17d9f43d4d32bea5c41631017c9da208c` |
| runtime/continuation.rs | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| primitive receiving theorem | `a043c69eb9fd82127bb7ad59d797abf3f10c5edf83bd80316183074f48c28606` |
| receiving construction theorem | `ae05faea870634f7cd8cceac9515537d59427c08ae74940c7da70b1f89f45e8b` |
| raw-template correspondence | `f3a4c925a197e63e5b7faf1ce1e1caf5736d76f1b86ba162c6acc85bfff8e7dd` |
| typed computation core | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| typed-boundary transport | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| Function profile construction | `e4dbbf9cb4e15f460279647c5f4f1b8f8513dce01ea6a0d4a0a08e24f81a54cc` |
| returned exposure classification | `6f2bc05137e451c38391655bb2d45e9224f12eebf7d58c7f5a78c8abd69c93f4` |
| annotation integration | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| receiver-relative protection | `c544ed3c7b83686a740aa43b1db92d901de31a3b197f81f90a4c9dbdae561134` |
| HIR module/source_annotation.rs | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| solver/candidate_call.rs | `cbad9cf51a05343eb7a29ab77aac520891467a8aa4edc3201ea3d91f978984a1` |
| solver/shadow_apply.rs | `357b274d0de509931bda3015a99b1a1cf2ac86d75a45d230d62ab456c56740ba` |
| solver/candidate_context.rs | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` |
| solver/lib.rs | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` |

Abbreviated runtime/solver paths are under
`tools/inference-playground/src/` and `crates/yu-solver/src/` respectively.
The main theory and design pins name the linked documents above. SHA checks
reproduced the primary's four runtime and two supplied theory pins exactly.
No dependency was edited; final comparison against a moving current HEAD is
primary-owned. Native line numbers were re-resolved at this baseline instead
of copied from the earlier Call-result audit.

Method/checks: bounded source reads, owner/constructor searches, baseline
resolution and SHA-256 calculation; final note whitespace, fence and local-link
checks. No builds, tests, executable probes, network, measurements, Git
mutations or children. At most five lightweight read-only shell commands in
a batch, zero heavy processes. Assigned wall bound: 25 minutes; CPU/RAM were
not instrumented. One primary verification owner remains unchanged. Requested
routing: normal Sol/high leaf. Observed model/effort metadata: unavailable,
therefore unknown; no Astra assignment or claimed override.

Unverified: arbitrary raw-source typing/profile applicability, complete native
Call/result interpretation, general negative visibility, Function payload/raw
response consumers, general adapters/imports, all-source materialization,
full-domain reuse, soundness, principality and production/F5 cutover. No
independent review or theorem certification is claimed.

Commit packet:

- Exact leased path: `notes/theory/2026-10-16-runtime-function-result-view-projection.md`.
- Baseline: `e26437142a0821aeaeeb7e30cacbd87493543ac0`; changed dependency
  hashes: none, all reads pinned to that commit. The primary revalidates any
  differing current dependencies before integration.
- Original producer review status: unreviewed bounded source/consumer
  obstruction when frozen; subsequent independent review is recorded above.
  Original Function-valued receiving parent remains OPEN.
- Checks already run: static owner census, pinned input hashes and note
  integrity checks; no executable validation.
- Suggested checkpoint: `research: locate Function result projection and complete-call owners`.
- Shared-record deltas left to primary/curator: record both missing source
  packet export and later complete-Call observation consumer, preserve the
  original Function gate and global parents OPEN, and avoid treating a
  `RootCompReturn` rewrite or matcher extension as sufficient closure.

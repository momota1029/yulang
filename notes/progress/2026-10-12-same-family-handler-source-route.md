# Same-family handler-body event: source route and publication premise

Date: 2026-10-12
Status: frozen research checkpoint; independent review pending
Claim class: bounded static constructor derivation and localized publication premise
Y3 baseline: `0ef6b49ef401df9fa24e94007869d0c03fc80cc2`, branch `research/simple-sub-intrusion`
Oracle source: immutable `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this file; leaf, no delegation

## Objective and unchanged H

This complementary source lane tests the independent same-family clause of
original H in [original proof attempt](../theory/2026-10-12-oracle-effect-hygiene-original-H-proof-attempt.md)
§1 and [global hygiene](../theory/2026-10-11-oracle-global-effect-hygiene-proof.md)
§1. Their original universal source domain, occurrences, scopes, binders,
actual uses, complete Call routes, symbolic tails and future lowers remain
unchanged. This note neither closes H nor supplies a source-qualified
counterexample. A constructor route is distinguished from successful solving,
an admitted independent projection carrier, and a published scheme/output.

Governing sections: annotation hygiene §§1–4; contextual attachment/admission
§§3–6; selected residual lineage; complete Call §§2–5; top-level inference
principles §§1–5. The retracted callback result is excluded. No new language
meaning, residual coalescing policy, output restriction or implementation is
selected. The prover owns the complementary constructive theorem lane.

All Oracle excerpts below are from `git show a58eefc31...:<path>` in
`/home/momota1029/rust/yulang2-oracle-capture`. Its live instrumented source
was not used. Unless a path includes another crate prefix, `annotation/...`,
`analysis/...`, `compact/...`, `constraints/...`, `generalize/...`, and
`lowering/...` are relative to `crates/infer/src/`; unprefixed module files and
`expr/...` or `body/...` shorthand in the lowering sections are relative to
`crates/infer/src/lowering/` (for example, `tail.rs` means
`lowering/expr/tail.rs`). Parser paths are relative to `crates/parser/src/`.
Direct Y3 inputs matched the supplied baseline byte hashes.

## Minimal candidate and exact occurrence

Take the accepted int fixture `/tmp/yulang2-run-projection.yu`, SHA-256
`73b4a2d12233b9b658188f3baa17edb04c14a89f94217198befca22db4af77d9`,
and replace only the matching arm's expression with this indented block:

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

The new occurrence is the first expression inside the effect arm body,
`ev::send (s, n)`. It is distinct from the arm's operation pattern, operation
declaration and terminal `ev::send (1,42)`. This candidate exists only in
this note: no fixture was edited, parsed or executed. No physical byte range,
ExprId, DefId, bound record or final scheme is observed for the candidate.
The earlier authenticated terminal Expr14/Expr15 and its 107-byte suffix
mapping cannot be transferred to this changed body.

There is static syntax support: `parser/src/expr/control.rs:917–926` parses
an arm body with `parse_inline_or_indent`; `lowering/control/syntax.rs:91–100`
selects its Expr/IndentBlock/BraceGroup. `expr/block_local.rs:72–89,129–141`
lowers consecutive expressions into a statement and tail. This is a
constructor-supported candidate, conditional on ordinary successful parsing,
name resolution and lowering; successful inference is not assumed. No
source-domain barrier was found at these owners.

## Emitted event and handler separation

Oracle paths in this and subsequent sections have prefix `crates/infer/src/`.
Use fresh symbolic coordinate names, not guessed numeric IDs:

| Coordinate | Owner |
| --- | --- |
| `u`, `v`, `s_a` | action annotation inner Effect, public Effect, fresh set-wide subtraction ID |
| `K_i`, `I` | new send invocation-return Effect and application Effect |
| `T`, `B` | `run (k ())` Effect and arm block Effect |
| `R`, `D` | catch result Effect and defined-body/skeleton Effect |
| `F`, `O` | actual exported Function return port and terminal outer Call Effect |

The qualified body expression resolves through
`name_ref.rs:7–37::lower_path_name_at`, using the actual
`modules.value_path_at(module,path,site)`. For a resolved operation target,
`expr/block_local.rs:990–1092` both queues ApplyRefResolution and directly
constrains its fresh use Value from that target's actual operation declaration.
It records the operation by target DefId in `poly.effect_operations`.
`body/signature_helpers.rs:217–260` inserts the resolved owner effect into
the operation's return row. `lowering/mod.rs:571–615` and
`signature_effect.rs:78–107` produce a Function with a positive concrete
`Row([Con(ev,[])])` return Effect for this nullary effect family. This route
does not require guessing which generalized `send` scheme was instantiated.
The operation-ref owner nevertheless has early-return/error branches; actual
activation is not a runtime fact here.

`expr/tail.rs:535–627` constructs the actual four-port application demand:

```text
send_use_value <: Fun(payload.Value, payload.Effect, K_i, result.Value)
send_reference.Effect <: I
K_i <: I
```

When that direct positive operation Function meets the demand, the return
Effect comparison in `constraints/machine/propagate.rs:210–263` supplies
`Row([ev]) <: K_i`. It preserves that comparison's actual incoming weights.
This yields the conditional generated/replayed route into `I`; generation
alone does not assert completed worklist activation or publication.

Block and handler owners emit, without an annotation wrapper at these seams:

```text
I <: B,  T <: B                         block_local.rs:1284–1308
B <: R                                 control.rs:1167–1175
R <: D                                 lambda.rs:791–807, when skeleton used
```

`lower_catch_with_scrutinee` constructs the handled row from the **scrutinee**
Effect, not from `B` or `R` (`control.rs:922–1021`). Its complete-handler
branch uses `R` as row tail; its incomplete branch instead forwards the public
scrutinee Effect to `R`. Thus the body event has a direct positive result route
separate from `v <: Row(handled,R)` and `Stack(u,push(s_a,ev)) <: Row(handled,R)`.
It need not survive via the residual gamma of the latter constraint.
Head matching at `propagate.rs:1007–1042` consumes matching scrutinee heads
without forwarding them to the tail; that fact does not delete the separately
generated `I <: B <: R` route. Conversely, an input-head match is not a proof
that `I` has a published output image.

The distinction retained here is source occurrence plus actual constructor
endpoints and demand/structural derivation parents. The new nominal `ev`
emission itself is not allocated an annotation SubtractId. Equal resolved
families therefore do not identify it with the action stack. The effect
forwarding and block joins use internal origins, however; their original
source-to-record correlation is not fully exported. This is structural
separation, not a complete semantic attachment certificate.

## Output predicate: the action stack is not an output POP premise

`annotation/constraints.rs:257–282` handles the parameter computation
`action: [ev] 'a` by returning `subtracts: value.subtracts` separately from
`effect_stack`. `AnnType::Var('a)` returns an empty output-subtract list
(`:317–324`). The effect stack's ID and PUSH remain in the parameter Effect
and local action view (`:548–593`); they are not automatically returned as
this parameter's output subtraction.

Independently, `lambda.rs:1580–1634::lambda_annotation_predicate_constraints`
removes any returned weight whose IDs consist entirely of this effect stack's
IDs. `lambda_parameter_output_predicate_constraints` at 1571–1579 retains
the resulting predicate for this Effectful annotation. Hence this source
does not justify putting `pop(s_a)` around the whole catch result.

The actual defined output predicate is
`dedupe(annotation ++ frame.subtracts ++ frame.latent_subtracts)`
(`tail.rs:1059–1073`). Its possible body additions have explicit owners:

- `k` is bound with `LocalCallReturnEffect::Annotated`
  (`control.rs:1562–1587`), so its application bypasses the fresh unannotated
  call-stack branch (`tail.rs:740–799`).
- Qualified send and the top-level recursive `run` reference have no local
  parameter call predicate; the current local binders are action, payload,
  continuation and value-arm binders. `local_callee_call_projection` requires
  an actual resolved local record (`tail.rs:691–707`). It cannot use a guessed
  `run=DefId(2)` mapping. Global name resolution is queued separately.
- The plain result annotation `'a` connects Value and returns no effect
  subtraction (`expr/method_body.rs:1715–1753` plus the Var case above).
  The displayed arm adds no ascription, local annotated binding or guard.

On these constructor branches the predicate is empty. The final wrapper
(`lambda.rs:948–974`, `tail.rs:1084–1116`) therefore emits `F = Pos::Var(D)`
(or the actual body Effect if no skeleton), rather than `NonSubtract(D,pop(s_a))`.
This equality concerns the constructed positive Function port, not its selected
compact image. If another actual frame predicate exists, the owner instead
folds `NonSubtract` wrappers around both Value and Effect; the exact frame
must be retained rather than assumed empty from the old final scheme.

Even that general wrapper is not a family-name deletion operation at the
inspected constructor: `expr/constraints.rs:137–144` builds `Pos::NonSubtract`;
`propagate.rs:26–36` prefixes its weight; `compact/collect/type_nodes.rs:265–279`
preserves a supplied positive concrete head while transporting its arguments.
This local fact does not prove unrestricted weighted replay, claim selection,
or every independent event's survival. The present candidate does not exercise
an output POP of the action ID at all, so it cannot by itself establish the
harder independent-survivor claim for such a POP.

## Exact consumer equations and first unestablished premise

The actual module root is generalized by `analysis/session/instantiate.rs:14–82`.
For its accepted generalization iteration, let `Q_M(z)` be the successful
selected-lower query from that fixed machine/proof view. Its collector equation
is directly from `compact/collect/mod.rs:848–927`:

```text
C_M(z,w) = merge_pos { compact_pos_bound_id(b.pos, left(b.weights) union w)
                      | b in Q_M(z) }
CompactFun(f).ret_eff = compact_pos_effect_id(f.ret_eff, incoming_weight)
```

The second equation is `compact/collect/type_nodes.rs:14–28,196–234`.
Variables recurse through selected collection; Union/Row children follow their
actual constructors. It is not an equation identifying `F` with some previously
selected return variable of the unchanged fixture.

The **earliest remaining publication premise** is the candidate's joint
source-to-bound-to-selected-Function map: show which actual records from
`Row([ev]) <: K_i <: I <: B <: R <: D` are admitted at the relevant epoch,
their correlated structural/replay/row parents, the encountered Function port,
and whether its successful `Q_M` contains that route or an exact replacement.
Owner: bound/carrier/claim construction and scoped scheme projection, followed
by the actual `run` generalization owner. This map has not been supplied for
the changed source. The old selected `run` scheme and terminal capture are
facts about a different program and cannot discharge it.

Specifically, `bounds.rs:2689–2717::projection_carrier_is_independent` tests
claim-producer and qualified-parent indexes. That operational classification
is not H's semantic independence predicate. `row_effect.rs:490–570` constructs
live reduction claims; `constraints/proof/mod.rs:11879–11918` can exclude a
claimed root with nonempty live coverage while including an Independent support.
The compact collector consumes selected bound clones, discarding their
projection evidence at this seam. The independent event's distinct constructor
route does not already prove this accounting equation.

After that premise, required equations are:

1. The actual generalization simplifications, substitutions and ancestors
   preserve a representation of that selected event in `fun.ret_eff`.
   `generalize/simplification.rs:99–120` can omit None-target variables and
   merge occurrences; it supplies no injective event map by itself.
2. `generalize/finalize.rs:3–28` freezes that same generalized root, and
   `compact/finalize.rs:415–426,542–549` installs its actual positive return
   Effect in the actual `Def::Let.scheme` through session instantiation §above.
3. The terminal actual lexical `run` use resolves to that definition. A
   quantified target receives InstantiateUse; an internal open target receives
   OpenUse (`scc.rs:266–288`, `analysis/session/selection.rs:1048–1117`).
   These branches may not be selected by guessing a DefId or execution order.
4. For InstantiateUse, `instantiate.rs:625–640,798–808,850–901` clones ports,
   shared variables and subtraction IDs with one per-use map. Session
   `instantiate.rs:345–525` installs the actual cloned predicate at that use
   Value. For OpenUse, the actual target-root-to-use relation must be used.
5. The actual outer demand compares that provider's return Effect to its fresh
   Call-return Effect `K_o`, and `K_o <: O` joins callee evaluation into the
   source application's actual result (`tail.rs:535–627`). Show the same event
   image at this designated completed observation, retaining future interface
   and provider identity required by complete Call. Four-port emission alone
   does not discharge the whole-operation contract.

The root witness sidecar explicitly omits root return/effect witnesses
(`generalize/provenance.rs:309–338`). Missing sidecar output is not evidence
of absence or failure. No conditional equation above assumes publication or
the event's final membership as an input.

## Checks, scope and resources

Method: static source construction/falsification, independent of the prover's
algebraic derivation. Both share the original H and immutable Oracle source;
this is not an independent semantic oracle or independent review. No finite
model, enumeration, seeds/ranges, mutation execution, runtime comparison,
Oracle invocation, build or test occurred. The single conceptual mutation is
the displayed handler-body send. Its successful lowering/inference, exact
resolved targets, completed carriers, selection, final scheme and future uses
are unverified. Universal H, complete Call, soundness, principality and Y3
cutover remain OPEN.

Commands: exact revision `git show ...:<path>` with bounded `sed`/`rg` excerpts;
read-only revision `git grep` for owner location; `cat`/`sed` governing-note
reads; `sha256sum` comparison of the ten Y3 inputs below against `0ef6b49ef`,
and immutable Oracle dependency hashing. No Git mutation, shared-record write,
source edit, delegation or interactive question. Initial combined output was
truncated and two guessed source paths were absent; decisive owners were then
read directly. No conclusion rests on incomplete search output. These are
document/source checks, not implementation tests.

Budget: less than the assigned 30-minute static-work limit; only lightweight
shell reads and the leased note write. CPU/RSS and exact wall time unmeasured.
No heavy process or execution budget consumed. Requested Sol/low; actual model
and effort metadata unavailable, so observed settings are unknown.

One recommended next action: hand the prover this constructor-supported
positive body route and its empty action-output predicate, then assign the
actual changed-source carrier/claim-to-export equation to the projection owner.
Do not spend the exhausted runtime budget or repeat the unchanged terminal
capture; the direct constructor route still needs its actual publication map.

## Dependency snapshot and commit packet

Y3 direct dependency SHA-256 values (baseline and live bytes equal at read):

| Path under `notes/` | SHA-256 |
| --- | --- |
| `design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `design/2026-10-10-contextual-residual-lineage-selection.md` | `d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98` |
| `design/2026-10-07-complete-call-contribution-definition.md` | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` |
| `design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `theory/2026-10-12-oracle-effect-hygiene-original-H-proof-attempt.md` | `686d0970affd4c16aa82d87156fdae96ee6a48548a886212059d824e53651a48` |
| `theory/2026-10-11-oracle-global-effect-hygiene-proof.md` | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| `theory/2026-10-12-run-effect-contribution-proof.md` | `6605bbac7dbc26f30edbb67ba356fca528313708be24651a76f828925cc9a138` |
| `theory/2026-10-12-native-negative-residual-constructor-derivation.md` | `d4dff22c2d5f171d8236e9a7e8a9e144ee3e12dc9a1e8642cc9f89f8740eb2d3` |
| `progress/2026-10-12-run-origin-lineage-capture.md` | `ea29c4ec3512e22d6e0e2340a06cbc2edeb68a2782894c492935b6a8019c8553` |

Newly pinpointed immutable Oracle owner `expr/block_local.rs` has SHA-256
`661386fe559d8e207a9597962cfee3c11f05f21aa2888e22b2c0143825051898`;
`constraints/machine/bounds.rs` has
`c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7`.
Other inspected owners are fixed by the Oracle revision; previously recorded
hashes were consistent for the fourteen source owners explicitly hashed here.
No dependency was edited.

Commit packet:

- Exact leased/changed path: `notes/progress/2026-10-12-same-family-handler-source-route.md`.
- Baseline: Y3 `0ef6b49ef401df9fa24e94007869d0c03fc80cc2`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; new artifact only. Input fixture unchanged.
- Review status: frozen, unreviewed research characterization; no self-review
  or theorem/production promotion.
- Checks already run: static owners, revision/input hash comparisons and
  scoped document integrity; zero executions/builds/tests.
- Proposed checkpoint message: `research: trace independent handler send to run publication premise`.
- Shared-record deltas left for primary/curator: preserve original H and
  complete Call OPEN; record the independent positive handler-body route,
  absence of an action-ID output POP premise, and remaining actual
  carrier/claim-to-export map. No task/index/authority/question file changed.

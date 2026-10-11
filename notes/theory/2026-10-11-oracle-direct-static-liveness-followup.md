# Oracle direct callback: native lower transport and incomplete replay evidence

Date: 2026-10-11
Status: frozen producer result; independent review pending; original H OPEN
Claim class: source-derived local transport and consumer lemmas, with an unresolved actual projection premise
Y3 baseline supplied by primary: `39968b554f3d4a71cece82e61188235a8559d706`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle read root: `/tmp/yulang2-oracle-read`
Exclusive output: this file only; leaf, no delegation

## 1. Fixed statement and method

This follow-up derives native bound accumulation for the frozen candidate,
rather than repeating the prior projection/selector owner map:

```yulang
pub act tick:
    pub ping: () -> ()
my direct(cb: (() -> [tick] ())) = cb
my provider() = tick::ping()
my observed_direct() = (direct provider) ()
```

Keep the original annotation occurrence a, lexical scope sigma, cb binder b,
constructor SubtractId s, actual direct scheme use u and returned-callback call
k jointly fixed as in the [previous direct note](2026-10-11-oracle-direct-liveness-proof.md).
They are actual source objects, not independently chosen witnesses. The leaf
target is whether s reaches a returned-callback lower, contributes through
actual projection/compact preparation, and belongs to the installed scheme's
actual selected ID set on this route.

The original H remains exactly the statement in
[global hygiene proof](2026-10-11-oracle-global-effect-hygiene-proof.md) §1:

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

Nested Function argument/result polarity, authentic errors and safe
nonpublication for incorrect lowers, Complete Call, soundness and required
principality retain their original scopes. Successfully lowered source is not
necessarily a completed inference/publication. One exact source-qualified
violation could refute H; this source cannot prove universal H. No assumption
supplies actual compact liveness, provider replay, complete evidence, numeric
identity from printed `#0`, or a chosen selector branch.

Authority: annotation-effect-hygiene-integration §§1–2, top-level inference
principles §§1–5, and compiler-engineering proof-obligation economy. The
accepted decisions prohibit rollback/retry type search and weakening ordinary
inference to ease proof. Static reads only; no Oracle execution or instrumentation.

## 2. The returned coordinate is an actual constructor output

Oracle citations below are relative to its read root, under `crates/infer/src/`.
Use C for the formal cb value variable, A for the annotation's positive Function
PosId containing the original PUSH(s, Set(tick)) return-effect view and paired
NonSubtract return-value view, Y for the named lambda skeleton's body_value,
and O for that layer's output_value. These denote source allocation outputs.

`lowering/body/mod.rs:2270–2380` lowers this named definition through
`lower_binding_body_with_args_to_named_self`.
`lowering/expr/mod.rs:300–340` supplies an actual internal self root to the
method-body lowering. `expr/method_body.rs:55–85` and
`expr/lambda.rs:244–273,644–776` take the defined, nonempty-parameter route.
The annotation connection constructs A and emits A <: C; this is the exact
constructor established by the frozen source note, not a newly inferred shape.

The named skeleton allocates Y and O in `lambda.rs:1128–1175`. Its Function
lower uses O as positive result and C as negative argument.
`lowering/local.rs:133–144` recognizes the Annotated return-effect mode as
connecting an empty predicate. Accordingly `lambda.rs:1181–1229` emits
Y <: O and O <: Y before the body. The reference cb resolves to C
(`lowering/name_ref.rs:149–176`; `expr/tail.rs:855–858`). Actual body lowering
then emits C <: Y (`lambda.rs:790–810`) and wraps a Function with positive
return Y (`946–974`). Thus Y is the actual returned-callback coordinate.

The formal's stored call predicate is populated, as established in both frozen
source audits. The bare Function's enclosing immediate output predicate is
empty, and no local cb application consumes the stored predicate. The later
App callee cannot recover b through the local-Var predicate read. This does
not eliminate the ID-bearing type graph just traced. No repair to the frozen
source-constructor note is required for this distinction.

## 3. The same A and s reach the native returned lower

The following is a local transport lemma for terminal-free completion of the
named native operations. It does not assume successful final projection.

**Retention at insertion.** The Function-to-Var branch
`constraints/machine/propagate.rs:150–158` calls `add_lower_bound(C,A,...)`.
`machine/bounds.rs:4523–4533` returns the same PosId from `extrude_pos`;
`4547–4620,4698–4725` lowers levels and traverses Function/stack/NonSubtract
payloads without replacing their ID entries. It neither freshens s nor removes
the annotation's PUSH. For the empty comparison weight, filter erasure
(`3174–3190`) leaves an empty weight. Alias-cycle subsumption (`4274–4295`)
requires a Pos::Var and cannot subsume this Pos::Fun A. Native insertion
(`630–711`; `constraints/mod.rs:2420–2443,2511–2606`) therefore stores A on C,
or returns the already stored exact lower. Call this r_A.

**Actual replay activation.** The emitted C <: Y follows the Var/Var branch
`propagate.rs:103–128`, creating an upper U=(C, NegVar(Y)) as well as the
opposite lower alias. Y is freshly allocated by the named skeleton; the earlier
Y/O connections do not mention C. The exact NegVar endpoint rule
(`bounds.rs:4234–4271`) therefore does not eliminate this first C/Y upper as
an earlier unrelated upper. `add_upper_bound:817–924` registers the upper
replay claim and then iterates projection lower records, including r_A.
This uses the real bound replay plan, not merely a stored comparison.

Let q be U's original Direct upper replay claim, admitted by
`register_constraint_upper_replay_claims:962–1028` and
`constraints/proof/mod.rs:7118–7140,7192–7245`. The source constraint C <: Y
has no replay-qualified parents at its initial admission; q's coverage root is
q. The source A <: C producer has no upper replay claim from its Function lhs.

**No row coverage for q at these production owners.** Live coverage insertion
is at `constraints/row_effect.rs:523`; its production caller
`register_unweighted_row_reduction` uses a row-reduction producer
(`490–535`). The production reduction route requires PosVar/NegRow and actual
row items (`88–135,238–335`; `propagate.rs:131`). U has immutable NegVar(Y),
so it cannot be that row-reduction producer. The production coverage wrapper
at `constraints/mod.rs:1572–1624` commits that state at
`proof/mod.rs:13050–13121`; the alternative direct `record_live_coverage`
helper at `13126` is test-used in the inspected call census. A descendant
claim inheriting q's coverage root does not turn U into a row-reduction
producer. This establishes that the initial alias q is uncovered under these
production coverage owners; it is not a theorem about every claim in the
program.

Replay composition therefore requires the generic pair
(`proof/mod.rs:9416–9529`). `bounds.rs:3565–3735` composes r_A with U into
A <: Y. It is nontrivial; the evidence-only Var/Var case (`3814–3830`) does
not apply to A. The action is actually consumed by
`apply_cpk_bound_replay_actions:3832–3890`. If this comparison already exists,
its semantic lower is already present; on first admission it is queued and
the Function-to-Var operation inserts the same A into Y. Extrusion retains
the same s again. Call this returned lower r_Y.

Thus the constructor/replay route supplies a native s-bearing returned lower
under terminal-free completion. This is stronger than the previous note's
mere C/Y reachability. It still does not establish the scheme-mode inclusion
of r_Y after all subsequent ledger updates or the survival of its weighted
effect tail through compact cleanup.

## 4. The first unresolved actual-state branch

For a newly admitted replay constraint, `machine/entry.rs:1208–1265` branches
on `replay_derivation_budget_allows(size_of::<BinaryReplayDerivation>(),1)`.
The session byte proxy uses checked addition and the incoming-edge bound
(`1308–1347`). Defaults are 64 MiB and 4096 edges per record
(`constraints/mod.rs:3265–3287`); a default constant does not prove the exact
prefix's byte proxy. The inspected non-test owners do not set a smaller budget.

If evidence is retained, `bounds.rs:3839–3847,2916–3004` installs q's qualified
replay parent. Lower admission `2332–2374` derives the corresponding support
ledger and replay clause. The intended first clause is the native conjunction
of r_A and U, with q uncovered. Its availability depends on those admission
transactions actually completing; the note does not replace that with a
printed-ID inference.

If evidence is rejected, the exact replay record is marked Incomplete and has
no retained replay derivation, but its semantic work is still queued
(`entry.rs:1222–1265`). `apply_cpk_bound_replay_actions` skips qualified parent
registration for this disposition. At the first lower admission, if this is a
fresh record with no other qualified parent, `register_lower_projection_delta`
returns without creating a ledger when both claims and the existing ledger
are empty (`bounds.rs:2493–2495`). Then r_Y is initially Unclaimed. Later
deduplicated replays or carrier admissions can bootstrap an existing record
(`2360–2420,2949–3024`), so initial Unclaimed is not proof of final Unclaimed.

The first unresolved branch of this bounded derivation is the exact replay
admission prefix: which canonical result record exists, its retained
derivations/qualified parents, and whether the byte-proxy check admits this
edge. The first premise needed for the leaf conclusion is the resulting
r_Y support/formula state **at actual scheme collection**, after those later
updates. No frozen input supplies either state. Deriving it statically requires
the actual prefix/ledger census; the local constructor chain alone cannot
determine it. This is a missing owner fact, not permission to assume failure
or the retained-evidence branch.

## 5. Incomplete evidence is not the terminal resource-failure signal

The primary requested the decisive consumer distinction. It is established
from production control flow:

1. `record_replay_budget_drop` (`entry.rs:1335–1355`) changes provenance
   completeness and its epoch. It does not set `proof_terminal_failure`.
   The rejected evidence branch queues semantic work as shown above.
2. With neither support nor formula, `project_lower_inner`
   (`proof/mod.rs:10015–10031`) returns `Ok(Unclaimed)`, not a ProofFailure.
   `scheme_projectable_lowers_in_round`
   (`constraints/mod.rs:1498–1548`) includes Unclaimed and Included bounds;
   it omits Excluded and latches actual projection errors. Scheme collection
   receives these returned bounds (`compact/collect/mod.rs:848–887`).
3. `generalize/provenance.rs:23–78` deliberately reports whole-scheme witness
   completeness Incomplete even after a successful capture; errors separately
   pass through the terminal-latching query gateway. Witness completeness
   therefore cannot itself serve as an acceptance gate.
4. `analysis/session/instantiate.rs:54–83` finalizes and calls `set_def_scheme`
   regardless of witness_completeness. `analysis/session/lifecycle.rs:4–22`
   records it; `analysis/session/generalize.rs:958–965` installs the Scheme.
   `generalize/finalize.rs:3–26` freezes a Scheme with no completeness field.
5. Loaded-file publication reads the separate terminal latch
   (`lowering/body/mod.rs:669–685,790–797`).
   `run_proof_compilation_attempt` discards output and returns
   `ProofKernelFailed` only when that latch is Some. Without it, this wrapper
   returns the output. A scoped production read census found no acceptance
   consumer of `replay_provenance_completeness()`; its additional calls are tests.

Consequently replay metadata Incomplete alone permits the scheme-installation
and loaded-file return control flow. More precisely: if later semantic/proof
operations complete without a separate error, an Unclaimed lower can reach
scheme collection and finalization without this quota drop producing a
terminal availability/error signal. This proves a conditional control-flow
path, not that the frozen candidate actually takes it or publishes a complete
result. Mismatched support/formula, invalid proof facts, and projection resource
failures instead return ProofFailure and are rejected by the terminal latch.

The resource-abort guarantee thus covers actual terminal ProofFailure, not
mere incomplete replay metadata. Whether losing this edge breaks an invariant
needed by H remains open: the native A/s graph is retained and Unclaimed bounds
are included, so missing proof metadata alone is not an effect-hygiene
counterexample. Conversely the proven abort wrapper cannot be cited as
evidence that every incomplete replay path is safely unpublished.

## 6. Reduced premise, exclusions and next owner

The concrete source route C <: Y and the same original s in native A <: Y
are now derived from the owners above, conditional only on their terminal-free
completion. What remains is the actual r_Y projection decision at scheme
collection, followed by compact effect-tail survival, installed quantifier
membership through both selector branches, and replay of the provider's Effect
on the actual later callback route. Those steps are not discharged here.

The Tuple route supplied by the complementary source lane is distinct: it
aggregates child output predicates on a returned Tuple and cancels an active
PUSH on its direct positive compact path. It is not substituted for direct's
named skeleton C/Y route and is not a dependency of the derivation above.

Under the proof-obligation-economy rule, another equivalent conditional scheme
transport lemma would not advance this obligation. The next owner is
ConstraintMachine replay admission/projection: establish the actual canonical
c_AY/r_Y prefix and final support/formula/coverage state, either by a complete
bounded static census or by the primary's separately authorized owner
observation. That result must be applied before advancing compact and selector
proof. No additional operational action is authorized by this note.

Omitted: complete program allocation/settle census, final compact tree,
selected-ID inventory, generalization ancestor cleanup, provider replay and
output contribution, independent attachment survival, other source programs,
and universal H closure. No tests, builds, instrumentation, Oracle calls or
Git operations were performed. This producer does not certify its output.

## 7. Dependencies, checks and commit packet

Unchanged input SHA256 values:

| Input | SHA256 |
| --- | --- |
| Previous direct liveness proof | `eeb4a6bc838fdbc1007cc2565e6654cf382f1c77d65583e318d74e2d8a4bcb8f` |
| Callback source constructors | `fd4e57a9cf5ab303cafa64fb0d841c25a57673767f61e331b053f7dcce792b3e` |
| Annotation scheme identity | `cd9ec15a679c456d81e35a8d9c977a9ddf11bc5f00579b7909e917424d71d215` |
| Direct projection owner audit | `4ffba49b46626787f0c5cde12e72d94996f7bf68cf18c0dbcb7cadc923f75c59` |
| Original H | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| Hygiene design | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| Top-level principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |

Newly relevant Oracle source SHA256 values, at the same pinned revision:

| Source under `crates/infer/src/` | SHA256 |
| --- | --- |
| `constraints/machine/bounds.rs` | `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7` |
| `constraints/machine/entry.rs` | `00c70ca0938b24d4d2dd38de6598fe54217aebd28150ac279b52839046b340b8` |
| `constraints/machine/propagate.rs` | `8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086` |
| `constraints/row_effect.rs` | `080472bb5dcb3f724e808ff745c6fba304cc7ea2574b8f8eb3e3466964e937c2` |
| `constraints/mod.rs` | `ad3cf5fd60462cb1a08ef1a5d6fc57c4fd640148597bc3b331d09729616d8392` |
| `constraints/proof/mod.rs` | `bc0f3fbcf8f5ed01245e74283d3fd9cb13aa1713aff252a1847fde76b11b8e03` |
| `generalize/provenance.rs` | `83859368c64d27abb5896f1efc491b7fd616adf893b03d36d99b8f57da1792e0` |
| `generalize/finalize.rs` | `a8e5a1c8e6ad57d1fac7e25a1ab6a329093e5c76e6d84c0625c124c349f07492` |
| `analysis/session/instantiate.rs` | `bf21175f47df78f35f2070fea51b3483d59a91ac4a606bace9e24f32878c2d19` |

Checks: scoped `rg` owner/call-site censuses and `sed` source reads, input/source
`sha256sum`, and leased-note integrity read. A few path searches accidentally
used the Y3 root or obsolete Oracle subpaths and returned missing-path errors;
correct Oracle owners were subsequently read. These searches supplied no
positive evidence. Reads were lightweight; builds/tests/process experiments
and measurement samples: zero. No nested delegation. Bounded Sol proof pass;
wall-time/CPU/RSS were not instrumented. Requested role/model/effort:
registered prover, `gpt-6.1-sol/high`; observed runtime model/effort: unknown.

Commit packet for primary integration:

- Exact lease: `notes/theory/2026-10-11-oracle-direct-static-liveness-followup.md`.
- Baseline: `39968b554f3d4a71cece82e61188235a8559d706`; Oracle baseline unchanged.
- Changed dependency hashes: none in the frozen input list above.
- Review: producer-frozen, independent review pending; H remains OPEN.
- Checks already run: static reads/censuses and hashes only; no verification execution.
- Proposed checkpoint message: `research: trace Oracle direct native lower and incomplete replay publication`.
- Proposed shared-record delta, left to primary/curator: replace the missing
  C/Y native-lower premise with this terminal-free owner derivation; retain the
  actual collection ledger, compact survival, selector and provider replay
  premises OPEN; record that metadata Incomplete alone does not cause terminal
  nonpublication. Do not mark H closed or refuted.

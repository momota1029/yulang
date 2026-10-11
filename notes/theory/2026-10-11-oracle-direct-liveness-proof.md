# Oracle direct callback: liveness owner and bounded obstruction

Date: 2026-10-11
Status: frozen research characterization; independent review pending; H remains OPEN
Claim class: source-derived predicate/selector characterization and reduced operational premise, not a completed liveness theorem or H counterexample
Y3 baseline: `afe402a7be1bd0bdfe89a531469927d5788112a2`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle read root: `/tmp/yulang2-oracle-read`
Exclusive output: this file only; leaf, no delegation

## 1. Frozen objective and original theorem

Determine whether the original annotation ID survives actual scheme projection
and selection for the exact source below, then whether its fresh-use root POP
cancels the provider's later callback Effect. Authority is
[annotation effect hygiene](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–2 and [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. The frozen inputs are
[source constructors](2026-10-11-oracle-callback-reuse-source-proof.md),
[scheme identity](2026-10-11-oracle-annotation-scheme-identity-proof.md), and
[the completed display probe](../progress/2026-10-11-oracle-callback-reuse-projection-probe.md).

```yulang
pub act tick:
    pub ping: () -> ()
my direct(cb: (() -> [tick] ())) = cb
my provider() = tick::ping()
my observed_direct() = (direct provider) ()
```

Freeze a as the concrete row in this formal annotation, sigma as direct's
original lexical body, b as this resolved cb binder, s as the ID allocated by
this row's paired constructor, u as the actual direct scheme use in
observed_direct, and k as the actual returned-callback call. These are jointly
designated source objects; they are not independently chosen witnesses.

The parent H is unchanged from
[the original proof](2026-10-11-oracle-global-effect-hygiene-proof.md) §1:

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

Nested Function arguments reverse polarity and results preserve it. Incorrect
concrete lowers require authentic checking/errors and safe nonpublication.
Successful lowering is not proof of complete inference or accepted publication.
Complete Call, soundness and required principality remain separate. A single
source-qualified violation can refute H; success on this source cannot prove H.
No source restriction, extra annotation, rollback/retry search, or weakened
ordinary inference is introduced.

Shared assumptions: the pinned source bytes, ordinary completed method calls,
fresh allocation without exhaustion, and the frozen probe's reported exit 0
with no diagnostics. No assumption supplies complete replay, live compact
paths, selected IDs, exported lineage, independent attachment or complete
output meaning. Display `#0` is not raw identity.

## 2. Direct has a populated binder predicate and no local activation

Oracle citations in this note are relative to the Oracle read root.
`crates/infer/src/annotation/constraints.rs:362–389,424–470,657–690`
construct the paired Function, effect coordinate e, PUSH(s, Set(tick)), filtered
negative companion, and POP(s) output constraint. `register_stack_facts:593–600`
declares the concrete fact on e. Symbolic coordinates and stack identity remain
different facts.

For this **bare, non-wildcard Function** annotation,
`crates/infer/src/lowering/expr/lambda.rs:1581–1593`
returns `connection.subtracts` as the binder's call predicate. It is nonempty:
the Function's immediate ret_eff is this concrete row. In contrast,
`lambda_parameter_output_predicate_constraints:1571–1579` returns empty for
Function annotations. `connect_lambda_pattern_annotation:1282–1307` keeps both
results separately; its populated binder predicate also enables the public and
erased callable-upper constructions. Their auxiliary IDs are not s.

`mark_lambda_param_call_predicate:919–936` stores the predicate on b.
The original source note §2 already describes retention/installation correctly.
Its phrase “no local call-induced predicate in its frame” means no activation,
not an empty stored binder predicate. The identity note §2's empty-call-predicate
argument concerns its different annotation, whose immediate result Effect is
pure and whose concrete row belongs to a nested returned Function. That argument
does not apply to direct.

The distinction is operationally visible:

- `name_ref.rs:149–176` resolves the return reference to b; `tail.rs:855–858`
  returns the same formal value when it has no local scheme. A reference does
  not call `extend_current_latent_predicate`.
- `tail.rs:690–705` obtains a stored binder predicate only for an actual local
  Var callee; `make_app_with_origins:550–551` activates it on an application.
  `extend_current_latent_predicate:719–726` adds it to the current frame.
- direct's body is a reference, so this activation does not occur. The Function
  annotation's immediate enclosing-output predicate is empty as above.
- The later callee `(direct provider)` is an application expression, not the
  original Var reference to b. `local_callee_def:844–850` accepts only
  `Expr::Var`; its local-binder predicate route therefore returns no b for this
  later callee. Returning b does not copy LocalBinding metadata onto App.

`crates/infer/src/lowering/local.rs:3–20` owns the stored binder metadata;
`crates/poly/src/types.rs:17–27` stores scheme type/stack quantifiers, recursive
bounds, role predicates and the type predicate, with no binder-call metadata.
The inference read of `call_predicate_subtracts` is the application projection
at `tail.rs:702`; the frame marker at `lambda.rs:940` only checks its presence.
This corroborates the separate source audit reported by the primary. It does
not imply that the type predicate lacks ID-bearing stack evidence.

Thus this source's later effect removal cannot be justified by claiming that
direct locally invoked b or that the later App consulted b's stored predicate.
The paired graph's PUSH/NonSubtract evidence can still propagate through types;
this conclusion does not erase it. The separately constructed quantified-root
POP is the remaining suspect, subject to actual selection and replay.

## 3. Native accumulation is not the projected returned witness

The annotation emits both comparisons in `constraints.rs:132–144`, including
its positive Function below b. `arena.rs:90–93` forwards actual constraints;
`constraints/machine/entry.rs:493–500` drains queued work. The Function-to-Var
case at `machine/propagate.rs:150–158` calls `add_lower_bound`.

The source body also emits real variable connections toward its returned Value:
defined-lambda lowering at `lambda.rs:790–810` connects `body.value` to the
skeleton body coordinate when that skeleton is present; empty-predicate
connection at `1190–1229` connects body/output coordinates in the selected mode.
`tail.rs:1092–1103` uses the unwrapped body coordinates when the output predicate
is empty. These are source-emitted connections, not a premise that all stored
lowers will be selected for the scheme.

The first missing operational fact is the actual **active lower route reaching
the returned callback coordinate at direct's collection boundary**, with the
original s-bearing port graph and its real projection derivations. Insertion
at `machine/bounds.rs:630–731` first extrudes to the target level, checks/erases
the left filter, may return through alias-cycle subsumption, records insertion
or equivalence, and generates replay actions. Seeing the original comparison
does not determine the terminal record, its weight after those operations, or
the support/formula ledger of the returned route.

This gap has a precise decision owner, rather than an unspecified concern
about “generalization correctness.” `VarBounds::projection_lower_records`
(`constraints/mod.rs:2664–2677`) enumerates evidence and ordinary lower records.
`structural_kernel/access.rs:862–898` invokes `project_lower` for each record
and skips exactly `Excluded`; the collector at `compact/collect/mod.rs:848–877`
consumes that filtered list.

At `constraints/proof/mod.rs:9993–10035`, an active lower with neither support
nor exact formula is Unclaimed. With both, the actual evaluator determines
inclusion; missing/inconsistent proof facts are errors. A standalone Independent
arm evaluates IncludedExact (`11635–11760,11906–11917`), but a derived unary arm
consults its premise and a replay conjunction consults **both** bound premises.
An independent label alone is not a replacement for that formula.

The source-origin shortcut also has an exact limit. `machine/bounds.rs:2490–2568`
installs independent standalone arms when it classifies a carrier independent;
`2618–2720` checks ConstraintOrigin against the lower's actual claims, and checks
structural/replay carriers against actual qualified-parent incidence. The
annotation lower has a genuine source-origin constructor
(`annotation/constraints.rs:53–89`); this does not make every derived returned
lower a standalone source-origin arm. Neither frozen note contains the actual
returned record, qualified parents, support/formula or projection result.

Consequently this pass cannot apply an inclusion rule to the designated returned
record without supplying its actual arguments. This is a limit of the bounded
derivation/evidence, not a claim that deterministic source code is inherently
incapable of being evaluated statically. A complete static operational trace
could discharge it; this pass has not constructed that trace. No assumption of
Unclaimed, independence, exclusion or completed replay fills the gap.

## 4. Selection and consumption after that missing fact

The exact selector would require the following *same* returned route.
Positive Function collection carries weights through ret and ret_eff, while
negative Function collection reverses the argument ports
(`compact/collect/type_nodes.rs:13–25,117–135`). A returned callback's latent
Effect is covariant relative to direct's root. A surviving positive Stack on e
would carry s onto its compact variable. Negative stack compaction can instead
emit a concrete row prefix and discard the stack weight from the tail
(`545–562`); an argument-side tick item is not the required s witness.

Both selection branches must be evaluated on the actual cleaned root:

1. `generalize/core/stack_ids.rs:23–49,76–179` selects s only if a covariant
   compact variable has a nonempty stack entry for s and its variable belongs
   to the actual type-variable quantifier set. That set uses the boundary,
   levels and non-generic membership (`generalize/mod.rs:900–915`). A PUSH in
   the original annotation is not this cleaned-root witness.
2. `generalize/mod.rs:867–889` adds encountered IDs for which the actual
   `fact_by_id` lookup yields Subtractability::All. The original registered
   fact is Set(tick), so its construction alone does not supply this branch.
   `fact_by_id` searches the current fact table (`constraints/mod.rs:3406–3411`);
   no unproved census of later facts with s is assumed here.

Prepasses and stack cleanup occur before selection
(`analysis/session/generalize.rs:430–547`); dead/stray IDs may disappear
(`generalize/core/prune.rs:39–80,605–629`; `generalize/mod.rs:177–238`).
Installation repeats cleanup and selection with ancestor simplifications
(`analysis/session/instantiate.rs:54–83`; `generalize/mod.rs:839–864`). Thus even
one included raw lower is not a proof that s is in the **installed** selected set.

The established identity note's finalization lemma can be used only after this
survival premise. `instantiate.rs:621–647,741–787` then allocates the use map
before cloning and wraps the root in POP(MAX) for each selected key. Exact-ID
composition (`constraints/directed_weight.rs:145–170`) explains a possible
cancellation, but neither this lemma nor equality of tick families proves the
provider's actual contribution followed that cancelled port. The two actual
applications generate four-port demands (`tail.rs:535–624`), and Function
propagation preserves result ports (`machine/propagate.rs:210–267`). Complete
provider replay and final Effect readout remain required joined evidence.

## 5. Economy audit and stop

The earlier source-constructor and scheme-identity passes already reached the
same export/use premise by different methods. This pass narrows its owner to
active returned-lower lineage and its projection formula before compact cleanup;
it does **not** count that owner refinement or the predicate correction as proof
of liveness. Stop before another equivalent freshening/dump argument.

Under `rules/compiler-engineering.md`, scoped subtraction and ordinary callback
inference remain A/B. Inferring original s from display #0 is D reconstruction
debt. The annotation, bound insertion/replay, projection, cleaned-root selector
and fresh-use constructor already know the needed facts. A primary-authorized
bounded capture of their actual joined lineage would retain existing facts
without choosing new semantics. This is proposed evidence, not adopted compiler
metadata or an implementation requirement. No C reclassification closes H.

One next action: obtain, at the existing collection/selection owners, the
designated original s, returned-coordinate lower records with their actual
projection result/support/formula, and the installation selector's cleaned root,
quantifier set and s membership. Reuse the already established transport lemma
only if that snapshot supplies survival; then follow that same use and provider
to the later Effect. No additional Oracle run was authorized in this packet.

## 6. Checks, resources, runtime and commit packet

Only this leased note changed. Static commands: cat/sed/rg, read-only revision
lookups, SHA-256 snapshots, and note whitespace/newline integrity. Some initial
combined outputs were truncated; decisive owners were reread narrowly. Guessed
Oracle paths and two reads accidentally issued from Y3 were absent and caused
no mutation. No compiler edit, Oracle execution, instrumentation, checker,
Cargo/build/test, network operation, delegation or Git mutation occurred.
Heavy processes and executable samples: zero. At most three independent light
read commands ran concurrently; CPU/RSS and wall time were not instrumented.

Requested: registered prover, gpt-6.1-sol/high, one bounded leaf pass.
Observed identity: `/root/oracle_direct_liveness_proof`; model/effort runtime
metadata unknown. Configuration registers prover, with absent role pins and
Sol/high subagent defaults. No Astra or live reload claimed. No self-certification;
independent review remains pending. Writes stop at this handoff.

Unverified: actual terminal lower lineage/projection, compact survival, both
executed selector branches, use map, provider replay, complete Effect readout,
H, all-source complete Call, soundness and principality.

Dependency snapshots are SHA-256; none was edited by this worker:

| Y3 input | SHA-256 |
| --- | --- |
| source proof | `fd4e57a9cf5ab303cafa64fb0d841c25a57673767f61e331b053f7dcce792b3e` |
| identity proof | `cd9ec15a679c456d81e35a8d9c977a9ddf11bc5f00579b7909e917424d71d215` |
| projection probe | `975c2f7460ca5a9663938485cc2ce8669160b864c19928151589c9904016ccd2` |
| hygiene authority | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| top-level principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| original H | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |

Decisive additional Oracle owners at the pinned revision:

| Path under `crates/infer/src/` | SHA-256 |
| --- | --- |
| `constraints/machine/bounds.rs` | `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7` |
| `constraints/machine/entry.rs` | `00c70ca0938b24d4d2dd38de6598fe54217aebd28150ac279b52839046b340b8` |
| `constraints/proof/mod.rs` | `bc0f3fbcf8f5ed01245e74283d3fd9cb13aa1713aff252a1847fde76b11b8e03` |
| `constraints/mod.rs` | `ad3cf5fd60462cb1a08ef1a5d6fc57c4fd640148597bc3b331d09729616d8392` |
| `constraints/structural_kernel/access/legacy_read_view.rs` | `d51ab100c247f34ccf94cd75af2c28e1bf845a9b1a8719780843b02ba2bd35a6` |
| `lowering/name_ref.rs` | `699c7dc84a2b4889355ffe9cd23b3e871c295957dbcb3fbad96ee9ee36470ede` |
| `lowering/local.rs` | `300bc2b12d8f13aed0ae5f65cdec93683e7de2719be38bb33724f51730e52f81` |
| `arena.rs` | `e407480ee4984e24ce214543bfe23ed83e34883129487878df034090688bd9db` |
| `constraints/directed_weight.rs` | `de71ae7ed5a5aed22f3e5d35ca0ebcd52872ff965fcc22523a662cffdd6f28db` |

The additional `crates/poly/src/types.rs` snapshot is
`9211e62291b82e71e1b78763b83fe9f1d81e0fe4396d9e12d42e9a4a9b13b47c`.

Remaining cited Oracle hashes match the identity note's dependency table:
annotation constraints, lambda/tail, propagation, access, collector/type_nodes,
generalization/mod/stack_ids/prune, session generalize/instantiate and
instantiate.rs. These were individually hashed in this pass.

- Exact lease: `notes/theory/2026-10-11-oracle-direct-liveness-proof.md`.
- Baselines: Y3 `afe402a7be1bd0bdfe89a531469927d5788112a2`; Oracle
  `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; integration must revalidate the frozen inputs.
- Review status: unreviewed research characterization; no theorem/counterexample
  or production closure. H remains OPEN.
- Checks already run: static source reads/revisions/hashes; final note integrity.
- Proposed checkpoint: `research: pinpoint Oracle direct liveness projection owner`.
- Shared-record delta for primary/curator: replace tasks/current.md's “annotation's
  immediate local-call predicate is empty” with “the binder call predicate is
  populated; direct does not activate it, and the enclosing Function parameter's
  immediate output predicate is empty.” The committed source note needs no
  semantic repair; optionally clarify §2's frame sentence with that distinction.
  Retain actual returned-lower projection and installed selection as OPEN;
  preserve provider replay and H as OPEN. No shared record edited.

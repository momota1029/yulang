# Independent handler-arm contribution in the actual Oracle output image

Date: 2026-10-12
Status: frozen bounded derivation; independent `compiler_referee` review clean; original H OPEN
Claim class: bounded conditional application of reviewed source-to-image results
Y3 baseline: `ba1729bf9869c849172a05f33d7a233d36a69155`, branch `research/simple-sub-intrusion`
Oracle source: immutable `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this file only; leaf, no delegation

## 1. Frozen statement and original boundary

The original universal **H** is unchanged, from
[original H](2026-10-12-oracle-effect-hygiene-original-H-proof-attempt.md) §1:

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

Apply the reviewed derivations to exactly P+ in
[handler proof](2026-10-12-same-family-handler-output-proof.md) §1:

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

Keep its exact annotation occurrence a, original function scope sigma, Value
binder `'a`, formal `action`, arm payload binders `s,n`, continuation `k`,
value arm `v`, declaration, recursive call and outer call. E denotes the
resolved nullary family of this declaration. A is the outer argument send;
B is the first application inside the matching effect arm; C is its recursive
tail application. These are distinct source occurrences, not numeric IDs or
independent choices of family witnesses.

The assigned bounded conclusion is: whenever the normal owners for this fixed
P+ complete, B's actual contribution has an included native route to the real
public Function return, and its actual compact/generalized/published/use image
reaches that outer Call's own result Effect O. Establish this in the same
construction that processes a's scrutinee view, retaining the actual Function,
argument, provider/use and output ports. Identify exactly how far this supplies
H's independent-contribution clause. It does not replace H's quantifiers.

Hypotheses are the immutable bytes, valid fresh allocation before exhaustion,
and completed normal owning calls/admissions/scoped queries in the reviewed
inputs' nonterminal scope. Consume the reviewed source-to-T, recursive return
and forward-image conclusions with their displayed qualifications. Do not
assume P+ acceptance, a selected control scheme, an independently chosen
output witness, complete replay, successful pending-use activation, annotation
attachment adequacy, or the desired output membership. No executable probe is
part of this derivation.

Authority: [annotation hygiene](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–4; [attachment/admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§§3–6; [selected residual lineage](../design/2026-10-10-contextual-residual-lineage-selection.md);
[complete Call](../design/2026-10-07-complete-call-contribution-definition.md)
§§2–5; [top-level inference](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. The corrected callback result is excluded. Separate recipe lineages,
actual provider/entry, whole argument and future interface remain requirements;
Oracle key coalescence supplies no successor policy or lineage identification.

## 2. Joint source construction: the matched input and B's own route

All Oracle locators below have prefix `crates/infer/src/` at the immutable
revision. Coordinates are the reviewed notes' actual allocations: V is the
public formal Effect, U/alpha its inner coordinate and subtraction ID, T the
catch result, R the recursive body Effect, and G the public definition Value.

The parameter owner constructs a's view and argument port together:

```text
Push_alpha(U) <: V
actual_arg_eff = Var(V) intersect Row({E}, Top).
```

Owner: `annotation/constraints.rs:546–590`. The public V and stacked U are
the inputs of `lowering/control.rs:995–1021::subtype_scrutinee_effect_to_row`.
For this complete handler, `control.rs:957–974` uses T as the handled row tail
and emits the actual two comparisons:

```text
V             <: Row({E}, T)
Push_alpha(U) <: Row({E}, T).
```

At the concrete row consumer, a matched E is compared to its actual matched
head; only an unmatched head is sent to the upper tail
(`constraints/machine/propagate.rs:1007–1042`). The weighted Var-to-Row owner
may produce its own feedback/gamma derivations. Neither matching nor those
derivations is an operation deleting every E lower at T. This states the real
local comparison, not that all A effects have been semantically removed.

In the same lowering of this arm, B reads `s,n` and resolves the operation
declaration. Its direct operation-reference Function comes from that
declaration, with return `Row([Con(E,[])])`; it is not obtained from the local
`action` view. The reviewed [handler proof](2026-10-12-same-family-handler-output-proof.md)
§§2,5 constructs the actual Function lower at Z_B and its complete application
demand. Native Function comparison supplies the concrete row at K_B. The arm
block then supplies this actual forwarding route:

```text
B -> declaration-derived row at K_B -> C_B -> B_eff -> T -> R.
```

`lowering/control.rs:1164–1168` joins the arm body's Effect into T. The
scrutinee-row owner above takes neither K_B nor C_B nor B_eff as its input.
The reviewed Direct roots and actual DerivedUnary/ReplayConjunction clauses
include B's seed and each edge into T (handler proof §§4–6). The reviewed
[recursive-return proof](2026-10-12-same-family-handler-recursive-return-proof.md)
§3 extends that very parent tree to b_R. Original Var-to-Var forwarding claims
are not identified with a Var-to-Row coverage producer merely because both
occur in this handler. This is why the input row's matched-E processing does
not exclude the independent B route's included clause.

Here "independent B" denotes this separately constructed operation contribution:
its row is supplied by the declaration at B's own reference/application, and
its incoming derivation does not use A or a's V/U/alpha scrutinee route. It
does not mean the projection enum `Independent`, nor disjoint family support,
nor a complete proof of H's semantic attachment judgment. Shared payload
Values and the same E family do not replace these actual construction parents.

## 3. The actual return is not wrapped in the action's output POP

This P+ tests an independent arm return in a handler; it does not exercise
the stronger case of an output POP of alpha around that return.

The parameter connection returns its Value's `subtracts` separately from its
`effect_stack` (`annotation/constraints.rs:263–276`). The plain `'a` Value
case returns no output predicates (316–322).
`lowering/expr/lambda.rs:1581–1626` filters the parameter's immediate output
predicates using the actual stack IDs; it does not copy the formal Effect
stack into an otherwise empty output predicate. The reviewed source inventory
also computes the actual body/frame predicate as empty for this P+:
annotated continuation `k`, local named-self `run`, qualified operation calls,
and the plain result `'a` supply no missing alpha output predicate. The
recursive `run` uses the internal S, distinct from public G
(recursive-return proof §2). No control-fixture frame is substituted.

Thus `lowering/expr/tail.rs:1058–1072,1092–1101` and the actual wrapper owner
construct the public Function with bare return `Pos::Var(R)`:

```text
f_G = Fun(actual_arg, actual_arg_eff, Var(R), actual_ret).
```

Its projectable admission at G and b_R's projectable admission at that same
return R are the joined conclusion of recursive-return proof §4. This is
not a pair of marginal witnesses. Absence of an action output POP supplies
no theorem about programs in which such a POP exists; that part of H remains
OPEN. It is also not a restriction imposed on ordinary source inference.

## 4. Apply the actual forward map, keeping the complete demand fixed

Consume [image-preservation proof](2026-10-12-same-family-handler-image-preservation-proof.md)
§§2–6. That proof starts with exactly b_R/f_G above and follows the actual
constructors; it does not start with an arbitrary positive E valuation.

| Actual map/consumer | B's correlated forward object |
| --- | --- |
| scoped query and collection, `compact/collect/mod.rs:848–918`; Function/row collection, `compact/collect/type_nodes.rs:196–225,261–286,404–445` | b_R's endpoint at f_G's own return becomes e_C in the actual compact root |
| positive accumulation, `compact/merge/entries.rs:288–306,409–432` | its nullary E item is retained at the positively merged Function return; it is not selected from an unrelated Function |
| actual generalization sequence, `analysis/session/generalize.rs:412–549`; finalization, `generalize/mod.rs:837–865`, `compact/finalize.rs:415–426,542–549,641–689` | the same inline return item has finalized image e_S, after the real variable rewrites, cleanup and ancestors |
| publication, `analysis/session/instantiate.rs:14–82`; `analysis/session/generalize.rs:958–964` | the finalized predicate is installed on this actual G definition |
| actual use, `analysis/session/lifecycle.rs:1092–1101`, `scc.rs:266–300`, `analysis/session/instantiate.rs:342–519`; consistent cloning, `instantiate.rs:625–648,732–845` | the quantified branch reads G's installed scheme and gives e_S its image e_U in the same copied Function; the open branch instead uses G-to-Z_O and the real R/b_R route |
| actual Function return comparison and result forwarding, `constraints/machine/propagate.rs:212–263`, `lowering/expr/tail.rs:535–627` | that provider's own return reaches K_O and then this Call's O, giving e_O |

This application imports the input proof's source-specific collector recursion
and recollection argument, full positive-row transformations and native
activation argument. It does not merely quote a local row-key lemma. Whole
return rows, including retained variable/opaque parts, are admitted; the proof
does not replace the provider return by a newly invented pure E row.

Keep the actual outer demand fixed throughout:

```text
Z_O <: Fun(actual_A_Value, actual_A_Effect, K_O, actual_result_Value)
callee_evaluation_O <: O
K_O                 <: O.
```

`actual_A` is the whole outer `ev::send (1,42)` computation. It is not B,
nor a freely chosen diagonal argument. The Function lower is the actual
published/copy or open provider for G, not the declaration of `send` or the
recursive S skeleton. Publication, copy and the outer demand therefore share
one actual definition/use/Function route. The same whole-root transformation
acts on its argument and return fields; any retained variables/subtraction IDs
freshen through the same memoized use map. This does not assert preservation
of alpha if an earlier transformation discharged or removed it.

The outer return demand is bare K_O, because the global G reference bypasses
the unannotated local-parameter wrapper
(`lowering/expr/tail.rs:740–755`). Retained scheme-quantifier POPs are still
present in the copied branch. They have filter All and are carried in the
actual left context; they are not presumed absent. The reviewed outer replay
argument proves they do not delete e_U on this return-to-Var/forwarding route.
Argument-port comparisons and their row reductions have their own original
producer keys; they are not the outer Var-to-Function demand's coverage root.
The included copied/open Function and uncovered demand support the actual
FunctionReturnEffect and K_O-to-O projection clauses (image proof §6).

Consequently the application yields this bounded implication:

```text
the actual P+ owners/admissions/queries and outer use complete normally
---------------------------------------------------------------------
B's declaration-derived contribution has the forward route
  B -> b_T -> b_R at f_G.ret_eff -> e_C -> e_S -> e_U -> e_O in O,
or its actual open-provider route, while the same source construction
processes a's V/Push_alpha(U) against the handled row at T.
```

The arrows name applications of those actual operators to their preceding
objects. Positive merging may be many-to-one: they do not provide an inverse
from e_O to a unique B certificate. The native B clause is preserved through
R; downstream B correlation is this forward derivation, not an assertion
that the generalized witness sidecar records that clause. Root-return witness
omission therefore neither invalidates this image application nor proves H.

Later additions at this same ordinary O do not remove this concrete row by
Var-only alias subsumption. An actual later normal same-session copy of this
published G provider and an ordinary bare global Call have the reviewed
forward-image argument again. This states the exact limited stability from
the input proof. It proves neither every contextual future call nor retained
checks for every future lower reaching an arbitrary transformed variable.

## 5. Exact boundary of the result and missing premise

The bounded result applies the existing B-origin map to the independent arm
in the *same* handler/annotation/outer-use construction. It shows B's own
admitted support reaches O despite matched scrutinee E processing. It does
not assert that P+ is accepted or executes, that A is wholly removed, that
alpha survives in the scheme, or that every H attachment/residual/check has
the right image. A source-qualified counterexample was not obtained.

The first unsupported inference if one attempts to turn this into the full
independent-contribution clause of H is:

```text
this B-origin positive image and the actual V/U/alpha construction
  => a's authorized attachment, original scope/binders and residual/check
     interface have their required correlated images under every actual
     collection, rewrite, cleanup, use and current/future consumer.
```

None of the three reviewed inputs establishes that implication. The precise
source interface includes `compact/collect/mod.rs:848–879,1099–1128`, where
selected bound endpoints pass onward and Var lowers become secondary
occurrences; `compact/analysis/occurrence/substitution.rs:109–169` and
`generalize/simplification.rs:100–152`, where actual variable occurrences
may disappear or change representative/weights; and
`generalize/core/prune.rs:504–557,865–930`, where subtract IDs can leave
variable weights. One-map cloning of what survives does not prove the
semantic adequacy of those earlier operations for original attachment,
symbolic-tail and retained-check obligations. These are identified owners,
not a claim that the earliest failure lies in a particular one or that an
identity was actually lost.

There is no missing premise for reapplying the reviewed nullary B-positive
map within its stated scope. The missing premise concerns the larger
annotation/interface correspondence. No requirement of injective event tags,
chosen decisive certificates or additional runtime metadata is invented.
Separate residual constructor lineage and qualifying parent/copy intrusion
must retain their original contracts; this Oracle-only discriminator proves
neither a Y3 intrusion pair nor a successor implementation bridge.

Economy audit: native source registration, recursive-return construction and
the forward-image route already resolve the former positive B-output seam.
Repeating a same-family E-key lemma or trying another certificate-selection
route would leave the interface premise untouched. The remaining safety and
natural-inference requirement is A/B. Reconstructing erased source evidence
from the merged row alone is D; first inspect the constructors/transformations
that know the actual ports and relations. Evidence retention is a possible
primary-reviewed design response, not a representation change made by this
leaf. No reclassification closes the original gate.

One next action: primary consume this bounded application and the reviewed
image result in the existing annotation/interface lane; require its exact
collection/rewrite/stack-cleanup preservation argument with original scope,
binders, residual lineage and current/future-check quantifiers. Do not schedule
another equivalent positive-head proof. Original H, complete Call, soundness,
required principality, acceptance and production/cutover remain OPEN.

## 6. Freeze, checks and resources

Static source/record reads and document integrity checks only. Oracle reads
used `git -C /home/momota1029/rust/yulang2-oracle-capture show a58eefc31e:<path>`;
live capture instrumentation was not consumed. Direct dependency comparison
against Y3 baseline returned no changed path. The reviewed inputs' hashes
matched their recorded snapshots. Immutable source blob locators checked:

| Oracle path relative to `crates/infer/src/` | Blob ID |
| --- | --- |
| `annotation/constraints.rs` | `d2cf0e18266233c1e3c2943448244ee2a3499529` |
| `lowering/control.rs` | `2ae09cdd9abd3f4ce4a39f0091f3f98556de04bd` |
| `lowering/expr/lambda.rs` | `724b103cda8b4e2c457aacf0a674372fb191e3d6` |
| `lowering/expr/tail.rs` | `8289bfdc6a17b2469ae168ac7939d34813fda474` |
| `constraints/machine/propagate.rs` | `d558e7b9c17d33e91c5bb39c4cd85ebbfa4a8b09` |

No Oracle/build/test/runtime model, inference executable, network request,
measurement, Git mutation, compiler/test/shared-record edit or delegation.
Executable experiment process/sample count zero. Lightweight static shell
reads are not inference verification; at most four ran concurrently. CPU/RAM
were not instrumented. The primary remains the sole verification/integration
owner. One guessed source-route note pathname was absent; the actual frozen
progress note was located and read. Truncated aggregate reads were followed
by focused governing/decisive reads; no proof relies on a truncated search.

Requested runtime: `gpt-6.1-sol` / `high`, explicit primary packet; role pins
are absent in `.codex/agents/prover.toml`, with Sol/high defaults in the
registered `.codex/config.toml`. Observed effective model/effort: unknown;
this leaf receives no runtime metadata. No Astra, override success or hot
reload is claimed. Budget: one leaf, 40-minute static lane; final freeze and
mechanical result are recorded in the commit packet.

## Commit packet

- Exact changed lease: `notes/theory/2026-10-12-same-family-handler-independent-image-proof.md`.
- Baseline: Y3 `ba1729bf9869c849172a05f33d7a233d36a69155`;
  Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Frozen inputs, SHA-256:

  | Input | SHA-256 |
  | --- | --- |
  | handler output proof | `d4d77622765d986cb46cbbe0b79fdfa6b18d9099ec53129c877b4cfc0e6f367f` |
  | recursive-return proof | `7502f699b0269fb785c90b8e13ad7a74fbae912f1de0816999c6bb232765ee2b` |
  | image-preservation proof | `643a2906090eef4ce783cf2f1d2217cccdb997a6942ab7ecad47a27884b39abe` |
  | source-route progress note | `5b797e286e5ce787e31d4a63a2a70981f03c0b3d1077677cfd4c216c223efa70` |
  | original H attempt | `686d0970affd4c16aa82d87156fdae96ee6a48548a886212059d824e53651a48` |
  | global H | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
  | annotation hygiene | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
  | attachment/admission | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
  | residual lineage | `d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98` |
  | complete Call | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` |
  | top-level inference | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |

- Changed dependency hashes: none; only the leased new note is written.
- Review status: research-only bounded conditional application; independent
  `compiler_referee` review found no findings. Input reviews are dependencies,
  not review of this note.
  No theorem status, H closure, accepted counterexample or production claim.
- Checks already run: immutable source locators/blobs; scoped baseline
  comparison; eleven frozen input hashes. Final mechanical checks below are
  document checks, not inference execution or independent certification.
- Proposed checkpoint message: `research: apply handler contribution image to independent arm output`.
- Shared-record delta for primary/curator: record the bounded application of
  B's reviewed image in the same scrutinee-handler/actual outer-use route;
  explicitly retain the absence of an action-alpha output POP in this candidate
  and the original attachment/residual/variable/current-future-check gap.
  primary integrated this delta into `tasks/current.md`; `tasks/research-lab.md`,
  theory maps and design/index records remain primary/curator-owned.

Final static checks passed: no whitespace diagnostics from the leased-note
`git diff --check --no-index` comparison (exit 1 denotes the new-file diff),
zero trailing whitespace, sixteen balanced fence markers, final newline,
all extracted local Markdown targets present, and no draft placeholders.
All eleven input hashes matched the initial freeze; the scoped baseline
comparison found no changed dependency. First recorded clock sample:
2026-10-12 01:04:55 UTC; final-check sample: 2026-10-12 01:09:23 UTC.
These samples do not measure prior reading time, CPU or RAM. The bounded
application and its independent review are complete. Original H and production
gates remain open.

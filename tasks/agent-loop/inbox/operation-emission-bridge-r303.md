# Operation emission bridge R303 — frozen r1

Assignment `OPERATION-EMISSION-BRIDGE-R303`, revision 1; direct `/root`
assignment at supplied baseline `c23c27edc`, <=1200 seconds, no children/Git.
No distinct sprint contract was supplied. The retained R286 current-state
contract concerns another assignment and supplies no R303 semantic authority.
Author `/root/operation_emission_proof`; runtime session ID UNKNOWN. Requested
Astra/medium by role; observed model/effort UNKNOWN/UNKNOWN. No coauthors.

Outcome **source-native audit / BLOCKED**, not a new proof or a counterexample
to SIG. Original SIG, IF, R159, and source soundness delta: **zero**. No new
Lean module was written: the required actual-native certificate is unavailable,
and a mirrored constructor or an assumed emission relation would leave exactly
the original premise open. The unused leased path is
`notes/theory/lean/YulangClosure/OperationEmissionBridgeR303.lean`.

## Parent and exact application boundary

Unchanged parent: Theorem SIG §7 of
`notes/theory/2026-10-08-source-signature-incidence-construction.md`, selected by
`notes/design/2026-10-08-native-signature-formation-definition.md`; IF §6 of
`notes/theory/2026-10-08-call-source-interface-construction.md`. SIG preserves
complete origin partitions, introductions, actual routes, independent witnesses,
registered sharing, binders and whole tuples; IF requires independently typed
complete primitive/root interfaces and their lawful whole actions for every
original arm before arbitrary challenges. Native Function ports alone supply
neither semantic input.

Original `SourceProblem.InferenceSoundness p` is still
`∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
 ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a`.
The independent F1/FK1/W/Z quantifiers and shared source witness are unchanged.
R300 `actual_union_consumer` points to R159's original computation check
`callableImage → synthesis`; R302's `app_source_packet_and_target` still needs
original decode, finite Checking and image membership. No R303 fact supplies
these or `DeclContribution`, GR1 registration, child licenses or logical
admission. R302-ORIGINAL-1 remains separate from R302-EMISSION-1.

## Source evidence and narrower obstruction

The checked source chain is:

1. `candidate_source.rs:629–634` accepts a resolved operation only with an
   unannotated outer Function, recursively supported value constructors and
   `preflight_annotation(..., true)`. `operation_signature_values_supported`
   at 989 rejects holes/tuples on this path; the complete HIR carrier remains
   wider. At 1718–1731 it clones the actual declaration Arc into
   `Action::Operation`, retaining owner, occurrence, target and level; 2515
   invokes `candidate_operation`. This is the actual current native domain,
   not a narrowing of the original whole-language theorem.
2. `candidate_effect.rs:1280–1303` creates ONE value-variable cache, ONE distinct
   effect-variable cache and ONE row-position view cache per operation call.
   It invokes the signature at `level+1`, positive polarity AND positive
   variance, then admits its exact returned Term at occurrence slot 42.
   `candidate_scheme.rs:5138–5150` retains the exact lower/upper Terms in a SemanticFact joined by FactId to
   the provenance cause before live-value propagation. `lib.rs:4007–4056`
   deduplicates only exact Term pairs (`FactKey`, 4135–4158). Therefore direct
   slot-42 provenance is the first root evidence to read; the observer's
   unique reachable Function is not itself this equality.
3. `candidate_signature_value`, 2545–2690, evaluates Function children in
   order `a`, `r`, `ae`, `re`, then constructs `[a,ae,re,r]`. It reverses
   polarity and variance independently only for argument edges. `ae` reads
   `argument.effects` with no family. `re` reads `result.effects`; its family
   is present exactly when the actual `ty` pointer is the declaration root.
   Every recursive value call shares those same caches. The Primitive-only
   correlated entry-row override does not apply to Operation.
4. `candidate_signature_effect`, 2692–2831, performs the mutable work absent
   from the pure R300 plan. Written negative-variance rows reject concrete
   members and more than one variable; a singleton symbolic tail reuses the
   operation's effect-variable cache, otherwise they return the empty leaf.
   Written positive-variance rows resolve the tail before row-position cache
   lookup, reuse/create a view, then allocate a fresh port and insert the
   actual bound. Cache hits do NOT reconstruct or recheck allowed/tail fields.
   Omitted rows with Self create an uncached Support view and fresh port;
   omitted operation rows without Self return the polarity-specific empty
   leaf. This branch distinction must survive the evidence.
5. `lib.rs:10631–10659` passes the four exact Terms to the arena.
   `candidate_scheme.rs:2048–2181` converts actual Terms to typed endpoints;
   `Capture::intern_shape` at 1956 canonicalizes them, and `row` at 1991 uses
   the capture-time representative and `level > boundary && !non_generic`.
   `expand_node` at 2226–2281 captures the exact Function view's four fields,
   kinds `[Value,Effect,Effect,Value]` and signs `[!p,!p,p,p]`.
6. `candidate_scheme.rs:4733–4784` reconstructs a Function in the actual shared
   FreshUse `terms` vector from the four already mapped children. `FreshUse`
   retains that vector, mapped rows and effect operands at 816–828.
   `shadow_apply.rs::source_operation_apply_effect_joins` (2090–2223) checks
   exact retained declaration provenance, source BoundKey and FreshUse row
   for invocation/application effects. It does not identify every operation
   Function child or its source path.

`tools/native-signature-observer/src/main.rs` uses the real parse/HIR and
public capture. Its fixed positive fixture checks full ordered Support members,
actual declaration pointer, occurrence and owner, children and signed leaf/row
shapes. It finds the sole Function in root lower-bound closure. Its final source-observation dump DOES include slot 42 and its retained
Terms, through public `source_occurrence_observation` at 2251–2280. It does
not select/authenticate that fact as its chosen Function root, inspect its
Term fields, or join raw allocations, variable-name maps, view-cache events
or the complete operation FreshUse crosswalk. No new Rust run
is claimed here; the existing observer source was audited read-only.

There are THREE identity stages. `CandidateGraphNode::same_identity` compares
one graph pointer and node index (2862). `CandidateGraphRow::same_identity`
compares graph-state pointer and the CURRENT intrusion representatives (3043),
even for rows originating in different captures. `Capture::row` used the
representative AT CAPTURE. Equal observed rows thus do not establish equal raw
allocations, the same historical representative, or the same construction
occurrence. Do not replace this distinction with one Nat label.

## Exact readout needed: no assumed theorem interface

The following is a proposed observational record, not new compiler semantics,
not a Lean axiom and not an implemented certificate. Native identities must
be retained/authenticated inside the same solve; any serialized ordinals need
one explicit same-run table. A finite trace would establish only that run,
not the general Rust/Lean simulation theorem.

Retain an operation attempt ID with the actual declaration Arc, owner,
occurrence, target, source parse identity, starting level and success/rollback
outcome. Within it retain each call's source path `p`, exact subtree reference,
independent `(polarity, variance)`, sequential event index, returned Term and,
for Functions, exact child Terms `a,ae,re,r`. Retain effect events with child
side, complete optional source row, actual `family` argument, variable-cache
name/hit/miss/row, view-cache key/hit/miss/view, allowed/tail snapshot, fresh
port, inserted raw BoundKey and result Term. Keep Value and Effect name tables
separate. A cache hit must link to the actual earlier creation event in this
attempt; comparison with a newly computed expected view is insufficient.

The first unconsumed root readout is ALREADY in actual retained provenance.
Select the exact operation occurrence and local slot 42 from a complete
`source_occurrence_observation`, then read `fact.lower()` / `fact.upper()`.
The archived observer `positive.log` prints `FactId(2)`, lower Term brand 1
index 262, upper Term brand 1 index 1, for occurrence ordinal 3 / slot 42.
These labels are that run only. No cross-run equality is claimed.
The root equations to authenticate against the constructor/capture are:

```text
slot42.source = operationOccurrence
slot42.slot = 42
slot42.lower = returnedTerm(operationAttempt, [])
slot42.upper = batch.component_term_at(actualTarget)
```

For each actual Function event at source path `p`, the constructor equations
that must be checked against the arena are:

```text
sourceSubtree(p) = Function(argument, result)
term_view(T[p]) = Function(polarity[p], A[p], AE[p], RE[p], R[p])
A[p] = T[p ++ [argument]]       R[p] = T[p ++ [result]]
sourceRow(AE[p]) = argument.effects
sourceRow(RE[p]) = result.effects
family(AE[p]) = None
family(RE[p]) = if ptr_eq(sourceSubtree(p), declaration.signature)
               then Some(declaration.family) else None
```

The source path/subtree pointer equation must be derived from the actual
recursive call, not reconstructed by comparing type shapes. Root-only Self
is then a statement about that pointer and call provenance; explicit inclusion
of the same family elsewhere does not count as Self. R300 `field_readback` and
`polarityAt_composition` apply to the authenticated retained source paths after
this missing call/readout correspondence, not before it.

For a written positive-variance effect event, the actual mutable incidence is:

```text
view = views_before[sourceRow.position]                  (hit)
  OR view = createdView(owner, sourceRow.position,
          family.toList ++ sourceRow.concrete, resolvedTail,
          Operation(declarationArc, occurrence)); views_after[key] = view (miss)
port = actualFreshEffect(level)
insertedKey = BoundKey(EffectRow(port), polarity,
                      if polarity=Positive then Support(view) else Allowance(view))
term_view(returnedEffect) = LiveVariable(Effect, polarity, port)
```

These are distinct from negative-variance symbolic-tail/empty and omitted
Self/empty cases described above. Record the actual return status: resource
failure and rolled-back prefixes do not become successful emission facts.
The cached view payload must be read on a hit; its compatibility with the
current row/family/tail is a source/cache invariant still to establish.

At capture `c`, retain the actual endpoint-to-node entries used during capture:

```text
n[p] = intern_c(term_endpoint_c(T[p], Value, polarity[p]))
children_c(n[p])[i] = intern_c(term_endpoint_c(childTerm[p,i], kind[i], sign[p,i]))
graphRowKey_c(i) = rep_at_capture(rawRow_c(i))
```

`intern_c` above denotes the recorded successful native operation, NOT a new
function presumed to agree with Rust. Record the capture identity/event cursor,
raw endpoint, canonical endpoint, graph node/row index, level/non-generic data
and boundary. Current row equality cannot replace `rep_at_capture`.
For each actual FreshUse route `u` then read:

```text
term_view(retained_u.terms[n[p]]) =
  Function(polarity[p], retained_u.terms[children_c(n[p])[0]],
                       retained_u.terms[children_c(n[p])[1]],
                       retained_u.terms[children_c(n[p])[2]],
                       retained_u.terms[children_c(n[p])[3]])
portRowImage = route_u.rows[exactCapturedRowIndex]
viewImage = retained_u.effect_operands[exactCapturedSupportNode]
```

This uses ONE actual route for all four ports and the corresponding bound,
view, scope and relation records. It does not combine independently matching
routes. Intermediate path edges select value slots 0/3; only the terminal
effect edge selects slot 1/2, as in the formal-only path helper at
`shadow_apply.rs:2742–2776`. That helper's formal-root registration cannot
supply the operation root needed here.

## Minimal implementation request and stop condition

**R303-READOUT-1**, refinement of **R302-EMISSION-1**, owner Luna/native observer:
first consume the ALREADY public slot-42 fact readout, then expose a
research-only same-run Term-field/capture crosswalk for that exact lower Term,
joined to the operation Arc/occurrence. No new fact/provenance store is needed.
Add constructor-local observations only for the information currently lost:
source recursive path, root-pointer Self argument, variable/view-cache events
and raw port/bound identities. Join those records to the actual capture and
retained FreshUse maps. Preserve the existing inference calls and state;
do not add a production acceptance check, new semantic relation or allocator.
Implementation requires Luna's separate exact lease; none is exercised here.

Required falsifiers: swapped AE/RE; nested re tagged as Self; explicit E treated
as inserted Self; cache hit from another occurrence; two raw allocations
collapsed by later representatives; a capture-time representative replaced by
the final one; independently chosen FreshUse routes per port; equal value and
effect variable spellings merged; repeated same-kind names freshly allocated
per path; a partial/rolled-back attempt reported as slot-42 success. The current
positive fixture and its negative controls cannot discriminate all of these.
Keep their existing expectations intact and extend only in a separately
approved observer/test packet.

**R303-SOURCE-CACHE-1**, owner Luna/source proof: after a real readout exists,
prove the operation-local cache discipline across the actual recursive traversal,
including hit compatibility and same-kind name sharing. Its input must include
actual source-position identities and constructor order, not a globally assumed
`EmissionCorrect`. A positive finite trace remains evidence for that trace only.

No in-lease constructive step now yields the missing actual native evidence.
Stop at this genuine input/implementation boundary. Reused R300's source/path
and pure policy, R301's extracted HIR, R302's semantic consumer and observer;
rejected a mirror, family-only matching, final canonical-row equality, and a
conditional theorem assuming the exact emission correspondence as its premise.

## Checks, frozen inputs, authors and cessation
Pinned native Lake `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`;
Lake `5.0.0-src+eb6cafb`, Lean `4.35.0`, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Isolated verification owner
`/root/operation_emission_proof`, scratch `/tmp/yulang-operation-emission-r303`.
All 58 copied Lean imports and all 75 frozen inputs match workspace bytes.
Focused build passed 59 jobs; all FOUR EXISTING named theorem checks passed
exit 0 with the complete types and transitive axiom lists below. No new
theorem is counted. No default integration build or Rust execution claimed.
Command: bundled `check_lean.py --project /tmp/yulang-operation-emission-r303
--lake <native path above> --timeout 120
--module YulangClosure.SourceSignatureNativeBridgeR302`, with the four fully
qualified theorem names below. One checker invocation; single-thread helper,
project `-j1 -M1024`. One earlier read-only `rg` command used the wrong working
directory and exited 2; corrected before checking. No proof/checker failures.
Existing dependency diagnostics remain in the frozen log.
No new Lean source, assumptions, kernel bypasses or dependencies. No Cargo,
Git, production code, tests, expectations, shared state or root imports changed.
Only repository write: this exact handoff. Scratch is the isolated source/config
copy, `.lake/**`, `dependencies.json`, `check-start.txt`, `checker.log`, and
`theorem-audit.txt`; the helper temporary audit directory was removed by the
helper. No descendant or outstanding process. Total active time was not
instrumented (UNKNOWN), within the <=1200-second assignment bound; checker
wall cap 120 seconds. STOP at the actual-certificate boundary, no claimed
background work.
Reused producers: R300 `/root/source_signature_formalization`, R301
`/root/source_signature_lean_bridge`, R302 `/root/native_signature_bridge`.
Observer original author UNKNOWN in this assignment; its package README pins
the reviewed source hash. These dependencies are not coauthored or modified
here. Independent review of R303 remains Luna-owned and pending.
Frozen hashes:
- 75-input manifest `642579974e01d0fb097360bca8c0f114b1db8346838519afd0208635af733880` (`/tmp/yulang-operation-emission-r303/dependencies.json`).
- Checker log `8870b3e6088e7b71b2f146a30fde6dc981780d95850adeb326ba5a3d3c5b7a20`.
- Named theorem audit `c8ca4057c16b5ab731dee87393553e09f110a03b490f6bf1d3058809abf9b3f1`.
- Archived observer positive log `e930e62e2ea4db0f8298ec3c4ad5b61f9bd0f89dc7a7a6efb3231f4d0959bb95` (`/tmp/yulang-native-signature-observer-20261103/positive.log`); read-only historical evidence, not a new execution.
- `crates/yu-solver/src/candidate_effect.rs`: `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15`.
- `crates/yu-solver/src/candidate_scheme.rs`: `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e`.
- `crates/yu-solver/src/candidate_source.rs`: `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`.
- `crates/yu-solver/src/shadow_apply.rs`: `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5`.
- `crates/yu-solver/src/lib.rs`: `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be`.
- `tools/native-signature-observer/src/main.rs`: `cb33d461e2559c163484a3c23713976ca47e4cccd8e1fa62f3c726775ac30bfb`.
- `notes/theory/lean/YulangClosure/SourceSignatureRealizationR300.lean`: `384ac75df5fe6269b76faf06971cca345a6029f4f6a173296042fcfdceae8449`.
- `notes/theory/lean/YulangClosure/SourceSignatureExtractedChecksR301.lean`: `279e8771297dad208af6fce199f8163b8a0e0508b11a748a9c22b5a8c2aaddbe`.
- `notes/theory/lean/YulangClosure/SourceSignatureNativeBridgeR302.lean`: `090b09fd04fac56b99b4e637786948fae750150c1e9afc38a532cf290c6f0b30`.

Writer **STOPPED**, revision 1 frozen for Luna intake. The handoff byte hash
is reported separately to avoid a self-referential hash. No parent gate is closed.

## Existing theorem types and complete axiom lists

```text
YULANG_AUDIT_BEGIN YulangClosure.SourceSignatureRealizationR300.field_readback
@YulangClosure.SourceSignatureRealizationR300.field_readback : ∀ {E H : Type}
  {a b : YulangClosure.PrimitiveOperation.Annotation E H}
  {path : List YulangClosure.SourceSignatureRealizationR300.Step}
  (field : YulangClosure.SourceSignatureRealizationR300.Field a path b),
  YulangClosure.SourceSignatureRealizationR300.lookup a path = Option.some b
'YulangClosure.SourceSignatureRealizationR300.field_readback' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.SourceSignatureRealizationR300.field_readback
YULANG_AUDIT_BEGIN YulangClosure.SourceSignatureRealizationR300.polarityAt_composition
YulangClosure.SourceSignatureRealizationR300.polarityAt_composition : ∀ (positive : Bool)
  (p q : List YulangClosure.SourceSignatureRealizationR300.Step),
  YulangClosure.SourceSignatureRealizationR300.polarityAt positive (p ++ q) =
    YulangClosure.SourceSignatureRealizationR300.polarityAt
      (YulangClosure.SourceSignatureRealizationR300.polarityAt positive p) q
'YulangClosure.SourceSignatureRealizationR300.polarityAt_composition' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.SourceSignatureRealizationR300.polarityAt_composition
YULANG_AUDIT_BEGIN YulangClosure.SourceSignatureRealizationR300.actual_union_consumer
YulangClosure.SourceSignatureRealizationR300.actual_union_consumer : ∀ (context : YulangClosure.OriginalSource.Context)
  (mark : YulangClosure.OriginalSource.Mark)
  (callee argument : YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression),
  YulangClosure.OriginalSource.Premise.checking
      { mode := YulangClosure.OriginalSource.CheckMode.computation, site := mark.site, context := context,
        lower := { site := mark.site, port := YulangClosure.OriginalSource.Port.callableImage },
        upper := { site := mark.site, port := YulangClosure.OriginalSource.Port.synthesis } } ∈
    YulangClosure.SourceAppAdmissionR159.appPremises context mark callee argument
'YulangClosure.SourceSignatureRealizationR300.actual_union_consumer' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.SourceSignatureRealizationR300.actual_union_consumer
YULANG_AUDIT_BEGIN YulangClosure.SourceSignatureNativeBridgeR302.extracted_result_ports_distinct
YulangClosure.SourceSignatureNativeBridgeR302.extracted_result_ports_distinct : YulangClosure.SourceSignatureRealizationR300.operationEffectPlan
      4
      (YulangClosure.SourceSignatureRealizationR300.effects
        YulangClosure.SourceSignatureExtractedChecksR301.expectedResult)
      (YulangClosure.SourceSignatureRealizationR300.selfFamily 0 []) Bool.true Bool.true =
    Option.some
      (YulangClosure.SourceSignatureRealizationR300.EffectPlan.view Bool.true 6 [0, 1, 0, 1] (Option.some "'out")) ∧
  YulangClosure.SourceSignatureRealizationR300.operationEffectPlan 4
      (YulangClosure.SourceSignatureRealizationR300.effects
        (YulangClosure.PrimitiveOperation.Annotation.primitive
          (Option.some YulangClosure.SourceSignatureExtractedChecksR301.resultRow)
          YulangClosure.PrimitiveOperation.Primitive.int))
      (YulangClosure.SourceSignatureRealizationR300.selfFamily 0
        [YulangClosure.SourceSignatureRealizationR300.Step.result])
      Bool.true Bool.true =
    Option.some (YulangClosure.SourceSignatureRealizationR300.EffectPlan.view Bool.true 7 [0] Option.none)
'YulangClosure.SourceSignatureNativeBridgeR302.extracted_result_ports_distinct' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.SourceSignatureNativeBridgeR302.extracted_result_ports_distinct
```

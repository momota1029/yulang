# Contextual live PUSH: exact construction prefix and missing operation

Date: 2026-10-12
Status: unreviewed research source derivation; original source/output theorem OPEN
Claim class: conditional constructor prefix and static implementation obstruction
Assigned baseline: `7aeeb477257e030c218fbba23ed1e60c32d541cb`
Branch: `research/simple-sub-intrusion`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this file; leaf, no delegation, compiler edits, or Git mutations

## 1. Frozen obligation and scope

For each of the two paired expression-ascription programs in
[recursive PUSH source construction](../progress/2026-10-10-recursive-push-source-invariant.md),
normal source construction must emit the live contextual relation required by
[the reviewed count-image proof](2026-10-12-contextual-cycle-summary-proof.md)
and connect its actual contributions to the matching output/POP consumers,
preserving source scopes, attachment identity, operation order, shared inputs,
provider/origin evidence, and separate residual constructor lineage.

The original programs are:

```yulang
act io:
  pub ping: () -> ()

my witness = ((\x -> io::ping ()) as (int -> [io; 't] ())) as (int -> [; 'e] ())
```

```yulang
act io:
  pub ping: () -> ()

my witness = ((\x -> { io::ping (); \y -> io::ping () }) as (int -> [io; 't] (int -> [; 'h] ()))) as (int -> [; 'e] (int -> [; 'e] ()))
```

Retain the historical binders: shared actual provider Value `V`; first
annotation's fresh return-Effect owner `r`; distinct written tail `t`;
second annotation's symbolic owner `e`; nested first annotation's distinct
inner owner `h`; first concrete attachment instance `i`; resolved nullary
family `S={io}`; each actual operation contribution `c` and its origin
`o(c)`. The nested operation occurrences remain separate contributions even
though their nominal family agrees. The historical primitive component is
`r --PUSH_i[S]--> e --I--> r`, with `r <--> t` identity aliases;
the nested component additionally has `h --POP_i--> e --I--> h`.

The required conclusion covers every finite replay history and every actual
downstream continuation in these complete source components, with its actual
sharing and observations. It cannot be replaced by existence of a weight
handle, a detached algebra value, independent marginal witnesses, or an
assumed endpoint correspondence. The pre-generalization Oracle constructor
result does not itself prove Y3 admission or exported output.

Authority is contextual attachment/admission §§3–6, annotation effect hygiene
§§1–4, residual lineage selection, and the top-level inference principles.
The latter supersede unconditional full rollback requirements. No arbitrary
negative-formal admission, new source restriction, complete Call weakening,
callback output oracle, or production promotion is part of this packet.
The older contextual-effect-path note's callback expected scheme is retracted
by the governing hygiene record and is not used.

## 2. Strongest exact prefix at the actual owners

Assume the real HIR for either displayed program is formed and its ordinary
candidate constructors reach the cited calls successfully. This is a condition
on the prefix derivation, not a claim of an executed successful source run.

1. `yu-hir/module/local_source.rs:518` retains each ascription occurrence and
   clones its existing lexical scope. `source_annotation.rs:508–565` retains
   each exact row position, resolved effect operand, and written variable.
   The top-level initializer has Definition scope; the inner block scope does
   not replace the enclosing ascriptions' scope.
2. `candidate_source.rs:223–239` peels Ascription/Group children to the actual
   endpoint before scheduling. Both ascriptions therefore target the same
   provider endpoint. Their distinct source occurrences and annotations are
   preserved; no intermediate facade or scheme use is introduced.
3. `candidate_expression_ascription` at `candidate_effect.rs:1194–1199`
   passes that endpoint as both endpoints to `candidate_annotation_pair`.
   The latter constructs the negative signature first, then the positive
   signature, with one shared per-pair view map; it admits
   `V+ <: A-` and `A+ <: V-` at source slots 45 and 46, and similarly
   for `B`. Its computation-effect helper adds no root-row check to these
   outer Function annotations.
4. At the exact covariant row `[io; 't]`,
   `candidate_signature_effect:1513–1577` resolves the scoped tail `t`,
   creates one view keyed by that row's exact position, and uses it on both
   signature polarities. The actual ports are fresh rows
   `a^-` and `a^+`, with negative
   `a^- <: Allowance(view_A)` and positive
   `Support(view_A) <: a^+` bounds. The view's tail is `t`.
   These ports must not silently be renamed to the single Oracle owner `r`.
5. `candidate_signature_view:758–765` calls `source_weight` even though
   this annotation has a symbolic tail: its attachment source is present.
   The retained weight has the annotation owner, exact row position, resolved
   `{io}`, composed positive polarity, lexical scope, and member ordinal 0.
   Its LocalWeightId supplies one retained set identity. The positive/negative
   signature views share that same weight, rather than selecting two grants.
6. The symbolic rows `[; 'e]` also use the covariant view constructor on
   this ascription route. They retain their scoped `e` tail with fresh
   positive/negative ports and an empty allowed set. A retained source-weight
   handle there is not another emitted PUSH. In the nested second annotation,
   both written `'e` occurrences use the same scoped variable lookup
   (`candidate_formal_effect_variable:979`), while their distinct row
   positions retain distinct views.

This prefix establishes actual retained source preparation and exact provider/
tail sharing at those constructors. It does not establish the Oracle primitive
cycle or a live residual recipe. `admit_candidate_value_link`
(`candidate_scheme.rs:1337`) invokes ordinary constraint processing
synchronously; the source executor completes one action before the next.
The Oracle argument that both annotations exist before its enclosing queued
drain cannot be imported as a Y3 scheduling theorem.

## 3. The decisive failure at source_weight

At `candidate_context.rs:2173–2196`, the authentic `source_weight` call
constructs:

```text
LocalWeight {
    left_word: [],
    right_pops: [],
    allowed: resolved members,
    boundary, owner, position,
    attachment: retained polarity/scope/ordinals,
}
```

The live word fields have types `[(); 0]` (`:115–118`).
For the nonempty positive concrete set, `AttachmentSet.unit_push` is
`Some(SourceUnitPush)`; this is explicitly dormant preparation
(`:126–135,2187`). The live constructor neither inserts an operation into
a word nor returns a ContextExpr/RelationId.

There is a second direct obstruction on precisely these source rows:
`candidate_signature_view` sets `closed_weight=None` whenever the tail
exists. `candidate_context_source:2483–2495` consults only an upper
Allowance's `closed_weight` when making a source PrefixLeft node.
It does not consult the open view's source-weight PUSH marker. Consequently
this exact `[io; 't]` source preparation cannot seed the required live
`PUSH_i[S]` relation through that function.

The available adapter `materialize_unit_push:2200–2220` copies the members
to a `DetachedWeight` with one detached PUSH. Its type, return value, and
owning comment explicitly exclude a live ContextExpr, relation, bound,
registration, or executable local word. `evaluate_context:1487` accepts
externally supplied detached weights; it has no source consumer. Neither
operation discharges the missing premise.

A static closure argument also excludes discovering that PUSH later within
the inspected route. Source-seeded contexts are identity or PrefixLeft of
zero-word closed filters. Function-port admission `:2559–2605` preserves
result contexts and swaps argument contexts; ordered bound replay
`:2911–2970` combines existing lower/upper contexts. Transport and
`rename_fresh_contexts:1270–1365` reuse or rename those existing nodes and
their weight handles. None reads the dormant unit marker to introduce a
nonzero live word. Checking/discharge `:2610–2810` accepts the zero-word
filter fragment, validates the closed-weight receiver, and retains/discharges
its checks. These operations cannot create the missing source PUSH from
identities and zero-word filters.

This is a bounded source-code derivation of absence of the required emission
on the named candidate route, not a global audit of every compiler mechanism,
and not an executed source rejection. It refutes the claim that the inspected
baseline already supplies this operational bridge. It does not refute the
approved semantics or either reviewed mathematical count image.

## 4. Actual consumer seam and lineage boundary

The original Oracle owner couples its entry and output operations:
`annotation/constraints.rs:363–389` wraps the positive returned Value
with the return-effect's NonSubtract predicates; `:424–470` builds the
positive stack and filtered negative port. The reviewed nested circuit's
left POP comes from normalizing that actual returned-Value wrapper, rather
than arbitrarily appending POP to the effect row.

The current `candidate_signature_value:1397–1443` directly constructs
the positive/negative Function from its four ports. It emits no matching
returned-Value POP wrapper. Actual Function dispatch lives in
`lib.rs:12496–12556,12641–12669`, using
`candidate_function_port_admit`; the result Value and result Effect preserve
the parent's retained context. That consumer cannot recover a missing
source-owned POP from a nominal family, row equality, or the weight handle.

The current concrete consumer is
`candidate_check_effect_operand:889–959`: Support emits distinct
AnnotationMember operands and its tail; Contribution/AnnotationMember against
Allowance checks resolved membership and forwards an unaccepted member into
the view's tail. This is a real consumer of covariant Support/Allowance.
It is not a constructor of the selected attachment-qualified residual gamma,
its reverse feedback, or matching output POP.

The retained-graph consumer
`candidate_scheme.rs:445–456,1047–1107` captures EffectOperand and tail
coordinates and reconstructs mapped views/context handles.
`CandidateInference::export` (`shadow_apply.rs:121–148`) exports that
private graph after conflict checks. Graph retention/export is not the missing
subtraction/output discharge. No residual lineage has been constructed by
the inspected entry-to-source_weight prefix, so there is no justified lineage
map from that prefix to an actual POP/output consumer.

The historical output distinction remains required:
Oracle `compact/collect/mod.rs:1019–1043` tests `cancelled.contains(fact.id)`;
`constraints/row_effect.rs:1190–1244` transforms retained family payloads
while keeping IDs/counts. An active-only summary would not cover these
observations. These historical consumers motivate the exact bridge, but do not
establish that current graph export implements it.

## 5. Minimized unresolved premise and economy audit

The first absent premise is exactly:

> At the first ascription's covariant `[io; 't]` row, the retained
> source-owned attachment set produces a live unit left-PUSH operation on
> the actual paired return-Effect construction, with an established mapping
> to the reviewed `r/e/t` circuit; the matching returned-Value/output POP
> and each residual recipe retain that same source attachment and separate
> constructor lineage through actual replay and discharge.

Its construction owners are `candidate_signature_effect` /
`candidate_signature_view` → `source_weight`; the live admission/operation
owners are `candidate_context_source` and `candidate_context_execute`.
Its returned-Value/POP owners are `candidate_signature_value`,
Function dispatch and `candidate_function_port_admit`. Concrete residual
consumption belongs at the actual Effect operand/bound consumer seam, with
capture/export correspondence at `candidate_scheme` /
`CandidateInference::export`. No `candidate_constraint.rs` exists in this
baseline; ordinary dispatch/bound replay live in `lib.rs`,
`candidate_extrusion.rs`, and `candidate_context.rs`.

The reviewed algebraic/count-image attempt and this constructor trace leave
the same source premise open. The obligation is A/B: safe hygienic output
and intended ordinary inference. Source metadata already knows occurrence,
polarity, resolved members, scope, and provider endpoint; reconstructing a
live grant/lineage from equality or successful export would add D debt.
The gap is an absent coupled operation/consumer, not a missing same-key
fresh-map lemma. No third equivalent algebraic attempt, new semantic layer,
or obligation reclassification is proposed.

Next action: the primary should resolve this exact existing construction/
consumer bridge under its approved internal gate and current proof-first
authority, keeping source/output, complete Call, hygiene, soundness,
principality and production gates OPEN.

## 6. Checks, runtime and commit packet

Checks: narrow `rg`/`sed` constructor/consumer reads; pinned Oracle
`git show` for the entry, returned-Value and output consumers; read-only
branch/HEAD/status; SHA-256 and byte comparison of the 18 dependencies below
against the assigned baseline; leased-note whitespace inspection and final
dependency revalidation. No builds, tests, probes, benchmarks, Git mutations,
children, or writes outside this lease. One lightweight command at a time
during source derivation; independent initial documentary reads were batched.
Measurement samples and verification workloads: zero. Wall time and peak
RAM were not measured. The primary remains verification/integration owner.

Requested routing: ordinary prover, configured `gpt-6.1-sol/high`, no role
model/effort pin. Observed runtime model/effort: unavailable, unknown.
No Astra, routing override, or reload is claimed. No independent review of
this artifact has occurred; the producer does not certify it.

Exact leased path: `notes/theory/2026-10-12-contextual-live-push-prover.md`.
Baseline: `7aeeb477257e030c218fbba23ed1e60c32d541cb`.
Proposed checkpoint message:
`research: pin contextual live PUSH constructor and output obstruction`.
Shared-record deltas left for the primary/curator: link the constructor prefix,
record the exact missing entry/POP/residual consumer seam, retain all parent
gates OPEN. No task/index/theory-status/question file was changed.

Direct dependency SHA-256 at read/freeze:

```text
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  notes/design/2026-10-10-contextual-attachment-admission-design.md
503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98  notes/design/2026-10-10-contextual-residual-lineage-selection.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
6e5561c8614148a8c19c72231cecb9706a64757c58d8fae7a23199591cc387c1  notes/theory/2026-10-12-contextual-cycle-summary-proof.md
fb7793967fd9e5aa1610c4b1bca5686247c1744c04bff149c107afb36e343790  notes/progress/2026-10-10-recursive-push-source-invariant.md
0091c38913fcf77b31f56a06e3be4b45097746c48e7c20729f3e708d6d5a6f8a  notes/progress/2026-10-10-recursive-push-results.md
346c6dd86e3c3b6da34dbf15939f78a322420b90869409188f11fe4d7316aab4  notes/progress/2026-10-10-contextual-effect-path-theorem.md
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df  crates/yu-solver/src/candidate_effect.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411  crates/yu-solver/src/shadow_apply.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb  crates/yu-hir/src/module/source_annotation.rs
```

Changed dependency hashes: none. All 18 dependencies matched the assigned
baseline and were unchanged at final revalidation after HEAD moved to
`8d2582f93c659677ebfb277fae1d55d5d159a4b6`.
Unverified scope: actual parsing/execution of these
sources, complete Y3 provider/concrete-lower admission, complete source SCC
recognition, live PUSH/POP/residual construction, all future-lower/output
consumers, generalization, qualified intrusion, lifecycle certification,
complete Call, whole-source soundness/principality, and F5 replacement.

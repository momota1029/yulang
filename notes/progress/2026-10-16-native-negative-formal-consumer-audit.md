# Native negative concrete formals: constructor and consumer audit

Status: independently reviewed complementary static source/consumer evidence.
Baseline: primary-pinned `2140859b1`; no Git inspection or mutation.
Exclusive lease: this file. No implementation or semantic authority.
Independent semantic/source-native review: checked_result_semantics, CLEAN
at producer SHA-256 `03ce2a99437b4b29d1b913469afd268f4fad35d7da6db6de0cc88eab7a527a70`.
The primary accepts only the bounded constructor/consumer characterization
and specified shortcut obstruction, with all native/source parent gates OPEN.

## 1. Objective and governing source

Audit an OPEN native effect coordinate carrying contravariant concrete local
permission, preserving original source positions, composed polarity, shared
variables/tails, resolved invariant family arguments and correlated Function
fields. This is complementary to the independent constructive formal-pair lane;
that lane's live artifact was not read.

[Annotation hygiene](../design/2026-10-10-annotation-effect-hygiene-integration.md)
sections1/1.1/1.2 distinguishes local subtraction permission, constraint-derived
inflow and the residual produced by an actual handler. In particular, a negative
`[signal]` does not exclude otherwise compatible additional `write`, and does
not independently create either an inflow member or a subtraction event.

The selected [known Function first-call profile](../design/2026-10-16-known-function-first-call-profile.md)
retains nested occurrences at their own paths; nested Ctrl is not outer-call
permission. Complete native profile/handling correspondence remains OPEN.

Claim class: bounded characterization of actual constructors, validators and
consumers, plus falsification of specified reuse shortcuts. No source-qualified
counterexample to the original all-provider theorem, complete source acceptance,
native execution result or chosen implementation is claimed.

## 2. Authentic occurrence and current admission boundary

For the original formal

```text
receive(f : Unit -> alpha+)
alpha+ = ([ctrl] Unit) -> [ctrl] Int
```

the formal constructor starts with composed variance Negative. Outer result
preserves that sign; the inner Function argument reverses it and inner result
preserves it. Thus the inner argument-effect Ctrl and inner result-effect Ctrl
are DIFFERENT source occurrences with Positive and Negative composed variance,
respectively. Their equality as nominal effects cannot identify their roles.

Actual owners in `crates/yu-solver/src/`:

| Owner | Actual behavior |
| --- | --- |
| `candidate_source.rs:423–425,457–462` | Formal preflight recursively rejects the negative concrete inner result row. |
| `candidate_effect.rs:1207,1119–1140` | Formal pair construction also rejects negative concrete rows before completing the paired target; Function arguments reverse variance. |
| `candidate_effect.rs:1145–1161` | Omitted and singleton symbolic ports use shared rows; concrete paired views are constructed only at Positive variance. |
| `candidate_effect.rs:1626–1656` | General signature-effect construction likewise rejects negative concrete atoms; negative symbolic tails stay connected. |

These are private candidate availability boundaries, not source-language
rejections. The proposed shortcut branches below are NOT current executed routes.

## 3. What the existing view can retain

`candidate_effect.rs:172–180` stores owner, exact source position, resolved
members, optional tail, provenance, `source_weight` and `closed_weight`.
`candidate_context.rs:126–139,2401–2421` can retain an AttachmentSource with
either composed polarity, original lexical scope and member ordinals. This
is positive retention evidence: the data format does not forbid recording a
negative source occurrence on an open-tailed view.

Copying is also explicit. `candidate_copy_effect_view:891–914` validates the
original payload, preserves source polarity/scope, owner/position and all
resolved members, and accepts the mapped tail. `candidate_scheme.rs:529–534,
1173–1189,1216–1229` retains endpoint polarity, maps the tail through the joint
FreshUse row map, shares the copied view through its per-use view map, and
validates original and copied payloads. No text/family-name reconstruction is
needed on these existing paths.

This does NOT establish a permission consumer. In particular, retaining
AttachmentSource is not an executable grant or actual subtraction.

## 4. The decisive closedness invariant

The existing View API couples tail absence to executable closedness:

```text
candidate_signature_view:777–790
  source_weight exists for an annotation with no tail or AttachmentSource;
  closed_weight = source_weight exactly when tail is None.

validate_payload_view, candidate_context.rs:1626–1630
  requires closed_weight == tail.is_none().then_some(source_weight).
```

The validator does not branch on composed source polarity. Consequently a
permission occurrence with no written symbolic tail cannot reuse that API by
merely suppressing `closed_weight`: copy/FreshUse validation would reject that
state. Introducing a fresh tail avoids this invariant only by adding an ACTUAL
row coordinate and its constraint routing, not by recording inert permission.
This is a concrete representation/consumer contract, not evidence that an
alternative representation is impossible or selected.

## 5. Actual executable reads and the shortcut discriminator

| Consumer | Executable meaning/read |
| --- | --- |
| `candidate_check_effect_operand:980–1001` | Support expands every declared member as an AnnotationMember LOWER operand and forwards its tail. |
| Same function:1004–1034 | Allowance accepts exact resolved members; a nonmember flows to the actual tail, or records an effect mismatch when there is no tail. |
| `candidate_context_source:2859–2869` | An upper Allowance with `closed_weight` produces PrefixLeft; other pairs get Identity. |
| `candidate_context_execute_relation:3227–3286` | Zero-word filters execute those Allowance checks/registrations. They do not inspect AttachmentSource polarity to switch to local permission semantics. |
| `candidate_function_port_admit:3020–3063` | Argument/AE Swap inherited context; Result/RE preserve it; child-local wrapper checks precede the inherited operation. Source occurrence is not replaced by a same-family row. |
| `candidate_source.rs:870–885` | Catch forwards the whole scrutinee effect and joins arm effects. This owner performs no permission-qualified subtraction. |
| `candidate_scope.rs:1–4` | Scope transformers change route tags/protection scopes; capture grants and effect members are expressly outside their state. |

The source-approved discriminator is the annotation-policy section1.1 formal
`thunk:[signal]Int` (or its callback counterpart) receiving an otherwise
compatible `[signal,write]Int` computation. The source permits local handling
of signal and requires write to survive. Reusing the positive signature branch
for its negative occurrence creates Support/Allowance by
`candidate_signature_effect:1658–1695`. With no tail, its Allowance rejects a
write operand by the concrete consumer above. The actual Function ResultEffect
dispatcher (`lib.rs:12659–12664`) forwards a provider lower into that upper;
context discharge does not turn the mismatch into a local permission check.
This refutes that CLOSED-ALLOWANCE reuse as a representation of the selected
negative input policy whenever the authentic write inflow reaches this bound.
It is not a completed current-compiler/source-program counterexample: current
preflight already defers the negative annotation and no experiment was run.

An open Allowance is not the same shortcut: it routes unmatched write into its
EXISTING tail. That tail's source owner, equations and later uses must remain
correct; an arbitrary new tail cannot stand in for a named shared variable.
The paired Support side also deliberately supplies lower type operands. Their
role must be justified at that negative occurrence rather than called actual
emission or residual merely because Support is present. Covariant target
publication elsewhere remains legitimate under the settled annotation law.

The alternative “drop the concrete atoms and return a shared fresh row” avoids
this closed cap, but supplies no executable permission through these existing
consumers. Original HIR/Action annotations remain available
(`candidate_source.rs:729–745`); this is NOT a proof that permission evidence is
irretrievably lost. A future consumer could use that retained source. The
current native handling obligation is simply not discharged by the row alone.
The existing root-computation formal owner makes the same separation explicitly:
`candidate_formal_entry_annotation:1176–1188` connects a symbolic tail and keeps
the concrete annotation for later handling integration without installing a cap.

## 6. Next owning responsibility and limits

The next native constructor/consumer packet must establish how the original
negative concrete occurrence supplies local permission at its actual receiving
path while its effect coordinate remains open, including shared-tail equations
and actual handler eligibility/residual lineage. It must account for the
View tail/closedness validator and all copy/context consumers above. This is
not a request to select a representation, add an eager semantic query, bypass
scoped guards, alter source annotations, or infer execution behavior.

Unknown or unresolved variables/filters remain ordinary constrained coordinates.
No all-source profile supply, general subtraction, same-z result theorem,
soundness/principality or production gate closes. No missing stored field alone
was treated as semantic loss, and no private-test construction was treated as
accepted source.

## 7. Freeze and verification

Checks: bounded `rg`, `nl`, and SHA-256 reads; local Markdown link/fence and
trailing-whitespace inspection after writing. No Git, compiler edit, test/build,
probe, delegation, live proof read or shared-record change. One static leaf,
approximately 5 minutes; CPU/RAM unmeasured, zero executable samples/seeds.
Independent review and primary acceptance are recorded above.

Frozen dependencies:

```text
44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9  crates/yu-solver/src/candidate_effect.rs
72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6  crates/yu-solver/src/candidate_context.rs
2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e  crates/yu-solver/src/candidate_scheme.rs
efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38  crates/yu-solver/src/candidate_source.rs
9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a  crates/yu-solver/src/candidate_scope.rs
2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f  crates/yu-solver/src/lib.rs
a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
b779ba779b66515eddb7e44ba1d0772a6853e69a1aa13a6c4528dbd8ea0852a1  notes/design/2026-10-16-known-function-first-call-profile.md
```

Commit packet: this leased file only; baseline `2140859b1`; research evidence,
independently reviewed within the bounded scope above. Suggested checkpoint: `research: audit negative formal view consumers and open permission constraints`.
Primary retains shared task/theory/index updates and every original parent gate.

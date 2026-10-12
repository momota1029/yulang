# Formal Function effect selector: entry-field falsification audit

Date: 2026-10-13
Status: frozen non-authoritative research; bounded independent review passed
Claim class: bounded source audit and conditional discriminator, not a source counterexample
Pinned baseline: `4555abdd46ef3c052cd4f48198beaa6898657ae5`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file; no descendants, compiler edits or Git mutations
Original annotation law, H, complete Call, soundness, principality and F5: OPEN

## Objective and result

Audit whether adopted source clauses determine the map from a written negative
Function result-effect selector to the actual formal callable's dependent
observation field. The reviewed [precursor](../theory/2026-10-13-negative-formal-annotation-source-rule-construction.md)
§§3–4 constructs source selectors, polarity, members and scope, but leaves
that semantic correspondence unconstructed. The formal's later supplied
callable is distinct from the enclosing Lambda that owns its annotation.

The inspected clauses require entry effects to remain in complete invocation
observations. They refute replacing complete invocation by body/native return.
They do **not** determine whether the written selector's subtraction permission
governs an entry contribution. Both proposed permission maps remain open in
this bounded cone when B retains entry as a separate checked observation.
This is not a proof that both extend to globally valid semantics.

## Exact sources and attempted falsifiers

| Source and section | Established content; limit for this question |
| --- | --- |
| [Annotation policy](../design/2026-10-10-annotation-effect-hygiene-integration.md) §§1,4 | Composed-negative `[E]` permits function-local subtraction at its actual position; unrelated contributions and symbolic links survive. It does not identify that position with an entry field. |
| [Function call-view direction](../design/2026-10-05-inferred-function-call-views.md) §§1.1,2,4,5.3 | Written contracts differ from inferred/internal views; source positions persist. §4 expressly leaves which contribution is governed and when removal is realized to be specified. |
| [Contextual Function membership](../design/2026-10-08-contextual-function-membership-definition.md) §2; selected [construction](../theory/2026-10-08-call-semantic-input-realization.md) §§2,3.1 | Same actual provider accepts every independent checked challenge and all its complete/pending observations satisfy the whole descriptor. Complete descriptor admission/observation relations remain independently interpreted inputs. No written negative-port projection is supplied. |
| [Source-interface selection](../design/2026-10-08-call-source-interface-definition.md) §§2–4; selected [IF constructors](../theory/2026-10-08-call-source-interface-construction.md) §§3.1–3.3,4,5 “Producer and entry”,7 “Receiver pending” | Entry-Value retains receipt, one-layer Force, rebind and body. Entry/body/native-return/consumer/complete-invocation subinterfaces receive distinct inclusions. Slots preserve actual contracts; they grant no permission and do not equate body with invocation. |
| [Native Source-Generalize selection](../design/2026-10-08-source-generalize-definition.md) §§2–3; selected [rules](../theory/2026-10-08-source-generalize-definition-and-proof.md) §2 L3–L4, §§3.1–3.2 | Parameter/Lambda/Call retain actual entry and complete invocation; Function checking proves whole observation inclusion on the checked domain for the same callable. Annotation realization remains a genuine local premise, not a consequence of retaining the slots. |
| [Charter](../design/2026-09-29-scc-intrusion-redesign-charter.md) §§16,21,24 | Recorded user entry decisions: a Value parameter forces inside its actual invocation even if unused; pure body does not erase entry effects. §24 replaces universal Handler classification while retaining entry mechanics. The charter's wider status remains Reviewed. |
| [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md) §9 “Entry is part of the interface, even with a pure body” | Explicit Request/Bind reduction separates `J_arg`, `J_body`, `J_call`; its example distinguishes effectful entry from pure body. Wider core remains Draft; only selected source premises are used through the definitions above. |
| [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md) §§3.1–3.3,4 | Separates emission, admission and complete provider envelope. Reviewed conditional package, not a newly adopted concrete descriptor grammar. |

Candidate B would contradict these sources if it meant that entry is absent
from complete membership/checking, that a pure body suppresses entry, or that
the checking view changes the supplied callable's actual role/entry. The
assigned B instead keeps entry separate and asks which field the permission
governs. None of those contradictions follows from that B.

Candidate A is consistent with retaining entry in complete invocation, but
that fact alone does not prove that a written selector governs every constituent
of that invocation. No source slot inclusion licenses subtraction. Function
membership's whole-observation quantifier does not settle the projection of
the written annotation into that observation.

## Small conditional discriminator

Fix one original environment `X`, actual formal callable `U`, independently
admitted complete challenge `chi`, and one actual concrete contribution `w_E`.
Keep the same actual provider, scope, receipt, carrier, world and operation
instance in both proposed interpretations. Required hypotheses are:

1. `U` has independently established Value entry and constant Unit body;
   its body returns without introducing or consuming `E`.
2. `chi` independently admits carrier `t`. Its designated execution exposes
   one request carrying `w_E`, then after an independently typed response
   returns an ordinary value. The complete context and valid primitive law
   precede checking of `U` at the proposed annotation; admission is not inferred
   from output safety, permission, row support or successful comparison.
3. The actual formal annotation has a resolved composed-negative result-effect
   occurrence `[E]`. There is no sibling contribution or second occurrence.
4. For an observable removal conclusion, additionally supply the original
   local checking/realization and handler/receiver eligibility laws. They are
   not supplied by this audit.

Constructor reduction, using the selected Value-entry and original Bind laws:

```text
Force(t) = Request(q_E, C, k)
ExecuteCallable(U,t) = Force(t) >>= (a,C'). Rebind(a,C'); Return(Unit,C')
                    = Request(q_E,C,(r,C'). k(r,C') >>= rebind/body/return)
```

Thus `w_E` is an actual entry observation of the complete invocation; the
post-entry constant body introduces no `E`. This is a conditional derivation
under hypotheses 1–3, not an independently constructed admission certificate
or successful negative-concrete formal annotation application.

| Proposed field interpretation | Permission on this same entry `w_E` |
| --- | --- |
| A: the written selector governs complete invocation, including this entry crossing | Applicable at that crossing, subject to original realization. |
| B: the selector governs post-entry body/native-return; entry is separate | Not supplied by this occurrence; entry remains in complete checking/output. |

The immediate discriminator is permission applicability. If the genuine
local realization realizes that permission on `w_E`, A may remove that
contribution while B must retain it absent another legitimate permission.
Permission alone guarantees neither subtraction nor runtime handler selection.
If removal is not realized, the two may have identical outward requests.
Neither map may delete an independent sibling with the same family.

The witness has one supplied callable, one invocation, one carrier request,
one contribution and a constant body. It needs no recursion, copy, adapter,
nested Function or residual cycle. Removing the request or using retained
entry with this constant body removes the distinction. It is minimized for
this phase distinction, not by an exhaustive source search. These admitted
interfaces are hypotheses: no raw source spelling or full admission proof is
claimed. The selected Value-entry clauses support the operational reduction;
they do not establish the annotated-formal law at issue.

## Actual code owners and unavailable operational oracle

At the pinned revision, `source_annotation.rs:349,438` retains annotation
owner/position and Function children; `local_source.rs:289` retains the actual
parameter binder, annotation and scope. They supply syntactic selectors.
`candidate_effect.rs::candidate_formal_pair:1034` reverses argument polarity
and preserves result polarity; `candidate_formal_effect_port:1054` builds its
supported pairs. Its negative-concrete branch is rejected before formal links
and `formal_domains` installation (`:1094–1107`), and
`candidate_source.rs::preflight:97` / `preflight_formal:117` blocks that route
independently. These are candidate availability facts, not language rejection.

`lib.rs::admit_lambda_fact:11233` supplies the enclosing Lambda's separate
entry/body effects and links both into its returned effect before forming
the positive Function. `shadow_apply.rs:1343–1385` creates the negative
Function demand with separate argument and fresh invocation effect. These
owners corroborate the entry/body/invocation distinction; they do not implement
the missing negative annotation map for the actual callable supplied to the
formal. Removing the guard would not prove that map.

There was no executable oracle or checker. The conditional witness and both
candidate maps share the admitted primitive/context and original entry/Bind
laws. Direct adopted clauses are independent of the reviewed precursor for
the entry reduction; neither the precursor nor current candidate guards are
independent validation of annotation permission incidence.

## Snapshot, coverage and recommendation

Reads used `git show 4555abdd4:<path>`; no mutable task record is evidence.
Current HEAD had advanced to `06a40496324ce78be64db5780a11fd753853f44b` at
initial inspection. Complete-byte comparisons of these 19 direct dependencies
matched the pinned revision; baseline SHA-256 values follow.

| Dependency | SHA-256 |
| --- | --- |
| `notes/theory/2026-10-13-negative-formal-annotation-source-rule-construction.md` | `bce702b9bbe8414e3094f97355e5b8a0d696bec9160a916790dc9118f3d532af` |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| `notes/theory/2026-10-08-call-semantic-input-realization.md` | `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a` |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `crates/yu-hir/src/module/source_annotation.rs` | `a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/shadow_apply.rs` | `cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |

Coverage: bounded governing clauses and named code ranges, not a repository-wide
absence search. No tests, builds, probes, mutations, seeds/ranges or measurements
ran. Commands were static `rg`, `git show`, read-only revision/status queries
and one-process Python byte/hash comparisons; note integrity checks are in the
handoff. Peak RAM/CPU and elapsed wall time were not measured. No heavy process,
child delegation, network operation or configuration change occurred.

Unverified: actual complete admission for this annotated formal, annotation
checking/exposed correspondence and local realization, contribution incidence,
production conformance, Call/output/residual transport, all source/copy paths,
H, soundness, principality and F5. Neither A nor B is adopted or globally
validated. Stop rather than repeat another permission-only toy probe.

Recommended next action: primary obtains the independently reviewed exact
Parameter/Function clause determining this selector's applicability to the
entry contribution. If the constructive lane cannot derive it from existing
authority, present this permission-applicability difference and its conditional
removal consequence through the existing user-decision path; do not infer a
choice from complete-invocation membership alone.

## Commit packet

- Exact leased path: `notes/progress/2026-10-13-formal-entry-effect-field-falsification.md`.
- Baseline: `4555abdd46ef3c052cd4f48198beaa6898657ae5`.
- Changed dependency hashes: none among the 19 compared direct inputs above.
- Review status: frozen non-authoritative bounded source audit; one independent `compiler_referee` passed the clause/quantifier scope with no findings. No original theorem or admission gate closed.
- Checks already run: pinned static source/rule reads and complete-byte SHA-256 comparisons. Zero builds/tests/probes/measurements/Git mutations.
- Proposed checkpoint message: `research: audit formal Function permission maps at effectful entry`.
- Shared deltas for primary/curator: distinguish mandatory complete entry accounting from unresolved written-port permission mapping; retain the exact annotation law and dependent H/Call/conformance gates OPEN; record the conditional discriminator and absent authentic annotated-formal admission/realization. No shared records or question bundles edited.

### Independent review

The `compiler_referee` independently checked that complete invocation
membership retains entry observations without establishing the written
negative-port permission projection, and that the conditional discriminator
keeps admission, realization and the parent challenge quantifier separate.
No blocking, major or minor finding remained in that scope. The reviewer
checked all 13 document dependency hashes; compiler-owner assertions and six
code hashes, operational conformance, authentic annotated-formal
admission/realization, broader source/copy/Call paths, and global semantics
remain outside review. The bounded audit and original gates remain OPEN.

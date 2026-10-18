# Fixed-c contribution: current source/native owner map

Date: 2026-10-18  
Sprint: `choose-primitive-license-and-source-map-20261018-r13`, revision 1  
Contract SHA-256: `9ef858b0a909d4db6842d985f0cca05fa7496da328940a3e4364a7c09ae83e2c`  
Baseline: `2a3f2a47d5013761f0e0717b0c6073c54c62d36`  
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, fixed `c`, unchanged source domain and quantifiers; **OPEN / closure 0**  
Outcome: `NO_SAFE_CODE_SLICE` for authentic fixed-c contribution lineage

## Result

Current HIR and candidate solver owners preserve source declarations,
annotations, effect families, operation signatures, candidate support views,
effect-row operands, and diagnostic identity. They do not construct or
transport the mathematical `DeclContribution(q,h,c;Omega,rho;d)` for the
parent's fixed `c`, its original governed-field correspondence, or the lawful
field action at the actual output of `A_decl`.

**`NO_SAFE_CODE_SLICE`.** The decisive mismatch is constructor identity and
meaning: the Rust `candidate_effect::Contribution` is a candidate effect-row
atom containing `(SourceEffectId, SourceNodeKey, instance ordinal)`. It is not
an original semantic contribution `c`, its `DeclContribution` derivation,
primitive license, full origin partition, dependent route, or output field
map. Existing consumers test effect-family membership against a candidate
annotation allowance. No inspected code has an `A_decl` producer/consumer or
corresponding actual returned-provider/scope field action.

The next unlock is a reviewed accepted proof input identifying the fixed
original `c` by inversion of its real constructor, with its exact catalogue
port, origin partition and route, independent license where that constructor
requires one, and its governed-field map at the actual complete `A_decl`
output. The map must preserve the same dependent tuple and all original
provider, scope, domain, admission, future and `G/R/W/Z` evidence. Then a fresh
lease can trace that same constructor and field through a concrete native
producer, propagation and actual consumer. No empty certificate or constructor
is proposed here.

## Governing mathematical constructor and fixed-c law

The adopted native formation contract and its reviewed incidence construction
separate four objects:

1. `PortProv(q,h;Omega,rho)` records the actual typed catalogue port and its
   original origin partition `Omega` and field/telescope map `rho`.
2. `DeclContribution(q,h,c;Omega,rho;d)` packages the already-fixed
   contribution `c` at that port under the actual source-clause constructor.
3. `PrimLicenseContribution(alpha,h,...)` and `PrimOrigin(intro_alpha,h)` are
   premises only after inversion reaches the genuine primitive constructor.
   A support slot, syntax declaration or matching endpoint supplies neither.
4. Root insertion is a separate receiver route. It appends the actual
   insertion map and changes only the receiver; it does not overwrite `Omega`,
   change an antecedent's original owner, or reclassify an imported field.

The other original cases remain distinct: operator image carries its actual
typing/license fields, complete operand interfaces and genuinely local
introductions; operand and reference preserve the child partition; Alt keeps
the actual branch and both complete schemas; Pair retains both licenses and
partitions on one shared tuple; Scope/Rename transport the whole package.
Thus no primitive-license premise can be demanded before constructor
inversion, and no composite antecedent can be flattened into a primitive leaf.

For this parent, `c` is fixed before the observation. A chosen `q_c`, fresh
Call contribution `c_e`, family ID, effect atom, or row endpoint cannot replace
it. The original declaration-completion tail is

```text
D_tail_src(r_resp,Cnow) = Return(r_resp,Cnow) >>= A_decl.
```

At an actual return from `A_decl`, use its actual complete output
`out(d_A) = (r_out,Cout)` and the original dependent substitution/field action
there. A responder proof at `(r_resp,Cnow)` transports only under the original
law. It cannot be cast to a different provider, world, scope or result
interface by shape or by the candidate solver's effect family. The `s1`
governed field and every original `W/Z` alternative remain. HIR source storage
is not itself this mathematical relation, and an actual source/native path
would need a typed map between them.

## Current HIR construction and transport

`crates/yu-hir/src/module/source_annotation.rs` is the source parser/former
for the current experimental effect/annotation data:

- `declarations` first creates a `SourceEffectId { module, declaration }`
  from the actual family source node and registers it in a spelling namespace.
  A second pass forms nullary `SourceOperationDeclaration`s, keyed by family
  and source declaration node, with declaration/name/signature source
  positions and a parsed signature. Parameterized operation declarations and
  unsupported/recovery-bearing shapes fail closed.
- `form` / `parse_annotation` retain the owning `SourceRootId`, annotation
  source position and parsed type tree. `parse_type_source` accepts the
  selected Unit/Int/Bool/Str/variable/Function forms and rows. `parse_row`
  resolves concrete effect names only when the namespace has one matching
  declaration; it retains concrete `SourceEffectId`s or one symbolic row
  variable and the row's source node key.
- These records authenticate source identities and a bounded syntax shape.
  They do not store semantic contribution `c`, primitive license evidence,
  `Omega`, constructor route, an `A_decl` result, dependent provider/scope
  action, or original `PortProv`/`rho`.

The exact current producer owners are `source_annotation.rs::declarations`
(`:135`), `form` (`:317`), `parse_annotation` (`:342`),
`parse_type_source` (`:409`) and `parse_row` (`:529`). A targeted `rg` over
these source/native owners found no code identifiers for `A_decl`,
`DeclContribution`, `PrimLicenseContribution`, `PortProv` or `PrimOrigin`.

This is important scope: a `SourceEffectId` identifies an effect-family
declaration, not a licensed contribution witness. A concrete row member names
the family; it is not a declaration-completion field proof.

## Candidate effect producer, propagation and consumer

The actual candidate path is private and effect-row specific:

| Owner | Actual construction/consumption | Difference from fixed-c law |
| --- | --- | --- |
| `candidate_source.rs::emit_candidate_source` (`:1018-1031`, `:1507`) | `LocalSourceForm::Operation` schedules `Action::Operation { declaration, owner, occurrence, target, level }`; annotation/ascription actions retain `SourceAnnotation`. This brings HIR source records to the candidate inference session. | The action records the source operation and occurrence but has no `DeclContribution`, original `c`, complete `A_decl`, or governed-field proof. |
| `candidate_effect.rs::candidate_operation` (`:844`) | Recursively builds a candidate value type from the operation's annotated signature and constrains it against the target at slot 42. `candidate_signature_value`/`candidate_signature_effect` (`:1610+`, `:1704`) preserve signature paths/maps; an operation-family support view is added only at the existing pointer-identified outer signature result-effect case. | Candidate function/effect structure and local support are not original complete declaration formation or an independent primitive contribution license. Signature pointer identity is a candidate construction guard, not an original field map. |
| `candidate_effect.rs::candidate_annotation` (`:1435-1457`) | Builds positive/exposed and negative/checking annotation views and adds ordinary value constraints. Root computation-effect rows constrain the actual computation effect. `View` stores owner, source position, allowed `SourceEffectId`s, tail and `ViewOrigin`; source-context weights are created only for eligible annotation views. | Annotation allowance and support are candidate effect-row structures. The original annotation rule, contribution licensing, fixed-c identity and `A_decl` output correspondence do not follow. |
| `candidate_effect::Contribution` / `candidate_effect_contribution` (`:149`, `:987-1009`) | Allocates an effect operand with `effect`, source `origin: SourceNodeKey`, and candidate-local `instance`; it returns `EffectEndpointKey::Contribution(id)`. Candidate scheme capture/FreshUse reads the stored effect and origin, then calls `candidate_effect_contribution` to allocate a fresh instance (`candidate_scheme.rs:1655-1659`; `candidate_effect.rs:999-1006`). It does not preserve the prior instance value. | No field carries `c`, `h`, `Omega`, `rho`, primitive `alpha`, `PrimLicenseContribution`, actual `A_decl` output, or full original semantics. Instance identity exists for candidate provenance/diagnostics, not theorem identity. |
| `candidate_extrusion::candidate_apply_effect` / `candidate_effect::candidate_check_effect_operand` (`candidate_extrusion.rs:944-962`, `candidate_effect.rs:1011`) | Propagates effect-row relations. A contribution/member against an allowance is accepted when its `SourceEffectId` is listed, forwarded to the row tail if present, or reported as an incompatible effect at that occurrence/cause. | This is the actual candidate consumer for an effect atom. It checks family inclusion/tail behavior; it does not prove original `L`, `A`, `DeclContribution`, a governed field, or execution/declaration completion. |
| `shadow_apply` observations / `candidate_receiver` | Observers expose contribution family, source origin and instance, or operation-interface member with declaration/owner/position/occurrence. `ReceivingResidualExperiment` can observe a bounded catch-result effect family. | These are candidate observations and a bounded receiver experiment. Neither selects the original fixed `c` nor consumes an original `A_decl` field proof. |

`candidate_effect` itself notes that a `FormalPermission` record (`:189`) is “local
source permission only” and not an arrival, provider, contribution or consumer
witness. Formal permissions are a distinct route from the `Contribution`
atoms. Neither one is an `A_decl` proof.

`candidate_signature_view` also distinguishes `ViewOrigin::Operation` from
`ViewOrigin::Annotation`; its source-weight/attachment setup is restricted by
view kind and row/tail. This internal candidate distinction does not implement
the mathematical constructor alternatives `Prim`, `Op`, `Ref`, `Alt`, `Pair`,
`Scope`, `Rename`, nor a typed map between them.

## Exact source/native gap and falsifiers

The HIR owner cannot establish original semantic attribution from syntax
identity alone. The solver owner receives source effect family IDs and
constructs effect constraints, but has no input that distinguishes the
parent's fixed `c` among possible contributions or carries its complete
constructor partition. The existing consumer sees only effect endpoint and
allowance data. `A_decl`'s complete output-dependent field map is absent from
both paths. This is a concrete producer/transport/consumer break, not a
negative proof that an original source derivation exists or fails.

The precise first missing code input is therefore an accepted derivation
`d:DeclContribution(q,h,c;Omega,rho)` for the fixed original `c`, coupled to
the original lawful `rho` action at the actual returning `A_decl` output. If
inversion proves the primitive case, it additionally needs that primitive's
actual `intro_alpha`, `PrimOrigin`, and `PrimLicenseContribution`. If
inversion yields another constructor, it needs that actual constructor and its
independent field/license premises instead. After that, a source-owner map must
identify which HIR/solver identity corresponds to that exact field and where
the actual consumer checks it. The current files cannot be modified to
approximate this input without inventing meaning.

Falsifier of `NO_SAFE_CODE_SLICE`: an already reviewed original proof input
instantiates the parent's fixed `c` and the actual `A_decl` output at the same
dependent indices, identifies the genuine `DeclContribution` constructor and
governed fields, and a trace through existing HIR/native fields proves those
exact identities reach a consumer without losing `Omega/rho`, output provider,
scope, license, domain, admission, future, or W/Z cases. Family equality,
an effect conflict test, a native instance ordinal, a candidate support
member, or a green test is not such a falsifier.

If a later accepted proof supplies that input, the smallest vertical lease
should begin at its actual source field constructor, follow source identity
through `candidate_effect` contribution/view construction, and end at the
consumer that checks the same mapped field. Its falsifier is any reachable
source path where the consumer sees a different `c`, tuple, output provider,
scope, field or license, or any original `W/Z` case loses its action. Until
that proof and map are reviewed, no source/native implementation step is
ready. No test or build was run in this read-only assignment.

## Prior evidence reused and limits

- r12 proof and closeout establish that no complete `Sigma_choose^0`,
  authentic `DeclContribution`, or governed-field map was derived; they locate
  the next required work at fixed `c` and actual `A_decl` output. This audit
  reuses that result and traces only the named current native owners.
- The adopted native signature/incidence documents provide an independently
  reviewed constructor grammar and correspondence for the selected native
  mathematical route. They explicitly state that compiler `SF`/`Build(G)` is
  separate, actual annotation interpretation and governed-port correspondence
  remain independent, and they grant no production implementation/cutover.
- The 2026-10-10 concrete annotation checkpoint establishes current bounded
  source annotation/effect-row behavior and its focused tests. It explicitly
  does not claim source operation execution production or semantic contribution
  issuance. The passing historical tests are not re-run here and are not proof
  of the current fixed-c theorem.
- The 2026-10-17 native field map and NPAIR native implementation readiness
  artifacts state that native contribution nodes preserve family/origin/
  instance and that capture/FreshUse remaps candidate graphs, but those facts
  do not authenticate the full source presentation or source-rule witnesses.
- r10's source/native probe hit a compile error at `candidate_effect.rs:2351`
  before test executable creation; direct test invocation count was zero.
  Therefore the proposed probe supplied no observed HIR or scheduled operation
  behavior. This audit does not treat it as validation.
- The 2026-10-17 operation-response proposal's source/native map distinguishes
  retained annotation AST and candidate signature recursion from the absent
  semantic default/admission, response realization and complete Function
  contract. Its limitations remain relevant; no unavailable primitive or
  composite law is inferred from it.

The fixed parent remains **OPEN / closure 0**. No source domain, accepted
meaning, diagnostics or inference behavior is changed by this audit.

# R116 conditional callable identity and role bridge

Status: **candidate conditional source-to-consumer derivation; fresh review pending**.
Sole author/writer: `/root/r116_method_proof`; no coauthors or descendants.
Assignment `R116-METHOD-PROOF`, artifact revision 1. Governing contract revision 3:
`tasks/agent-loop/sprints/method-role-and-approved-surface-20261019-r116-rev3.md`,
SHA-256 `0b9653736e84baa63a04a74bbc0b23742c17941be38b4cceede4cb91d0393ea5`.
Baseline: the contract's R114-closed workspace; no Git operation performed.

## Parent claim and finite source input

R100-P2-MEMBER requires the authentic selected implementation member's executable
binders, their original annotations, actual body and lexical environment. P3's
receiver-first ordinary Apply target and P4's complete candidate/runtime admission
remain separate. The exact accepted source is the contract's 148-byte LF fixture,
without final LF, SHA-256
`fb54857e70924c178842692d7cce1a9c35b7c2a55bceab78710889b913d7dfcb`:

```yu
role SecondInt {
    my second: int -> int -> int
}
impl int: SecondInt {
    my second self selected = selected
}
my answer = SecondInt::second 1 2
```

Consume R108's reviewed finite source-entry observation, rather than infer entry
from an assumed transition. It identifies the authentic ImplDeclaration at
`52..114`, nested member BindingStatement at `78..112`, ordered IdentifierPattern
binders `self` at `88..92` and `selected` at `93..101`, and the distinct body
IdentifierExpression `selected` at `104..112`. Same-parse keys and retained raw
positions distinguish these occurrences. R108 does not supply executable IDs.
R112's reviewed finite obstruction supplies the production failure below; this
note does not re-prove its full case analysis or rerun its historical evidence.

The approved role authority is **only charter §21**, explicitly a user source
decision and not compiler implementation approval. Its surrounding charter has
Reviewed status. An omitted or ordinary value annotation gives Value; an explicit
outer computation annotation gives Computation. Body usage or a solved empty row
does not choose the role. R85's positive role-call offer remains Draft/unadopted.

## Conditional bridge and exact hypotheses

For every successful invocation of the pinned callable formation and consuming
constructors satisfying H1–H4, the following preservation result holds. This
quantifies over a finite ordered vector supplied by that authentic callable
producer, within the owners' supported bounds; it does not quantify over arbitrary
source programs or assert that today's method producer supplies such a vector.

- **H1, authentic admission:** one Binding RootPlan and its DefinitionRootId are
  authentically admitted for the original member occurrence. The admitted vector
  and HirParameter vector have the same length and order. Each parameter has its
  own IdentifierPattern source key, spelling/range and original optional annotation;
  IDs are minted from this owner and their distinct ordinals. No substituted
  top-level binding or signature provides these facts.
- **H2, exact body/environment:** the original body is passed to LocalSource
  formation with its original namespace and lexical scope. For the R100 body,
  the vector is exactly receiver `self`, then `selected`, with neither annotation
  present, and the body is the original one-name OperatorChain. No intervening
  binder shadows that `selected` occurrence. This is a requirement on the missing
  member producer, not a reconstruction from spelling.
- **H3, successful formation/publication:** source keys belong to the same parse;
  recovery, supported-depth, allocation, annotation parsing and identity staging
  checks succeed; the resulting LocalSource is retained by that exact HIR owner.
  Success is an explicit premise, not a totality claim. For the two named formals,
  the owner-local limit of fewer than 128 formals is satisfied arithmetically.
- **H4, successful consumers:** candidate preflight/collection and RuntimeProgram
  admission succeed for this exact HIR-owned source, with the required root and
  occurrence ownership. Their full-module availability and later solver/machine
  execution are not consequences of H1–H3.

**Conclusion.** Formation retains the ordered parameter IDs, their source keys and
their own annotations in the nested Lambda carrier. The original body name resolves
to the selected parameter ID. Candidate formal registration/name endpoints and
runtime Lambda/Name instructions preserve that correspondence. Both consumers'
role classifiers equal the same function of that parameter's annotation:

```text
rho(p) = Computation  iff p.annotation exists and its ty.effects is Some(_)
         Value        otherwise.
```

In the conditional R100 instance both roles are Value. This establishes no `int`
endpoint, body-result typing, selected method target, execution or result `2`.

## Constructive owner correspondence

1. **Header to executable identity.** `module::plain_binding_header`
   (`module.rs:2937–3063`) extracts parameters in actual tail order, retaining each
   own IdentifierPattern key and optional annotation node. It accepts only its
   explicit supported simple patterns. `lower_plan` (`2099–2114`) enumerates that
   vector, creates `HirParameterId::new(definition_root, ordinal)`, and records each
   key using `HirSourceIdentity::record_parameter`. The ID stores owner and ordinal
   (`410–425`); the source map stores IdentifierPattern origin
   (`source_identity.rs:119–120`). Under H1, equal vector lengths prevent the later
   zip from silently omitting a formal. No general validation of arbitrary manually
   supplied vectors is asserted.

2. **Identity to ordered lexical carrier.** `local_source::form`
   (`local_source.rs:556–643`) starts at the supplied root, zips the parameter and
   admitted vectors, clones each ID, original key/range/spelling and parsed own
   annotation into LocalSourceParameter, pushes its Parameter resolution, and
   emits a Lambda whose body is the next slot. Induction on vector position yields
   `Lambda(p0, Lambda(p1, ... body))` in header order. Scope advances to the current
   parameter ID; `record_named_group` (`811–817`) retains ordered formal IDs and
   Lambda indices plus terminal body. This group is construction evidence only;
   it supplies no method-selection or receiver policy.

3. **Lexical resolution.** `Builder::push_binding` (`746–778`) records the prior
   latest entry and updates the spelling index to the new identity. `restore`
   (`779–790`) restores the predecessor or removes the name. Induction over these
   operations proves that latest points to the innermost active entry. For the
   exact two-formal body, distinct `self` and `selected` pushes leave selected's
   latest entry equal to Parameter(p1). The one-head OperatorChain reaches the
   original IdentifierExpression without adding a binder (`848–970`). Its Name
   branch (`1007–1040`) consults latest before the module namespace and clones
   that resolution. Thus it emits Parameter(p1), including in the presence of a
   same-spelled module definition. This is environment-based resolution; body and
   formal source occurrences remain distinct.

4. **Source provenance and publication.** `Builder::set` (`818–846`) records the
   expression's actual node key, occurrence, scope and form. The formal source key
   stays on LocalSourceParameter; Lambda expression provenance uses the plan node,
   so these keys must not be conflated. `form_ordinary` (`502–554`) stages formation,
   orders expression occurrences by the plan's authentic descendants, and merges
   only after success. `order_occurrences` (`110–143`) preserves forms and parameter
   fields while replacing expression occurrence IDs. `append_stage`
   (`source_identity.rs:75–103`) checks same parse and disjoint identities, then
   extends the original maps; it does not replace the existing top-level parameter
   source mapping. An Unsupported carrier outcome is not a successful bridge.

5. **Own annotation.** `parse_annotation_with_marker`
   (`source_annotation.rs:359–387`) retains the supplied annotation's key and owner;
   `parse_type_source` (`410–498`) constructs its outer effects from the actual
   annotation syntax, keeping function argument/result nesting distinct. No role
   signature is read here. Missing annotations stay None. The conclusion's rho is
   about this retained outer field; it does not equate nested effects or solved
   latent effects with outer source entry.

6. **Candidate consumer.** `emit_candidate_source`
   (`candidate_source.rs:826–938`) requires pointer identity with the HIR-owned
   LocalSource, authentic root/receiver ownership and owned occurrences. It creates
   parameter recipes, maps actual HirParameterIds to positions and registers each
   Lambda with its own rho. Parameter Names use that ID map, not spelling, for
   CandidateEndpoint::Parameter and FormalNameInput. The Lambda visit (`991–1034`)
   keeps parameter levels, records original omitted-formal identity when annotation
   is absent, and queues the actual annotation actions when present. Lambda recipes
   (`1409–1425`) link parameter position, registration and actual body endpoints.
   `initialize_candidate_source_levels` (`1516–1549`) checks recipe identity and
   attaches native parameter roots, with a fresh entry effect only for Computation.
   These are source-to-native registration facts, not a proof of the full native
   solver or call-hygiene theorem.

7. **Runtime role consumer.** `RuntimeProgram::from_hir` (`program.rs:249–301`)
   requires admitted HIR roots with retained sources. Its role map (`414–434`)
   keys NameConsumption by actual parameter ID using the same rho; Name instructions
   (`455–475`) clone the exact resolution and reject conflicting supplied consumption
   evidence. Lambda instructions (`488–509`) clone the ID, emit rho and pass the
   original parameter to RootCompSchema::from_parameter. This note proves that
   invocation's input identity, not the schema constructor's internal guarantees.
   Label construction (`323–330`) checks source ownership, while Code sites
   (`555–566`) retain source root/occurrence/range. Name consumption is Observe for
   Value and Execute for Computation. Instruction emission does not prove machine
   entry, forcing, resumption or final execution.

## Apply the bridge to R100-P2 without assuming its producer

R108 discharges finite syntax entry. R112 then establishes that production
`lower_module` does not supply H1 for this source. The current pins still exhibit
its exact gates:

- `lower_module` (`module.rs:1103–1112`) uses default counters, initializes source
  identity and enables ordinary_source_carriers. Defaults leave local_source and
  shadow_applications false (`1375–1391`). `lower_module_with_counters` plans direct
  root nodes (`1173–1184`). `plan_root` (`1976–2025`) recognizes OperatorChain and
  BindingStatement; the authentic ImplDeclaration returns UnsupportedItem before
  member descent, `plain_binding_header`, DefId or parameter allocation. `lower_plan`
  returns HirItem::Error for that plan (`2067–2088`). Binding/Expression carrier
  passes (`1296–1326`) supply no carrier for the Error. This consumes R112's result
  and allows earlier availability failure; it assumes no whole-module success.
- Independently, `plain_binding_header` (`2974–2977`) rejects more than one tail
  unless shadow_applications or local_source is true. The original member has two
  ML tails. Even direct header submission under those production defaults would
  fail this gate. `form_ordinary` temporarily enables local_source only after
  admission (`519–525`); this cannot retrospectively admit the member/header.
  This counterfactual isolates a second producer obligation and is not a new
  accepted-source restriction or a proposal to flatten the member.

Consequently this bridge supplies a reusable downstream preservation argument
for P2 **once** its authentic producer and successful admission premises are
established. It does not reduce the unsatisfied producer to a flag flip. The
current source still lacks this member's executable owner, binders and environment.
R85 adoption is a separate semantic premise; adoption alone cannot supply H1–H4.
P3's target/Apply origin and P4's complete admission remain separately OPEN.

## Exact mutual TODOs and falsifiers

| Request / owner | First missing evidence, proposed output and falsifier |
|---|---|
| R116-P2-PRODUCER / Luna, future approved `plan_root`/`lower_plan` and LocalSource producer owner | Input: original R108 member keys and original P2. Output: a separately approved authentic member plan/root with equal ordered executable/admitted vectors, original annotations and exact body environment; retain ordinary inference constraints. Minimal provisional implementation TODO only, with no code lease here. Falsifier: an existing pinned route already emits that member, or a proposed producer substitutes a top-level/signature binder, loses a key/ordinal, or resolves original body selected to another ID. |
| R116-R85-ADOPT / Luna and user semantic decision owner | Input: unchanged Draft R85 positive contract. Output: explicit adoption/rejection through its existing authority process. Falsifier of adoption claims: no explicit authority receipt for those exact semantics. §21 source authority alone supplies no role lookup or target-selection rule. |
| R116-P3-P4 / future approved target, candidate and runtime owners | Input: authentic P2 output and independently approved target semantics. Output: whole-operand receiver-first Apply edges, ordinary constraints and complete admitted root/target metadata. Falsifier: Operation head substituted for member, operand reversal, missing source metadata, or unrelated Act-error exemption. |
| R116-REVIEW / Luna | Freeze this candidate and appoint fresh source and semantic reviewers. A producer/coauthor cannot certify it. Falsifier: any mismatch between stated fields/gates and pinned owners, missing successful-consumer premise, signature-derived role, or conflated source identities. |

R100's own constructor/consumer evidence and R108/R112 closeouts are reused only
within their reviewed finite scope. R85 provides the original obligation and
proposed semantic boundary, not adopted authority. Assumed transition tests,
R106/R107 failures, same-spelled standalone bindings and effect placeholder
exemptions supply no missing member evidence. This note changes method from
source obstruction to constructive consumer preservation; it does not rename
the unchanged producer premise as parent closure.

Original Simple-sub/evaluator A/B, F1/FK1 including foreign continuations, and all
six effect-hygiene fronts remain independent and OPEN. Generation, accumulation,
propagation, levels, extrusion, qualifying intrusion and generalization remain
required. Residual/provider/witness lineages stay distinct. No withdrawn bypass,
weaker ordinary inference, source execution, semantic change or production
authority follows.

## Frozen direct dependencies and authors

All entries below were checked against rev3. Syntax/solver pins not used in the
derivation remain contract inventory, not implicitly proved dependencies.

| Direct input | SHA-256 |
|---|---|
| charter §21 | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| R100 proof | `84a2aad8a63cad8673e2862e343eff27664c3daf003e97015a0289ba9569a971` |
| R108 closeout | `cfc0e6a45b329e099f1263833bc7c0160c8d0e034bf7596ffef1dc5da10666e8` |
| `crates/yu-hir/src/tests/shadow_method_role_source.rs` | `ea90e8ef445aae1155e28e10356068dfaecb8b2bc430d5bf6f18094acee21e1a` |
| R112 proof | `9444f51d980c2a8d01aacb407e81c4d2278f88785d6486c0d0ec696da1e48ca9` |
| R112 closeout | `7f6e27c07a7a39424eed647a0250822075ec65233e06ead3677ceff3a6a6a6b1` |
| R85 Draft | `fee3feaec5e8873fe4f056df3a9ae9ca16c342f0a8b314c027a35719eedd4609` |
| `crates/yu-hir/src/module.rs` | `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a` |
| `crates/yu-hir/src/module/local_source.rs` | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |
| `crates/yu-hir/src/source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| `crates/yu-hir/src/module/source_annotation.rs` | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| `crates/yu-solver/src/candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` |
| `tools/inference-playground/src/runtime/program.rs` | `7bc27580711d3ef09044e324541904ef3388aca8e3b4f3a72437b1e04dc0210a` |

R100 proof author `/root/r100_member_proof`; R112 proof author `/root/r112_proof`.
R108/R112 closeout and R85 decision receipts: Luna. Charter author: historical
primary as stated in its header. Compiler/test byte authors remain UNKNOWN.
Historical independent reviews are consumed through the pinned closeouts, not
reissued or upgraded by this producer.

Checks: static source/authority inspection and SHA-256 only. No tests/builds,
compiler/runtime/CLI, probes, formatter, Git or external contact. Rev2 stopped
without writes at the missing charter pin; rev3 explicitly supplied it. No other
owner was added. Requested Sol/high; observed model/effort UNKNOWN/UNKNOWN.
The cumulative 600-second proof cap was not renewed; exact total/CPU/memory use
and remaining allocation are UNKNOWN, with unobserved use retained as charged.
The handoff contains the final clock/freeze receipt. Exactly this note and the
assigned inbox are new paths; no scratch/generated files. Next in-envelope step:
freeze and STOP. Parent and production gates remain OPEN pending Luna intake and
fresh independent review.

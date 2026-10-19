# R119: refinement obligations for an authentic member producer

Status: **conditional constructive refinement; fresh independent review pending**.
Assignment `R119-PROOF`, revision 1. Sole author/writer:
`/root/r118_proof_lane` (the actual reused worker identity); no descendants.
Contract revision 2, SHA-256
`6639951a68a8248c705e5df8c954488ae782e8ffb0fbf8639fb821c4326bed58`;
baseline `af551a720`.

## Parent and result

Original R100-P2-MEMBER requires the authentic selected implementation member's
ordered executable binders, their original annotations, original body and lexical
environment. R85 P1 target/interface facts, P3's receiver-first ordinary call,
and P4's complete candidate/runtime admission remain separate obligations.
Their quantifiers and supported source domain are unchanged. R85 is Draft and
unadopted; this note grants no semantic or implementation authority.

For the exact R100 source, the result is a fact-to-owner-to-consumer refinement
of the missing producer. Conditional on the authentic producer facts listed
below and successful existing consumers, R116 applies: the two own unannotated
parameters remain Value, and the original body resolves to the second parameter
identity. Independently, conditional on an authenticated member target and the
proposed two ordinary Apply edges, the inspected candidate/runtime constructors
preserve their operand order and source-owned edges. None of those conditions
establishes actual source execution, an `int` endpoint or result `2`.

The exact fixture is the historical 148-byte LF source without final LF,
specified SHA-256 `fb54857e70924c178842692d7cce1a9c35b7c2a55bceab78710889b913d7dfcb`:

```yu
role SecondInt {
    my second: int -> int -> int
}
impl int: SecondInt {
    my second self selected = selected
}
my answer = SecondInt::second 1 2
```

R112's pinned closeout supplies the reviewed finite entry/obstruction for this
fixture. R100 supplies the source-owner distinctions and original P2–P4 cuts.
R116 supplies only its explicitly conditional preservation bridge. Current
source pins below are re-inspected; historical line numbers and source hashes
are not substituted for current owners.

## Authority and two distinct role decisions

Charter §21 assigns each executable parameter its own source entry role:
unannotated or ordinarily value-annotated means Value; explicit outer computation
annotation means Computation. Body usage, empty solved rows and role signatures
do not choose or rewrite that role. Value entry forces and rebinds the whole
argument once within the invocation even when unused; Computation entry retains
the argument carrier. This is source authority, not implementation approval.

Charter §24 selects the function receiver role before Function-interface
effect-port interpretation and distinguishes it from §21 parameter entry.
It does not make every function a handler and does not select a role member.
In particular §24 supplies no operand-order or qualified-method-lookup rule.
The receiver-first shape below is R85's still-unadopted proposed P3 premise;
its identity, lookup and ambiguity semantics are not decided by this note.

## Constructor refinement table

Let `K_m`, `K_s`, `K_t`, `K_b` denote the same-parse original member, receiver
formal `self`, explicit formal `selected`, and body-name occurrence respectively.
They are symbolic authentic source keys, not fabricated values. Formal and body
`selected` are distinct occurrences. Let `D_m` be a future authentic executable
member owner and `p0`, `p1` its parameter IDs. Proposed outputs in this table are
proof obligations on a future producer, not new approved fields or APIs.

| Required source fact | Current retaining/rejecting owner | Required producer output | Existing consumer, or exact unsupplied seam |
| --- | --- | --- | --- |
| Authentic member belongs to this role's implementation | R100/R112 retain the nested syntax ancestry; current `module::plan_root` rejects its ImplDeclaration | A source-qualified semantic target-to-original-member witness, after the separate adoption/selection gates | No role/impl/member identity validator is demonstrated by these pins. Ordinary `DefId`/SourceRoot lookup does not establish this witness. P1/P3 remain OPEN. |
| Original member has an executable source owner | `plan_root` (1955–2009) accepts OperatorChain or BindingStatement; ImplDeclaration takes UnsupportedItem before member descent | An authentic admitted callable plan/root for `K_m`, with a proven join to the selected member; no synthetic top-level substitute | `lower_plan` (2031 onward), `local_source::form`, then candidate `emit_candidate_source` require an already supplied authentic owner |
| Executable/admitted vectors have exactly two entries in source order | `plain_binding_header` (2916 onward) retains ML-tail order when admitted; current production defaults independently reject multiple tails | Equal-length vectors `[self, selected]` and `[p0,p1]` belonging to `D_m`; exact count/order correspondence | `lower_plan` enumerates and `form` zips these vectors. Equality of lengths is essential because zip itself does not prove it. |
| Distinct original formal identities | `lower_plan` (2078–2094), `HirParameterId` (406 onward), `source_identity::record_parameter` (118) | IDs branded by the actual source owner and ordinals 0/1, each mapped to its original IdentifierPattern key | LocalSourceParameter, candidate parameter recipes/registration and RuntimeProgram Lambda/parameter-Name instructions use these IDs |
| Own annotations preserved, including their absence | `AdmittedParameter.annotation`; `form` (601–613) reads that own field | For this fixture both annotations remain None; no type or annotation copied from the role signature | Candidate role at 878 and runtime roles/Lambda at 414–434, 488–509 use the parameter's own outer effects field |
| Exact body and lexical environment | `lower_plan` pushes actual parameters into ScopeStack; `form` (615–643) pushes each Parameter binding before scheduling the original body | Body at `K_b`, original namespace, ordered parameter environment, no intervening shadowing | `Builder::push_binding/restore`, `Builder::expression` Name branch (1007–1040) resolve body to Parameter(p1) before module namespace lookup |
| Original occurrence provenance and supported publication | `Builder::set` (818–846), `form_ordinary` (502–554), `HirSourceIdentity::append_stage` (76 onward) | Same-parse source mappings and actual occurrences; successful staged publication under `D_m` | Candidate checks pointer-identical HIR-owned LocalSource and owned occurrences; runtime labels/Code.site retain source owner/occurrence/range |
| Qualified callee denotes that same executable member | `lower_ordinary_admission` (1421 onward) excludes PathTail; LocalSource's initial PathTail is interpreted through `resolve_operation` (1091) | Approved, authenticated target-to-executable-owner join yielding `C_member`; not an effect Operation and not a spelling match | Existing ordinary ModuleDef/definition-label consumers can consume their normal authenticated input; no member-selection producer or its semantic validator is demonstrated here. This is a separate P3 seam. |
| Whole receiver `1` and argument `2` retain caller scope and provenance | LocalSource Apply construction (870–940) allocates separate callee/argument slots; ordinary projection accepts two-child MlArgument/CallTail shapes | Proposed `u = Apply(C_member,E_1)` and `v = Apply(u,E_2)`, retaining both complete source operands and own sites | Candidate ApplySourceInput (1258–1368) retains both endpoint/effect pairs and source cause/level; runtime Apply clones callee/argument labels (510–516) |
| Member body/result and all endpoint obligations checked ordinarily | Candidate Lambda/Name registration and LambdaRecipe (826–938, 1409–1425) read the actual retained body | Authentic complete source plus successful ordinary body/result/endpoint constraint generation and solving; no signature-based endpoint substitution | Emission retains actual parameter/body endpoints and schedules Action::Lambda/Action::Candidate. Whole ordinary solving and CheckedBody are premises, not proved by this table. |
| Complete candidate/root/target admission precedes runtime publication | Candidate preflight (451–504), owner authentication (826 onward); RuntimeProgram item/source gate (275–301) | Successful full admission with complete source-owned root/target metadata for the same module; no unregistered role/impl Error bypass | Runtime accepts Binding/Expression source roots and only the specific registered effect-declaration placeholder errors. No existing method-specific admission certificate is established. P4 remains OPEN. |

The table is intentionally not a completed vertical implementation proof.
Two required semantic joins have no demonstrated producer/validator in the
inspected vocabulary: role/impl/member identity and its mapping to an admitted
ordinary executable target. Those rows are precise obstructions. A hypothetical
record containing their names would not establish either fact or supply an
existing consumer. The implementation packet must preserve these gates instead
of claiming that every row is already implementable without further authority.

## Conditional derivation and application to P2/P3

Define the producer premise **M** as follows: after independently approved
semantic selection, the actual nested member `K_m` is authentically admitted
with `D_m`, exactly ordered vectors `[p0,p1]` / `[self,selected]`, each original
source key and own annotation, original body/namespace/environment, and successful
same-parse supported publication. No new representation is selected by M.
Let **A** mean successful authentic candidate and RuntimeProgram consumers.

1. Under M, `lower_plan`'s ordinary enumeration maps ordinal 0 to `p0` and
   ordinal 1 to `p1`, recording their distinct source origins. Neither the role
   signature occurrence nor `answer` is their executable owner.
2. In `form`, induction on that exact ordered two-entry zip yields
   `Lambda(p0,Lambda(p1,body))`. `push_binding(self,Parameter(p0))` followed by
   `push_binding(selected,Parameter(p1))` leaves the latest selected entry at
   `p1`. No binder is added by the original single-name body chain. Therefore
   its Name branch resolves to Parameter(p1), irrespective of a same-spelled
   module name. Body and formal occurrences remain distinct.
3. Both own annotations are None under M. Thus both consumers evaluate
   `rho(p) = Computation iff p.annotation.ty.effects is Some; Value otherwise`
   to Value. Candidate formal registration and Parameter endpoints preserve
   `p1`; runtime Name resolution preserves `p1` and uses Observe consumption.
   Runtime Lambda keeps each own ID and Value role. This specializes R116's
   finite-vector preservation without changing that result's H1–H4 premises.
4. Candidate LambdaRecipe connects actual body endpoint to actual lambda root;
   native formal initialization checks the parameter recipe and registers its
   own root/level (1512–1547). That does not establish int types, body/result
   validity, complete inference, or native solver correctness. A remains needed.

Therefore M and A suffice for this downstream P2 preservation consequence.
Current production does not establish M. This is the application to the parent:
its remaining first source obligation is the authentic owner/vector/body
producer, rather than another proof of downstream binder spelling or role
classification. It cannot be discharged by more parser-association evidence.

For P3 add a separate premise **T**: approved unique target evidence joins
`C_member` to `D_m` and authentically emits the proposed two source-owned ordinary
Apply edges `u` and `v` above. The existing LocalSource reverse-tail constructor
demonstrates how two ML arguments preserve inner/outer edge order, but its current
PathTail head is an effect Operation, not T. Under T and successful ordinary
consumers, candidate emission retains inner callee/member plus receiver `E_1`,
then outer callee `u` plus `E_2`; both carry their actual endpoints/effects,
source owner, checking cause and level. Runtime instruction construction clones
those labels without swapping or flattening them. These are inspected structural
consumer facts, not a machine-execution theorem. No runtime machine, CLI owner
or additional source was inspected for this assignment.

P4 still requires whole-module source/target admission before `from_hir` can
publish a RuntimeProgram. The admitted-root and effect-error tests are gates;
they cannot be bypassed by treating role declarations as Act placeholders.
Nothing in M, A's conditional use, or T proves present source acceptance.

## First missing premise and concrete falsifiers

The **first executable source premise**, `R119-MEMBER-OWNER-1`, is M's authentic
admitted member owner at `module::plan_root` / `lower_plan`, before executable
parameter allocation and LocalSource formation. Current `plan_root` returns
UnsupportedItem for the authentic ImplDeclaration; `lower_plan` returns Error;
production carrier passes (1298–1326) only accept Binding/Expression. This
re-inspects and consumes R112's finite obstruction under current pins. It allows
earlier availability failure and makes no repository-wide absence claim.

There is an additional header gate: production counters default both local_source
and shadow_applications to false, and `plain_binding_header` rejects two tails
under those defaults. `form_ordinary` temporarily sets local_source only after
ordinary admission; it cannot repair that earlier rejection. A flag flip alone
would still supply neither authentic member ownership nor target semantics.

Exact falsifier of the bounded obstruction: an existing route within these
pinned owners which consumes this same original nested member and creates its
authentic admitted executable owner, both ordered parameters, original body and
environment. If found, report that route instead of proposing a duplicate.
A top-level same-spelled binding, role signature, retained syntax association,
root-loop occurrence, manufactured LocalSource or unresolved Operation is not
that falsifier.

Exact falsifiers of the conditional refinement: mismatched vector lengths;
reversed parameter order; wrong owner/source key; inserted signature annotation;
body resolving to another identity; publication with unsupported/error metadata;
or an Apply edge that loses/reorders whole operands, caller scope or provenance.
Tests of such assumed transitions would not establish M or T.

## Mutual TODOs and stop boundary

| Request / owner | Required input and proposed next evidence | Falsifier / boundary |
| --- | --- | --- |
| `R119-MEMBER-OWNER-1` / Luna; future separately leased HIR member producer owner | Exact R100 source, original P2, R112 finite obstruction, adopted source judgment; establish M against actual plan/root/vector/body construction | Existing authentic current route falsifies obstruction; synthetic member substitution or missing own source identity falsifies refinement. No code authority here. |
| `R119-TARGET-JOIN-1` / Luna; future approved role target and ordinary admission owner | Original P1/P3 plus semantic adoption and M; establish unique original-member-to-ordinary-target join T | Spelling/declaration order, parser association, effect Operation, or an unowned target does not satisfy T. No lookup/ambiguity/diagnostic choice is made. |
| `R119-ADMIT-1` / future separately leased candidate/runtime owner | Authentic M/T source and ordinary complete endpoint/body/effect evidence | Failed preflight, incomplete metadata or role/impl Error exemption blocks P4. A correct own role alone does not prove int endpoint or CheckedBody. |
| `R119-PAIR-1` / independent implementation-assessment lane via Luna | Use this refinement as requirements for its post-adoption packet, explicitly retaining both missing semantic joins and all admission gates | A packet claiming full present feasibility without an owner/validator for a required fact fails the contract. No cross-lane write or new dependency is granted. |
| `R119-REVIEW-1` / Luna | Freeze both lanes and obtain fresh compiler/source and spec reviews; preserve R85 as the sole unchanged semantic offer | Producers/coauthors cannot independently certify either combined result or adoption. Review cleanliness does not supply user adoption. |

Next in-scope step after freeze: none for this writer. Luna owns intake,
independent review and any later adoption/implementation contract. No code/test
TODO is approved for execution by this note. Original Simple-sub/evaluator A/B,
F1/FK1 including foreign continuations, all six effect parents, R100-P2/P3/P4 and
R85 adoption stay OPEN. Generation, accumulation, propagation, levels, extrusion,
qualifying intrusion, generalization and independent residual/provider/witness
lineages are preserved. No withdrawn bypass or weakened ordinary inference.

## Frozen dependencies, provenance and resources

| Direct input | SHA-256 |
| --- | --- |
| R119 rev2 contract | `6639951a68a8248c705e5df8c954488ae782e8ffb0fbf8639fb821c4326bed58` |
| R100 exact-source proof | `84a2aad8a63cad8673e2862e343eff27664c3daf003e97015a0289ba9569a971` |
| R112 progress closeout | `7f6e27c07a7a39424eed647a0250822075ec65233e06ead3677ceff3a6a6a6b1` |
| R116 conditional bridge | `39183afeac8b11366bb68fd357c95ed18de0a969a40640f4908c4a05f53b65ef` |
| R85 unchanged Draft offer | `fee3feaec5e8873fe4f056df3a9ae9ca16c342f0a8b314c027a35719eedd4609` |
| charter §§21,24 | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `crates/yu-hir/src/module.rs` | `153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907` |
| `crates/yu-hir/src/module/local_source.rs` | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |
| `crates/yu-hir/src/source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| `crates/yu-solver/src/candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` |
| `tools/inference-playground/src/runtime/program.rs` | `c2363ad42104b895519bb29a8eb9aeda545bd0176cebbd78750d3a2df90849ca` |

All direct pins were SHA-256 checked. R100 author `/root/r100_member_proof`;
R116 author `/root/r116_method_proof`; R112 closeout, R85 and contract owner Luna.
Compiler source/charter byte authors UNKNOWN here. R100's old parser-entry
conditional is not restored: the pinned R112 closeout consumes the reviewed
finite entry result. R116's consumer preservation is reused with its hypotheses,
not upgraded to authentic member construction or native correctness.

Inventory error disclosed to Luna before writing: the similarly named R112
theory note was initially opened while locating the contract's closeout hash.
It is not a direct dependency, not authority and supplies no new result here;
the pinned closeout and current named owners support the claims above.
No unpinned source owner or additional producer implementation was inspected.

Requested model/effort: Sol/high; concrete version observation UNKNOWN;
observed model/effort UNKNOWN/UNKNOWN. Actual runtime worker remains
`/root/r118_proof_lane`, rather than the unlaunched proposed R119 identity.
Checks: static text/source inspection and SHA-256 only; no tests/builds,
compiler/runtime/CLI/probes, code edits, Git or descendants. First explicit clock
receipt `2026-10-19 09:17:47 UTC`; pre-clock inventory remains charged.
Cap 420 seconds, unexpanded; exact allocation-start duration and CPU/memory
UNKNOWN. Final clock/resource receipt is in the handoff.
Only this note and `tasks/agent-loop/inbox/20261019-r119-proof.md` are new;
no scratch/generated paths. **Freeze revision 1 and STOP after handoff.**

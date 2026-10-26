# Original scoped closure: source presentation, copies and actual export readback

Date: 2026-10-27. Producer: `/root/principality`, bounded `lean_prover` leaf.
Status: **checked lossless source presentation and publication allocation;
full SG instance semantics and original principality OPEN**.
Independent review: not yet performed. No compiler, original semantics or
existing proof file was changed.

## 1. Constructed result

[OriginalScopedClosure.lean](lean/YulangClosure/OriginalScopedClosure.lean)
constructs an occurrence-addressed program from the **existing full original
Source, Definition and Client builders**. It stores every rule and premise,
all binder and execution constructors, publication/restore instructions and
the complete original residual. A structural theorem proves erasure for
every original constructor; no presentation-correctness proposition is an
input field.

Copies add a description-frame namespace while retaining the original
source owners, scope tree, Shared references and actual-event references.
An alias reuses the same existing description program. Publication extraction
finds the actual `publicationFinalRoot` clause and, for an annotated binding,
its enclosing emitted boundary. The endpoint is that boundary's **upper**
endpoint. Opening it uses the original publication lookup and restore
operation, with checks of both source origin and binding site.

The direct application uses the existing doubly annotated record source in
`OriginalSourceRecordBoundary.Witness.original`. Its initializer annotation
is 100 and its outer binding annotation is 101. The computed exported endpoint
is `(20, writtenTarget)`, and that exact endpoint remains selected after a
copy and after opening the corresponding original publication record.

This is the representation/addressing part of SG allocation. It does not
claim that adding a frame namespace performs a semantic endpoint substitution.
The original Kernel and its admitted data are unchanged. Full fixed-dependency
closure, eligibility, symbolic endpoint graft interpretation, source/native
publication adequacy and the all-valid-view extension theorem remain separate
construction obligations.

## 2. Original representations reused

Authority is the selected [Source-Generalize definition](../design/2026-10-08-source-generalize-definition.md),
particularly the [manuscript §§3.3–5.2](2026-10-08-source-generalize-definition-and-proof.md#33-owning-rules-declarations-and-event-telescopes).
The [preceding principal-order packet](2026-10-27-original-principal-order.md)
identified the already specified ordinary-use operation and its remaining
extension theorem. This construction implements a representation portion of
that operation without choosing a replacement order.

| Existing owner | Objects reused |
| --- | --- |
| `OriginalSourceSyntax` | All original Source categories/constructors, Definition, Client, RuleTree/RuleForest, premises, endpoints, annotations and binding kinds. |
| `OriginalSourceGeneration` | `sourceRules`, `clientRules`, `Build`, `BuildJoint`, `compile`, independent `Judgment`/`SourceJudgment`, original `Satisfies`, complete Environment, publication identities/records, restore and alias operations. |
| `OriginalSourceEvents` | Source occurrence `Route` and `ScopeEntry`; routes distinguish constructor positions without assuming all numeric sites are unique. |
| `OriginalSourceRecordBoundary` | Complete `ScopeStep`, the actual annotation-boundary owner record, and its already source-generated two-boundary fixture. |
| `OriginalSourceEnvironment` | The imported complete payload/environment representation remains available unchanged; the new data-level theorems are polymorphic in Value and therefore apply to its original Payload without projecting fields away. |

The new program is constructed directly from these original builders. It is
not a generic finite graph supplied by a caller. The program retains an
original rule's full rule tag, site, context and entire premise list. Premises
are never reconstructed from endpoint shapes or successful comparison.

## 3. Scope construction and exact erasure

`Position` contains an original declaration, constructor route, complete
static telescope and incoming description-frame namespace. `Program` mirrors
every original RuleTree constructor. `allocate` descends the existing tree;
it extends the telescope with the actual `existsE`, `forallE`, initializer,
execution, Shared, publication, restore, alias or choice step encountered.
Both branches and every child are retained. A real `publishedInstance`
binder is the only binder that opens an additional description frame.

The core unconditional theorem is:

```lean
erase_allocate (position : Position) (tree : RuleTree) :
  (allocate position tree).erase = tree
```

Its mutual forest theorem covers every original child list. Both are proved
by structural recursion over the actual constructors. They are not stored
as fields of `ScopedClosure`. The resulting public equations are:

```lean
source_residual (origin : Declaration) (context : Context)
    (raw : Source category) :
  (source origin context raw).residual = Build context raw

definition_residual (raw : Definition) :
  (definition raw).residual = Build raw.context raw.source

joint_residual (origin : Declaration) (context : Context) (raw : Client) :
  (joint origin context raw).residual = BuildJoint context raw

copy_residual (framePrefix : FrameId) (program : Program) :
  (program.copy framePrefix).residual = program.residual
```

`source_copy_adequacy` and `joint_copy_adequacy` then use the already proved
original reconstruction theorem. They quantify over the same arbitrary
original Kernel and Environment. The conclusion is equivalence with the
existing finite local-rule judgment; it does not instantiate the original
semantic Kernel or discharge `SourceProblem` soundness/principality.

The `ScopedClosure` record stores the origin, original context/raw Source and
constructed program. `prepare` computes those fields. The constructor does
not accept an equality, safety predicate, source derivation or correctness
law. Theorems about `prepare` derive its residual equation from the actual
construction above. They certify that computed output, not an arbitrary
manually populated `ScopedClosure` record.

## 4. Binder ownership and actual event routing

Each binder occurrence retains its full original Binder and source telescope.
The presentation distinguishes these references:

| Original binder class | Reference and copy behavior |
| --- | --- |
| `description` | Incoming frame plus original binder owner; distinct copy prefixes yield distinct references for the same original declaration. |
| `viewLogic` | Incoming frame plus the original description-region owner and telescope. |
| `eventProof` | Incoming frame plus original owner/telescope; `proofKey` additionally retains the actual current event path. |
| `publishedInstance` | The original explicit instance introduction; no Alias introduces one. |
| `shared` | Original owner, independent of description-copy prefix; actual selection still uses `Environment.anchorValue`, including its original event path. |
| invocation, receipt, Return/rebind, rigid operation, response, OneShot | Original event owner, with the actual BinderKind retained; copy prefixes do not change it. |

`copied_owner` proves that copying does not change the original binder,
constructor route or telescope. `copied_shared_reference`,
`copied_event_reference` and `shared_anchor_copy_independent` establish the
corresponding unchanged references and anchor lookup. These statements do not
turn a scope-indexed Shared strategy into one ground value for every event;
they retain the original strategy and its actual allowed dependencies.

`Occurrence.actualKey` combines the original occurrence with the actual
Environment event path and the candidate's occurrence/data. The theorem
`actual_key_uses_original_event` proves that this path is exactly the path
computed by **the existing** `Environment.extend`. No description frame is
inserted into the runtime event identity. The whole candidate payload remains
present. `proofKey` keeps both the incoming frame and actual current event
path; logical extensions leave that path unchanged. Thus per-description
EventProof references do not duplicate runtime response, world or continuation
fields.

These are data-routing theorems. They neither restrict original candidate
admission nor supply semantic evidence about the candidates. The erased
formula retains its original universal and existential binders and the full
original Kernel admission predicates.

## 5. Actual publication root, restoration and alias

There is a concrete reason not to store only `Definition.source` as the whole
public export: Definition contains raw initializer code but no separate outer
binding annotation. The original `bindingsRulesK` emits that annotation's
formation and boundary before the binding's `publicationFinalRoot` clause.
The full source program is therefore used for publication extraction.

`publications` traverses every original rule constructor, retaining scope and
ancestor annotation boundaries. At a binding clause it keeps the entire
`publicationFinalRoot` atom, including context, name, initializer incidence
and annotation. An unannotated binding selects the initializer's final-root
port. An annotated binding must find its matching actual enclosing formation
and selects that boundary's upper endpoint. If the required boundary is
missing, extraction returns no publication; it does not guess an older
synthesis or interior root. This is a representation readout failure, not a
new source rejection rule.

The existing source fixture computes exactly:

```text
name      = 30
binding   = 20
export    = (20, writtenTarget)
annotation = 101
initializer incidence = [10]
```

The inner initializer annotation 100 and its original clauses remain in the
full residual. `copy_publications` proves that the complete publication list,
including this boundary and target, survives copying. No semantic transitivity
of concrete conversions is used.

`openPublication` first finds that source publication, resolves the actual
name in the original Environment, checks the source origin and binding site,
and invokes the existing `atPublication`. It copies the retained program but
does not execute or recreate an initializer. `opened_restore_fields` derives:

- unchanged root, global anchor strategy and publication map;
- the captured record's original origin, entry event path and entry names;
- its recorded entry frames followed by the caller's non-fixed description
  frames, exactly as the original restore definition specifies;
- its fixed replay frames and initializer-entry stack.

The direct theorem `actual_annotated_export_opened` applies this operation to
the source-generated two-annotation program. Its six premises are all raw
original data readbacks:

| Premise | Exact type |
| --- | --- |
| Named publication | `environment.publicationName 30 = some identity` |
| Stored record | `environment.publications identity = some record` |
| Same complete identity | `record.identity = identity` |
| Original fixed-frame check | `record.fixedFrames.all (fun frame => frame.binder.isFixed) = true` |
| Same source declaration | `identity.origin = 7` |
| Same binding occurrence | `identity.site = 20` |

From those readbacks the theorem constructs a successful `openPublication`,
its endpoint `(20,writtenTarget)`, the exact `environment.restore record`,
and the complete original Build residual. There is no SourceJudgment,
complete Call certificate, carrier/world Meaning, Force safety or assumed
presentation law among these premises. Deriving the readbacks from a native
execution remains the source/native publication owner’s obligation.

`Opened.alias` calls the original alias operation on the stored caller
environment and reuses the existing description. Its theorem proves equality
of the complete publication object, identity, program and restored
environment, together with the original global anchor/publication maps.
It creates neither a new instance frame nor another Shared witness.

## 6. Acceptance boundary and next owner

The constructive result is a lossless scoped source presentation, frame-copy
operation, exact annotated export extraction and original publication
readback/application. Its scope includes **all original source and client
constructors** at the representation layer; the two-annotation application
does not restrict the source domain of those general theorems.

The following remain open and are not constructor fields:

1. The full SG dependency walk that decides which owned semantic Desc
   declarations remain eligible after every Established/OneShot/free-field
   dependency is fixed. The new addresses record all original declarations;
   they do not assert that every recorded Desc is semantically freshenable.
2. Evaluation of symbolic endpoint-term grafts and its correspondence with
   original admitted payloads. `Program.copy` changes presentation frame
   indices; its exact erasure does not rename Kernel endpoints by fiat.
3. Connecting a stored closure and actual returned public root to the full
   `originalNewInstance` atom. `joint` retains that original atom and its
   complete generated source premise; it does not replace the atom by a
   successful query or call it discharged.
4. Complete original local Kernel meanings, independently admitted future
   domains, source/native extraction and full public direct-query evidence.
5. The original all-valid-view extension condition `E_V`, joint shared
   strategy across all lawful uses/futures, and the actual SourceProblem
   solution/instance interpretation.

The immediate next owner can use the constructed publication and full program
to implement the original fixed-dependency/eligible-declaration walk, then
connect its endpoint-term action to the original payload admission. An opaque
field saying that a copy is an admissible instance would not discharge that
task. No original principal order was invented, and no Meaning-to-Background
cast or alternate acceptance relation was added.

## 7. Verification and origin audit

The frozen source is
`b316a5e18a14b4c9750cc97f294aea824ce6b0a704fc67929fa4a016e94ebeab`.
Direct check 09 exits 0 without warnings or errors using pinned Lean 4.35.0,
`timeout 120`, `LEAN_NUM_THREADS=1`, `-j1 -M1024`, without `-o`.

Nine of the 18 permitted proof/inspection invocations were used. Check 03 was
a data evaluation to inspect the concrete publication list; it is not used
as a proof. The final source uses ordinary kernel-checked proofs, including
the concrete source computation. The parent owns all builds and caches.

The parent rebuilt the exact final module successfully: 17 jobs, zero
diagnostics, recorded in `/tmp/yulang-scoped-closure-build-final.log`.
The independent producer census then ran with `-j1 -M2048` under the same
120-second limit, without compiled output. Audit 01 exited 0.

The census identifies declarations by their **originating module**, including
private and generated constants. It prints every complete type and transitive
axiom set and rejects any axiom outside `propext`, `Classical.choice` and
`Quot.sound`. Result: **578 declarations; 262 theorem constants, comprising
30 authored and 232 generated theorems**. The remaining declarations are
270 definitions, 10 recursors, 10 inductives and 26 constructors. There were
no diagnostics, `sorryAx`, project axioms or type-output elisions.

The complete authored-theorem axiom classification is:

| Axiom set | Authored theorems |
| --- | --- |
| none | `copied_owner`, `copied_shared_reference`, `copied_event_proof`, `actual_key_copy_independent`, `proof_key_copy`, `shared_anchor_copy_independent` |
| `propext` | `erase_allocate`, `erase_allocate_forest`, `erase_copy`, `erase_copy_forest`, `copy_residual`, `copied_event_reference`, `actual_key_uses_original_event`, `proof_key_logical_extension`, `copy_publications` |
| `propext`, `Quot.sound` | `description_copy_distinct`, `opened_alias_same_description` |
| `propext`, `Classical.choice`, `Quot.sound` | `source_residual`, `definition_residual`, `joint_residual`, `source_copy_adequacy`, `joint_copy_adequacy`, `prepare_residual`, `opened_readback`, `opened_restore_fields`, `open_publication_of_readbacks`, `opened_source_residual`, `actual_annotated_publication`, `actual_annotated_copy`, `actual_annotated_export_opened` |

Verification artifacts:

| Path | SHA-256 |
| --- | --- |
| `/tmp/yulang-scoped-closure/AuditFull.lean` | `c42d18dbab47386ee02a6c12a7672888878acd59c38086a37fe860950bb3aeb6` |
| `/tmp/yulang-scoped-closure/audit-01.log` | `6a524173f0347a96c6a07adcaf528ea332351b8a3ea7e99896321f23fee429c0` |
| `/tmp/yulang-scoped-closure/census.json` | `b9a0077bd3cd9671530b3f7b5a81f3692e2601e5e9dd5f88a5a1043fe7e37512` |
| `/tmp/yulang-scoped-closure/check-09.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |

Total worker budget consumed: **9/18 proof/inspection checks and 1/2 audits**.
There is no running worker checker or other worker process. Source writes
stopped at the final freeze; note writes stop after final hash verification.

Read-only input pins:

| Path relative to the repository | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |
| `notes/theory/lean/YulangClosure/OriginalSourceEvents.lean` | `cfd5f502a1e68a97e27e11a75400fae8789f167c92596aedb08ef7dfbb724342` |
| `notes/theory/lean/YulangClosure/OriginalSourceRecordBoundary.lean` | `c7889284745ebd23ec300cf3e4de0a8f7ffc4546a9af2eccf5df76d071a0dd1a` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |

The only repository writes in this packet are this note and its paired Lean
module. No original whole-language soundness, Effect hygiene, principality or
full inference-termination root is declared complete.

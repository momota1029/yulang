# R342 original scoped Union arms — constructor boundary

Assignment `R342-ARMS`, handoff revision 1; baseline supplied by primary:
`92a5212a0`. Contract `tasks/agent-loop/sprints/original-continuation-union-r342.md`,
SHA-256 `e31e094b9c2d6185c5297e31dea91db991082154ce054f05ab08dbe1bba10858`.
Author/worker `/root/r342_arms`; launch and active-work evidence: direct parent
assignment and progress messages in this session. Runtime session identifier,
effective model and effort: UNKNOWN. No descendants.

Outcome: **source-evidence / construction blocked; parent-edge delta NONE**.
No new Lean file, theorem, counterexample or semantic definition. The primary's
follow-up permits construction only if it actually removes a premise at the
original R293/R306/R159 consumer; otherwise return the exact missing owner.

## Original source law and quantifiers

The selected authority is
`notes/design/2026-10-08-call-source-interface-definition.md` §§2–4, selecting
`notes/theory/2026-10-08-call-source-interface-construction.md`
§§3.1–3.3, 4–6. The actual law already permits **arbitrary independently typed
complete original contracts**. A concrete selection of W/Z predicates is not a
precondition for its parametric construction. This corrects the tempting reading
that another concrete-W/Z search must precede every IF theorem.

For each original clause formation, IF §3.2 computes its dependent interface.
IF-Insert retains that clause's full interface and original clause/result
relation in its registered root; IF-Use retains the whole registered interface
under the actual scoped substitution at the actual reference occurrence. The
Call constructor (§4) retains `arms : IF(ArmDecl_e)` together with callee,
whole argument, actual CalRet/current configuration, receiver, result and
output-dependent future. Section 6 constructs the complete frame and all arm
placements from those original declarations and reference formations, before
any challenge or observation. Primitive validity and lawful whole actions
remain independent semantic inputs. The arbitrary W/Z contract's actual output
provider and dependent future fields stay its own.

EI-All §4 in
`notes/design/2026-10-24-computed-call-result-constructor.md` requires exactly
those original scoped arm descriptors, tags, guards, fields and independent
laws; it does not synthesize missing declarations or discard an arm.
GR1–GR3 in `notes/theory/2026-10-24-generated-computed-result-correspondence.md`
specify the typed two-pass source construction and correspondence. That note
is a research construction, not independent semantic authority. Source
Generalize's selected definition §§2–4 retains the same original ViewLogic
frame, shared strategy and local laws. The birth-level intrusion correction
was read; no cross-level SCC premise is used or changed here.

## Existing constructors actually found

* `YulangClosure.OriginalClauseCompilerR318.Local.Clause` is an existing
  independently typed original contract grammar, not merely an endpoint list.
  It has primitive, Union, conjunction, scope, rename and registered-reference
  cases, with arbitrary complete dependent catalogues, licenses and original
  whole-packet relation witnesses. `Table.scopeAgreement` preserves each
  declaration's own scope. `compileDerivation` / `compileLegacy` construct
  licensed children by induction on original finite derivations, including
  finite developments through recursive references. `atUse` / `legacyUse`
  subsequently construct IF use. These are reusable existing constructions.
* That grammar does **not** have the complete Bind/Delay/Call constructor
  cases from IF §3.2. `SourceSignatureConstruction.Node.image` / `.call`
  retain supplied catalogues and local `OperatorContract` semantics;
  `SourceDeclarationRetentionR295.CallData` retains supplied six regions,
  arms and result. They do not compute the missing full original IF contract.
* `SourceDeclarationRetentionR295.primitive_at_use` already constructs a
  primitive child and both contextual transports from the primitive's own
  packet/license. `OriginalSourceUnionConsumerR338.table_primitive_registered`
  already applies that kind of primitive to R306, retaining the explicit
  catalogue agreement. Repeating either would be a wrapper.
* `ComputedCallTypedFormationR310.Arm` keeps tag, full original `Position`,
  local binders and the full scoped computation reference. `Request` is
  emitted from actual source Call rows. `resultExpression` and
  `OriginalSourceViewRegistrationR330.Definition` still receive their arm
  list; no independently typed contract-to-Arm producer occurs there.
* `OriginalSourceScopedInterpretationR335` authenticates original callee and
  primitive references from actual source rows. Its `calleeClause` interprets
  an existing original callee endpoint. It has no complete ArmDecl resolver or
  full IF Bind/Call interpretation. Successful primitive resolution does not
  supply the missing independent arm contract/result map.

## Exact failed application and remaining owner

No new application to the parent is claimed. The currently available route is

```text
original typed clause derivation
  -> R318.compileLegacy / legacyUse
  -> licensed child with that original dependent catalogue
  -X-> R306.arm_contribution_registered
  -> original R159 computation check and remaining App premises
```

The missing edge is **source-owned full contract interpretation and result
correspondence**, not a finished child and not a choice of W/Z meanings.
R306's actual arm consumer requires

```lean
sameCatalogue : childNode.catalogue =
  ComputedCallUnionRealizationR293.armsCatalogue inputs state scope arms
packet : Packet (armsCatalogue inputs state scope arms) raw
```

as well as the child. R318 supplies a child at its original catalogue; it does
not compute this equality. R293's catalogue uses `Fin arms.length`, a single
`scope`, and complete trace clauses read from `state.interfaces : Endpoint →
Interface`. The source arm grammar retains full scoped keys and arm-local
telescopes. No inspected constructor maps the original full contract to that
endpoint-indexed interpretation while proving its original relation/result
maps. Equality cannot simply be presumed: IF §3.2 explicitly retains original
branch/result relations rather than equating their worlds or catalogues.
This is a representation/application boundary, not a theorem that no lawful
scoped interpretation could exist.

TODO `R342-FULL-IF-ARM-READBACK-1`, owner primary / original IF interpretation
owner: implement the selected IF §3.2 and §4 full contract constructors at the
actual source declaration/reference formation, retaining every complete
parameterized arm and its original fields/actions. Compute the scoped
contract-to-result catalogue map required at R293/R306 (or establish an
appropriate scope-preserving generalization with the genuine legacy
application). Then feed the independently constructed licensed derivation
through that computed map. A supplied Table plus the desired catalogue
equation merely restates the missing edge. No semantic change is proposed.

At `SourceAppAdmissionR159.app_admission_iff`, arbitrary source operands,
contexts, both annotation cases, incoming annotation locals, genuine logical
admission, all App locals and both child judgments still use the one unchanged
candidate extension. This assignment removes none of these premises.
Original Checking remains independent; source membership cannot prove a fixed
foreign result target. The whole-language preservation obligation remains open.

Falsifier for a proposed repair: two arm occurrences can have the same endpoint
but different original scopes, licenses, substitutions or introduced-provider
future domains; both must survive independently. Include an unanchored arm,
nonreturning/pending developments and a registered recursive reference. No
successful source execution or arbitrary endpoint list authenticates these.

## Execution, coverage and cessation

Actual commands, all exit 0, in `notes/theory/lean`:

```text
elan which lake
  /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake
<resolved lake> --version
  Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
<resolved lake> env lean --version
  Lean (version 4.35.0, x86_64-unknown-linux-gnu,
        commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

Project/toolchain/manifest and skill source/execution references were read.
No build or bundled checker ran: no new declaration was constructed and the
continuation lane owns initial verification. No fresh kernel or axiom-audit
claim is made for historical declarations; new theorem types/axioms are N/A.
No failed Lean attempt, invented checker receipt or project axiom is hidden.
The work covers source authority, existing full dependent primitive/Union/
Conj/Scope/Rename/Ref constructors and exact downstream consumers. The full
Bind/Delay/Call semantic interpretation and its source/native correspondence
remain unconstructed. R341 countermodels are abstract evidence only.

3000-second grant; elapsed work was not separately instrumented. Bounded
read-only searches/reads and two version probes; no heavy build, installation,
background process, Git command or compiler/test/config/shared-state write.
Writes: this handoff only. Leased Lean file and `/tmp/yulang-r342-arms` were
not created. No descendants or generated cache outputs. **STOPPED; writes
stopped at frozen handoff notification.** Pending primary intake and any
independent source review; this is not self-certification or production approval.

## Frozen direct inputs

```text
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c  notes/design/2026-10-08-call-source-interface-definition.md
278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98  notes/theory/2026-10-08-call-source-interface-construction.md
2f3a5461b6dacaa29e881ba8b3003120b912e441dd5e4c47fc4ccaa27d3b31a6  notes/design/2026-10-24-computed-call-result-constructor.md
58ab61f7252818e208cc27be29fcc2c7633b35467c47dda0de126fa8bc87544b  notes/theory/2026-10-24-generated-computed-result-correspondence.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38  notes/design/2026-10-08-source-generalize-definition.md
15ac251eec2927cf32d2a5d32f7487f7de0e9f64b0d7b7032103bb3c2791ec6b  notes/theory/lean/YulangClosure/OriginalClauseCompilerR318.lean
077a114bf3f6f190ce4fc125f6113e411b15ea221f8183c6385e51940595ec38  notes/theory/lean/YulangClosure/ComputedCallTypedFormationR310.lean
50b1ce82dbd81d8c17a99461a78b77a9066094896f38e046d70fb4dd69365543  notes/theory/lean/YulangClosure/ComputedCallUnionRealizationR293.lean
77fa332ef53d272fe67a0c511fdebf9a3def7bf64baebfed84a3eec739ef203e  notes/theory/lean/YulangClosure/ComputedCallPhaseDescriptorR306.lean
5e948a1f8a3aab66028f885ebf16b6ffeed81999039e8a5a4e9c3caf84464408  notes/theory/lean/YulangClosure/SourceAppAdmissionR159.lean
deea4e7f8128ab9ad2caf7192bc4cb5b2ae16cc4c5682e01e85e7f13b1d92a1c  notes/theory/lean/YulangClosure/SourceDeclarationRetentionR295.lean
fd8ea7bed1bc42f5ed6ff32dbf01b812d8967e6cc33a4536ced74bb5710c375e  notes/theory/lean/YulangClosure/OriginalSourceViewRegistrationR330.lean
219eecf85e03aae12b71b773497a9506f229832e7a7c7e8c5bf944a84063cc10  notes/theory/lean/YulangClosure/OriginalSourceScopedInterpretationR335.lean
ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c  notes/theory/lean/lean-toolchain
212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4  notes/theory/lean/lakefile.toml
058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3  notes/theory/lean/lake-manifest.json
```

# R181 — proposed App inference-result owner and readback

Status: **FROZEN_CONDITIONAL_PROPOSAL; NOT_ADOPTED; UNREVIEWED**.
No definition, language meaning, kernel, compiler behavior or theorem is
adopted here. Original `SourceProblem.InferenceSoundness` remains OPEN.

## Authentication and exact dependency boundary

Primary baseline: `3529921c1eef91cc692a6ec9f821316486b45ebf`.
Contract SHA-256:
`763dfdfbdd53063a490d171a75ebe0f3aea886e5373c9853d633b45797649b36`.
Activation SHA-256:
`77fde96af1843a9974cfbef6f6e83049c266bffd6837f978b1e999e0a4a73372`.
The ACK-only pass verified both artifacts, strictly counted 16 distinct exact
direct-input rows with full 64-hex SHA-256 values, and recomputed 16/16
matches, zero mismatches. No semantic reads preceded authorization.

Content reads then reached the exact defining boundary at
`notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean:1`:
`import YulangClosure.OriginalSourceSyntax`. Its module-path owner is
`notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean`, outside the 16
pins. The actual Endpoint/Port/Context and source-category declarations are
needed to authenticate a complete endpoint/write catalogue. That owner was
neither opened nor hashed. The lane stopped further content reads and freezes
the proposal below as conditional. Existing endpoint uses are supported by
the admitted consumer code; completeness of their defining catalogue is not
claimed.

## Preserved parent and exact existing consumers

`Contracts.lean:103` declares an abstract SourceProblem. Its `generates`,
`solves`, `sourceJudgment` and `sameScoped` are independent fields, not a
concrete Yulang inference instance in this declaration. At lines 128–130:

```text
forall s x d a,
  p.supported s -> p.generates s x d -> p.solves d a ->
  exists e, p.sourceJudgment s x e /\ p.sameScoped s x e a
```

The quantifier over every satisfying `a` is fixed. Nothing here changes those
relations or adds typability to `supported`. The preceding contract comment
requires rigid imports, one hidden witness, all uses and futures; endpoint
equality alone is insufficient. A concrete instance/projection from these
abstract fields to the source-rule environment is not identified by the
admitted declarations. This is an unresolved integration dependency, not
permission to choose convenient new definitions.

`OriginalSourceGeneration.lean:111` fixes the unannotated App inventory:
one `.viewLogic` binder `b = <site,.viewLogic,0>`, local atoms for descriptor
formation, whole-argument compatibility, complete Call certificate, source
Call incidence and callable image (plus the existing conditional role atom),
and the two original children. The exact checks are:

```text
value:       <callee.site,.returnedValue> <= <site,.descriptor>
computation: <site,.callableImage>        <= <site,.synthesis>
```

They are not equations identifying these endpoints. Written annotations keep
their existing outer wrapper. `OriginalSourceChecking.lean:940`
`generated_application_ports` authenticates that same inventory; its following
`generated_application_checking` consumes `Satisfies` and projects an already
admitted candidate and finite value Checking proof. It does not construct
them from the abstract `p.solves` relation.

`Build` is the source-directed `compile(sourceRules ...)`, independently of
solver success (`OriginalSourceGeneration.lean`, Build definition).
`Satisfies` interprets `.existsE` as an existing admitted candidate plus body
satisfaction. Its locals already require original Local/Checking proofs.
`source_reconstruction` and `generated_constraints_imply_source_judgment`
therefore correctly consume full original formula satisfaction. Defining
`p.solves` to mean that satisfaction in order to obtain admission would assume
the missing connection. No such redefinition is proposed.

The exact payload consumer is
`OriginalSourceEnvironment.Logical` (lines 249–254): descriptor writes,
interface writes, viewMeaning, eta and joint witness. `Decoded.logical`
(line 346) installs those logical fields without replacing actual value/root/
binding objects. `LocalAdmissions.logical` (line 599) is the unchanged owning
relation. `DataAdmitted` requires its truth and binder-kind equality.
`scopeCandidate` (line 644) sets parents to the full environment event path
and retains selected occurrence and entire payload; `admitted_scoped_iff`
only reduces this to the same local admission after a genuine decode.
`Environment.extend` (generation line 567) appends the actual frame to the
complete existing frame list; it does not rebuild a per-App environment.

## Concrete data proposal, requiring owner confirmation

Proposed name: **AppInferenceResult**. This is an owner-facing record layout,
not a Lean structure or accepted semantic definition. It contains data and
construction provenance only, with the following explicit fields:

1. Source identity: actual App site, original context, original callee and
   argument source references, and references to their generated child
   records. These references do not contain the desired typed child judgment.
2. Prefix identity: reference to the complete preceding telescope, original
   scope graph and shared source dependencies, rather than a fresh telescope
   selected for this call.
3. Whole argument: the Call's actual ReifyOrigin and its Carrier-Delay of the
   original argument code and lexical references. No execution result or
   per-port fresh existential replaces that whole carrier.
4. Original generated operands: dependent F_c/R_f, complete Call result and
   result port, actual VIncl/WholeArgCompatible emission origins, and the
   actual-provider-indexed ordered entry/body/consumer/return suffix schema.
   These are syntactic origins, not semantic truths.
5. Complete symbolic image/profile recipe: references to the actual producer
   entry, body, designated consumer, native return delimiters, complete
   argument interface, all dependent fields/guards and shared dependencies.
   The recipe is intended to denote the complete original ExecuteCallable
   image; it is not a support-row union or closure-body-only profile.
6. Write recipe: separately named descriptor and interface destinations and
   symbolic terms, with original constituent/source ownership and dependency
   routes retained. The confirmed callee-check destination is
   `<site,.descriptor>`; the computation check's `.callableImage` and
   `.synthesis` remain distinct. The actual whole-argument port and full
   write set remain unresolved until the syntax catalogue and semantic owner
   confirm them. Do not invent an argument-port constructor.
7. View recipe: the source-owned interpretation of actual views, retaining
   interface identity and all dependent indices. It contains no preproved
   Function containment, admission or source typing.

The semantic equations for fields 5–7 are precisely the outstanding owner
definition, not an arbitrary function parameter declared to be sound. The
record would retain enough original construction information to make that
equation a direct construction target. Extraction from the unchanged
generation derivation, including totality on the existing source envelope,
must be proved rather than added as a condition of `p.generates`.

Proposed readback, written schematically rather than as executable code:

```text
r       = extractApp(original generation record, actual App site)
prefix  = read the complete preceding telescope at the same satisfying a
L       = evaluate all r's logical recipes at a and that same prefix
v       = scopeCandidate(environment_of(prefix), selected_occurrence(a,r),
                         .logical .viewLogic L)
next    = environment_of(prefix).extend b v
```

This names the required operations without asserting they exist. A faithful
readback must give simultaneous equations for all five Logical fields:
descriptor/interface write terms are interpreted at the actual endpoints;
viewMeaning comes from that same source-owned view interpretation;
eta and joint witness are the original solution's readouts at this complete
prefix. The types of parent Witness, semantic Assignment and JointWitness
are distinct; no raw equality between differently typed objects is assumed.
Their original correspondence must be proved. The selected occurrence is
read from the same retained witness/solution provenance; binder index 0 does
not justify arbitrarily choosing a runtime occurrence. No independent
per-field or per-call witness is generated.

`LocalAdmissions.logical` is **not** a record field, output premise or
definition of readback success. Its introduction is a subsequent theorem
about the constructed L using the original owning source rule. Likewise the
descriptorFormation atom, other local atoms, two finite checks and original
child derivations are proof obligations. A data-only readback may be useful
even while those obligations remain open; it cannot be labelled sound then.

## Authority matrix

Each row separates an existing equation/constraint from an unresolved choice.
R180 reports are frozen reviewed source evidence; their citations are not
permission to reopen sources outside this contract.

| Proposed line/obligation | Exact admitted authority | Disposition and authority needed |
| --- | --- | --- |
| Parent quantifiers, fixed a, original source judgment and sameScoped | Contracts.lean:103–130 | Fixed contract; no change authorized. |
| Generation without typed-derivation/solver premise | OriginalSourceGeneration.lean Build and file preamble | Fixed source-directed formula construction; actual p.generates projection remains uninstantiated here. |
| Meaning of p.solves and solution-to-prefix/readout | Contracts.lean:110–112 | Abstract consumer signature only; original concrete interpretation must be identified/confirmed, not replaced. |
| Actual callee returned value and App descriptor check endpoints | sourceRules App; generated_application_ports | Determined at these consumer uses. Full Endpoint/Port catalogue requires the unpinned syntax owner. |
| Whole inert argument and syntactic origin record | source-input construction §§3.1,3.4,4; frozen R180 outcome | Fixed requirement; child source typing is not supplied merely by an origin. |
| Complete Call image with actual entry/body/consumer/native returns | typed core §§3,9; frozen R180 outcome | Selected semantic content; effective symbolic recipe/evaluation still needs construction. |
| Full dependent constituent/interface frame | Call-source-interface construction §§2–5; frozen R180 source report | Original fields and routes must be retained; no witness existence or local admission follows from slot construction. |
| Descriptor term assigned at site.descriptor, interface write set, view interpretation | Logical declaration and original local atoms | Concrete representation/evaluation equation unresolved; requires semantic-owner confirmation and independent review. |
| Difference between site.callableImage and site.synthesis | sourceRules App; generated_application_ports | Existing checking relation, not permission to identify or overwrite both. |
| Existing preceding telescope and actual candidate frame | Environment.extend; scopeCandidate; decode/admitted_scoped_iff | Structural consumer determined; same-solution prefix reconstruction remains to prove. |
| One external assignment and lawful whole hiding | linking §3; frozen R180 source report | Conditional algebraic law under admissible transport/local separation; does not construct its premises. |
| eta/joint witness readback and parent sameScoped | Logical fields; SourceProblem.sameScoped contract | Must refer to the same original solution/witness package; exact readout functions and correspondence unresolved. |
| Occurrence/payload/parent event path | ScopedValue/ActualEvent; scopeCandidate; Environment.choose/extend | Actual candidate retained; selection provenance from original solution unresolved. |
| Unchanged logical admission | LocalAdmissions.logical, DataAdmitted | Prove introduction from original owning rule after readback; never assume or define away. |
| DescriptorFormation and remaining atoms | Kernel.atom; sourceRules App | Independent original local semantics; no permissive replacement kernel authorized. |
| Finite value/computation checks | Checking grammar; generated_application_checking | Separate constructive obligations; source-to-image recipe does not close them. |
| Scoped whole witness, all uses/futures, rigid imports | Contracts.lean preamble and sameScoped | Parent consumer fixed; assembling App payloads is insufficient without the whole-scope correspondence. |
| Native/Rust correspondence | SourceProblem.NativeCorrespondence declaration | Separate claim; outside this proposal and no Rust change proposed. |

## Underdetermined decisions and proof target

The admitted sources do not choose between these faithful representation
alternatives:

- Retain a constructor-directed symbolic image/profile term in the generated
  artifact, then interpret it directly at a; or retain a generated reference
  to a canonical original source image and prove its evaluation/readback
  correspondence. Both must preserve complete origin/dependency information.
- Use deterministic original readback if the original solution fixes all
  fields; or use a source-owned relational interpretation if original
  semantics permits multiple realizations. The latter still needs existence
  for every original satisfying a and one globally compatible witness, not
  independent App choices.

No alternative is selected here. The semantic owner must confirm the complete
image and endpoint/readout equations and whether representation choice is
merely a faithful formalization. A new admission, inference or source policy
requires explicit user semantic approval after independent review. Existing
accepted meaning should be formalized without reopening it; representation
convenience cannot strengthen the original generates/solves relations.

Once those equations are authenticated, the constructive leaf target is:
from the actual App projection of an unchanged generation derivation, the
same original satisfying a, and the legitimate induction results for the
preceding telescope and original children, construct the above L/v and prove
original logical admission, descriptor formation, and their exact
same-solution readback equations. The child/telescope induction results are
proof dependencies, not new hypotheses added to the parent soundness claim.
Assemble remaining atom/checking proofs into the original App rule; extend
the single parent witness and prove sameScoped with the unchanged a.

This is a non-adopted constructive target, not a conditional soundness theorem
already proved. Current concrete blockers are the unauthenticated syntax
catalogue, original SourceProblem instantiation/readout, and source-owned
image-to-Logical/admission equation. Recommended next action is sequential
admission of the exact syntax owner above, followed by semantic-owner
confirmation of the unresolved rows. Do not begin a proof by assuming any
of these rows as successful inference outputs.

## Evidence, limits and commit packet

Actual commands: exact path locator for R181 contract/activation; strict
ACK-only hash parser; admitted contract/R180 outcome/proof excerpt reads;
exact in-file searches and bounded reads of Contracts, source generation,
environment, interpretation and checking declarations; this sole leased
write. No broad repository source search, unpinned owner read/hash, executable
experiment, oracle comparison, proof check, Lean/Rust/build/test/runtime,
scratch/cache/environment, delegation, shared-state write or Git mutation.
All commands completed successfully; long historical report coverage was
bounded, not an exhaustive reread of every pinned file. Exact aggregate CPU,
elapsed time and peak memory were not instrumented; only lightweight commands
ran within the lane's 600-second packet. No completeness, production
conformance, parent closure or language-policy adoption is claimed.

Commit packet:

- Exact leased changed path:
  `tasks/agent-loop/inbox/app-inference-owner-intake-r181.md`.
- Baseline: `3529921c1eef91cc692a6ec9f821316486b45ebf`.
- Dependency changes: none observed at ACK; all 16 direct digests matched.
- Review status: frozen, fresh independent review pending.
- Checks: exact 2-artifact/16-row authentication and bounded source inspection;
  no tests or theorem commands.
- Proposed message: `Propose original App inference result and same-solution readback`.
- Shared-record deltas left to primary: STOPPED, non-adopted conditional
  proposal, exact syntax-owner boundary, unresolved authority rows and parent
  OPEN. No shared record was changed by this lane.

STOPPED: all reads and writes ended after this freeze; no descendant or
background process exists.

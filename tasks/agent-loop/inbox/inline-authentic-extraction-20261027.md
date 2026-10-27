# INLINE-AUTHENTIC-EXTRACTION-20261027/r1 — proof-lane obstruction

Assignment `/root/inline_authentic_extraction_proof`; handoff ID
`inline-authentic-extraction-20261027`, revision **1**. Outcome class:
**source-owner obstruction / incomplete probe**. Contract SHA-256
`015c8c276dde26747b82cea6bf1ff14784a19ced91a8234487cff93c46b09254`;
baseline `7a8423743c3f3b7bed9860a2def5f4c23e3e943b`.
Requested role: registered `lean_prover`; observed model/effort/session UUID
**UNKNOWN**. No descendants. The primary's final directive was to finish this
packet with a handoff only after the extractor's two-call cap; no substitute
candidate theorem module is authorized.

## Result and first missing evidence

No frozen `OriginalAuthenticInlineExtractionTrace.lean` exists. The source
producer reports both Cargo invocations exited 101 while compiling `yu-solver`,
before executing the extractor: allocation failures of 34832 and 1605648 bytes,
respectively. These are dependency/resource failures, not a source-language
counterexample. The proof lane did not run these commands and relies on the
source producer's frozen receipt linked below. No finite byte-span, owner,
resolution, tree, or extraction theorem was constructed or checked.

The immediate next premise is a corrected, actually executed and frozen trace,
owned by the provisional extractor lane under a new primary resource grant.
Three source defects/omissions were reported to the primary before any trace
was imported:

- `inline_origin` returns `lambda_range.start..binder_range.end`, later emitted
  as `outerBinderTokenRange`/`innerBinderTokenRange`. This includes the Lambda
  prefix. The exact binder range is the `binder` PositionId range returned by
  `parameter_source_origin`, and must equal `LocalSourceParameter.range`.
- `actual_callee_index` can designate a Group whose projected inner node is the
  Lambda. The serialized `applyCalleeIsInnerLambda = true` does not establish
  equality of those raw indices. Original `Source` has no Group constructor;
  an explicit source projection/Group-erasure equation is required.
- The proposed serialized fields do not include outer-body range/form and its
  complete ordered child list. They cannot independently establish the full
  block incidence needed to reconstruct the surrounding source Context.

These findings describe the unexecuted candidate source, not runtime receipts
or an independently reviewed frontend defect. The source lane accepted the
findings in its frozen handoff and did not mutate active build inputs.

## Governing source and unchanged parent

Read root `AGENTS.md`, `AGENTS.pre-sprint.md`, `rules/goal-driven-sprints.md`,
`rules/design-authority.md`, the admitted packet, and the Lean proof skill plus
its `references/sources.md` and `references/execution.md`.

The original parent remains `docs/yulang-whole-proof-closure-ja.md` §1/§4 and
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §1/§3/§5:
every supported original source program, every lawful finite construction
history, every retained extrusion occurrence, the same source scopes and joint
witness, complete Call, effects, required principal coverage, natural inference
and algorithmic termination. The authoritative birth-level correction is
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6; the unchanged
algorithmic contract is the 2026-10-11 top-level principles.

For source construction, the authority is
`notes/design/2026-10-08-source-generalize-definition.md` §2, selecting the
source construction manuscript §§3–5; inspected its actual Parameter, Lambda,
Name, Bind and complete Call rules. `docs/yulang-source-type-safety-ja.tex`
`sec:source`/`sec:all-source` supplies the 13/11/3 syntax inventory and its
opening correction/status notice remains binding: the manuscript is an
unreviewed research integration draft, not blanket semantic authority.

Lean parent definitions in `YulangClosure.SourceProblem` (`Contracts.lean`):
`InferenceSoundness` quantifies over supported source, generation and solution
and returns one source judgment and `sameScoped` witness;
`PrincipalCoverage` additionally quantifies over every lawful source derivation
and preserves its instance relation; `InferenceTermination` requires
accessibility from actual inference initial states. They remain proposition
definitions, not established concrete instances. This packet supplies none of
their missing source/native, inference, effect-hygiene or execution premises.

## Exact original application frontier

Inspected actual `YulangClosure.OriginalIdentityRealization.Identity`:
`declaration : OriginalSource.Declaration`,
`ambient : List OriginalSourceEvents.ScopeEntry`,
`context : OriginalSource.Context`, four Sites (`lambdaSite`, `formalSite`,
`patternSite`, `nameSite`), and `name : OriginalSource.Name`.
Site, Name and Declaration are Nat aliases. `Identity.parameter` computes the
actual unannotated Value formal, administrative `.wild`, and resolved `.name`;
it accepts no typing/safety derivation. `OriginalSource.Source` retains all
13 expression, 11 pattern and 3 statement constructors and its finite
containers; this packet omits no cases from the parent domain.

The reviewed reusable source-stated equations are unchanged (no fresh Lean
printing/axiom audit occurred here). With namespaces as in the actual module:

```lean
OriginalIdentityEntryOrigin.identity_source (source : Identity) :
  source.parameter.source =
    .lambda ⟨source.lambdaSite, none⟩
      ⟨source.formalSite, source.name, none, false⟩
      (.wild source.patternSite) (.name ⟨source.nameSite, none⟩ source.name)

OriginalIdentityEntryOrigin.identity_name_binding (source : Identity) :
  lookupBinding (bodyContext source.parameter) source.name =
    some {name := source.name, owner := source.formalSite, kind := .formal,
          entry := some .value, singleUse := true}

OriginalIdentityEntryOrigin.identity_application_owners
    (source : Identity) (callSite : Site) (argument : Source .expression) :
  sourceCallOwners source.context
    (.app ⟨callSite, none⟩ source.parameter.source argument) =
    .application callSite source.context source.lambdaSite argument.site ::
      (sourceCallOwners source.context source.parameter.source ++
        sourceCallOwners source.context argument)
```

Also inspected all originating entry-origin declarations:
`identity_registration`, `identity_registration_operands`,
`identity_closure_owner`, `identity_application_ports`,
`identity_invocation_owner`, `identity_receipt_owner`,
`identity_value_entry_sequence`, and `identity_name_rule`, together with
`OriginalFormalShared.actual_lambda_tree`, `formalContext`, `bodyContext`,
`OriginalParameterWorld.Parameter.source`/`registration` and
`OriginalIdentityRealization.identity_body_resolves_formal`.
Their complete source types and existing audit commands remain in the frozen
29-file source cone and unchanged `AuditOriginalIdentityEntryOrigin.lean`.
No new theorem/type/axiom result is delivered by this assignment.

After a valid trace exists, applying these equations requires an actual owner
witness mapping the same branded parse/HIR/root/occurrence/formal identities to
original expression Sites, formal Sites, administrative pattern/statement
Sites, resolved Names, declaration, root Context and ambient event telescope.
No current original allocator law for that witness was located. Numeric
occurrence/local-source/runtime ordinals cannot supply it by coincidence;
`OriginalInlineIdentityInterpretation`'s candidate pairCode is not authority.
This is the next original-model premise, owned by Luna's source-allocation
intake/proof lane, after the corrected trace prerequisite.

The inner Context is *derivable from* the source allocation and complete outer
body: `OriginalFormalShared.bodyContext outerParameter` computes the outer
formal and actual `outerParameter.body.nameCount`-based `singleUse`, followed
by the independently allocated root Context. This computation is not evidence
for the root Context, declaration or event telescope. The inner identity body
gets its own head formal via that same `bodyContext`; the actual Apply argument
must remain the outer-parameter Name, and the later sibling must resolve again
to that outer parameter. No arbitrary lexical prior, chosen argument,
independent Expansion.context or candidate numeric convention was substituted.
Name separation, if needed for exact use-count simplification, must follow
from the real allocator. No universal Rust extraction refinement, chosen
Closure/provider, Callee/Delay prefix, receipt/admission/readout or source/native
simulation follows from finite trace consistency.

## Read-only HIR owner basis

`module/local_source.rs`: same-root index authentication (`LocalSource.expression`),
source-ordered occurrence republication (`order_occurrences`), root-branded
parameter allocation, lexical `push_binding`/`restore`, inline Lambda
construction around lines 2092–2122, and sequence sibling restoration around
2629–2669. `source_identity.rs` retains original parse-root keys and
`InlineLambda { lambda, binder_range }`; `shadow.rs:parameter_source_origin`
authenticates the HIR/root, exact parse, Lambda node and unique binder token.
`parameter_source_position` intentionally returns MissingSource for inline
binders. `module.rs:owns_source_root`/`source_carrier_for` enforce the original
owner. These were read, not newly machine-verified. Focused inline HIR tests
were read and never run.

`runtime/program.rs` checks same-root LocalSource indices before label
`offset + ordinal` construction; `runtime/machine.rs` creates Lambda Closures
with captured environments and uses the actual Apply callee/argument in the
Callee frame. Neither equates such labels to original Sites or establishes the
full source/native theorem.

## Environment, hashes, resource use and cessation

All 28 contract pins matched by Python SHA-256 comparison. Read
`lean-toolchain`, `lakefile.toml`, `lake-manifest.json` and relevant README
sections: exact pin `leanprover/lean4:v4.35.0`, no external packages,
`moreLeanArgs = ["-j1", "-M1024"]`. Actual read-only command
`elan which lake` exited 0 and returned
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
No Lake/Lean binary was invoked; actual `--version` output is therefore
**NOT_OBSERVED**, not a claimed verified version. The primary withheld all
Lean execution pending corrected frozen trace and Cargo cessation; no such
trace arrived. Checker calls **0/6**, checker time **0/360 seconds**. No Lean
errors/goals/printed types/axiom results exist from this assignment. No test,
Cargo, installation, dependency mutation or Git operation occurred in this lane.
The exact active-time measurement is unavailable; the 1200-active-second
finite envelope was not extended.

The proof lane copied the complete 29-file entry-origin source cone and three
unchanged project config files to
`/tmp/yulang-inline-authentic-extraction-20261027/proof/project`; it never
built that copy or modified its inputs. Complete source-cone manifest:
`/tmp/yulang-inline-authentic-extraction-20261027/proof/base-cone.json`, SHA-256
`3fd93c3d560dab78c975cf2fe38b277368a09b2b26510b1c4e3b050dcd291386`.
This is a planned dependency snapshot, not an imported/generated proof artifact.
The complete copied source cone follows:

| Source under `notes/theory/lean/` | SHA-256 |
| --- | --- |
| `YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `YulangClosure/NativeClosureEnvironment.lean` | `39aa5cefa078dd423e54f0d9790f9a48e136326742e01f65149f317c907be957` |
| `YulangClosure/NativeDictionaryDenotation.lean` | `d44a78f08970a09ca4c3e99a1d8dea846286a299d1a2bc91ec3b5e0eabea9070` |
| `YulangClosure/OriginalCalleeDelayProvenance.lean` | `3acb041c530b19e78703b3f3030edd1b304ab7c20329974f0afc2d387428dbfe` |
| `YulangClosure/OriginalCheckingAdmission.lean` | `77a8dd74f5913814d3628f0aed189be24b4aafc4780839eaa57237676a157da7` |
| `YulangClosure/OriginalForcedParameter.lean` | `d16a45c459ea78b0f583ebd34d7a442d7247b55358ff6d990e3416c3d841aedf` |
| `YulangClosure/OriginalFormalAdmission.lean` | `77230ab7984ee544db16fe4d9663b73f98b9afa9c5d2610fad59c26753d5ac7c` |
| `YulangClosure/OriginalFormalShared.lean` | `abb9d69546e284fcb5fe6be9bb3c18269227e91da94e09eebf1a62e0b56e67f7` |
| `YulangClosure/OriginalIdentityCarrier.lean` | `f26878514518f14a4a99e799dad2ca28e4513c467a8dd24d86e6329b9e640616` |
| `YulangClosure/OriginalIdentityEntryOrigin.lean` | `9df7fccfe03becec491665a28a7fb65760e1245d76e68330fc9626da5533163e` |
| `YulangClosure/OriginalIdentityRealization.lean` | `30b0676f4af22dc7da2c75596a338db57a24b17662a4057801cfdff7ab4a2f42` |
| `YulangClosure/OriginalNameForceExtraction.lean` | `10ff6a2d4ac8a4a2c386396c495e0edfecc9bd4bb3ae40c8e0ab07e4cb0c7531` |
| `YulangClosure/OriginalParameterSemantics.lean` | `733c5b05e0db226f95d14ff2161c46e9a389b43d86b365b000a9656ec4fd0bd2` |
| `YulangClosure/OriginalParameterWorld.lean` | `7b5f849f744dbe56f374d8be6b11a5a218176abf6eeda2fb9da8180c7b1ff802` |
| `YulangClosure/OriginalRecursivePair.lean` | `1069c185c6fa190c2a0dd776ebf4efc7bfab8ece7e36f2f4049d480e50fa65e7` |
| `YulangClosure/OriginalRetainedParameter.lean` | `ae8915cf002019541d0658895f0604e98700ac23f47aac479fc8382cf65ef799` |
| `YulangClosure/OriginalReturnWorld.lean` | `0710f5d969af927c8f42b42f4972ba4f53ddce4ddb082e9d3d360e90c9ccf12b` |
| `YulangClosure/OriginalSourceChecking.lean` | `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6` |
| `YulangClosure/OriginalSourceClosure.lean` | `e39f165848c512830e6f92893c61e2d9f07cec66b729e8878c5f7d3491ab429a` |
| `YulangClosure/OriginalSourceEnvironment.lean` | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |
| `YulangClosure/OriginalSourceEvents.lean` | `cfd5f502a1e68a97e27e11a75400fae8789f167c92596aedb08ef7dfbb724342` |
| `YulangClosure/OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `YulangClosure/OriginalSourceInterpretation.lean` | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| `YulangClosure/OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `YulangClosure/OriginalValueEntryDemand.lean` | `9a171ecfbad7d632b2a15ef1f57d2d2dd46444aa36452de9158f1d1c7cfdae63` |
| `YulangClosure/OriginalWorldReadout.lean` | `edb82b9ecc62be486e057ee50152e30dad709f9a90196f78cab803838f08fb00` |
| `YulangClosure/SourceFunctionMembership.lean` | `8d370ee57e486ae48607d1bab493ae5135f28bf8a5a7ff1b0ef240fc0247e424` |
| `YulangClosure/SourceIdentityWorld.lean` | `6019fd9d57cde50183e016bd0c72de2c6eee72009065d85119fb0348dbcf0168` |
| `YulangClosure/SourceSignatureConstruction.lean` | `ed07890e29b4dcb38cabd18ec0e196efde9e95c64902942a9906a470b38c3311` |

Additional frozen dependencies:

- `notes/theory/lean/AuditOriginalIdentityEntryOrigin.lean` — `dc2eaa3f53d9b841c108040fd2a4d7bb6f05d8eac52bd4b37e4957d1a79583b2`.
- `notes/theory/lean/lean-toolchain` — `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`.
- `notes/theory/lean/lakefile.toml` — `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`.
- `notes/theory/lean/lake-manifest.json` — `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.
- `tools/inference-playground/src/bin/inline_authentic_extraction.rs` — `1ab6f3ed86d6bfc6d8f73baa40e5e46d5e3d451922af06fc1092a93ca29a39c0`.
- `tasks/agent-loop/inbox/inline-authentic-extraction-20261027-source.md` — `a6b09733222243b779cfb8ed4c2e7ba4da3aa0fc3c765c0bc225ef7852463d30`.

Only this leased handoff and the named scratch copy/manifest were written.
`notes/theory/lean/YulangClosure/OriginalAuthenticInlineExtraction.lean` and
`notes/theory/lean/AuditOriginalAuthenticInlineExtraction.lean` were not created;
no trace was imported. All own writes and processes stop with revision 1;
no checker/cache process was ever started and no descendant lease exists.
Independent review and Git/integration remain with Luna. All original A/B,
whole-language inference/executor, receipt/admission/readout, native and
production gates remain OPEN. This packet has no proved parent application.

# Frozen Oracle typed ACT and argument-contract provenance route

Status: frozen unreviewed research characterization; non-authoritative.
Gate: `ORIGINAL_ASSOC`, source/artifact correspondence method only.
Producer: delegated researcher; no independent review claimed.

## Objective, pins and authority

Determine whether a distinct typed ACT, portable bundle or source-contract
producer supplies an original owner/receiver typed path and complete Call
contribution before the pending comparison establishes success.

- Yulang3 baseline: `b7687afb33b1ae3367986c6f95145eb17820de74`.
- Frozen Oracle: `/tmp/yulang2-oracle-rebuild`, HEAD
  `a58eefc31e22141574b6f20c6a5748151c6d79f1`; inspected status was clean.
- Governing source: inferred-function-call-views §§1–5, especially §2 and
  §5.1; source-contracts-and-common-allowance §§2.1–3 and §10.
- Retain the primary's decisions: same original `X`, original scopes,
  `xi=(nu,K,D)`, actual callable role/entry, directional upper-output
  protection, approved annotation permission, Option A/Option 2. Oracle
  behavior supplies historical evidence only.

The call-view document requires source-produced `beta`, `Slots(beta)`, typed
paths, ownership and receiver incidences; it leaves their construction
judgments open. Source-contracts §2.1 takes independently typed owner/view
kernel contracts as input; §3.5 assumes them. This note supplies none of those
missing judgments by choosing a historical ID or path as their meaning.

## Scope and novelty

Read the `tasks/current.md:305–388` historical-route inventory before tracing.
Ordinary App lowering, resolved-use/SCC, selection incidence, Function
explanations/projection, Specializer2 demand reconstruction, role declaration
slots, Pattern boundaries, and cast/synthetic Apps are existing routes.

This pass follows two adjacent retained carriers outside the ordinary App
producer: finalized typed ACT capture/portable rehydration, and explicit
argument-effect annotation metadata. The latter's **producer and metadata
transport** are the distinct evidence; its downstream App consumer merely
identifies how that metadata is used. A bounded text check of the declaration
slot, Function path, prior annotation-licensing, Specializer2 consumer and
ordinary-Call novelty notes found no `ArgEffectContract`/`arg_effect_contracts`
or typed-ACT-bundle trace. This is a bounded novelty check, not an exhaustive
search of every historical note or Oracle subsystem.

## Route A: finalized ACT constructor → portable identity → consumer

All locators below are relative to the pinned Oracle root.

1. `module_table/nominal_act_identity.rs:9–54` under
   `crates/infer/src/` records template root/type identities, source paths,
   value member owner `TypeDeclId`, source `DefId`, kind, and field receiver
   `Value`/`Ref`. These are nominal declaration identities.
2. `module_table/typed_act_template.rs:309–365` captures only member
   `Def::Let { scheme: Some(..) }`; otherwise it returns
   `MissingClosedScheme`. A shared graph cloner copies reachable scheme types.
   Its member key (`:646–676`) is owner-relative nominal path, member kind and
   name. Scheme data (`crates/poly/src/types.rs:17–23`) contains quantifiers,
   role predicates, recursive bounds, stack quantifiers and predicate.
3. `module_table/typed_act_body.rs:84–139` reserves detached IDs, captures
   external targets, copies body nodes/runtime metadata and labels. External
   references (`:625–660`) are keyed by remapped `RefId`/`SelectId` and stable
   namespace identity. `typed_act_template.rs:97–184` constructs external
   `Method`/`FieldMethod` keys with nominal owner path, name and receiver kind;
   `:186–269` resolves through the same namespace tables and requires exactly
   one deduplicated target.
4. Body node copying (`typed_act_body.rs:688–775`) carries member schemes,
   lexical resolutions and `Expr::App(remapped_a,remapped_b)`. It does not add
   per-App typed contribution fields. `crates/poly/src/expr.rs:9–18` explicitly
   places temporary expression/use/selection types and open SCC state outside
   the Poly arena; its App constructor is the operand pair (`:478–483`).
5. `typed_act_bundle.rs:67–97,881–969` converts to portable identity, scheme
   and detached-body records. Member capture-run source IDs are omitted from
   the portable member pairs. `:618–727` rehydrates by nominal member key,
   obtains live source IDs, and sets `body.source_defs=Vec::new()`.
6. `module_table/typed_act_catalog.rs:141–269` applies schemes/body, resolves
   eligible external anchors, validates imported schemes and assembles a
   runtime surface with empty boundary interface. `:286–305` imports the
   surface and seeds finalized member definitions. The seed
   (`analysis/session/lifecycle.rs:197–215`) registers already closed schemes
   with the SCC manager as quantified definitions.

This is a concrete retained declaration/body identity and closed-scheme
transport route. Prefix capture (`lowering/body/act.rs:261–293`) and portable
generation (`typed_act_bundle.rs:760–815`) both call that finalized capture.
Thus this route cannot remove the need to construct the template member's
scheme in the first place. A closed captured member is a prerequisite; its
mere availability is no independent proof of pre-query source formation.

The nominal `owner` and receiver *kind* here are not the typed ownership path
or actual invocation receiver incidence required by the original Call fiber.
No inspected constructor connects them to original `p0,j_call,s,c,xi`.

## Route B: explicit annotation constructor → parameter identity → hygiene

1. `lowering/expr/lambda.rs:1244–1339` builds the annotation and successfully
   connects its parameter constraints, then produces
   `LambdaPatternAnnotation.argument_effect_contract`. No annotation yields
   `None` (`:1250–1265`). This route therefore covers explicit annotations,
   not the approved provisional unannotated `f` seed.
2. `:1357–1436` accepts a top-level Function annotation and collects explicit
   effect atoms. Each marker contains effect declaration path, nesting depth,
   and `PreserveMatchingPath`. Function traversal increments depth; both
   argument and return effect rows use that same depth. Tuple/application
   traversal keeps depth, and duplicate markers are removed.
3. `:896–917` stores the contract at the parameter `DefId` only for `Pat::Var`
   or `Pat::As`. In the ordinary defined-lambda path (`:287–320`) storage
   follows annotation connection/pattern lowering and precedes recursive
   lowering of the body. This establishes pre-body source metadata timing,
   **not** independence from all annotation constraint checking.
4. `crates/poly/src/expr.rs:76–81,147–162` serializes the map and marker
   fields. General compiled-runtime import explicitly remaps its `DefId`
   key and clones markers (`crates/infer/src/compiled_runtime.rs:1766–1803`).
5. `crates/specialize/src/specialize2/emit.rs:249–266,1149–1164,1177–1236`
   reads a call's callee spine, finds its lambda parameter by positional index
   or resolved definition, and obtains the contract at that parameter ID.
   It wraps the emitted argument boundary using that metadata.
6. `specialize2/runtime_shape.rs:879–905` and `hygiene.rs:39–93` consume it
   in a Function adapter hygiene plan; `PreserveMatchingPath` generates a
   guard marker with own-path protection and preserve-on-resume enabled.

The constructor receives annotation/declaration data, not pending `Q`
success. The consumer also receives solved actual/expected runtime shapes;
that later use cannot retroactively prove the metadata is an independently
typed original contribution. Nominal path, syntactic depth, and parameter
identity remain three different pieces of historical metadata.

## Discriminating derivations and exact hypotheses

**Established by source inspection:** the selected explicit annotation route
stores declaration-path metadata at a parameter before body lowering; the
finalized ACT route preserves nominal member/external identities and copies
already closed schemes. These are historical implementation facts, without
execution coverage or Yulang3 semantic authority.

**Bounded derived characterization:** assume a resolved effect declaration
`e`, legal finite `AnnType` structures, and the displayed pure marker
collector. Define two one-Function annotations with identical inert parameter
and return annotations, no other effect atoms:

```text
A = Function(param=_, arg_eff=Some([e]), ret_eff=None, ret=_)
B = Function(param=_, arg_eff=None, ret_eff=Some([e]), ret=_)
```

By `lambda.rs:1380–1399,1426–1433`, both produce exactly
`[(path(e),1,PreserveMatchingPath)]`. The sole mutation moves one effect atom
between two distinct Function ports. The collector loses that port choice;
therefore no function of this marker alone can invert both port positions.
One Function and one effect atom suffice. This is an AST-level metadata
discriminator, not two admitted source programs with identical complete
artifacts: annotation constraints and final schemes can differ and can retain
other information. It establishes no ambiguity of the approved language.

**Conditional artifact erasure lemma:** fix a valid template identity, all
member closed schemes, body graph, namespace tables and labels. Take two Poly
arenas equal except that one selected parameter has a nonempty
`arg_effect_contracts` entry in one arena and no entry in the other. Assume
capture otherwise succeeds. `BodyImporter::new` creates a fresh target arena;
its definition/expression import and complete `import_runtime_metadata`
(`typed_act_body.rs:575–590,688–775,910–961`) never copy this map. Hence the two
detached captured bodies are equal in that coordinate: both have an empty
argument-contract map. This follows from inspecting the importer, not running
a checker. Such twins are not asserted to arise from independently admitted
source. Current Var/LabelSub templates were not inspected for a nonempty map;
no observable Oracle defect or required production repair is claimed.

Both derivations test retained-artifact sufficiency. Neither supplies the
missing source rule, a complete licensing grammar or complete `CALL_TYPE`.

## Exact mapping to the open target

| Target | Historical retained analogue | Missing premise |
| --- | --- | --- |
| `beta`, `Slots(beta)` | Nominal member key; parameter `DefId` | Source-owned static slot formation and exhaustive inventory |
| typed `p0` | Effect namespace path plus nesting depth | Original typed structural port, owner and scope incidence |
| `j_call` | Detached App operand identity; downstream call-spine index | Original call introduction linked to typed kernel |
| `s` | Nominal declaration owner or parameter key | Original kernel's slot denotation; no identification is chosen |
| `c` | Scheme/body and explicit guard marker | Original complete contribution, receiver/body/consumer/pending suffix |
| shared `xi` | One cloned scheme graph and nominal substitutions | Same original jointly scoped `nu,K,D` and semantic incidence certificate |

The precise blocker is the absent bridge from these historical carriers to an
independently typed original owner/view-kernel witness. Increasing searches
of nominal keys or guard markers would leave that premise unchanged.
`ORIGINAL_ASSOC` and dependent gates remain open; this is not a global absence
or nonderivability result.

## Independence, checks, coverage and resources

No Oracle source/output/test was executed. No checker, mutation test, build,
formatting, benchmark or Git mutation was run. There are no random seeds or
enumeration ranges; the two finite symbolic comparisons above are the whole
discrimination domain. The single local-command stream used `rg`, bounded
`sed`, `cat` for rules, read-only Git pin/status/diff, and SHA-256 hashing.
Initial combined full-file reads of `tasks/current.md` and ACT source were
truncated; claims rely on subsequent targeted complete constructor/consumer
ranges, not those truncated captures. A first locator search named nonexistent
flat module/compiled-surface paths; corrected reads used module directories
and `compiled_runtime.rs`. Those search errors were not evidence of absence.

The capture/rehydration producer and resolver share nominal namespace metadata;
runtime consumers share the same Poly body and annotation marker representation.
They are not independent semantic oracles. A roundtrip/differential would check
agreement on those assumptions only. There is no source-adequacy proof from
transition rules assumed by a checker.

Budget: maximum 15 minutes, serial lightweight commands, no heavy process;
CPU/RSS were not instrumented. Wall time was within the assigned window; exact
process peak/CPU totals are unknown. No scratch output files were created.
Only this leased note was written; writing stops upon handoff for frozen review.

Final narrow commands: `git diff --no-index --check /dev/null
notes/progress/2026-10-08-frozen-oracle-typed-provenance-route.md` reported no
whitespace diagnostics (exit 1 denotes the added-file difference);
`git status --short -- <leased-path>` showed only that untracked note.
`git rev-parse HEAD` and Oracle `git -C <oracle-root> rev-parse HEAD` still
matched both pins; Oracle `git status --short` remained empty. Input hashing
used `sha256sum <the direct paths listed below>`.

Omitted: actual bundle decode or content inspection; admitted-source
construction for the symbolic twins; all template bodies; all source import
and specialize alternatives; generalization semantics; whole receiver
histories; production conformance; exhaustive repository-wide absence.
Failure conditions: changed producer/importer dependencies, unsupported marker
AST forms, failure to resolve `e`, failed template closure/anchor validation,
or another independently typed source-kernel constructor outside this bounded
route. Those would require revalidation or a different result, not choosing
an association by ID.

Recommended next action: return the localized P2 owner/view-kernel bridge to
the primary; retain these two carriers as historical analogues without another
equivalent Oracle probe. Any separate investigation of the ACT metadata
omission should first establish an actual supported template with a contract
entry and receive its own scope.

## Dependency hashes

SHA-256 of inspected direct inputs; Oracle paths below start at `crates/`.
All are pinned observations, not changed dependencies.

| Input | SHA-256 |
| --- | --- |
| Y3 inferred-function-call-views | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| Y3 source-contracts-and-common-allowance | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| infer/src/module_table/nominal_act_identity.rs | `57d8d2976c28f7258e5df84c0ea64dec620d74c99026e64717811a3946e83dd5` |
| infer/src/module_table/typed_act_template.rs | `368b08f0be1a6901b8c1124b676378a4414abf4a09b2d3a2b117b91ef65a2cf4` |
| infer/src/module_table/typed_act_body.rs | `940fffe24897bb88bbbff92982b98dc3b73deaee7368c5511bf91c222b839ef2` |
| infer/src/module_table/typed_act_catalog.rs | `51a41a3cb195bb5e0991717056eb6c6cd71cfcecfdefd8e40e7b38dd6bb2a49f` |
| infer/src/typed_act_bundle.rs | `88e9444796446dd714d8ddc65c174c1aa3ddc8d886b766b1a124c6c3909ba6c1` |
| infer/src/lowering/expr/lambda.rs | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| infer/src/compiled_runtime.rs | `9c352576fb01b00d623eae34f32176f5da8af67ed9a69e5bea68e3f371001b58` |
| infer/src/analysis/session/lifecycle.rs | `196b0f1eeef891e3547bf77e3d00f5f0574399e24bc59c4697219df6ff93d5ed` |
| poly/src/expr.rs | `fbee59668b778c09cf32ad5b59c919feb36726b1af75cb630bca1ca9b7aebd88` |
| poly/src/types.rs | `9211e62291b82e71e1b78763b83fe9f1d81e0fe4396d9e12d42e9a4a9b13b47c` |
| specialize/src/specialize2/emit.rs | `7318b132cef4217ae089d084577fb28f3abed34a5728474ee8569e4079d71e7c` |
| specialize/src/specialize2/runtime_shape.rs | `e4443fa1c23a1ea0d957d4582f484abea53e1aa0dffe2f86a3f44fc70aa2e0e4` |
| specialize/src/hygiene.rs | `266c05f4c937fc9f9d95cb6b1c435e9ff74181ffc5e8d7719faeefc7a8ff33e4` |

## Commit packet

- Exact lease: `notes/progress/2026-10-08-frozen-oracle-typed-provenance-route.md`.
- Baseline: Y3 `b7687afb33b1ae3367986c6f95145eb17820de74`; Oracle
  `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; governing Y3 files had empty diff from pin,
  and Oracle status was clean. Primary rechecks before integration.
- Review status: frozen, unreviewed, non-authoritative historical
  characterization and conditional artifact derivation.
- Checks already run: source/locator reads, pin/status/diff inspection and input
  SHA-256; narrow note whitespace check with no diagnostics; no executable or
  test/build checks.
- Proposed message: `research: characterize frozen Oracle typed ACT and argument-contract provenance`.
- Shared deltas deferred to primary/curator: add bounded historical route and
  exact P2 bridge stop to the relevant inventory if adjudicated useful; keep
  `ORIGINAL_ASSOC` and all dependent gate statuses unchanged. No shared records
  or question bundles were edited.

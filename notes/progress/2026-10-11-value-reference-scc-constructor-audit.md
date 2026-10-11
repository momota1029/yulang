# Value-reference SCC constructor audit

Status: frozen, independently reviewed research checkpoint; bounded source correspondence audit
Baseline: `57820e44e7062404e90b5226def58f94445aafcb`
Owner/method: complementary researcher; source constructor and consumer inspection
Lease: this file only; no compiler/design/shared-record edits, tests, builds, or Git mutations

## Objective and governing premise

Locate actual candidate Value-variable construction and reference transport for
the user's graph: vertices are Value variables; edges are references in their
values; comparisons and parent metadata do not themselves create edges.
Extrusion copies remain distinct vertices until an authorized equality applies.
This audit neither selects another graph nor proves or refutes parent/copy SCC
reachability.

Governing sections are `rules/design-authority.md` §Authority order,
`rules/compiler-engineering.md` §§Natural compiler behavior and proof-obligation
economy / Deterministic Simple-sub inference,
`notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–5, and
`notes/design/2026-10-10-parent-copy-scc-intrusion.md` §§Selected operation and
compiler responsibility / Value-reference SCC clarification. The current
`notes/design/2026-10-11-source-value-reference-intrusion-draft.md`
§§Relations that must remain distinct / Missing bridge / Decision required
before authority can move is a research input, not new authority. Its binding
abstraction is not an established projection to solver Value identities.

## Direct construction evidence

All locators below are repository-relative, at the pinned baseline.

| Owner | Directly observed construction | Evidence limit |
| --- | --- | --- |
| HIR local initializer | Installs temporary self identity for a function initializer, parameter identities, then its Lambda/body slots | `crates/yu-hir/src/module/local_source.rs:329–363`; these are source identities, not solver rows |
| HIR Name | Retains lexical or module resolution in `LocalSourceForm::Name` | `local_source.rs:636–657`; establishes which binding a source occurrence names |
| HIR Block | Retains separate binding initializer slots and a final expression; schedules initializers separately | `local_source.rs:793–829`; containment alone supplies no reference |
| Candidate expression | Creates Value/Effect component recipes for expressions | `crates/yu-solver/src/candidate_source.rs:187–218`, `shadow_apply.rs:1022–1037`; parameter Names select a parameter endpoint, and ascriptions can alias existing endpoints (`candidate_source.rs:219–233`) |
| Session initialization | Allocates one dense Value row for each Value component and one for each parameter recipe | `crates/yu-solver/src/lib.rs:10047–10103`; rows start with empty `VariableBounds` |
| Fresh Value allocator | Appends an empty bounds row, level, Fresh metadata, and extrusion mark | `lib.rs:10156–10180`; allocation alone supplies no value-reference adjacency |
| Extrusion | Above the target level, allocates a fresh Value copy, records actual parent/polarity/target, and inserts a one-sided bound on the original | `candidate_extrusion.rs:90–123`; parent record is explicitly absent from adjacency (`candidate_intrusion.rs:171–220`) |
| Fresh scheme use | Allocates a Value row for a captured local row still above boundary and generic; canonical shared anchors retain their existing identity | `candidate_scheme.rs:1008–1020`; the mapping is per use, with one entry per canonical source identity |
| Annotation/signature | Allocates scoped annotation variables, a local annotated scheme root, and operation-signature variables | `candidate_effect.rs:958–976`, `:1160–1173`, `:1385–1396`; these additional Value constructors prevent an expression-only inventory |

The annotation/signature neighbors were inspected because the source schedule
dispatches formal/local/expression annotations and operations as well as Names,
Lambdas and applications (`candidate_source.rs:660–683`). This inventory covers
the audited private candidate paths, not every legacy/public Value allocator.

## What constructs stored references

The audited representation demonstrably constructs **term references** and
**bound payload references**. Their correspondence to references in the value
owned by a Value variable is the open premise.

* Lambda constructs a positive Function whose argument points to a parameter
  term and whose result points to its body Value endpoint
  (`lib.rs:11233–11261`, `:11342–11362`). It attaches that Function to the
  Lambda root by admitting `function <: root`.
* Apply constructs a negative Function demand from the argument and result
  endpoints, then admits `callee <: demand`
  (`shadow_apply.rs:1331–1400`). The native input retains the precise callee,
  argument, result and demand ports (`:1373–1381`). The demand is checking
  structure; an edge in the approved graph does not follow from its comparison.
* Group and Block final-expression flow create `CandidateRelation::Group`
  (`candidate_source.rs:438–443`, `:462–470`), which admits child-to-result
  comparison (`shadow_apply.rs:1327–1330`).
* Active local recursion emits `Action::Link` from the initializer endpoint to
  the Name occurrence row. Published local Names emit `Action::Local`; parameter
  Names use the parameter endpoint; module Names use the internal/incoming route
  (`candidate_source.rs:369–388`, `:660–681`). This distinguishes four real
  Name paths rather than treating one recursive callsite as exhaustive.
* Function construction stores four supplied ports in the term arena
  (`lib.rs:10266–10290`). Scoped annotations also build positive and negative
  Function pairs (`candidate_effect.rs:1034–1050`).

`VariableBounds` stores lower/upper rows and exact endpoints
(`lib.rs:3968–3978`). `candidate_apply_value` chooses a storage owner using row
levels and endpoint shape (`candidate_extrusion.rs:808–831`). Those stores do
not independently certify an edge owner under the user's graph.

## Lifecycle evidence and its precise limit

Extrusion memoizes copy identities before traversing selected bounds, remaps
Function ports with polarity reversal for argument ports, rebuilds changed
Functions, and transfers bound origins (`candidate_extrusion.rs:27–34`,
`:124–162`, `:224–253`, `:308–323`, `:325–352`). These are direct facts about
operational payload reconstruction. No audited edge-owner record accompanies
the remapping as an actual Value-reference graph.

Generalization capture classifies rows by `level > boundary && !non_generic`
(`candidate_scheme.rs:301–325`). Older shared rows retain live mutable bounds
instead of being expanded into the captured graph (`:567–572`); local rows
capture both bound lanes (`:576–614`). Module component members finish their
open schedules before capture/publication (`:842–915`). A local scheme retains
its identity, live root and boundary (`:1320–1334`); later local use recaptures
that live root (`:1362–1378`). Module use similarly recaptures the stored live
root before instantiation (`:947–961`).

Freshening remaps generic rows, rebuilds Function nodes using the remapped ports
(`candidate_scheme.rs:1008–1020`, `:1109–1160`), restores captured bounds, and
admits the fresh root-to-use comparison (`:1500–1518` for local use;
`:1268–1304` for module use). Shared anchors and fresh-use independence are
therefore explicit operational mechanisms. Their preservation of the approved
reference relation cannot yet be concluded because that relation has not been
attached to the original Value constructors.

Current intrusion consumes a different explicit representation:
`candidate_intrusion.rs:390–412` follows both Value bound lanes; `:415–443`
follows Effect rows/views; `:445–468` follows structural Function ports.
`Dependencies::intern` admits Value rows, positive/negative Function terms,
Effect rows, and Support/Allowance views (`:622–634`). It checks recorded
parent/copy representatives for component equality (`:474–486`). Parent
metadata is correctly excluded as an adjacency source (`:213`, `:480`).
Whether structural/Effect vertices can be eliminated to compute exactly the
fixed Value-variable reference SCCs remains unproved; their mere presence is
not itself a source-qualified counterexample.

## Derivation and first missing bridge

Hypotheses: (H1) the user's fixed Value-variable graph definition above; (H2)
the pinned candidate constructors/consumers just inspected. No assumption that
a solver comparison or a bound lane is a semantic edge is added.

1. HIR Name construction independently establishes resolution to a source
   binding (`local_source.rs:636–657`).
2. The candidate distinguishes that reference's endpoint and occurrence but
   emits `Link` or a local-use action (`candidate_source.rs:381–388`).
3. Link execution and the end of local fresh use call
   `admit_candidate_value_link`, which records a comparison/cause and invokes
   Value solving (`candidate_scheme.rs:1337–1344`, `:1516–1518`).
4. The SCC consumer later obtains adjacency from bounds and structural ports,
   without consulting the HIR reference owner/resolution
   (`candidate_intrusion.rs:390–468`).

The first missing premise is the mapping at steps 2–3: **which actual Value
variable owns the referenced value at this construction, which actual Value
identity its reference denotes, and why that exact incidence is retained or
faithfully represented by the later SCC adjacency.** The containing source
binding, a Name occurrence facade, and an extrusion-created identity are not
interchangeable without this bridge. Merely tagging a comparison with its
source occurrence does not prove the mapping.

This is a bounded source characterization and a reduced premise, not an
established general theorem, semantic refutation, SCC witness, soundness result,
or independent review. It stops at that construction premise as assigned.

## Checks, coverage, resources and handoff

Commands: read-only `rg -n`, `rg --files`, numbered `sed` excerpts, `sha256sum`,
and `git diff --name-only <baseline> -- <direct dependencies>`. The dependency
diff was empty. The current sharpened Draft was reread before freezing.
Broad locator output was truncated; no exhaustive whole-repository search is
claimed. Relevant constructor/consumer ranges listed above were read directly.
No executable oracle, seeds/ranges, mutations, tests, builds or runtime traces
were used. Source inspection is independent of the prover's mathematical
derivation, but shares its user-selected semantic premise and candidate source
baseline; it cannot certify the source rules by assuming solver transitions.

Resource envelope: one sequential lightweight source-read pass, zero Cargo or
heavy processes, zero child agents. CPU/RAM and exact wall time were not
instrumented. Unverified: legacy/public paths, all source forms beyond the
audited candidate envelope, runtime histories, rollback/replay edge transport,
and SCC preservation after equality or structural-vertex elimination.

Recommended next action: assign the existing source/constructor owner the
single missing Name/Lambda/Apply-to-Value-reference mapping, including extrusion
copies and shared/fresh use identities, before another payload-SCC witness
search or dependent implementation change.

## Commit packet

* Exact leased path: `notes/progress/2026-10-11-value-reference-scc-constructor-audit.md`.
* Baseline SHA: `57820e44e7062404e90b5226def58f94445aafcb`.
* Dependency changes: none relative to baseline on audited paths. Selected
  SHA-256 fingerprints: parent-copy authority
  `2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0`;
  sharpened Draft
  `4323a2223dbeb563f7822e6ff4fb889438c36d5a9139c0872070ac8112fefd94`;
  candidate source
  `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49`;
  intrusion consumer
  `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0`.
* Review status: compiler_referee passed bounded semantic/source-bridge review;
  no gate closure or production conformance claim.
* Checks already run: source reads, dependency diff, fingerprints; no tests/builds.
* Proposed commit message: `research: audit Value-reference SCC constructor bridge`.
* Shared-record deltas left for primary/curator: link this reduced premise from
  the existing graph/source correspondence gate and record its owning lane;
  preserve OPEN status of original reachability and inference obligations.

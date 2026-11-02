# R103 logical-occurrence repaired construction, revision 1

Status: **CONSTRUCTED / UNCHECKED / FROZEN / WRITES STOPPED**. This leaf has
not run Lean, Lake, the checker, tests, or a build. Kernel acceptance, complete
axiom results, independent review and primary adjudication are pending.

Sprint: `EFFECT-PERMISSION-CAPTURE-COHERENCE/20261101-R103`, contract r1,
SHA-256 `084e12892159d2ed9b503a4691442fe8b2975b216270767c0a3d01d052526156`.
Assignment/author: `/root/r103_occurrences_proof`, sole author of this repair;
prior R93 author retained as provenance for the copied candidate. No children,
coauthors, reviewer appointments, background processes or descendant leases.
Requested role: `lean_prover`; effective runtime model/effort: UNKNOWN to this
leaf. Primary supplied baseline: `739cb332d` on `yulang3`; no Git lookup or
mutation was performed. Claim class: candidate syntactic construction.

## Governing source and unchanged parent

Read root `AGENTS.md`, `AGENTS.pre-sprint.md`, `rules/goal-driven-sprints.md`,
`tasks/agent-loop/README.md`, the Lean skill and its sources/execution references,
and the primary's fixed R103 packet. Source selection follows
`notes/design/2026-10-08-source-generalize-definition.md` §2 (SHA-256
`46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`), selecting
`notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §§3–5
(SHA-256 `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`).
Its §3.3 distinguishes ViewLogic before challenges, retained Shared, and
EventProof under the original event telescope. The source manuscript's opening
correction and §§`sec:source`/`sec:all-source` were read:
`docs/yulang-source-type-safety-ja.tex`, SHA-256
`2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`.
The manuscript and the 2026-10-26 generation-construction note are research
source maps, not new semantic authority.

Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1,3,5,7, SHA-256
`3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`.
It retains every supported source, lawful finite construction history and actual
qualified extrusion, and one joint lawful strategy at the original scopes with
all original external conclusions and correlated evidence. The current correction
is `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6, SHA-256
`ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`:
qualification uses the immutable Value birth-level induced graph. No parent
quantifier, witness, language feature, scope, or semantic admission is changed.

## Frozen dependencies and artifact

| Input | Actual SHA-256 |
| --- | --- |
| `YulangClosure/OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `YulangClosure/OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `YulangClosure/SourceLogicalOccurrencesR93.lean` | `3c3ac12f0e652b361925ff0d80db78b4bae96f4bd2cc83f3f8346d6e5db54192` |
| `lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lakefile.toml` | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| `lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| R95 result review | `f0676825d9bea19204ed4900f160a661aef5db8484aee421d7d14349bea95cb6` |

Paths in the first six rows are under `notes/theory/lean/`. The source module's
only project import is `OriginalSourceGeneration`; Generation imports Syntax,
and Syntax imports `Std`. The current pin reads `leanprover/lean4:v4.35.0`;
the manifest has no external packages. These files were read and hashed without
executing a toolchain or modifying dependencies.

Changed artifact: `notes/theory/lean/YulangClosure/SourceLogicalOccurrencesR103.lean`,
23,187 bytes, SHA-256
`e31503875088a2f8dae68b1269433c4b9093a7d95e11ded03b7a169f56d6ecf0`.
Only the artifact and this handoff are written. No root import, original source,
Rust, config, task index/state, scratch, `.lake`, audit file or generated output
is written.

For the primary's existing flattened-stdin strategy: byte-concatenate Syntax,
Generation, and this R103 module, stripping only the leading Generation import
of Syntax and this module's leading import of Generation, preserving `import Std`
and adding no separators. The in-memory result is 111,624 bytes, SHA-256
`b0194148fb82d5a7c4b9af2bf8934764ec356cf2989b6cccd1cc9df1c69b7dcf`.
It was hashed only, never executed or written as scratch. The primary must freeze
and independently review its exact execution input before its one invocation.

## Repair and material failure evidence

R95 result review and its retained verification receipt are the actual diagnostic
source. The R95 call exited 1; eight of ten theorem roots depended on `sorryAx`.
That failure is preserved, not replaced by this candidate's static inspection.
The four repaired local mechanisms are:

1. `encode_lookup`: every tree/forest child now explicitly instantiates
   `ih nextScope (.tree child)` or `ih nextScope (.forest children)`. R95's
   thirteen stuck `apply ih` goals had reduced `encodeTree`/`encodeForest` and
   an implicit cursor that unification did not recover. Every other direction
   still reduces to reflexivity; no generated constructor is omitted.
2. `source_provenance`: after the `follow` case split and occurrence equality
   transport, the goal is already a reduced `some ... = some ...`. Its witness
   is `rfl`, replacing the ill-typed pre-rewrite `hfollow`.
3. `appRule`: the complete original call-kind list has explicit `List AtomKind`
   context. This fixes the six underconstrained dotted constructors without
   changing the list or its conditional singleton-formal premise. `app_exact`
   still uses both annotation alternatives and the unchanged source equation.
4. `lambda_body_exact`: all four annotation/entry cases first rewrite the
   well-founded `sourceRules` equation. A `change` then definitionally reduces
   the private generator helpers and route traversal to the exact original body
   rule with the explicitly accumulated telescope. `simp` normalizes only the
   telescope/formal-entry expressions and list association. The body and its
   arbitrary formal annotation, pattern and context remain unchanged.

In-memory header comparison against R93 reported ten byte-identical theorem
headers modulo their enclosing namespace; no assumption was added or conclusion
weakened. Static forbidden-term search found only the existing explanatory comment
containing the word `axiom`; no forbidden declaration or tactic was introduced.
These are construction inspections, not Lean acceptance or independent review.

## Exact ten theorem statements and audit obligation

All names below have prefix
`YulangClosure.OriginalSource.LogicalOccurrencesR103.`. The following are source
statements, not claimed fresh printed types. Every root has embedded fully
qualified `#check @...` and `#print axioms ...` commands in the leased module.

```lean
theorem inventory_iff_lookup (index : Index) (route : Route) (occurrence : Occurrence) :
    (route, occurrence) ∈ inventory index ↔ lookup index route = some occurrence

theorem encode_lookup (scope : List ScopeFrame) (cursor : Cursor) (route : Route) :
    lookup (encode scope cursor) route = observe scope cursor route

theorem observe_eq_follow (scope : List ScopeFrame) (cursor : Cursor) (route : Route) :
    observe scope cursor route =
      (follow scope cursor route).bind (fun position =>
        payload position.enclosing position.cursor)

theorem source_membership_iff (context : Context) {category : Category}
    (source : Source category) (scope : List ScopeFrame) (route : Route)
    (occurrence : Occurrence) :
    (route, occurrence) ∈ sourceInventory context source scope ↔
      observe scope (.tree (sourceRules context source)) route = some occurrence

theorem full_route_unique (context : Context) {category : Category}
    (source : Source category) (scope : List ScopeFrame) (route : Route)
    (first second : Occurrence)
    (hfirst : (route, first) ∈ sourceInventory context source scope)
    (hsecond : (route, second) ∈ sourceInventory context source scope) :
    first = second

theorem source_provenance (context : Context) {category : Category}
    (source : Source category) (scope : List ScopeFrame) (route : Route)
    (occurrence : Occurrence)
    (member : (route, occurrence) ∈ sourceInventory context source scope) :
    ∃ binder body,
      follow scope (.tree (sourceRules context source)) route =
        some ⟨occurrence.enclosing, .tree (.existsE binder body)⟩ ∧
      logicalKind binder.kind = true ∧
      occurrence.binder = binder ∧ occurrence.subtree = body

theorem app_exact (context : Context) (mark : Mark)
    (callee argument : Source .expression) (scope : List ScopeFrame) :
    observe scope (.tree (sourceRules context (.app mark callee argument)))
      (annotationRoute mark) =
      some ⟨⟨mark.site, .viewLogic, 0⟩, scope, appRule context mark callee argument⟩

theorem lambda_body_exact (context : Context) (mark : Mark) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) (scope : List ScopeFrame) :
    observe scope (.tree (sourceRules context (.lambda mark formal pattern body)))
      (bodyRoute mark formal) =
      some ⟨⟨body.site, .eventProof, 0⟩, bodyScope scope mark formal,
        bodyRule context mark formal pattern body⟩

theorem app_inventory (context : Context) (mark : Mark)
    (callee argument : Source .expression) (scope : List ScopeFrame) :
    (annotationRoute mark,
      (⟨⟨mark.site, .viewLogic, 0⟩, scope, appRule context mark callee argument⟩ : Occurrence)) ∈
      sourceInventory context (.app mark callee argument) scope

theorem lambda_body_inventory (context : Context) (mark : Mark) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) (scope : List ScopeFrame) :
    (bodyRoute mark formal,
      (⟨⟨body.site, .eventProof, 0⟩, bodyScope scope mark formal,
        bodyRule context mark formal pattern body⟩ : Occurrence)) ∈
      sourceInventory context (.lambda mark formal pattern body) scope
```

For **each of these ten roots**, the actual printed type and complete transitive
axiom list are **NOT RUN**. The primary's check must accept all ten as theorem
declarations, return exit 0 with no elaboration errors/recovery holes, and retain
every complete printed type/axiom line. Allowed standard axioms are at most
`propext`, `Classical.choice`, `Quot.sound`; each actual list must be reported.
No empty list or clean axiom result is claimed here. Any `sorryAx`, project axiom,
native-evaluation assumption or bypass fails the gate. The skill checker was read
but not run: its Lake build/cache operations conflict with this exact no-build,
primary-only, one-invocation packet. No checker settings were changed.

## Coverage, parent application and remaining owner

`OriginalSource.Source` and `sourceRules` retain all 13 expression, 11 pattern,
3 statement forms and every container/default/guard/operation-arm/binding/module
and block continuation. The generic traversal retains all 10 `RuleTree`
constructors and both `RuleForest` constructors. App's arbitrary operands,
conditional singleton-formal branch and both annotation alternatives remain.
Lambda retains both Value/Computation entry modes, both outer annotation
alternatives and arbitrary formal annotations, patterns, bodies and input scopes.
No distinct-site assumption is imposed. Full routes distinguish repeated sites.

Routes are binary structural positions. An annotation adds `[false,false]`.
Lambda has eight initial false steps, an extra false for Value execution, then
`[false,false,true,false]`: Value lengths 13/15 and Computation lengths 12/14,
without/with annotation. Its telescope is Description, ViewLogic, Invocation,
Receipt, optional Return/rebind execution, Shared, in that order. The observed
EventProof is not inserted into its own enclosing telescope. The stored subtree
is exactly the original generated `RuleTree`, not a replacement source program.

Once kernel acceptance and independent review exist, applying `app_inventory`
and `lambda_body_inventory` to `source_provenance` supplies the original generated
App ViewLogic and body EventProof nodes with their full routes, binders, telescopes
and original subtrees. It supplies syntactic evidence for the parent inversion
step; it does not construct any semantic payload or joint strategy.

First remaining source bridge: the primary source/proof owner must adapt these
binary routes to `OriginalSourceEvents.sourceOwners`/`Owner`/`ActualKey`'s route
convention, then derive original-source logical admission and decoded formal
contract readout for these exact occurrences in both entry modes. R92's source
handoff and R93's source handoff identify this bridge: App ViewLogic/body
EventProof admission must preserve the selected descriptor/interface and Shared
owner through the actual Name consumer. The current flat-binder admission and
arbitrary `base.logical` do not establish that law. No semantic counterexample
or lawful joint equality lift has been produced. Original A/B, effect hygiene,
source/native correspondence, concrete `SourceProblem.InferenceSoundness`,
principality, termination, semantic admission and production remain OPEN.

## Commands, resources and STOP

Actual commands were read-only `cat`, `sed`, `rg`, `sha256sum`, and small `python3`
programs for the two leased writes, in-memory header comparison and hashing.
Successful shell invocations exited 0. Initial locator reads returned exit 1/2
for nonexistent guessed paths and were corrected by `rg --files`; broad initial
search output was truncated, followed by exact file/section reads. No failed
Lean output is invented from these locator failures.

Executable bytes were read with `sha256sum` at
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`:
`bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.
Actual `lean --version`, Lake version, Lean exit, peak RSS, elapsed check time and
axiom census for R103: **NOT RUN**. Primary owns the only future invocation:
`lean --stdin -j1 -M1024`, at most 120 seconds / 1 GiB, exact input digest and
complete output after independent frozen-source review. No retry is allocated
to this leaf and no version invocation was spent by it.

Leaf bound: 1,000 seconds, no renewal; zero Lean/Lake/checker/build/test calls,
zero descendants, zero generated/cache/scratch bytes. UTC clock observations
include `2026-10-31 17:54:52 UTC` and `17:56:42 UTC`; total sampling wall time
was not independently instrumented by this leaf and remains primary-runtime
accounting. Writes stopped at this frozen handoff. No process, child, or deferred
write remains. Next action belongs to the primary: independent review, then its
single authorized check, complete type/axiom audit and result review. Do not
report this construction as proof closure before those gates.

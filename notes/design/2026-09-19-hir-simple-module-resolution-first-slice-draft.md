# First HIR module resolution slice

Status: Authoritative

Scope: a bounded standalone `ParsedFile -> HirModule` slice for ordinary
module-local bindings. It follows association and excludes types, solver, core,
imports/module graphs, parameter patterns, application syntax, and tracked
revisions.

Drafted-by: primary agent
Approved-by: user
Approved-at: 2026-09-19
Reviewed-by: spec_auditor and compiler_referee (two review/revision rounds, 2026-09-19)
Supersedes: `2026-09-17-syntax-freeze-and-vertical-implementation-amendment.md`
Gate 3 existing-fixture selection condition, only for this test input

## Fixture exception and preflight

This gate narrowly supersedes the prior *existing accepted fixture* condition:
no existing source proves both a recovery-free literal binding and a successful
module-local reference. The exception is test input only, not a syntax feature
or contract corpus:

```text
crates/yu-hir/tests/fixtures/simple_module_name_resolution.yu
my x = 1; my y = x
```

Public-parser preflight uses `scan_header` and `parse_file`, requires lossless
CST and no published syntax diagnostics, then requires no CST-derived Missing,
maximal raw-Error group, or Invalid occurrence. Failure returns to fixture
selection; HIR never reconstructs syntax from token adjacency or source slices.

## Product and phase boundary

```text
lower_module(ModuleIdentity, ParsedFile, SemanticImports::empty())
  -> Result<HirModule, HirAvailabilityError>

HirModule { identity, source_revision, items, errors, diagnostics }
HirItem = Binding(HirBinding) | Error { errors, range }
HirBinding { id, visibility, name, value, range }
ResolvedExpr = Integer { spelling, range }
             | Name { name, resolution, range }
             | Error { errors, range }
```

`ModuleIdentity { file: FileId, module: ModuleId }` is supplied by the compiler
owner. `FileId` equality is the collision-safe identity of supplied
`FileKey { realm, normalized_workspace_relative_path }`; `yu-hir` neither
normalizes paths nor accesses the filesystem. `ModuleId::SourceRoot(FileId)` is
the only module construction in this slice.

`SemanticImports` is opaque and only `empty()` is constructible. This is not the
final general resolve query. `UNTRACKED` revision is copied only as provenance,
never identity/cache/readiness. `HirName` stores exact token spelling/range;
error and diagnostic IDs are dense phase-local indices. `yu-types` remains
deferred because this slice carries no type; that is a scheduling deferral only.

## Association and recovery authorities

Current public Gate 3 API remains unchanged. A crate-private
`associate_chain_owned(&ParsedFile, CST OperatorChain) -> OwnedAssociatedExpr`
is the single authority. It reads the exact parser-retained
`ParsedFile::operators()` table and never rebuilds an environment. It captures
atom spelling via `SyntaxToken::text()` and token range via `text_range()`. The
public adapter consumes it into existing `HirExpr`; module lowering consumes it
by move into `ResolvedExpr`. No lowering call builds or retains whole-file
`AssociatedChains`.

The existing structural interpreter remains sole authority for Missing, maximal
raw-Error groups, Invalid, preorder, and structural path. A narrow read-only
`ParsedFile` projection exposes occurrence kind/range/ordinal/path/optional
direct-root ordinal, not ledger/catalog/text/CST mutation. Lowering calls it once and never
regroups recovery or makes another whole-tree recovery walk.

Each HIR error records syntax or lowering origin, attachment (module/direct-root
item/definition/value), range, kind, and optional HIR diagnostic. `HirErrorKind`
is finite: `InheritedMissing`, `InheritedRawError`, `InheritedInvalid`,
`UnsupportedItem`, `UnsupportedTarget`, `UnsupportedExpression`, `MissingBody`,
`DuplicateDefinition`, `AmbiguousName`, and `UnresolvedName`. Root recovery with
no direct-root owner attaches to Module. Each Missing,
raw group, and Invalid becomes one syntax-origin marker in interpreter preorder;
Invalid precedes descendants. Syntax-origin markers have no HIR diagnostic.
Unsupported owner, duplicate-after-first, and each unresolved/ambiguous use
produce defined lowering errors/diagnostics. Required slots retain ordered causal
error IDs and later root items continue. Structural occurrences are interpreter
preorder within their direct-root owner; caused lowering errors follow, then
independent lowering errors follow direct-root/source order. Unsupported
body/item lowering emits one outer error and discovers no nested names.

All syntax, recovery, unsupported-lowering, duplicate, unresolved, and ambiguous
cases return `Ok(HirModule)`. `Err(HirAvailabilityError)` is limited to validated
structural-projection or exact-operator-environment invariant failure, supplied
identity inconsistency, identity/ordinal exhaustion, and future cancellation.

## Admission, resolution, and identity

Pass one examines direct Root children only. A definition enters the value
namespace iff a BindingStatement's direct BindingHeader owns exactly one plain
IdentifierPattern/Identifier with no tail or recovery. `my`, `our`, and `pub`
map to Private, Our, and Public. Body support/recovery does not affect admission;
bad bodies retain their ID and get an error value. Compound, sigil,
recovery-bearing, and nested targets never enter this namespace.

Pass two lowers bodies against the complete planned namespace, so forward and
backward references agree. Duplicates retain deterministic IDs, every occurrence
after first reports DuplicateDefinition, and every use of that spelling is
AmbiguousName; no first/last-wins rule exists.

The compiler/module-resolution owner supplies validated
`FileKey { realm, normalized_workspace_relative_path }`. `yu-hir` owns opaque
`FileId`, `ModuleId::SourceRoot(FileId)`, and `DefId` equality:

```text
DefKey = (ModuleId, Value namespace, spelling, same-name source-order ordinal)
```

Unique admitted declarations keep IDs across trivia/body edits, reordering, and
differently named sibling edits. Same-name ordinal stability is not promised in
an erroneous duplicate group, nor across rename/file/realm/module changes.

## Cost, stop conditions, and approval

For CST nodes/tokens `N`, direct-root/header nodes `R`, admitted body nodes `B`,
retained HIR `H`, errors `E`, and copied spelling bytes `S`: structural
interpretation is `O(N)`, planning `O(R)`, body work `O(B)`, and lookup expected
`O(1)`; retained memory is `O(H + E + S)` plus temporary definitions and one
largest-body association tree. No deep clone/second retained tree is allowed.

Tests cover preflight, x/y resolution/ranges, determinism, unique-ID stability,
forward reference, bad-body admission, target rejection, nested exclusion,
duplicates, unresolved names, recovery ordering/attachment/nonduplication, and
visit/emission/byte counters.

Return to design on preflight failure, required syntax heuristics, import/type
need, non-moving association result, or superlinear work. User approval is
required for the fixture exception, product/error/projection APIs, association
seam, resolution/duplicate semantics, identity contract, empty-imports/Result
boundary, and `yu-types` deferral. M2 implementation then receives spec and
compiler review.

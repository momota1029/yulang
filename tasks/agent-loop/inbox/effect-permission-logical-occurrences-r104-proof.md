# R104 logical-occurrence App repair — revision 1

Status: **CONSTRUCTED / UNCHECKED / FROZEN / WRITES STOPPED**.
Assignment: `/root/r104_app_proof`; role `lean_prover`; author this leaf only,
with R93/R103 copied construction retained as provenance. Runtime model/effort
metadata is UNKNOWN to this leaf. No descendants or descendant leases.
Sprint: `EFFECT-PERMISSION-SOURCE-CAUSALITY/20261101-R104`, contract r1,
`tasks/agent-loop/sprints/effect-permission-source-causality-20261101-r104.md`,
SHA-256 `0f70cfbcbe18c74c2b1b6aa0130fc425261c916d2418b4e6e10251568a9357dd`.
Baseline supplied by contract: `15b082032`; no Git command was run.
Claim class: candidate syntactic proof construction, pending kernel execution,
fresh independent review and primary adjudication.

## Scope, source and original parent

Read root AGENTS.md, AGENTS.pre-sprint.md, goal-driven-sprints, current state,
assignment protocol, selected R104 contract, yulang-lean-proofs and its
sources/execution references. The primary's exact NEW_TASK prohibits all
Lean/Lake/checker/build/test invocations by this leaf and reserves one flattened
stdin invocation to the primary after independent review. That narrower packet
controls execution. No source, dependency, import, cache or generated-output
ownership is assumed.

Semantic selection: `notes/design/2026-10-08-source-generalize-definition.md`
§2 selects construction §§3–5; actual source §3.3 was read in
`notes/theory/2026-10-08-source-generalize-definition-and-proof.md`.
ViewLogic precedes challenges, Shared is retained once, and body EventProof
remains under its original event telescope. Manuscript
`docs/yulang-source-type-safety-ja.tex`, opening correction and
`sec:source`/`sec:all-source` relevant source definitions: App retains the whole
inert argument and complete Call; Lambda retains both Value and Computation
entry, pattern, annotations and sequential body. Its research corrections
are not blanket semantic authority.

Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1,3,5,7. For every supported source, lawful finite construction history and
actual retained qualified extrusion, preserve the external source conclusions,
required coverage, scopes and correlated evidence with one lawful joint strategy.
Current qualification is immutable Value birth-level induced SCC, per
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. No quantifier,
accepted language feature, original scope, provider or shared witness is changed.
The generic LocalLaws/SourceProblem propositions are not concrete instances.

| Source | Actual SHA-256 |
| --- | --- |
| source-generalize decision | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| source-generalize construction | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| source manuscript | `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166` |
| original parent | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| birth-level correction | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |

## Frozen inputs, output and construction

Paths in this table are relative to `notes/theory/lean/`.

| Path | Bytes | Actual SHA-256 |
| --- | ---: | --- |
| `YulangClosure/OriginalSourceSyntax.lean` | 22040 | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `YulangClosure/OriginalSourceGeneration.lean` | 66485 | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `YulangClosure/SourceLogicalOccurrencesR103.lean` | 23187 | `e31503875088a2f8dae68b1269433c4b9093a7d95e11ded03b7a169f56d6ecf0` |
| **output** `YulangClosure/SourceLogicalOccurrencesR104.lean` | 23908 | `0e7a42d66578388585a5abd1da12c77a9d7d46823687ed511d26e359b3078f39` |
| `lean-toolchain` | 25 | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lakefile.toml` | 311 | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| `lake-manifest.json` | 145 | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |

The pinned project reads `leanprover/lean4:v4.35.0`, `-j1 -M1024`, no external
packages. Actual version commands were not run by this leaf. R103's observed
Lean 4.35.0/Lake 5.0.0-src+eb6cafb receipt is historical evidence, not an R104
invocation. The contract pins executable SHA-256
`bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.

R104 copies frozen R103 into new namespace
`YulangClosure.OriginalSource.LogicalOccurrencesR104`. The only non-header
construction changes are:

- `appRule`: the conditional extra list is explicitly `List AtomKind`, with
  constructor `AtomKind.roleAndInitialCallOrigin`. The original five base kinds,
  singleton-formal guard, checking premises, endpoint fields, operand sites and
  two original generated child trees are retained.
- `app_exact`: separate absent/present annotation branches rewrite the actual
  `sourceRules` equation, change to the exact observed occurrence, then use
  reflexivity. Absent annotation observes `[]`; present annotation descends
  `[false,false]` through rule/forest with no added scope frame.

All ten theorem headers compare byte-identical without any namespace text
inside the headers. Nine entire theorem blocks, including tactic scripts, are
byte-identical; only `app_exact` changes its proof. `app_inventory` consumes that
repaired root by the unchanged `source_membership_iff`. No stronger hypothesis,
smaller source language, semantic success assumption or circular definition was
introduced. Source scan found no sorry/admit/project axiom/bypass syntax; the
single word `axiom` in a comment describes the audit. This is static evidence.

## Historical failure retained and new audit obligation

Actual R103 stdout was read, including all App goals. It reports
`lean.invalidDottedIdent` for `.roleAndInitialCallOrigin` at flattened line 1950,
and `rfl` failures in both annotation branches at line 1964. The original
complete logs remain untouched:

- `tasks/agent-loop/history/effect-permission-capture-coherence-20261101-r103-lean.stdout`:
  15703 bytes, SHA-256 `a33c8114f75e40687d7dcbd9755ac7a94bf4208ce2f174beed24b0875f3266dc`.
- matching `...-lean.stderr`: 864 bytes,
  SHA-256 `12e4a1797fa26678ede1e38abfdb310a8239f44cbcdffc00190e3bc585ff2f83`.

R103 exited 1, 16.03 s, 901016 KiB peak RSS; these are inherited measurements.
Its unused `Prod.exists` simp-argument warning is preserved; this packet limits
proof changes to App and does not suppress the linter.

Every name below has prefix
`YulangClosure.OriginalSource.LogicalOccurrencesR104.`. All have adjacent fully
qualified `#check @...` / `#print axioms ...` commands in the module. Their source
types are unchanged from R103; actual R104 printed types and axiom lists are
**NOT RUN** for every row. The inherited lists below are R103 results only.

| Root | R103 actual complete axiom list | R104 status |
| --- | --- | --- |
| `inventory_iff_lookup` | `propext, Quot.sound` | unchanged construction; unchecked |
| `encode_lookup` | `propext` | unchanged construction; unchecked |
| `observe_eq_follow` | `propext` | unchanged construction; unchecked |
| `source_membership_iff` | `propext, Classical.choice, Quot.sound` | unchanged construction; unchecked |
| `full_route_unique` | `propext, Classical.choice, Quot.sound` | unchanged construction; unchecked |
| `source_provenance` | `propext, Classical.choice, Quot.sound` | unchanged construction; unchecked |
| `app_exact` | `propext, sorryAx, Classical.choice, Quot.sound` | repaired construction; unchecked |
| `lambda_body_exact` | `propext, Classical.choice, Quot.sound` | unchanged construction; unchecked |
| `app_inventory` | `propext, sorryAx, Classical.choice, Quot.sound` | repaired dependency; unchecked |
| `lambda_body_inventory` | `propext, Classical.choice, Quot.sound` | unchanged construction; unchecked |

Exact primary execution input: concatenate Syntax + Generation + R104, strip
only the leading Generation import of Syntax and R104 import of Generation,
retain `import Std`, and add no separators. Hashed in memory only: **112345
bytes**, SHA-256
`e5c6d9f734bb648c4280a2307243a2f74e3015bd02fd73910710e4dad298a85e`.
No flattened file or other scratch was written. After fresh independent frozen
source review, primary owns exactly one pinned `lean --stdin -j1 -M1024` call,
≤120 s / 1 GiB. Require exit 0, all ten actual printed theorem types, complete
acceptable transitive axiom lists and independent receipt review. No retry.
Skill checker was not run because it requires Lake build/cache operations
outside this packet. No setting/checker was weakened. Flattened execution does
not establish ordinary module-import integration or full default-build coverage.

## Coverage, parent application and first remaining bridge

Generic statements quantify arbitrary context, category/source, full route,
occurrence and enclosing telescope; uniqueness uses the full route and no
site-distinctness assumption. Provenance returns the exact original binder,
subtree and telescope. All ten RuleTree and both RuleForest constructors are
retained. SourceGeneration still represents all 13 expression, 11 pattern,
3 statement forms and their containers/continuations. App covers arbitrary
callee/argument, both annotations and both values of the conditional guard.
Lambda retains arbitrary formal annotation/pattern/body and all four outer
annotation × Value/Computation entry cases. Omitted claims: semantic membership,
source typing, runtime observations, publication/use allocation and native
correspondence; no syntax case was deleted to omit those obligations.

Conditional parent application: use `app_inventory` or `lambda_body_inventory`
as the `member` argument of `source_provenance`. This locates the generated App
ViewLogic/body EventProof at its exact full route and telescope, without changing
its retained original subtree. It supplies the syntactic inversion input in
original parent §5, not the lawful joint equality lift itself.

First remaining structural/source bridge, owned by Luna's source/proof lane:
relate these Bool tree/forest routes to
`YulangClosure.OriginalSourceEvents.sourceOwners`, `Owner` and `ActualKey`'s Nat
route convention. This is not a pointwise Bool-to-Nat map: owner forest head
steps consume no tag, sibling uses 1, choice-right uses 3; binder scopes also
retain their owner routes. `binderOwner` catalogs events/Shared/EventProof and
omits ViewLogic, so a logical admission catalogue/interface is still required;
App ViewLogic cannot be presumed to be an existing runtime Owner.
Read-only events-module SHA-256:
`cfd5f502a1e68a97e27e11a75400fae8789f167c92596aedb08ef7dfbb724342`.

First remaining semantic premise: derive original-source logical admission
(`YulangClosure.OriginalSourceEnvironment.LocalAdmissions.logical`) and decoded
formal contract readout for these exact generated occurrences, preserving the
selected descriptor/interface and Shared owner at the actual Name consumer in
both entry modes. The supplied logical admission relation or arbitrary
`base.logical` is not that derivation. The parent still needs one lawful joint
strategy across publication/use under the original scopes. No counterexample
or semantic source-owner bridge is established here. Original A/B, concrete
InferenceSoundness/principality/termination, effect hygiene, source/native and
production remain OPEN.

Mutual TODO `R104-LOGICAL-OWNER-1`: Luna/source-proof owner consumes this syntax
result only after the theorem gate; relate source routes/telescopes and prove
admission/readout at the original source rule. Falsifier: missing owner route,
wrong telescope, lost descriptor/Shared incidence, or a concrete lawful source
case violating the proposed bridge. This request grants no new lease.

## Resources, commands and STOP

Bound: 600 s, no renewal. Actual commands: read-only `cat`, `sed`, `rg` and
`python3` for two exact leased writes, hashes, in-memory flattening, theorem-header
and theorem-block comparisons. Successful commands exited 0; broad initial
captures were truncated and narrowed. No Lean diagnostic was generated by this
leaf. Zero Lean/Lake/checker/build/test calls; zero Git/network/install calls;
zero scratch/cache/generated bytes; no children, background processes or
outstanding writes. Clock observations: 2026-10-31 18:09:10 UTC and 18:09:58 UTC;
actual total worker elapsed/RSS remains primary runtime accounting.

Only writes: the R104 module and this one handoff path. R93/R103, compiler,
root imports, shared state/task/index/config/toolchain/dependencies and other
workers' paths were untouched. **Writes STOPPED at frozen submission; no
remaining process/descendant lease.** Next action belongs to primary: independent
source review, one bounded exact check, full type/axiom audit and independent
receipt review. This leaf does not certify its own construction or close a gate.

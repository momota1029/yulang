# NATIVE-FRESH-USE-VALIDATION/r1 — proof handoff, stopped incomplete

Author/current-session worker: `/root/native_fresh_use_validation_proof`.
Requested model/effort: `gpt-6.1-sol/high`; observed: UNKNOWN (runtime metadata
not exposed). Contract authenticated by actual `sha256sum` exit 0:
`fa16e84d3bd7cdb3c134bbc798c5bfd47e8af0686b80b961c7a8f49a692cf4f8`.
Primary stop instruction received and honored. This is a partial research
construction, **not checked, not independently reviewed, not source/native
correspondence, not parent closure, not production authority**.

## Frozen artifact and dependencies

Only changed source: `notes/theory/lean/YulangClosure/NativeFreshUseValidation.lean`,
SHA-256 `951317b3617b0a399c1192291819f4dc61b4561ab80065e24c40a5c1e32a19a6`.
Only other write: this exact handoff. No scratch/generated/cache output.

Actual dependency authentication (`sha256sum`, exit 0):

| Input | SHA-256 |
| --- | --- |
| NativeFreshScopeTransport.lean | 1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5 |
| NativeScopeTransformer.lean | 68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6 |
| Contracts.lean | 2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e |
| OriginalEffectHygiene.lean | 926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f |
| lean-toolchain | ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c |
| lakefile.toml | 212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4 |
| lake-manifest.json | 058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3 |
| README.md | 8d27e0b90fc04eb8a0a30606a857e564e5269e8e33e72fddbf1190cb6a7072e3 |

Frozen Rust source reads were from
`isolated/selected-module-entry-freshening-repair-r1/crates/yu-solver/src/`:
candidate_scheme `33235b840c42be38be1df634291e309c0d143fa62f412afa633768be9b40aa0e`;
candidate_effect `8d80a98b4fe22bd91409b645dbac3d5bcd10eed4b45bbe6f5c17a773e65874f6`;
candidate_context `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`;
candidate_source `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`;
term `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`;
lib `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`.
All matched the contract; exit 0.

## Original source and unchanged parent

Read `docs/yulang-whole-proof-closure-ja.md` §§1, 4 (SHA
`17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5`),
the integration draft `docs/yulang-semantics-and-soundness-ja.md` §§1–5
(`2a0b173406353524950e1ab690c679918185167e63929c9b6724547b5cd379f2`),
and original source manuscript correction notice and `sec:owners`
(`docs/yulang-source-type-safety-ja.tex`,
`2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`).
The latter explicitly distinguishes fixed historical receivers from fresh
execution owners and identifies candidate/unadopted semantics. These drafts
did not supply authority for new native payload semantics.

Original parent: `YulangClosure.SourceProblem.InferenceSoundness`,
Contracts.lean:128:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

The same original `x` and witness `e` must satisfy both conclusions. No source
judgment, supported language, original quantifier, or source definition changed.
`OriginalEffectHygiene` is a separate OPEN component, not proved by this file.

## Constructed surface and exact limitation

Namespace: `YulangClosure.NativeFreshUseValidation` throughout.
`Graph`, `Node`, `graphView`, `interpret` decode captured data independently
of retained terms; `observe` recursively decodes a separate native-read function.
The root of the interpreter is `graph.root`, never `retained graph.root`.
Fuel bounds recursion, not the original source domain; successful validation
requires nonempty successful observations. Missing observations and fuel
exhaustion do not validate as `none = none`.

Represented ordinary constructors: all 13 Atom values; Value/Effect rows with
exact polarity and ordinal; Function children in argument/argument-effect/
result-effect/result order; all tuple children; record names, optional flags,
and values; ordered variant tags and every payload including nullary alternatives.
Raw tuple/record/variant slices are bounds checked. Shared child indices remain
one graph lookup, but no theorem establishes native DAG allocation/sharing.
EffectOperand has a separate retained endpoint observation and cannot validate
as an ordinary term slot. Its modeled forms distinguish contribution,
allowance, support and annotation-member; tail rows require Effect kind.
Other Endpoint forms reject in the graph operand decoder.

Map recipes represent region/scope/input IDs, context-use, scoped transformer
content and dependent demand root/use/scope/input, attachment payloads,
ContextExpr observations, evidence snapshots, role-obligation row and all four
FieldTail rows. Scope/input numeric images use the existing actual `fresh`
definition; no existing scope transport theorem is applied with weakened
hypotheses. `unresolved` recipes reject. `BothFromRight` is represented and
rejects, matching the pinned fresh-context source's certificate rejection.

**Exact stopping obstruction:** these recipes are not a complete native
interpreter instance. In candidate_effect.rs:1394, fresh Contribution copies
effect/origin but assigns `instance = contributions.len()`. In `View` (line
360), source_weight/closed_weight and tail can change during copying. Native
Context prefix/suffix weights reference those changed views. A generic complete
payload equality does not derive these changing identities. The supplied
Context recipe currently observes its argument; it does not compute authentic
native weight remapping. The file header records this limitation. No full-table
validator, map-domain completeness theorem, allocation witness, contribution
instance reconstruction, context weight remapping, or opaque native handle
equality has been proved or claimed. This is not a completed Shape-only
substitute for the required native equation.

## Authored theorem signatures (not printed/checker accepted)

All six declarations remain constructed-but-unchecked. `Payload : Type` and
`[DecidableEq Payload]` are implicit in every signature below; names are fully
qualified by the namespace above.

1. `validateObservation_sound`: for any `expected actual : Option (Tree Payload)`,
   `validateObservation expected actual = true →
   ∃ value, expected = some value ∧ actual = some value`.
2. `validateNode_term_sound`: for arbitrary graph, shared rows, snapshot,
   nativeRead, fuel/index/term and effectRead,
   `validateNode graph rows snapshot nativeRead fuel index (some term) effectRead = true →
   ∃ value, interpret graph rows snapshot fuel index = some value ∧
   observe nativeRead fuel term = some value`.
3. `validateNode_effect_sound`: for the same parameters with no term,
   `∃ endpoint tail polarity, graph.nodes[index]? = some (.effectOperand endpoint tail polarity)`
   and `validateNode ... index none effectRead = true` imply
   `∃ value, interpret ... index = some value ∧ effectRead index = some value`.
4. `validateMap_sound`: for arbitrary graph/rows/snapshot/fuel/allocation/recipe/actual,
   `validateObservation (interpretMap graph rows snapshot fuel allocation recipe) actual = true →
   ∃ value, interpretMap graph rows snapshot fuel allocation recipe = some value ∧
   actual = some value`.
5. `unresolved_map_rejected`: for every field/actual and common parameters,
   `validateObservation (interpretMap ... (.unresolved field)) actual = false`.
6. `returned_root_observation`: arbitrary graph/rows/snapshot/nativeRead/fuel/returned,
   retained and effectRead, under exactly
   `returnSite : retained graph.root = some returned` and
   `valid : validateNode ... graph.root (retained graph.root) effectRead = true`,
   concludes `∃ value, interpret ... graph.root = some value ∧
   observe nativeRead fuel returned = some value`.

The last theorem applies validation to a native return-site identification;
that identification is not the desired interpretation equation. An attempted
additional handle theorem was removed before freeze because its proposed
reconstruction equation would merely assume the missing image bridge.

## Execution, audits and parent application

No Lean/Lake, helper checker, Cargo, test, Git or installation command was run.
The primary exclusively owns the isolated project and verification cache.
Read pin: `leanprover/lean4:v4.35.0`; actual executable versions: NOT RUN.
Lean command exits/goals/diagnostics: NOT AVAILABLE. Printed theorem types:
NOT RUN. Complete `#print axioms` for every authored theorem: NOT RUN/UNKNOWN.
The proposed next checker target is module
`YulangClosure.NativeFreshUseValidation` with the six theorem roots above;
primary decides whether the incomplete artifact merits execution. Do not
report this handoff as kernel acceptance or an axiom audit.

Actual read-only shell commands included `cat`, `sed -n`, `rg -n`, and the
`sha256sum` calls recorded above; those relevant authentication commands exited
0. `ls` before construction exited 2 because both leased outputs did not exist.
Source scan found no proof holes, axiom declarations or kernel bypasses in the
new source; comment matches were inspected. That search is not an axiom audit.
No mathematical method failed against actual Lean goals because execution was
not assigned to this lane. The material source failure evidence is the changing
Contribution/View/Context identities above, preserved rather than relabeled.

Application to the parent remains conditional: the authored root observation
lemma could supply a native reconstruction observation clause once its native
reader and interpreter are authenticated. It cannot construct the original
source derivation or shared witness. **First remaining premise/owner:** primary
native/source lane must retain/read authentic contribution allocation instance
and copied-view weight handles/tails, construct Context weight remapping from
those same shared maps, and instantiate these observations field by field.
Then establish recipe/domain completeness and every required actual validation;
the parent still needs the original source-to-Graph generation and shared
source/native witness. No supplied `LocalLaws` or proposition definition closes it.

Resources: one leaf, no descendants, no heavy process, no generated writes.
Grant 1,000s charged in full by contract; stopped early at primary instruction.
Final observed clock during freeze: 2026-10-28 06:13:42 UTC. No CPU/RSS runtime
measurement was taken. Lean source writes stopped before this handoff; all
writes stop upon this handoff submission. Both exact outputs are frozen for
primary intake. Any repair needs an explicit resumed lease; no further work is
running and no review/self-certification is claimed.

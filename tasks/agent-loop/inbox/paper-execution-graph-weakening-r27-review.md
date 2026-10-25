# R27 independent M1 review — revision 1

Assignment: R27-INDEPENDENT-M1; sprint `FULL-PAPER-TYPE-SUBSTITUTION-20261026/r27`, contract r2. Reviewer: `/root/r27_independent_m1`, fresh non-author; no construction contribution or descendants. Launch commit supplied by primary: `eb1ae7cff`; RUNNING commit and explicit review signal supplied by primary: `4c4e61b61`. Child session identifier UNKNOWN; primary session binding recorded in current.json is `01a172ef-fec1-72e3-bd47-bc4d7f51d6aa`. Requested role: registered lean_prover/role default; observed exact model and effort UNKNOWN. Config and state rows are not independent runtime evidence.

**Recommendation to Luna: accept the frozen intermediate R27 lemma at M1 scope. No BLOCKING, MAJOR, or minor correctness finding identified.** Primary adjudication/integration remains with Luna. This review establishes no full-paper, source/native, compiler, or production authority.

## Frozen target and governing source

Baseline supplied by contract: `5beb8df530080ea768abf275bdef85e3b471b23b`. Candidate checkout: `/tmp/yulang-r27-graphweakening`. Read root AGENTS.md, AGENTS.pre-sprint.md, rules/goal-driven-sprints.md, rules/design-authority.md, the Lean skill and both source/execution references, current.json, handoff protocol, r2 contract, candidate, worker handoff, worker failure/audit log, primary verification, actual relevant source definitions and project pins. No Git command was used to establish the baseline.

Original manuscript: `docs/yulang-operational-type-safety-ja.tex:953–977` (simultaneous term/type/name substitution), `:980–990` (immutable graph extension), `:1141–1146` (typed fresh external responses). Read its opening 2026-10-23 source-owner correction: raw-resume owner renaming does not establish existing source-owner correspondence. This remains a research manuscript, not semantic approval. The paper graph lemma includes well-typed heap extension, allocation, simultaneous recursive substitution and guards; the candidate explicitly supplies only derivation weakening for six existing partial relations.

Independently rehashed these bytes using Python hashlib, exit 0; each matches the supplied frozen identifier:

| Artifact | SHA-256 |
| --- | --- |
| r2 contract in root `tasks/agent-loop/sprints/paper-execution-graph-weakening-r27-r2.md` | `9f9a3cbf295784d97ba544209c059a585d4b868660c82d62e655d2d8b0eb230f` |
| candidate `notes/theory/lean/YulangClosure/PaperExecutionGraphWeakening.lean` | `b0ff39ad89fcb83559cca3147ae55fa7e7f6c31c1b130ec9cd7608e33d1f696e` |
| worker handoff `tasks/agent-loop/inbox/paper-execution-graph-weakening-r27.md` | `4624fe0b4dfd893f4bc274a42a719bbe2a70bdb2bc0363664a49d64132333426` |
| root primary verification `tasks/agent-loop/inbox/paper-execution-graph-weakening-r27-primary-verification.txt` | `3b7c36cb14d879eebfa57c26451f1eea43f8c4f0c0a76b64ad09327396af64be` |
| manuscript, root and isolated checkout | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |

Also independently hashed all six frozen Lean inputs, toolchain/lakefile/manifest, and R26 adjudication: every result equals the r2 contract and worker input table. In particular `PaperExecutionSyntax.lean` = `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`; `PaperExecutionTypingSubstitution.lean` = `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41`. R26 remains FAILED_CHECK; its candidate/cache was not accessed.

## Exact statement and proof review

All following names have prefix `YulangClosure.PaperTypes.`. Actual definitions in `PaperExecutionSyntax.lean:524,555,571–574` make GraphEnvironment an ordered `List (Nat × Ty)`, mapping preserve identities/order while substituting types, and lookup select the first matching identity. `GraphLookupPreserved old new` quantifies over every identity/type and preserves every successful old lookup with exactly the same type.

For arbitrary declarations D, old/new, term environment Γ, and all indicated indices, the six printed statements each have exactly `GraphLookupPreserved old new → J D old Γ indices → J D new Γ indices`:

| Fully qualified suffix | Unchanged judgment indices |
| --- | --- |
| `PaperValueTyped.graphWeaken` | value, ty |
| `ValuesTyped.graphWeaken` | values, types |
| `ValuesAllTyped.graphWeaken` | values, ty |
| `RecordPayloadsTyped.graphWeaken` | fields, recordType |
| `PaperComputationTyped.graphWeaken` | computation, ty |
| `PaperContinuationTyped.graphWeaken` | continuation, responseType, resultType |

I inspected all six complete printed types in primary verification lines 2843–2899 and compared them with the unchanged relations. No freshness, heap well-typedness, declaration correctness, source restriction, LocalLaws, or replacement typing definition was added. The continuation response/result types stay distinct. Record shape, presence, labels, arities, operation instance equality and declaration-resolution witnesses are reused unchanged.

`GraphLookupPreserved.map` proves preservation under arbitrary shared substitution σ using the frozen `lookupGraphEnvironment_subst`. Its case split on the original old lookup is sufficient even for non-injective substitution: a mapped successful lookup supplies its original type; none is impossible, and some uses hpres before mapping. It neither assumes nor proves injectivity. In `PaperValueTyped.typeAbstraction`, the mutual IH is applied with the mapped new graph and `hpres.map (fun i => .var (i + 1))`; the original shifted declarations and term environment remain shared.

The principal theorem uses six recursor motives generalizing the target graph. I compared its callbacks with `PaperExecutionSyntax.lean:632–832`: all 40 constructors are present (2 ValuesTyped, 2 ValuesAllTyped, 2 RecordPayloadsTyped, 19 PaperValueTyped, 14 PaperComputationTyped, 1 PaperContinuationTyped). This includes record optional/required premises, both lambda entry environments, all three shared wrap premises, both intersection derivations, universal introduction/elimination, roll/unroll, perform/request with one operation instance, resume, and template invocation. Wrapper theorems for lists/fields perform ordinary structural induction; computation transport introduces delay then inverts its unique typing constructor; continuation transport reconstructs its one constructor using computation transport. No circular call is used to prove the mutual core.

`lookupGraphEnvironment_identity_mem` correctly derives domain membership from a successful ordered lookup. `GraphLookupPreserved.freshCons` uses `identity ∉ old.map Prod.fst` to exclude the equal-query case, and otherwise keeps lookup in the tail. It does not require Nodup or forbid old duplicates. All six `.graphFreshCons` declarations actually apply the corresponding `.graphWeaken` using this witness; their types preserve all original indices for arbitrary newType.

`graphLookupPreserved_shadowing_falsifier` is universal in identity: old `[(identity, int)]` resolves to int, while new `[(identity, bool), (identity, int)]` resolves to bool. Thus list inclusion alone is insufficient. This is a discriminator for the lookup relation, not a counterexample to well-typed fresh paper allocation.

## Checker evidence reviewed, not rerun

Reviewer checker/Lean/Lake invocations: **0**. No audit source, generated output, cache or .lake file was opened or written. I read the non-cache worker/primary logs and the skill script's audit generator/validator as text. I did not execute the checker or validator. Their reports establish checker evidence separately from this independent mathematical/source-scope review.

Pins read: Lean `leanprover/lean4:v4.35.0`, no external packages, `moreLeanArgs = ["-j1", "-M1024"]`. Logs report native Lake `5.0.0-src+eb6cafb`, Lean `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Native executable: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.

Worker literal invocations: `--version` exit 0 (0.032891 s); `env lean --version` exit 0 (0.062133 s); focused `build +YulangClosure.PaperExecutionGraphWeakening` exit 1 (20.759273 s); repaired focused build exit 0 (0.437924 s); `env lean -j1 -M1024 .lake/R27Audit.lean` exit 0 (1.470971 s). Total 5 calls/22.763192 checker seconds. Material failure remains in worker log lines 2843–2864: none branch had `lookup : none = some ty`; explicit `cases lookup` repairs it. Deprecated if_false uses were replaced by ite_false. Existing dependency warnings remain. No unchanged-command retry is claimed.

Primary preflight version queries succeeded (individual elapsed times UNKNOWN); focused build exit 0 (0.411153729 s); same exact audit exit 0 (4.077251027 s), total measured final checks 4.488404756 s. Primary log has all 16 ordered BEGIN/type/axiom/END records. Skill generator requires theorem declaration kind, prints the full type and #print axioms, then checks collected axioms against its standard whitelist. Read all complete primary types and axiom results:

- `GraphLookupPreserved.map`, `graphLookupPreserved_shadowing_falsifier`: `[propext]` each.
- `PaperValueTyped.graphWeaken`, `ValuesTyped.graphWeaken`, `ValuesAllTyped.graphWeaken`, `RecordPayloadsTyped.graphWeaken`, `PaperComputationTyped.graphWeaken`, `PaperContinuationTyped.graphWeaken`: `[propext, Quot.sound]` each.
- `lookupGraphEnvironment_identity_mem`, `GraphLookupPreserved.freshCons`: `[propext, Quot.sound]` each.
- `PaperValueTyped.graphFreshCons`, `ValuesTyped.graphFreshCons`, `ValuesAllTyped.graphFreshCons`, `RecordPayloadsTyped.graphFreshCons`, `PaperComputationTyped.graphFreshCons`, `PaperContinuationTyped.graphFreshCons`: `[propext, Quot.sound]` each.

No sorryAx, project axiom, Classical.choice or unsupported axiom is reported. My read-only rg scan of the candidate and six frozen Lean dependencies found no sorry/admit/axiom/checker-bypass token match (exit 1 for no matches); that scan supplements the supplied complete axiom receipts. No full/default build or tests ran in this review.

## Parent application, boundaries and cessation

R27 supplies the derivation-weakening step of manuscript :980–990 for exactly the six represented judgments; freshCons supplies a concrete lookup-preserving extension. It does not construct or type heap nodes. First remaining graph-extension premise: a concrete well-typed fresh allocation construction preserving old values/types, typing all allocated recursive right-hand sides/body by simultaneous substitution, and preserving guarded cycles. Owner: Luna/full-paper graph and recursive-substitution proof intake (`R27-HEAP-ALLOCATION-1`).

Omitted typing cases remain variants/nominal values, handler/mapper rules, graph allocation/recursive environments, primitive and pattern judgments, and registered template-body typing; existing template invocation alone does not cover them. R18 variant correspondence, R23/full mapOperation, full-paper type substitution, corrected machine/source-owner correspondence, inference/executor, original A/B, source/native/Rust and production gates remain OPEN. No source constructor or accepted language feature is removed by this partial theorem.

Adjudication target: Luna may accept these exact frozen intermediate lemmas and retain every parent boundary. No additional reviewer, repair lease, checker run, semantic change or production promotion is recommended by this review.

Resource receipt: first active review clock observation `2026-10-25 17:18:29 UTC`; final elapsed upper bound will be sent with the frozen report hash, within the 300-second grant. Exact process CPU/RSS and model effort unavailable (UNKNOWN); only lightweight reads, hashing and this one report write were used. No scratch files, source changes, Git, network, children, tests, checker or cache access. Sole changed path is this leased report. **Writes stop on completion of this report creation; no later report edits or background subprocesses. Descendants: 0.**

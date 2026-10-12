# Y3 effect attachment, alias Call, and output counterexample search

Date: 2026-10-12
Status: frozen, independently reviewed bounded source gap; no counterexample
Baseline: `99cd86fd9`, branch `research/simple-sub-intrusion`
Lease: this file only; complementary source falsification, leaf, no implementation

## Objective and governing premises

Try to separate a negative annotation's fresh subtraction identity from its
actual call, output, or current/future residual consumer. The distinctive attack
is a local alias between the annotated formal and the call, crossing local
publication and a later captured use. This does not repeat the constructive
constructor induction or the reviewed finite observer theorem.

Authority: `2026-10-10-annotation-effect-hygiene-integration.md` §§1,4;
`2026-10-10-contextual-attachment-admission-design.md` §§1,3–6;
`2026-10-10-contextual-residual-lineage-selection.md` in full; and
`2026-10-11-yulang-inference-top-level-principles.md` in full.
The primary corrected the packet's stale attachment filename to the admission
design. `2026-10-12-oracle-effect-source-transfer-audit.md` was read in full as
bounded prior evidence, not as a Y3 implementation oracle.

Retain composed-negative local subtraction, composed-positive allowance,
symbolic flow and later checks, annotation-set attachment identity with member
ordinals, independent same-family contributions, and separate residual
constructor lineages with current/future fan-out. Complete Call and consistent
publication remain required. The withdrawn callback output supplies no expected
scheme. Negative formal rejection in the private candidate is an unfinished
implementation gate, not an exclusion from the supported language domain.

**Claim class:** bounded static source characterization and a construction gap.
No successfully inferred source was shown to violate hygiene. No all-source
constructor closure, theorem closure, independent review, or production
conformance is claimed.

## Small source candidates and failure premise

The smallest searched call-bearing spine is:

```yulang
act io
my f (cb:int -> [io] ()) = cb 1
```

The alias attack adds one local binder and one local use:

```yulang
act io
my f (cb:int -> [io] ()) = { my g = cb; g 1 }
```

The open-tail variant changes the annotation to `int -> [io, 'e] ()`, retaining
the alias body. This targets future lowers and a residual tail; it does not
supply an implemented residual recipe. These are source candidates, not executed
counterexamples. The static trace assumes successful syntax construction,
unique resolution of nullary `io`, completed HIR formation, and no resource
failure. No minimality across the entire grammar is claimed.

Binding and ML application spellings follow
`syntax-reference/en/src/statements/binding-use.md` and
`syntax-reference/en/src/expressions/call-field-path-tails.md`.
Plain `[io]` annotation rows are the actual HIR parser's `BracketRow` branch.
The apostrophe-row syntax page does not establish this annotation's semantics.
The repository has no `spec/` directory. Existing formal-effect fixtures were
consulted only for source spelling, not acceptance or result evidence.

For either spine, the formal starts at composed Negative. Its Function argument
flips to Positive; its result retains Negative. Thus the nonempty concrete row
belongs to the Negative result. `preflight_formal` requires an explicit Negative
row to have zero concrete operands and exactly one variable. Both `[io]` and
`[io, 'e]` fail the concrete condition.

The earliest solver boundary is
`CandidateInference::solve` → `candidate_source::preflight` →
`preflight_formal(result, false)` → `CandidateError::Unsupported`, before
the source action schedule executes (`shadow_apply.rs:79–98`,
`candidate_source.rs:82–121`). The paired constructor independently rejects
the same row (`candidate_effect.rs:1034–1035,1052–1070`). Disabling preflight
alone would not construct a licensed attachment or establish output meaning.

Removing the alias leaves this premise unchanged. A Group wrapper, returned
function, repeated alias use, or symbolic tail cannot change that formal row's
first rejection. These were static seam checks, not successful source runs or
additional completed attacks. The one bounded attempt stops at this common owner.

## Construction trace and the alias seam

These are actual source owners, not an induction over all source constructors.
Paths are under `crates/`.

| Boundary | Owner and static evidence |
| --- | --- |
| Resolved operand/occurrence | `yu-hir/src/module/source_annotation.rs:349–377,399–478,505–563`: annotation owner/position, distinct Function children, row occurrence, namespace-resolved concrete operands, and separate variables. |
| Actual formal | `yu-hir/src/module/local_source.rs:289–319`: retains the parsed annotation on the parameter, installs lexical Parameter resolution, and forms its Lambda. Nested local parameters call the same parser at `772–788`. |
| Actual Apply/name | `local_source.rs:507–563,639–658`: source-owned callee/argument pair and lexical resolution. In the alias shape, `cb` is Parameter and `g` is Local. |
| Formal registration | `yu-solver/src/candidate_source.rs:188–245`: actual Lambda/parameter registration; only Parameter Names initialize `formal_names`. |
| Alias publication/use | `candidate_source.rs:315–327,380–389,644–681`: initializer endpoint is installed; later Local Name schedules a Local use. `candidate_scheme.rs:1316–1337,1354–1378` stores root/boundary, captures the actual graph, and prepares the later fresh use. |
| Call identity | `candidate_source.rs:394–408`: authentic callee/argument, recipe, checking occurrence, and application Effect. `formal_name` comes from the callee occurrence: Some for direct `cb`, None for bare Local Name `g`. |
| Wrapper transport | `candidate_source.rs:414,439,463`: Ascription, Group, and final Block expressions copy their child's formal name; Local Name does not. `candidate_call.rs:386–429` validates a formal registration through those wrappers to the actual Parameter Name. |
| Invocation/effect | `shadow_apply.rs:1308–1447`: checks the stored recipe, creates four-port demand and invocation Effect at application level, and forwards invocation plus callee-evaluation Effects to the application. |
| Output | `yu-solver/src/lib.rs:11233–11369`: actual formal domain/body Value, body Effect and inferred entry joined into return Effect, then Function construction. The inspected constructor emits no annotation-local output POP. |

The alias seam discriminates against a future argument that every callback call
is licensed solely by direct lexical formal registration. Local uses follow
capture/freshening while the bare Local callee has no `formal_name`. This is not
a demonstrated hygiene bug: native Value constraints might carry sufficient
evidence once the missing attachment mechanism exists. It identifies the
additional bridge required by that argument. Equal local/formal endpoints alone
do not establish preservation of fresh annotation authority.

## Uninstantiated consumers and precise remaining premise

The set-weight constructor `candidate_context.rs::source_weight:2174–2195`
retains identity/member ordinals but empty live left/right words. Its
`SourceUnitPush` preparation is composed-positive;
`materialize_unit_push:2200–2222` is explicitly detached from live relation,
bound, registration, and recipe construction.
`candidate_effect.rs::candidate_signature_view:733–774` exposes a closed
zero-word filter only without a tail. These corroborate the earlier audit;
they are not another proof of the finite count theorem.

The concrete consumer checks Support/Allowance and forwards unmatched concrete
operands unchanged to the tail (`candidate_effect.rs:888–958`).
`candidate_context.rs:2744–2813` stores the remaining context after zero-word
filter discharge; that record is not the concrete-head/gamma recipe constructor.
This lane therefore cannot instantiate an attachment-qualified future-lower or
reverse-gamma consumer and observe an incorrect output. A supplied PUSH/POP toy
model or Oracle direct-formal predicate would assume the missing bridge.

Exact remaining A/B premise: source-owned Negative set formation must create a
live relation; survive authentic direct or aliased Call and local capture/use;
supply matching actual Value/Effect output consequences; and reach every
applicable present/future recipe with distinct constructor lineage, retained
feedback, and exact outgoing gamma projection. The alias case requires evidence
crossing Local use when no direct formal-name witness exists. The first missing
owner is negative attachment formation; downstream parts stay open rather than
being declared false by absence.

Recommended next action: have the constructive lane explicitly retain the alias
Call obligation in its coupled invariant; resolve how formation and local
capture/use carry the same instance to output/residual consumption before the
dependent implementation. Another transition-only probe with the missing source
rule assumed would not advance this premise.

## Checks, resources, coverage, and freeze

Commands: bounded `cat`, `sed -n`, `rg -n`, `rg --files`, `wc -l`,
`sha256sum`, a lease-path absence check, and note integrity inspection. One
small foreground shell command at a time. Some combined captures were truncated;
governing documents and decisive sections were subsequently read in bounded
chunks. No compiler edits, tests, builds, runtime probes, checker, mutations,
random seed/range, benchmark, Git operation, delegation, or model-policy change.
CPU/RSS and elapsed wall time were not instrumented; no heavyweight process.
The packet gave one bounded attempt but no numeric wall/RAM quota.
Runtime model/effort metadata was unavailable: observed settings unknown. A
fresh generic independent semantic review passed with no blocking, major, or
minor finding; actual model/effort metadata remained unavailable. Its source
scope was the exact frozen artifact and its dependencies, not global hygiene.

No execution oracle was used. Oracle evidence is the primary's pinned audit,
independent of this Y3 alias trace; it cannot validate Y3's missing rule.
Static route claims share Y3's actual implementation as their operational
assumption and do not prove conformance to selected language semantics.
No provider was selected/validated. Solver drain, binary correspondence,
generalization/export preservation, intrusion/extrusion preservation, handlers,
Catch/runtime, arbitrary constructor families, recursive mixed components,
soundness, principality, and production admission were not checked.
The supported language domain remains unchanged.

The primary reported a clean tree at baseline dispatch. This leaf used no Git
commands. Committed-baseline byte validation remains the primary's check.
No observed dependency change is incorporated. Direct dependency SHA-256 values
are appended below.

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/design/2026-10-10-contextual-residual-lineage-selection.md` | `d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/progress/2026-10-12-oracle-effect-source-transfer-audit.md` | `f222d83d51af22f26b786bad6bc07d27a2b2fb5b97e0dadbada9159d667bbb32` |
| `crates/yu-hir/src/module/source_annotation.rs` | `a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `crates/yu-solver/src/candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `crates/yu-solver/src/candidate_call.rs` | `79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/shadow_apply.rs` | `cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| `syntax-reference/en/src/expressions/call-field-path-tails.md` | `0fbbe46d52328b0438c4acc5e2e958380efa45e74ef0020c4762383804d3c253` |
| `syntax-reference/en/src/statements/binding-use.md` | `18d08a59c211027dc95c9556d71703a8bda7b4c1d3dc72e253e7b7dae93c928f` |
| `crates/yu-solver/tests/candidate_formal_effect_polarity.rs` | `dc89def4c2653960e29474135d4e2f91c076bd8a27eb54b048088820a915d636` |

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-12-y3-effect-call-output-counterexample-search.md`.
- Baseline: `99cd86fd9`; branch `research/simple-sub-intrusion`.
- Changed dependency hashes: none observed; committed-baseline validation left to primary.
- Review: frozen producer evidence passed a fresh generic independent semantic review with no findings; no theorem closure.
- Checks: static owner trace and polarity/rejection derivation, dependency hashes, note integrity; zero builds/tests/probes.
- Proposed message: `research: trace effect attachment through alias Call boundary`.
- Shared deltas left for primary/curator: record bounded source gap and alias/capture consumer premise; retain negative formation, output/residual lifecycle, complete Call, hygiene and production gates OPEN. No shared task/index/authority/theory or question file changed.

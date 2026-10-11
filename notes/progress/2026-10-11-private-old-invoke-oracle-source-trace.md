# Historical `invoke`: parameter, application and hygiene source trace

Date: 2026-10-11
Current baseline: `f7f123a8f36aa4b5d4a7f0738ac07601af5ae214`
Historical checkout: `/home/momota1029/rust/yulang-private-old`
Historical HEAD: `5a087d34c199fb09a95a107090413d4549085b96`
Status: unreviewed research source characterization; original theorem OPEN
Method: static constructor/consumer and artifact-field inspection
Lease: this note only; all historical sources read-only
Budget: 30 minutes wall time; no builds, tests, interpreter or Oracle runs

## 1. Objective and governing boundary

Locate an actual historical introduction chain for the unannotated formal in
`my invoke f = f 1`, rather than supplying a semantic model that assumes the
missing introduction. The current gate is the complete original formal
origin/ports needed by Entry-Value, not merely native Function sort incidence.
The governing cuts are
[`invoke` correspondence §§1,4–6](../theory/2026-10-11-invoke-build-to-simple-sub-proof.md),
[registry conformance §§3–4](../theory/2026-10-10-original-registry-kernel-conformance-attempt.md),
[Source Generalize definition §§2–4](../design/2026-10-08-source-generalize-definition.md)
and its [construction/proof §§2–4](../theory/2026-10-08-source-generalize-definition-and-proof.md).
Top-level inference principles §§1–5 and Evaluation govern inference policy.
Read research-lab, design-authority, git-concurrency and agent-orchestration;
applied the yulang-proofs source-bridge discipline. No new semantics selected.

**Result:** historical TIR5 constructs a real formal DefId, native type root,
name/owner maps and a four-port Function constraint before/after body lowering.
Its HIR interpreter has concrete callee evaluation, argument execution,
parameter insertion and body/result owners. None of the inspected records is
the current complete `ParameterOrigin` / received-carrier / typed receipt /
designated one-layer Force / Rebind introduction. Historical implementation
analogy supplies source locators; it does not type that missing current map.

The historical checkout has unrelated uncommitted HIR2, library and web edits.
They were neither read as dependencies nor changed. The source cone below is
hashed separately. Historical HEAD is not the frozen Yulang2 Oracle revision
`a58eefc31e22141574b6f20c6a5748151c6d79f1`. `git cat-file -t` for that
revision in this checkout failed (object unavailable); no Oracle commit tree
was inspected here. A preceding `rev-parse --verify` accepted the syntactically
valid full SHA but did not establish object availability.

## 2. Actual TIR5 formal introduction and ordered data flow

All abbreviated source paths in §§2–6 are relative to the historical checkout.
Line locators describe the hashed working files, not current successor code.

| Order | Actual owner | Retained output / next consumer |
| --- | --- | --- |
| 1 | `crates/yulang-tir5/src/lower/stmt/binding/lhs.rs:33–45` | Decomposes direct header into binding pattern and `ArgPatInfo` values. `arg.rs:195–209` recursively collects header argument patterns. |
| 2 | `lower/stmt/binding/arg.rs:53–100` | Allocates formal `def`, `tv`, optional annotation and `arg_eff_tv`; registers DefId→tv; direct `f` gives `TypedPat::UnresolvedName(f)` at that tv and `(f,def)` local binding; registers name. |
| 3 | `lower/stmt/binding/decl.rs:50–57`; `recursive.rs:9–51` | Resolves binding owner and preconstrains provisional header Function roots, even before learning whether the body uses self. Formal value/effect roots are non-generic in that provisional frozen self scheme. |
| 4 | `lower/stmt/binding/decl.rs:59–99` | Pushes local frame, installs actual formal names, registers formal/local owner, lowers the body under `with_owner`, then pops frame. |
| 5 | `lower/expr/path.rs:48–58,83–99,182–184,329–342` | A resolved ordinary same-owner non-let formal with no role constraints/frozen polymorphism aliases its exact `def_tvs[def]`. Its read effect is registered effect if present, otherwise a new historical exact-pure effect tv. |
| 6 | `lower/expr/apply.rs:23–107` | Allocates result/call/evaluation effects, records callee Function demand and effect joins; returns `TypedExpr::App`. |
| 7 | `lower/stmt/binding/lambda.rs:15–88` | Reverse-folds header arguments around lowered body, connects pattern tv/local shape, records lambda parameter pattern/locals, emits positive four-port Function and `TypedExpr::Lam(def,body)`. |
| 8 | `lower/stmt/binding/decl.rs:111–133` | Retains principal body, connects binding annotation/pattern, and returns `TypedStmt::Let`. |

`LowerState::register_def_tv` (`lower/state.rs:200–203`) writes both lowering
and inference definition maps. `pos_fun` / `neg_fun` (`:374–389`) allocate
the ordered child polarities `[V-,E-,E+,V+]` / `[V+,E+,E-,V-]` in the
historical arena. These are actual type-variable/AST owners, not declarations
of the original semantic port telescope.

For an explicit single-argument lambda, `lower/expr/lambda.rs:108–159` also
allocates def/value/effect variables and installs the local binding before
body lowering (`:162–172`). It carries a diagnostic `TypeOriginKind::Param`
on the native value tv (`:122–126`). Its later positive Function owner is
`:202–216`. Header formals instead initially use `fresh_tv` (`arg.rs:54`).
Neither diagnostic origin is the current semantic `ParameterOrigin`.

### Bounded native derivation for the target

Hypotheses: ordinary parser/header decomposition with a direct unannotated
`f`; resolved ordinary same-owner formal with no role constraint or frozen
polymorphic formal scheme; successful lowering allocations; no computation
annotation, continuation or effect-operation formal. Parsing/acceptance was
not executed. Let `alpha` be the real formal tv, `s` literal tv, `beta` Apply
result tv, `ce,ae,re` the Name/literal/Apply effect tvs, `e` the fresh call
effect, `i` the outer formal argument effect, `vL` lambda value tv, and `l`
lambda creation effect. `Empty+/-` below name the historical arena constants
`Row([],Bot)` / `Row([],Top)` (`types/arena.rs:82–90`); no current semantic
Pure interpretation is inferred from these names.

```text
formal:    fresh alpha, i; register(def_f,alpha); bind_name(f,def_f)
           Empty+ <= i-; i+ <= Empty-
Name f:    value tv = alpha; Empty+ <= ce-; ce+ <= Empty-
literal 1: int+ <= s-; Empty+ <= ae-; ae+ <= Empty-
Apply:     mark_through(e)
           alpha+ <= Fun-(s+, ae+, e-, beta-)
           ce+ <= re-; e+ <= re-
Lambda:    Fun+(alpha-, i-, re+, beta+) <= vL-
           Empty+ <= l-; l+ <= Empty-
```

Formal effect choice follows `ann.rs:73–81` and `state.rs:334–340`; literal
follows `expr/literal.rs:12–31` (only the displayed int lower is emitted,
not the current successor's two-sided literal bounds). The Apply formal
branch `apply.rs:79–84` marks `e` through; function demand is `:87–96` and
effect joins `:100–101`. The literal is not itself an App, so the ANF branch
`:43–49,102–104` is absent. A further `ae+ <= e-` is emitted at `:97–99`
only if `func_accepts_pure_argument` recognizes a positive Function lower;
no such positive lower for the unannotated bare formal has been established.
Creation effect is exact-pure because `lambda_effect.rs:41–77` excludes the
formal's own read from captures. This fragment omits the additional provisional
self-header root equations explicitly identified in the table and binding-root
connection; it is not claimed to be the complete emitted session or a scheme.

The real Function consumer is `solve/constrain/shape.rs:21–44`: for positive
`Fun(A-,AE-,RE+,R+)` versus negative demand it constrains argument value,
argument effect, result effect and result value. **Conditional difference:**
when `live_neg_is_empty_row(AE-)` is true, argument effect is sent to the
demand's result effect (`:36–39`); otherwise to provider argument effect
(`:40–41`). Recognition is a concrete predicate (`constrain/util.rs:59–99`),
not a theorem that every unannotated formal triggers it. The frozen provider
consumer retains the analogous branch (`constrain/frozen.rs:68–108`).

## 3. Exported artifacts and HIR refinement

`crates/yulang-tir5/src/export/expr.rs:56–94` exports Apply children and
`ApplyEvidence { callee, arg, result: TypeBounds, role_method }`, and Lambda
parameter name, optional effect annotation/allowed-effects and body under
lambda scope. `crates/yulang-tir5-program/src/expr.rs:85–90,146–155` defines
exactly those fields. There is no entry-port package in those records.
`crates/yulang-hir/src/lower.rs:52–75` copies them into HIR.

HIR runtime inference is downstream refinement, not the original TIR5
constraint emitter. `pipeline/runtime.rs:53–69` annotates, inserts wrapper
casts/admin/value-position binds, wraps binding bodies, normalizes and
reannotates, then calls `infer_runtime_module_types`. Its `infer/engine.rs:15–107`
starts from existing binding schemes, iterates at most 24 rounds and erases
type variables afterwards. Lambda handling (`:239–284`) inserts an expected
parameter type into the local type map, refines the body/parameter/return,
restores the shadowed map entry and forms HIR `Type::Fun`. Apply handling
(`:285–417`) uses symbolic/evidence callee information, refines argument and
result, optionally reinfers/casts the argument, and updates the local callee
type. It preserves annotation and hygiene fields. These map updates supply
concrete refinement ownership; they are not typed semantic entry laws.

## 4. Actual historical runtime: operational analogue and ordering limit

`interpreter/mod.rs:82–102` creates a closure with the actual parameter name,
param/return types, cloned body and environment, then evaluates an Apply's
callee first. `runtime/value.rs:60–67` declares those closure fields and no
receipt field. `interpreter/apply.rs:80–112` consumes a thunk callee if needed,
then evaluates the argument; a request retains `ApplyCallee` / `ApplyArg` frames.
`:115–138` forces an argument thunk when `callee_expects_pure_arg` holds,
then calls `apply`. The recognizer (`:142–146`) treats closures with neither
Any nor Thunk parameter type, and primitives, as pure-argument callees.
Closure `apply` (`:19–39`) clones capture environment, installs self when
present, wraps argument to actual param type, inserts it at the formal name,
evaluates the body and wraps/retains request suffix for thunk return.

This is actual execution evidence for capture, argument consumption, parameter
binding and invocation result handling. It cannot be relabeled the current
ordered `Receive; Receipt_L; Force_entry; Rebind` typed entry: argument forcing
is selected in the caller's `continue_apply_arg_value`, and wrapper routing can
also place BindHere at the caller argument (`effects/wrappers.rs:122–133,578–592`).
Moreover `interpreter/thunk.rs:12–25` recursively consumes nested returned
thunks in the Expr case, rather than establishing the current designated
one-layer Force law. These are historical implementation facts, not a proposed
change to current accepted entry meaning.

## 5. Effect hygiene and Oracle boundary

Historical TIR5: unannotated parameter effect tv uses the exact-pure helper;
opaque `[_]` allocates an unconstrained argument-effect tv, while the read tv
can be marked through separately (`arg.rs:58–72,132–144`; `ann.rs:73–81`).
Row annotations constrain argument effect both ways (`ann.rs:39–69`), mark
row tails through (`:118–149`), and give the read only a lower bound. Through
variables skip named negative row heads (`solve/constrain.rs:139–140`,
`constrain/rows.rs:58–65`); this is concrete solver behavior, not the current
abstract protection theorem.

Historical HIR: `effects/admin.rs:75–124` derives allowed effects from explicit
function/parameter metadata or a returns-thunk shape, records protected local
hygiene, allocates a local guard ID if protection is restrictive and used,
and wraps with LocalPushId plus saved LastId. Protected thunk Name/Apply
results receive AddId (`:40–56,127–155`). `allowed_effect_for_param`
(`:543–568`) gives wildcard Any, explicit allowed paths a closed row,
region annotations the parameter thunk row, and unannotated returns-thunk
parameters an empty allowed row. `interpreter/mod.rs:221–248` pushes/restores
the guard and appends BlockedEffect to a thunk. `runtime/effect.rs:23–38`
computes disallowed guard IDs; `interpreter/thunk.rs:18–36` carries those
guards when forcing/issuing requests. A guard ID is not a current typed receipt.

Static retained fixtures corroborate intended local cases: TIR5 `tests.rs:827–935`
contains lambda-sealing, wildcard-not-through and row-tail tests; `:956` onward
has `pure_function_passes_argument_effect_to_return_effect`. HIR admin tests
at `admin.rs:646` and `:897` cover exact higher-order result protection and
tuple-pattern alias protection; interpreter tests named
`interpreter_restores_local_push_id_around_resumed_continuation` and
`interpreter_local_push_id_keeps_blocked_effects_blocked_after_resume_shallowly`
occur at `interpreter/tests.rs:1060,1135`. They were located/read selectively,
not run or treated as proved assertions.

`tests/higher_order_io.yu` is an actual source fixture:

```yulang
act io:
  our read: () -> int
my read = io::read
my h(f: () -> [io] _) = f()
catch h(read):
  io::read(), k -> k 1
```

It supplies syntax and an annotated higher-order use, not a retained output or
Oracle-qualified acceptance result. Search of historical `tests` and `crates`
for `oracle|Oracle|invoke` in `.yu/.rs/.sh` found no matching label. No frozen
Oracle executable/source was consumed and no output comparison was run.
**Oracle preservation remains unverified**, including for bare `invoke` and
for hygiene across nested calls, aliases, handler expiry and resumption.

## 6. Archived lower2/infer2: separate implementation generation

`archive/yulang-lower2/src/lower/expr.rs:17–89,669–709` registers argument
pattern type variables/local names before lowering the body, then folds
positive four-port Function constraints around it. Its explicit lambda owner
(`:320–367`) clones locals, allocates/registers annotated pattern tv and body,
and emits the Function. Its ordinary application (`:649–664`) emits negative
Function with actual argument effect and a fresh call effect, then combines
callee and call effects. `archive/yulang-infer2/src/lib.rs:663–685` directly
decomposes all four ports, without the inspected TIR5 pure-argument diversion.
This is a different archived pair of owners. It has no established typed map
to the current Entry-Value contract and cannot supply an absent receipt law.

## 7. Exact missing map, checks and next action

The smallest remaining input-elaboration obligation is still:

```text
actual (L,d_f,unannotated), empty captures, ordinary Desc scope,
historical/current syntax/name/native-root evidence
   -/-> complete original ParameterOrigin(L,d_f,Value(A_f),r_f)
        plus received-carrier, designated entry view, receipt,
        one-layer Force and Rebind introductions in original order
```

The slash is failure to derive the typed correspondence, not a counterexample
to language semantics or an assertion that no owner can exist elsewhere.
The complete current constructor input telescope and field-preserving action
laws are still required. Removing `f 1` leaves the same one-formal gap; no
globally minimal source counterexample is claimed. Native DefId/tv, diagnostic
Param origin, TypeBounds and runtime guard/frame fields supply different
facts. Assigning them the missing semantic names does not type the map.

Recommended next action: give the constructive prover this owner table and
ask for one explicit typed correspondence from the actual formal binding
constructor to the selected original Entry-Value telescope, exposing every
missing independent local law. If the needed telescope/introduction is absent,
return that exact source-definition gap to the primary's authority path;
do not add another assumed registry/model transition.

Commands: bounded `rg` / `rg --files`, `cat`, `nl -ba` / `sed`, read-only
`git rev-parse`, historical status/log/object inspection, dependency SHA-256
and pinned-blob comparisons. Some initial broad captures were truncated;
claim owners were reread narrowly. Mistaken `rg` paths (`tests` subdirectories,
arena/constraint glob locations) failed and were corrected with actual paths.
Search is bounded to the listed source cones and fixture locations; this is
not an exhaustive all-history or all-repository absence proof.

Build/test/Oracle/model processes: zero. Seeds/ranges/mutations: none. There
is no executable oracle independence claim. Static constructor inspection
grounds ordering independently of an invented model, but shares the compiler's
actual implementations and does not validate their semantic correctness.
CPU, peak RSS and exact elapsed wall time were not instrumented; commands
were sequential or bounded independent reads, without heavyweight work.
Omitted: parser acceptance, emitted runtime dump/scheme, full scheme lifecycle,
all callers/providers, diagnostics/recovery, VM/native execution, full hygiene,
source soundness/principality and parent theorem closure. Producer reread is
not independent review. Artifact is frozen on handoff.

## 8. Frozen dependency hashes

SHA-256 inventory follows; only the explicitly leased note was written.

Current direct governing dependencies (working bytes equal pinned blob unless stated):

| Path | SHA-256 | Baseline equality |
| --- | --- | --- |
| `rules/research-lab.md` | `3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69` | same |
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` | same |
| `rules/git-concurrency.md` | `2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6` | same |
| `rules/agent-orchestration.md` | `3b1e9c5a083ae4257d3d8ad4bacadf55adf07997d0b02c10bcbec4ccda3258be` | same |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` | same |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` | same |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` | same |
| `notes/theory/2026-10-11-invoke-build-to-simple-sub-proof.md` | `b453e05a5add06516a388c3d4470505efdfb264753d1e4027243409c2787816d` | same |
| `notes/theory/2026-10-10-original-registry-kernel-conformance-attempt.md` | `1857e96a4e080b2eeb6f5cf4b50ab946b7baf6052f9380b21de8ea97fb4c43c8` | same |

Historical source/fixture working bytes (all equal historical HEAD blob):

| Path relative to private-old | SHA-256 |
| --- | --- |
| `crates/yulang-tir5/src/lower/stmt/binding/lhs.rs` | `cf0fe4d0b4a804bb45e5dadd19d5bc0ffa5572a017e136386179ee82ce6dc54b` |
| `crates/yulang-tir5/src/lower/stmt/binding/arg.rs` | `2e52fa7f0785800085fdeeacc66849251cf613cff09dabdc8dcde4efcd32b845` |
| `crates/yulang-tir5/src/lower/stmt/binding/decl.rs` | `c5949b325091878b96397bd661cb0a9ec305cb4eec9f8d5eee8ca26ecfe22cb8` |
| `crates/yulang-tir5/src/lower/stmt/binding/recursive.rs` | `f4917ac7612a5574a8e2f3070558172f8d1accd4790507d0d4763e6d0602909f` |
| `crates/yulang-tir5/src/lower/stmt/binding/lambda.rs` | `0af1f98835979016c984ebafb201f1de37b642dd79753219c9114d98732e8e17` |
| `crates/yulang-tir5/src/lower/stmt/binding/body.rs` | `0422e5964fc0b3104b3916a2390684f47f864e6dff096d80872a11ea2b0c9fc0` |
| `crates/yulang-tir5/src/lower/stmt/support/lambda_effect.rs` | `3915e7b2bfc7448bff90e48fcbb56ef6d8390074f229d45efdd4f27750254cc8` |
| `crates/yulang-tir5/src/lower/expr/lambda.rs` | `924a724b49ef3842c0adcc7d455e1e641e45a5729daf82e77930c845299947b6` |
| `crates/yulang-tir5/src/lower/expr/apply.rs` | `4996234629c62f7c29b84af2c66ede1a76ec831e13536618c6e80fd0b98a079a` |
| `crates/yulang-tir5/src/lower/expr/path.rs` | `7fe4c5995a4b6322c00910f20c0265c79eac89ad5cd0b1a665f5d56ba5744dc8` |
| `crates/yulang-tir5/src/lower/expr/var.rs` | `dbca4729ea1b321bdaf99ef3409031a4cf2d28837e69ee360f32018ffb011792` |
| `crates/yulang-tir5/src/lower/expr/chain.rs` | `d3a4d199c59a915555261d97d5be892e5a01d1bdce0acb94694d926033cbb6eb` |
| `crates/yulang-tir5/src/lower/expr/literal.rs` | `42cd7a429d0f66d1ae302dc1d8be1ba5a78bc15893895d5f60ac6795e1895f68` |
| `crates/yulang-tir5/src/lower/ann.rs` | `4379756f55327acb6636462765d4cb84315fac33deabf2fc591ecd33fcbc4806` |
| `crates/yulang-tir5/src/lower/state.rs` | `bfccca09be48f6935d80eb9fda794ce459a016be432bd66342658c6dc4e3c80e` |
| `crates/yulang-tir5/src/solve/constrain.rs` | `ccc8f5e255ed69bae83d5439fb1985bcada81663bf3496526262a4b49c5d1a8d` |
| `crates/yulang-tir5/src/solve/constrain/shape.rs` | `7243b252cfd355e1d2f325de2151acccb4b4276eaa578520d78eebb7325a5f95` |
| `crates/yulang-tir5/src/solve/constrain/frozen.rs` | `5678f4cb857e6271932388c30e27cc700dae8f01cb4be7ee61cec05f9b82cb80` |
| `crates/yulang-tir5/src/solve/constrain/rows.rs` | `37affdd6232f3bd85a40e29e0e0d1b128e18ab587386202645149c764b846ce8` |
| `crates/yulang-tir5/src/solve/constrain/util.rs` | `bcc7feafab1eaeb4b8c5245d2ca577c408eab7c868bc41a6e760ef3212691ced` |
| `crates/yulang-tir5/src/types/arena.rs` | `6c15e4d6ae49918020ba14da347d34483a8838bea05e88cf43ad13c2aed8ff2b` |
| `crates/yulang-tir5/src/export/expr.rs` | `7c748231a0ca56d065040472825c302d0644fbb3b5e47827bc661da26ad1f178` |
| `crates/yulang-tir5/src/tests.rs` | `7e60d2642f23073d71c668ba24c7d7c303e2fb77203bda0402c66934c3fbdd30` |
| `crates/yulang-tir5-program/src/expr.rs` | `2d1d7f1b2fd90e97e58ad0999cb9de886f3f31a8a446daff1226c980a80b3db2` |
| `crates/yulang-hir/src/lower.rs` | `bc13e8884c3ea952e2f45324ccd613741930aa672519fdfefa2485c676d90e27` |
| `crates/yulang-hir/src/pipeline/mod.rs` | `fbda7e93c3f50694f2a9657e8188d0032492d1eff194a174193c4f66ace77cfc` |
| `crates/yulang-hir/src/pipeline/runtime.rs` | `9aff149e3edb94cfe81ca23025b3a5e481f985d9955b5655b25c6d1569673cb5` |
| `crates/yulang-hir/src/pipeline/infer/mod.rs` | `13e8277094c290d6f2c66dc24a4295f523da65f9e74c0f76ea893f209cac762f` |
| `crates/yulang-hir/src/pipeline/infer/engine.rs` | `8f25528292c55c4169b54c5fa380a8fde60b499a2c7a06b15089c7d2b060e3c4` |
| `crates/yulang-hir/src/effects/wrappers.rs` | `4df4304e4226fc30b68d988173ed1669583ea4949b7784d6af6c3f7f6396cb64` |
| `crates/yulang-hir/src/effects/admin.rs` | `7bdaff69f3132c0656fb82cf793541ecac9a6067b532891904924e875337f544` |
| `crates/yulang-hir/src/runtime/value.rs` | `e6a08591cf337f67ffc413354806eae506aaa577ea90aa4cb426d348a479dbdb` |
| `crates/yulang-hir/src/runtime/effect.rs` | `e2efaf254fe8355575efcedf83f17f125fa6aa3b8a8216189674c77f9f87916f` |
| `crates/yulang-hir/src/interpreter/mod.rs` | `41913645a8ddac33ab6626d7ec815ffa6504ca264363911aab77a7f22e40bdc5` |
| `crates/yulang-hir/src/interpreter/apply.rs` | `0e83f82fbef8e767d2775f7da4073e423902878d5e72c7f49a7dd4dbbd4b6bcf` |
| `crates/yulang-hir/src/interpreter/thunk.rs` | `28229f4f1411787d943119508dedc63f6e17838425ec2013f0e826fd2adbc881` |
| `crates/yulang-hir/src/interpreter/tests.rs` | `627fbf04ca943bde8020a171fd04eafae71384892de08800a037c78a7b56c6aa` |
| `archive/yulang-lower2/src/lower/expr.rs` | `e34f7973d857698569bef11726a75eacc34fa3b4ede15c6f0c68d78cdcac659c` |
| `archive/yulang-infer2/src/lib.rs` | `7ab27aa6cf534e5570f8d9d8f82f4aac0a34b013a3f24a2ad04564b7de83a757` |
| `tests/higher_order_io.yu` | `564fa47e65b51f10fee1625cebdf39537c2e59fe5f7a8691c6551a5c32217df5` |

Historical dependency changes from recorded HEAD: none.

## 9. Commit packet

- Exact leased path: `notes/progress/2026-10-11-private-old-invoke-oracle-source-trace.md`.
- Current baseline SHA: `f7f123a8f36aa4b5d4a7f0738ac07601af5ae214`; historical baseline SHA: `5a087d34c199fb09a95a107090413d4549085b96`.
- Changed dependency hashes: none in inspected direct governing/historical dependencies; unrelated historical working changes excluded.
- Claim/review status: frozen unreviewed bounded static source characterization; no current theorem closure or historical semantic adoption.
- Checks already run: source/fixture inspection, SHA-256 inventory, direct governing pinned-blob equality and historical HEAD-blob equality; no compiler/tests/Oracle execution.
- Proposed commit message: `research: trace historical invoke formal and call owners`.
- Shared deltas left for primary/curator: link this evidence to the OPEN formal Entry-Value source-introduction gate; record actual historical producer/consumer locators and unavailable Oracle object; retain complete Call, hygiene, soundness/principality and cutover as OPEN. No shared records edited.

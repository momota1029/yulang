# Frozen Oracle application endpoint production and occurrence registration

Date: 2026-10-06
Status: frozen, independently compiler-referee-reviewed bounded historical characterization; research only
Yulang3 baseline: `601c80804e02924d90ac502e794b8b94d66223f1`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle checkout: `/tmp/yulang2-oracle-rebuild`
Exclusive lease: this note only
Semantic and implementation authority: none
Review: compiler_referee PASS on the paired endpoint-characterization artifacts; scope covers source endpoint lifetime, call/demand/provenance ordering and payload, one-call coordinate discriminator, novelty boundary, and historical/non-authoritative limits

## Objective, method and result

Trace an ordinary source application from its transient expression endpoints
through Function-demand construction, asking whether a stored expression or
source-owner table binds those endpoints before comparison. The method is
static control-flow and payload inspection of the pinned Oracle. No Oracle
execution, build, test, checker, compiler edit or Git mutation occurred.

The bounded result distinguishes three representations:

```text
transient Computation(ExprId, value TypeVar, effect TypeVar, ...)
    -> Function demand containing argument and result endpoints
    -> synchronous subtype admission/propagation
    -> App ExprId allocation and source-span registration
    -> ExpressionActual provenance snapshot of result-value lower bounds
```

The App's persistent actual-occurrence record stores copied bound record IDs,
not the original `(value,effect)` tuple or a contribution-typing judgment.
The argument's expected-occurrence record instead stores the whole callee
Function-demand constraint root, also after subtype submission. On this path
neither record is a pre-comparison source-slot registration. This is new
characterization of endpoint lifetime, actual-occurrence registration and the
synchronous ordering; it does not repeat the downstream RuntimeEvidenceSite
or labelled-derivation/path investigations.

## Governing scope and hypotheses

Read directly: [inferred call views](../design/2026-10-05-inferred-function-call-views.md)
§§1–5, [Attach law attempt](2026-10-06-attach-law-construction-attempt.md)
§§3–5, and [main source generation](2026-10-06-main-source-generation-minimal-clause.md)
§6. Their current obligation remains
`OriginalAssocType_X(beta,p0,j_call;s0,c0)`: independently type the original
complete contribution and associate it with the original signature slot and
source occurrence, on the same original `xi=(nu,K,D)`. Source/public/internal
types remain distinct; source formation and admission are independent of Q.
Oracle is historical evidence, not a supplier of current semantic authority.
The accepted ordinary-call and nested-block meanings are retained.

The static derivation assumes the inspected ordinary source-tail route returns
normally, with already lowered callee/argument Computations, and passes through
`make_source_app`. For the actual-occurrence observation it additionally
assumes that application is the result returned through
`lower_expr_with_lambda_scope`. The source-span insertions require the
respective spans to exist. These are control-flow hypotheses, not assertions
of accepted source, completed inference, current typing, admission or a
successful Function comparison.

## Exact endpoint and registration chain

All source paths below are relative to the frozen Oracle checkout.

| Stage / API | Key or input | Payload / output | Order and scope |
|---|---|---|---|
| `typing::Computation::{new,value,computation}`, `infer/src/typing.rs:18–47` | Explicit `ExprId`, value/effect `TypeVar`, evaluation | Transient tuple, optional `EffectViewId`; `Computation` is `Copy` | Returned by lowering; no table insertion in these constructors |
| `ExprLowerer::fresh_type_var`, `lowering/expr/tail.rs:736–738`; `infer::Arena::fresh_type_var`, `arena.rs:34–38` | Current inference `TypeLevel` | Fresh TypeVar registered with the constraint machine at that level | Before Function demand; administrative level registration is not current original-kernel typing |
| `apply_arguments`, `lowering/expr/tail.rs:89–124` | Source callee plus each lowered argument and CST ranges | One source App per argument, with the preceding result reused as the next callee | Argument lowering precedes its own demand |
| `make_app_with_origins`, `tail.rs:535–562` | Callee/argument Computations | Fresh `result_value`, `result_effect`, `call_effect`; negative Function demand | Demand exists before this App ExprId |
| `InferArena::subtype`, `arena.rs:90–93`; `ConstraintMachine::subtype`, `constraints/machine/entry.rs:493–500` | Positive callee root, negative Function demand, origin | Enqueues root and drains when admitted or queue nonempty; synchronizes type IDs afterward | Propagation can run synchronously before App allocation; no successful-comparison guard surrounds later allocation |
| `register_type_occurrence_roots`, application call in `tail.rs:564–586` | `(Expression(arg.expr), ExpressionExpected, empty path)` | Root of the just-submitted callee/Function constraint, when recoverable; completeness | Post-submission argument ownership of provenance; not an App endpoint table |
| Effect edges and `PolyArena::add_expr`, `tail.rs:615–627`; `poly/src/expr.rs:239–243` | Callee effect and call return-effect lower; then `Expr::App(callee.expr,arg.expr)` | Effect inclusions into `result_effect`; fresh App ExprId; returned `Computation::computation(expr,result_value,result_effect)` | After the main demand and expected provenance registration |
| `make_source_app`, `tail.rs:630–687` | Source-boundary origin, returned App ExprId, spans | `ApplicationProvenanceTable[App ExprId]` stores origin/module/application/callee spans; separate boundary table stores argument spans | Boundary ID precedes demand; these span payload insertions follow App construction and synchronous subtype work |
| `lower_expr_with_lambda_scope`, `lowering/expr/chain.rs:8–28` | Returned Computation | Calls actual-bound registration with `computation.value` only | After the expression has been lowered; does not pass `computation.effect` |
| `register_type_occurrence_bounds`, `analysis/session/occurrence_provenance.rs:15–35` | `(Expression(App ExprId), ExpressionActual, empty path)`, value TypeVar, `Lower` | Copies current `lower_record_ids()` into `OccurrenceProvenanceRoot::Bound` values | Snapshot of existing bounds; if `bounds().of(var)` is absent, returns without entry |
| `register_type_occurrence_roots`, same file `:38–67` | `TypeOccurrenceKey`, roots, completeness, optional fresh-source parent DefId | `PendingOccurrenceProvenance { roots, completeness }`; roots merged/deduplicated; empty roots make completeness `Incomplete` | Stores no TypeVar; parent marks separate freshness sets, not a slot/contribution relation |

The source tail's endpoint equation is precise:

```text
L = Pos::Var(callee.value)
U = Neg::Fun {
    arg     = Pos::Var(arg.value),
    arg_eff = Pos::Var(arg.effect),
    ret_eff = return_effect.upper,
    ret     = Neg::Var(result_value)
}
subtype(L,U,source_origin)
callee.effect <: result_effect
return_effect.lower <: result_effect
App = Expr::App(callee.expr,arg.expr)
returned = Computation(App,result_value,result_effect,Computation)
```

`return_effect` is the lowerer's paired upper/lower representation of the
fresh `call_effect`, possibly wrapped by its existing local-callee handling
(`tail.rs:744–815`). No current meaning is imported from those wrappers.
In particular `result_effect` summarizes the whole App's effect constraints;
it is a different fresh variable from the Function demand's `call_effect`.
Neither its equality after solving nor its printed row would establish
original contribution identity.

The available formal join is narrower: `lower_local_name`
(`lowering/name_ref.rs:146–174`) resolves `RefId -> local.def` and records
`RefUse { parent, value, source_span }`, while the returned Computation adds
the local effect. For an unschemed local, `instantiate_local_value`
(`tail.rs:855–858`) returns `local.value`; `local_callee_def`
(`tail.rs:844–849`) only recognizes a direct `Expr::Var` and resolves its
reference. This shares a historical formal root with its demand; it adds no
App-keyed original slot or complete contribution. The optional local call
upper registry stores negative demand IDs under the local DefId, with frame
metadata (`tail.rs:603–613,707–719`), rather than an App occurrence/contribution
tuple. This trace does not rederive the already characterized formal-marker
or declaration-signature mechanisms.

`TypeOccurrenceKey` has owner/role/path; owners are Definition, Expression
and Pattern (`poly/src/provenance.rs:69–96`). Its pending payload is only
roots/completeness (`infer/src/constraints/mod.rs:2742–2761`), and the session
stores it in `FxHashMap<TypeOccurrenceKey, PendingOccurrenceProvenance>`
(`analysis/mod.rs:221`). The actual path inspected here is empty. `Expr::App`
itself stores two operand ExprIds (`poly/src/expr.rs:479–485`). The separate
`Typing` representation stores only `DefId -> TypeVar`
(`infer/src/typing.rs:106–130`); its definition is corroborating representation
evidence, not a claim that every Oracle type consumer uses that table.

## Minimal discriminator: one App, different owners and ports

Take one ordinary source-tail occurrence `f x`, with transient endpoint
symbols `(a_f,e_f)` and `(a_x,e_x)`. Allocate the three fresh result symbols
`r_a,r_e,k_e` exactly as this branch does. Assume only that the route returns
and the outer expression wrapper runs; no concrete provider or solved type is
needed.

Then the expected entry is keyed by **x's ExprId**, and its root is the
constraint `a_f <: Function(a_x,e_x,return_upper(k_e),r_a)`. The actual entry
is keyed by **the App ExprId**, and receives existing lower-bound record IDs
for **r_a**, with no `r_e` argument. The App's complete effect summary and the
Function-return effect are also distinct fresh variables before any equality
is established.

This single-occurrence witness discriminates the shortcut
“ExpressionActual/Expected means a stored original contribution type at the
same source slot.” The record sorts, owners, ports and program order do not
implement that statement. A demand root may indirectly mention several
endpoints; that does not turn its argument-owned provenance key into an
original typed slot, and a value-bound snapshot does not become complete
invocation typing. No claim of minimal accepted-source counterexample,
different final schemes or absent effect evidence elsewhere is made.

Two unexecuted diagnostic mutations make the failure conditions explicit:
identifying `r_e` with `k_e` loses the displayed distinction between whole App
evaluation and callable return-effect; replacing the snapshot by a persistent
`TypeVar` field changes the inspected payload and requires a new maintenance
rule. Neither mutation was applied. No seeds, enumeration ranges or executed
mutation counts exist for this static method.

## Independence, remaining premise and recommended action

The Oracle source independently grounds historical API payload and ordering
relative to the current research notation. It is not an independent oracle
for the current language judgment: both interpretations would still require
source-to-current correspondence, and the selected governing sections supply
the current obligation. There is no checker assuming transition rules and
then purporting to prove them. The source windows prove this bounded branch
characterization, conditional on the stated route, without a source-wide
absence theorem.

What remains is precisely the independently interpreted source introduction
of `OriginalAssocType_X(beta,p0,j_call;s0,c0)`. Historical endpoint connectivity
does not supply `s0`, type the complete `c0`, identify the contribution's
own-upper/inherited tags, or prove either licensing direction. Historical
TypeLevel and solver bounds do not supply the original shared `nu,K,D`, its
rigid scopes, completed profile or comparison-independent admission. No
replacement row, per-port witness, Q-successful result or projected path is
substituted for the same original `xi`. No soundness, principality, source
adequacy or production gate closes.

Recommended next action: use this lifetime/payload discriminator when deriving
the current source-owned contribution introduction clause, explicitly stating
the original slot/contribution sorts and same-X dependencies that an endpoint
tuple and provenance root leave unconstructed. Another downstream provenance
trace would leave the same premise untouched.

## Checks, dependencies and resource scope

Both HEADs matched their pins on initial inspection. The following read-only
checks passed with exit 0: Oracle `git diff --exit-code <oracle-pin> --` the
twelve files listed below; Yulang3 `git diff --exit-code <baseline> --` the
three governing dependency files. `git ls-tree` recorded exact baseline blobs.
Final HEAD rechecks matched both pins. `git diff --no-index --check --
/dev/null <leased-note>` emitted no whitespace diagnostics and returned 1,
the no-index status for a new file differing from `/dev/null`.
Searches used scoped `rg`; decisive reads used bounded `sed` windows. No
whole-repository search completeness is claimed; synthetic applications,
annotation/selection adapters, later bound changes, scheme transport and
other consumers are omitted. No compile or test result is claimed.

| Oracle dependency | Git blob at pin |
|---|---|
| `crates/infer/src/typing.rs` | `7d8ad7846aaf4942512a23ad3710ddfd9d2e78be` |
| `crates/infer/src/arena.rs` | `aaf7abcd99ad31c16e3b46d4931c4b78a38ed0ba` |
| `crates/infer/src/lowering/expr/tail.rs` | `8289bfdc6a17b2469ae168ac7939d34813fda474` |
| `crates/infer/src/lowering/expr/chain.rs` | `e85beb100231264e210062bd56d8532b09b6200f` |
| `crates/infer/src/lowering/name_ref.rs` | `929e21b022c5f7015c8168fb936ba590691100a4` |
| `crates/infer/src/lowering/local.rs` | `5b60e91edc1ff194486fe3292b53b292bf54d529` |
| `crates/infer/src/analysis/mod.rs` | `91cebc764f0b7a7415f21eb4b70885d074e2242d` |
| `crates/infer/src/analysis/session/occurrence_provenance.rs` | `6a3e4da511d8c2f6f512f2c22b6112ecda6076c8` |
| `crates/infer/src/constraints/mod.rs` | `14860e3664a7ac05f7493f1d51fe69a6f34216e5` |
| `crates/infer/src/constraints/machine/entry.rs` | `d75544523281cc7f5c6f1778fbe25eb42b7dfe7b` |
| `crates/poly/src/expr.rs` | `4cd13e8b9d71b63f768d4a5739a264b5a3b76c1e` |
| `crates/poly/src/provenance.rs` | `0980898542588402426b80cca421a5299fd75867` |

Yulang3 dependency blobs: inferred-call-views
`9493abd55e61dbc59de31f319c2ff9670204069a`; Attach-law attempt
`415e92ddc37d4e6cec6f3813516770f4cba309e2`; main-source-generation
`457c924b807540685b24b656425c99e9dbe4fdee`.

Budget: one sequential lightweight tool process at a time; no heavyweight
process. Wall time, CPU and peak RSS were not instrumented; the bounded pass
used the assigned 15-minute stop policy and shell read commands reported
sub-second elapsed times.
Only the leased note was written. Independent review is pending; the producer's
source inspection is not review. Shared task/theory/index changes are returned
to the primary rather than applied. The artifact is frozen on submission.

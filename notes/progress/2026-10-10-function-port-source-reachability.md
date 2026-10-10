# Function-port collision: frozen source-reachability audit

Date: 2026-10-10
Status: frozen, unreviewed research-only bounded source characterization and
conditional exclusion; no accepted source witness, theorem closure, production
bug claim, or implementation authority
Baseline: `9d4392ef4a4ef309c6c9c9194840deca3cbf6de6`
Branch supplied by primary: `research/simple-sub-intrusion`
Lease: this new note only
Method/budget: one static researcher pass; lightweight reads, no execution,
builds, benchmarks, children, or Git mutations

## Objective and authority

Audit the source premise of the minimized witness in
`2026-10-10-entry-circuit-source-falsifier.md`: an authentic Lambda slot-3
seed `E <: T`, plus a Function comparison whose ordinary ArgumentEffect/Swap
and ResultEffect/Preserve children are both `T <: E` in the same complete
generated component. Prefer a nonidentity parent only if a source owner
constructs it. Authority is the contextual attachment/admission design §§3–7,
especially the field-specific operations in §4 and complete-component
certificate requirement in §5. The accepted two-cycle gate, attachment grouping,
private deferral, and deferred concrete-formal scope remain as selected there.

Result: no actual accepted source/HIR witness was established. Direct Lambda,
written-interface and Apply construction do not supply the required crossed
negative ports. Their allocation and ownership rules reduce the remaining
question to preservation of port-owner separation across all source lifecycle
routes. The detached endpoint witness remains conditional. This note does not
promote a bounded constructor audit to a universal source-unreachability theorem.

## Exact equality needed

Write a Function comparison as
`Fun(a-, l_arg-, l_ret+, r+) <: Fun(b+, u_arg+, u_ret-, s-)`.
The frozen decomposition at `yu-solver/src/lib.rs:12023–12049` produces:

```text
ArgumentEffect / Swap:    u_arg <: l_arg
ResultEffect / Preserve:  l_ret <: u_ret
```

For both children to equal the requested reverse seed `T <: E`, the canonical
rows must satisfy all four equalities:

```text
l_arg = E       l_ret = T       u_arg = T       u_ret = E
```

For the original witness's inferred Lambda, the first two equalities hold at
its owner. The missing construction is a negative Function with its *own*
argument Effect port equal to that Lambda's return row and its *own* result
Effect port equal to that Lambda's entry row. Two edges in an SCC, equal variable
spellings, or semantic mutual subtyping do not establish these row identities.
An authentic origin elsewhere in the component also does not license a port.

## Constructor evidence and a direct near miss

- **Lambda owner.** `yu-hir/src/module/local_source.rs:288–318` and `:342–363`
  create Lambda forms for top-level and local binding parameters. Frozen
  `candidate_source.rs:420–434` retains their `LambdaRecipe`. At
  `lib.rs:11155–11225`, `admit_lambda_fact` allocates fresh `E` and `T`, emits
  slot 3 `E <: T` and slot 4 `body_effect <: T`, and authenticates only slot 3
  with `retain_inferred_entry`. At `:11229–11249` it separately publishes the
  positive Function `Fun(..., E-, T+, ...)` through slot 2. The expression's
  computation Effect component, body Effect component, `E`, and `T` are
  different constructional objects.
- **Written interface.** HIR annotation syntax stores row variable spellings
  and source positions (`source_annotation.rs:67–93`, `:399–479`, `:505–562`),
  with no field for referring to a Lambda's solver row ID. The syntax owner
  admits leading bracket rows and arrows (`yu-syntax/src/type_expr/mod.rs:780`,
  `:1235`, `:1595`, `:2198`). Scoped written names use
  `candidate_formal_effect_variable`, whose first occurrence allocates a fresh
  row (`candidate_effect.rs:843–855`). Signature arguments reverse variance
  and results preserve it (`:1254–1299`). A contravariant singleton symbolic
  argument is the raw scoped tail (`:1383–1393`); a covariant result is a *fresh
  port row* with a Support/Allowance bound, even when it has a named tail
  (`:1369–1382`, `:1395–1432`).
- **Illustrative near miss, not an executed fixture:**
  `my f x: (['r] int) -> ['e] int = x`. Under that annotation's frozen lowering,
  let `A` be the scoped row for `'r`, `B` the scoped tail for `'e`, and `R` the
  freshly allocated checking result port. The negative interface has ports
  `A+` and `R-`, with `R <: Allowance(view(tail=B))`. Its comparison against the
  inferred Lambda produces `A <: E` and `T <: R`, rather than two copies of
  `T <: E`. Renaming `'r` to `'e`, or swapping spellings, cannot choose either
  of the authentic Lambda rows. Annotation pairing at `:1097–1129` constrains
  the source endpoint and separately exposes a positive signature; it does
  not assign a scoped name to an existing Lambda row. This source text was
  neither parsed nor solved here and carries no acceptance claim.
- **Formal annotation exception to a simpler exclusion.** Paired formal
  annotations share omitted/singleton-symbolic rows on both polarities
  (`candidate_effect.rs:898–934`), and repeated symbolic names can make their
  own ports coincide. `:939–971` installs their positive/negative interfaces
  and formal domain. Thus “all negative Effect ports are fresh wrappers” is
  false. These shared rows are annotation-owned fresh rows, not Lambda `E/T`.
  This is why endpoint shape alone cannot settle the requested premise.
- **Apply owner.** `candidate_source.rs:369–386` retains the actual argument
  computation component separately from the application component. The
  negative checking Function uses that argument computation row and a freshly
  allocated **invocation** return row (`shadow_apply.rs:1339–1358`); its result
  port is not the application's computation row. Neither is selected by the
  name of an inferred Lambda port. The native interface records these inputs
  separately (`:1360–1376`). Closed-type negative Function import in
  `lib.rs:15407–15445` allows only bottom/empty Effect ports; finalization at
  `:16362–16369` likewise supplies bottom/empty, not a crossed live pair.

The relevant fresh allocator appends a new Effect row and returns its ordinal
(`lib.rs:10092–10121`). These are allocation facts, not claims that a later
constraint equates the resulting rows.

## Reduced conditional exclusion and its remaining premise

Use these explicit hypotheses for the bounded exclusion:

1. The positive Function's Effect ports are the authentic, distinct Lambda
   `E/T` or identity-preserving copies of them.
2. Negative Function roots originate only in the inspected signature/formal,
   Apply, or closed-type import producers above. Their direct Effect ports
   have fresh/initial-computation ownership separate from this Lambda's `E/T`.
3. Subsequent production routes preserve those separate port owners; no
   uninspected constructor or capture route synthesizes a negative Function
   whose own Effect slots are filled from an inferred Lambda's `E/T`.

Under these hypotheses, the negative Function cannot have `u_arg=T` and
`u_ret=E`, so the requested two-child reverse-seed collision is excluded.
Hypothesis 2's listed constructors are grounded in the reads above. Hypothesis
3 is the remaining **whole-source closure premise**, not an established theorem.

The inspected transport owners support that premise without replacing it:

- Extrusion allocates a fresh copy of its exact port row, retains that
  copy/parent pair, and reconstructs the same Function polarity with the
  same field positions (`candidate_extrusion.rs:81–123`, `:209–250`, `:323–350`).
- Intrusion tests only recorded copy/parent pairs for SCC membership
  (`candidate_intrusion.rs:171–218`, `:477–486`); the forest update at `:582`
  merges a qualifying copy into its parent. A cycle between unrelated fresh
  rows does not itself merge them. `canonical_effect` consults this forest
  (`lib.rs:11334–11339`).
- Scheme capture records actual Function polarity and field order
  (`candidate_scheme.rs:345–400`); fresh-use row mapping reuses a canonical
  source row or allocates one fresh row per source identity (`:840–851`), then
  reconstructs the recorded Function polarity and four fields (`:973–989`).

No complete activated source dependency closure, original-versus-fresh seed
origin transport, or all imported/module/recursive capture routes were audited
to universal closure. No source instance was produced that violates these owner
facts. The precise missing bridge is an exhaustive negative-Function
port-origin preservation argument across that lifecycle, together with the
mapping of any transported authentic slot-3 origin to its exact generated
relation. That belongs to the constructive prover lane. This researcher pass
stops here rather than treating another endpoint projection as source evidence.

## Parent context and operation boundary

At the frozen baseline `candidate_context_source` creates a nonidentity context
only for an Effect relation with a closed Allowance receiver; a Value relation,
including a directly seeded Function comparison, receives identity
(`candidate_context.rs:1306–1317`). `candidate_context_admit:1365–1369` chooses
the child's context from its own endpoints. `candidate_function_port_admit`
retains separate Swap/Preserve incidences at `:1395–1405`; its operation labels
are inert at this baseline (`:114–115`). Consequently the starting note's
nonidentity parent and detached PUSH discriminator are not an executed source
construction here.

Value-bound replay can retain a supplied context (`:1473–1495`, `:1553–1562`),
and fresh transport accepts a renamed context (`:1601–1609`). This pass has not
established a source path that supplies a nonidentity Function parent through
those owners, nor a universal exclusion over them. The selected §4 operation
contract remains required for the implementation gate independently of whether
this particular minimized source witness exists.

## Checks, independence, limits and dependencies

Checks used frozen `git show 9d4392ef4:<path>` with bounded `rg`, `nl -ba` and
`sed` reads; `git grep -n -E 'negative_function_term\(|negative_function\('
9d4392ef4 -- crates/yu-solver/src` with test-path exclusions; `git rev-parse
9d4392ef4`; and `git ls-tree` for the dependency blobs below. The constructor
search still returned inline test sections, which were not treated as source
producers. Task/index searches were output-limited and incomplete; they served
only as locators. Governing §§3–7 and the starting falsifier were read directly.
No moving working-tree version of a Packet 1 source path was read.

There was no independent oracle, parser/compiler execution, executable checker,
test, build, benchmark, mutation, enumerated seed/range, or minimized accepted
program. The static evidence is independent of the detached projection model
but shares the frozen compiler's construction rules; it does not validate
Oracle semantics or successful scheme publication. No local toy probe was run.
Reads were lightweight and batched up to four short read commands; no heavyweight
processes ran. The assigned CPU budget was one CPU; CPU affinity was not set,
and peak CPU/RAM and total wall time were not measured. Fixed revision inputs cannot change during this
audit; current HEAD/working-tree dependency equality is left to the primary.

| Frozen direct dependency | Git blob |
| --- | --- |
| `crates/yu-hir/src/module/local_source.rs` | `cc0f08da32b8cf3884597c53dee8d74d474f3bed` |
| `crates/yu-hir/src/module/source_annotation.rs` | `c6a738cd219d7ac5054971dc80739b350a1807e4` |
| `crates/yu-syntax/src/type_expr/mod.rs` | `8d042baa5fc8b69008a36e007dfad2b51679a7e1` |
| `crates/yu-solver/src/lib.rs` | `1b036291c8c52a5723f070d80ac655f6355e5629` |
| `crates/yu-solver/src/candidate_source.rs` | `dbc3ee822a61b4a861597f07654c52cacb8fb92d` |
| `crates/yu-solver/src/shadow_apply.rs` | `3578b31f3d0607f6c71b9fbf6e05e5b1085961b2` |
| `crates/yu-solver/src/candidate_effect.rs` | `57ec353d69e0c59d86434b6ed21c692aaac6da33` |
| `crates/yu-solver/src/candidate_context.rs` | `ac646a46dd687e4d56bcd09887545f91de32391d` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `4dc6dfef0203bd1bcf2bba2380008d58ffe114ac` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `7a750da800199c23d998bc2da23015256c4f265f` |
| `crates/yu-solver/src/candidate_scheme.rs` | `005ca3ccaf2fcfba3284a76168d7e8ba7a165666` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `c99873544ca90aa817c77941514f7868a8023d65` |
| `notes/progress/2026-10-10-entry-circuit-source-falsifier.md` | `224490ac364e41bfa548c7a0488214afcb15e974` |

Recommended next action: assign the prover the narrow port-origin closure
premise above, rather than attempting another reversed-annotation endpoint
fixture. A positive result would exclude this exact authentic-row witness; a
counterexample must identify the actual negative-Function producer and complete
origin-preserving generated component before any execution packet is warranted.

Commit packet: exact leased path
`notes/progress/2026-10-10-function-port-source-reachability.md`; baseline
`9d4392ef4a4ef309c6c9c9194840deca3cbf6de6`; changed dependency hashes: none
within the fixed snapshot, current integration equality unverified; review:
unreviewed research-only bounded source characterization/conditional exclusion;
checks: frozen reads and revision/blob inspection only. Proposed message:
`research: bound Function-port collision source reachability`. Shared deltas
left for the primary/curator: record the unresolved port-origin closure premise
and qualify the earlier falsifier's exact source-reachability claim; no gate,
theorem, authority, question bundle, or design-index promotion is proposed.
Writes stop at this artifact before review.

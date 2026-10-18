# R60 primary source-owner trace: paired Function-argument interface

Session: `current-conversation-2026-10-19-r60`
Contract: `tasks/agent-loop/sprints/paired-annotation-interface-20261019-r60.md`, revision 2, SHA-256 `6b40870963d796a9bc1d125334a39e049d893450da8d1b38bdc0b310b5f982f1`
Activation baseline: `b62bf4bed359ed5f8bd4728923d1807044f9e8c9`; activation commit: `a3ab8baff`; proof-lane receipt commit: `18bfb6635`; 25/25 pinned dependencies matched before activation.
Parent: original computation-forwarding preservation §§1,6–7 and Simple-sub A/B remain OPEN 0→0; R50 NOT ADOPTED.

## Fixed source and source identities

This lane is a static source-owner trace for the unchanged R58/R59 constructor candidate, not a parse or solve result:

```yu
act io:
    our tick: int -> int

my forward (t:[io] int): [io] int -> [io] int = t
my outer (q:[io] int) = forward q
```

The three occurrences resolving to `io` retain different source roles and identities. A resolved effect family does not merge source positions.

| Position | Native/source role | Owning obligation |
| --- | --- | --- |
| `p_t`: formal `t:[io] int` | Original Computation entry effect `E` | The selected policy gives this formal position local permission. Keep `E` open and retain ordinary generated constraints and symbolic dependencies. It does not grant a closed `E <= {io}` cap. |
| `p_A`: Function argument `[io] int` in the whole-function annotation | Contravariant Function argument permission | Its permission is owned by this annotation position and the same original provider construction. It is not the `p_t` permission. Current preflight/native builder both reject the concrete negative row before a paired constructor is reached. |
| `p_R`: Function result `[io] int` in the whole-function annotation | Covariant result allowance/interface | The declared result allowance does not establish actual inflow or a handler residual. Preserve correlated result constraints independently of the argument permission. |

Source positions are retained on `SourceAnnotation` / `SourceEffectRow` in HIR (`crates/yu-hir/src/module/source_annotation.rs`). Authority for permission and allowance roles is `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1, 1.1–1.2, 4–5. The reviewed formal-permission constructor in `notes/theory/2026-10-15-computation-formal-permission-construction.md` owns a formal parameter/path; it does not itself define the whole-Function annotation constructor.

## Existing path and first constructor boundary

Ordinary `CandidateInference::solve` uses non-scoped mode (`candidate_source.rs` preflight is called before collection/session creation from `shadow_apply.rs`). Root annotation preflight starts at positive polarity, then flips at the Function argument. `preflight_annotation` rejects a concrete row at negative polarity (`candidate_source.rs:459–460,603–615`) as `CandidateError::Unsupported`. If preflight were separately passed, `candidate_signature_effect` independently returns `IdentityExhausted` for a concrete negative-variance row (`candidate_effect.rs:1933–1935`). Neither guard may be bypassed under R60.

For an independently authorized future constructor, source planning schedules the body actions and then `Action::Annotation` (`candidate_source.rs:1450–1468,1687–1694`). The annotation pair builder (`candidate_effect.rs:1611–1704`) constructs checking and exposed signatures with separate root signs and admits slot 40, optional slot 42, then slot 41. The whole annotation has no root effect row here, so slot 42 contributes no root-row constraint; nested `p_A` and `p_R` enter through Function ports.

| Signature view | Argument value/effect | Result effect/value |
| --- | --- | --- |
| Checking `C` (root sign −) | `Int+`, `A_c+` at `p_A` | `B_c−` at `p_R`, `Int−` |
| Exposed `X` (root sign +) | `Int−`, `A_e−` at `p_A` | `B_e+` at `p_R`, `Int+` |

These are obligations for two actual constructor outputs. Their equality, independence, and source-qualified correspondence are not established merely by their shared position spelling. Native Function comparison of the original provider `P=(Int−,T−,R+,V+)` against `C` directs the ordinary tasks `Int+<=Int−`, `A_c<=T`, `R<=B_c`, `V<=Int−` (`candidate_effect.rs:1780–1871`; `lib.rs:12655–12683`). Slot 41 exposes `X`; it creates neither `A_e<=A_c` nor `A_e<=T`. A later ordinary Apply contributes `E_arg<=A_e` and `B_e<=E_call`, plus `E_call<=E_out` (`shadow_apply.rs:1788–1923`).

Thus the source/native premise R60 must locate is an admitted path from the exposed `A_e` through the checking `A_c` to this same original provider's `T`, or a genuinely admitted same-instance alternate path to `T`. The path must carry the `p_A`-local permission and the ordinary constraints that belong to the selected source contract. It cannot borrow permission from `p_t`, from `p_R`, or from another provider. The full paired judgment must retain the correlated result interface (`R`, `B_c`, `B_e`, and the original Name-to-exposed-result correspondence); an argument edge alone is insufficient.

## Physical owners after a successful constructor prefix

- Native endpoint tasks and physical BoundKeys are admitted by the source/effect and extrusion owners (`candidate_extrusion.rs:856–969`; `lib.rs:12355–12690`). Queuing a relation does not establish admission.
- Signed extrusion snapshots and transports endpoint relations with their source/co-parent provenance (`candidate_extrusion.rs:78–340`). Qualified intrusion merges preserve bound sides and canonicalize representatives (`candidate_intrusion.rs:308–386,568–713`); canonical row equality by itself does not preserve source-position permission ownership.
- The source schedule completes before enclosing-definition capture (`candidate_scheme.rs:1360–1435). Capture must reach the endpoints and attached evidence needed by the pair (`:755–790,1054–1132,1259–1292`). Route/FreshUse preparation owns per-use row maps and retained correspondence (`:1489–1608,1715–1755`), and actual bound restoration is owned by `:1860–1906`. R59/R60 have not established this sample's capture, FreshUse admission, later `outer` comparison, handler selection, subtraction, or residual.
- `candidate_formal_effect_port` / `FormalPermission` stores an original formal parameter, occurrence, owner, scope, path, source row position, and concrete family (`candidate_effect.rs:1385–1434,1464–1538`). It proves that a position-indexed representation exists for that formal constructor only. It does not prove the corresponding whole-Function argument permission or its consumer.
- After any admitted constructor, downstream consumer work must still distinguish declared permission/interface, constraint-derived inflow, and residual after actual handling. `candidate_context_execute_relation` and retained allowance filters are admission owners (`candidate_context.rs:3575–3660`); annotation support is not itself an execution/subtraction theorem.

## Owner-lane disposition

Current source owners identify the exact seam but do not construct it: a same-`p_A`, same-provider `A_e` to checked-provider entrance with permission provenance, ordinary constraints, and result correlation. The fixed source still stops at the pre-collection negative concrete-row guard. The source-owner read does not choose a shared-row representation or certify preservation of source-contract solutions; that must be shown by the proof lane with explicit auxiliary-variable correspondence, then checked independently.

No safe implementation slice follows from this trace. Keep both guards authoritative. No code, semantic edit, test, parser/solver/compiler execution, build, runtime, probe, or measurement was performed. The parent theorem and all downstream gates remain OPEN.

## Output and resource receipt

This lane writes only this trace and `tasks/agent-loop/inbox/20261019-r60-implementation.md`. Requested Luna/high; observed model/effort UNKNOWN. Allocation cap 500 seconds; actual elapsed/CPU/RSS UNKNOWN. Read-only source and authority inspection, no descendants.

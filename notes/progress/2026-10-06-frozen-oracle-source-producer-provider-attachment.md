# Frozen Oracle: downstream closure provider attachment

Date: 2026-10-06
Status: frozen, compiler-referee reviewed research-only historical characterization; no findings
Yulang3 baseline: `b26087ce26bc2e77f41709a1e7b58bc4c73c2db6`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this note only
Semantic and implementation authority: none

## Objective, authority, and result

Locate one historical mechanism corresponding to the missing typed capture
attachment producer, beyond the already characterized closure environment
fields. Method: three bounded static call paths and one existing manually
constructed fixture; no compiler execution or source acceptance claim.

**Claim class: conditional historical characterization and a local
constructor discriminator.** After inferred-formal typing, the evidence VM
builds capture requirements from direct effect-operation calls in control IR,
associates capture slots and provider candidates with a control expression,
fills missing providers at value construction, and activates stored providers
on closure entry. This is a concrete downstream attachment mechanism. It does
not introduce a typed relation for an unknown inferred formal.

Current authority remains inferred call views §§1.1–5 and nested-block source
realization §§1–3, narrowed by the current explicit directional decision in
`2026-10-06-directional-inferred-effect-protection-addendum.md` §§1–4.
Protection flows from an originally protected variable to its source upper
Function output effect; it does not back-protect an existing provider lower.
Older `U_c`/Handler discussions are retained historical research obligations,
not a license to reopen that direction. The current task's open gates 1–4
retain source-wide exposure, typed contribution/receipt/capture correspondence,
whole joint relation, and independent admission. Oracle supplies no authority.

## Three inspected paths

All following paths and line numbers refer to the frozen Oracle revision.

1. **Control IR requirements to expression-indexed capture slots.**
   `crates/evidence-vm/src/lib.rs:1923–1954` computes each Lambda body's
   `requirements_in_expr` and skips a Lambda with no requirements. That
   collector (`:2062–2140`) records an Apply only when its callee is directly
   `Expr::EffectOp` and its family is not handled by the current collector
   context. Records group operation expression IDs by
   `(family, UnknownFallback)` (`:2082–2097`, `:2321–2326`). The traversal
   stops at nested Lambda/MakeThunk/FunctionAdapter boundaries (`:2174`).
   `value_env_signature` deduplicates those requirement slots (`:2339–2353`).

   `build_lexical_handler_envs` and `LexicalHandlerEnvCollector`
   (`:2934–3054`, `:3126–3151`) associate value expressions with the IDs of
   lexical handlers whose family matches each non-Blocked capture slot.
   Catch traversal adds handlers only while walking its body, then restores
   the stack before walking arms (`:3044–3066`). Slot IDs come from an
   already supplied slot table. `build_value_objects` (`:2907–2925`) retains
   the value `ExprId`, slot IDs and these provider candidates. These are
   family/route requirements, not current original static `Slots(beta)`.

2. **Capture plan to closure attachment.**
   `crates/evidence-vm/src/runtime/plan.rs:973–992,1008–1021` imports the
   manually or compiler supplied value objects into expression-indexed
   provider and capture-slot tables. `provider_env_for_value` (`:485–507`)
   starts with that expression's static provider map, then attempts to fill
   missing captured slots. `provider_for_slot` (`:721–742`) selects the
   nearest matching active handler first, otherwise the nearest matching
   active provider environment. Candidates are restricted by the supplied
   per-slot candidate table. No candidate means no appended provider.
   `extend_missing` (`:862–874`) preserves an existing slot entry even if
   the runtime lookup offers another handler; it does not overwrite it.

   Runtime lowering preserves the control expression as `provider_expr`
   on the Lambda (`crates/evidence-vm/src/runtime.rs:9563–9567`). The value
   constructor looks up that expression, passes its current active handler
   and eligible provider-environment sequences (`:10851–10865`), and stores
   the result beside the cloned lexical environment (`:15570–15587`).
   The full eligibility filter for the active-environment sequence was not
   inspected; the selection characterization is relative to the sequence
   actually passed to the helper.

3. **Nonempty stored attachment to closure entry.**
   `crates/evidence-vm/src/runtime.rs:18317–18334` enters a closure with
   nonempty stored evidence via `with_provider_env`, then clones its lexical
   environment, binds its parameter and evaluates its body. The helper
   (`:10877–10913`) pushes a new provider frame, restores the active-frame
   stack after the run and closes the returned result under that environment.
   The immediate Value result is unchanged (`:10915–10927`); effect-result
   continuation closure was only located, not reconstructed. The previously
   characterized plain tail shortcut (`:16557–16566`) applies only when the
   stored provider environment is empty.

This is nearest to current attachment A because a value carries a distinct
provider map and its later entry installs that map before body evaluation.
The correspondence stops at those historical slot/handler associations:
there is no derived map from the exact source formal/use component to a
current original contract/profile, typed receipt or whole original `xi`.
It is downstream evidence-VM machinery after inferred-formal typing, not an
inference producer or a proof of the selected source semantics.

## Smallest local discriminator and explicit hypotheses

H1 (verified provenance): the three historical files equal their frozen Git
blobs. The fifteen current dependencies listed below equal the pinned baseline.
H2 (candidate control input): one successfully lowered Lambda body consists
of `Apply(Local(f), Local(x))`, with no additional direct effect-operation
calls or wrapper bodies. This control form is stipulated; the exact approved
source was not parsed or lowered in this lane.
H3 (constructor execution): the named helpers run normally on well-formed
expression/slot tables; later provider selection uses the supplied candidate
and active-provider sequences. No whole-program solver/runtime theorem is
assumed.

Under H2, the Apply's callee is not EffectOp, and both Local leaves produce
no requirement. The requirement set is empty, so path 1 creates no value
capture plan for this Lambda. A one-field **analytical control-IR mutation**
replacing only the callee with `EffectOp(path=p)` causes that Apply ID to be
recorded at `(p,UnknownFallback)`, provided `p` is not locally handled.
One Lambda, one Apply and one family suffice to distinguish the collector's
recognition rule. This is neither an executed mutation nor an accepted-source
counterexample; it does not assert that the two bodies share a type/behavior.
For the exact nested source, opaque captured `f x` cannot be treated as a
direct-effect capture producer by this local collector without an additional
lowering/analysis premise. Other plan builders or specialized callee bodies
remain unverified and may supply evidence elsewhere.

The single inspected existing fixture is
`crates/evidence-vm/src/runtime.rs:31645–31705`,
`provider_env_fixture_for_handler`. It manually supplies a Lambda value at
expression 30, capture slot 7 and an environment provider mapping to its
chosen handler ID, then calls `provider_env_for_value` with empty active
handler/environment sequences. Its expected constructor consequence is
retention of that supplied mapping. It does not generate the mapping from
source or validate typed receipts. The fixture was read, not run. No second
fixture, random seed/range, enumeration or executable mutation was used.

## Independence, newness, limits, and resources

The prior source-producer archaeology characterized closure fields, lexical
cloning and an empty-provider tail route; it explicitly left non-plain
provider invocation and full transport untraced. This note adds the concrete
body-requirement producer, expression/slot provider association, missing-slot
fill rule and nonempty entry route. It repeats none of the formal endpoint,
annotation-marker, frame-subtraction, solver-transfer or freshening attacks.

Frozen implementation control flow is independent of current toy checkers,
but lowerer, plan builder, runtime and any Oracle binary share one historical
implementation. The manually supplied fixture shares the helper's assumptions
and bypasses its source producer. A checker supplied with these transitions
would validate that model, not prove the source rules. Blob equality proves
provenance, not semantics. An independent compiler referee inspected the full
note, governing authority, cited Oracle ranges, immediate dependencies, plan
assembly and fixture; no findings were reported within that scope. The source-
to-control pipeline and other excluded areas below remain uninspected.

Coverage is exactly the three paths above and one fixture helper. Searches
were limited to evidence-VM/control-IR locators and prior-note newness checks;
no whole-repository absence result is claimed. Initial combined context and
one broad provider locator capture were truncated. Several locators named
nonexistent lower/tests/evidence-plan paths; decisive paths were recovered
in narrow captures. Omitted output was not used as absence evidence.

Only lightweight read/hash processes ran; frozen-source reads were sequential.
No heavyweight process, build, test, probe, formatter, Git mutation, child or
network query. Aggregate CPU, peak RSS and total wall time were not measured.
No separate numerical CPU/RAM/wall cap was provided; the assigned path/fixture
budget was met. Only this leased note was written, and writes stop at submission.

Failure conditions: changed blobs, a different control callee constructor,
additional direct operations, local handling, supplied static slot entries,
different active-provider eligibility, malformed tables or failed evaluation
invalidate the corresponding local premise. Static providers can include
multiple candidates; this lane proves no unique semantic provider selection.
Unverified: source-to-control lowering, exact source acceptance, inferred-formal
typing, all plan builders, provider grants/hygiene/lifetime, effect continuations,
recursive/generalized preservation, current `U_c`, original `beta/Slots(beta)`,
Q-independent admission, joint `nu,K,D`, typed receipt/rebind/capture/read
production, source adequacy, soundness, principality and production conformance.

Recommended next action: compare the missing current typed attachment judgment
with this explicit value-to-provider association and entry point, requiring a
source-derived certificate as input; do not adopt family/handler capture slots
as current original profiles or run another opaque-formal toy probe.

## Frozen dependencies and commit packet

All current dependencies matched baseline: the three required rules;
`tasks/current.md`; its pre-directional ledger; the theorem dependency map;
inferred call views; nested-block and directional-protection addenda;
source-producer archaeology; reachable-input, solver-mechanism and
falsification notes; original-call-registration attempt; formal-contract
boundary crosswalk. Their earlier historical note baselines were not substituted
for the assigned baseline. No dependency was changed by this lane.

Direct historical SHA-256:

| Oracle path | SHA-256 |
| --- | --- |
| `crates/evidence-vm/src/lib.rs` | `5bd90ba043d2aa57de38b0e8536608bb2f3fc6a55c19ed1ca0aaefb85c0beaad` |
| `crates/evidence-vm/src/runtime.rs` | `eb3f2d42752ff112b621d35471ebab79e767523f4597c7d6bd57329d02231ee7` |
| `crates/evidence-vm/src/runtime/plan.rs` | `18400db78c228ff5258d79a66cc2be77627939dc4397438a4d3528071c465be5` |

- Exact leased path: `notes/progress/2026-10-06-frozen-oracle-source-producer-provider-attachment.md`.
- Baseline SHA: Yulang3 `b26087ce26bc2e77f41709a1e7b58bc4c73c2db6`;
  Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none observed; fifteen current and three historical
  files matched their pinned blobs. Integration-time drift belongs to primary.
- Review status: compiler-referee reviewed with no findings within the bounded
  historical characterization; no source-rule closure or implementation
  authority.
- Checks already run: bounded static source/fixture inspection; revision reads;
  byte equality and SHA-256; exclusive-path absence guard and output-scope check.
  No tests/builds/probes.
- Proposed research-checkpoint commit message:
  `research: trace frozen Oracle closure provider attachment`.
- Shared-record deltas intentionally left for primary/curator: record the
  distinct downstream requirement/attachment/entry mechanism and its opaque
  local-callee limitation; retain the missing current source-owned `U_c`,
  typed source producer and every admission/proof/production gate as open.

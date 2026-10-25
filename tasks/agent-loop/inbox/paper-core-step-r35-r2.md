# R35/r2 leaf handoff — first proof-check failure, writes stopped

Author/runtime: `/root/r35_r2_registered_lean_prover`; actual receipt
2026-10-25T18:42:45Z; effective model/effort UNKNOWN. Primary committed/pushed
RUNNING acknowledgement `727fcb62d`, successful preflight receipt `38710cf76`.
Baseline `6e305bc84`; fixed r2 contract SHA-256
`a8265231871ad4ffae61d45c0f1a9236abf4c7342dc99fe719183435e7caa4d1`.
R1 handoff/log remain unchanged. Claim class: incomplete candidate construction;
no delivered kernel-accepted or independently reviewed theorem.

## Source and original parent

Read original operational manuscript correction notice, execution typing rules
203–240, reductions 301–316, and precise one-step preservation/display simulation
parent 1860–1875. Its opening correction denies unqualified correspondence of
old resume behavior with the source-owner machine. Corrected-core and simulation
research notes were consulted only as candidate context, never semantic authority.

The unchanged bounded target quantifies arbitrary shared `D`, `Xi`, `Γ`, `c`,
`c'`, and `A`:
`PaperComputationTyped D Xi Γ c A → step c = some c' →
PaperComputationTyped D Xi Γ c' A`, plus successful applicability for each typed
listed redex. Neither target was constructed. No hypotheses, contexts, result
indices, accepted source features, or shared witnesses were narrowed.

Frozen input SHA-256 values, freshly rechecked after failure:

- Manuscript: `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
- `PaperExecutionSyntax.lean`: `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`.
- `PaperExecutionTypingSubstitution.lean`: `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41`.
- `PaperTermSubstitution.lean`: `a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f`.
- `lakefile.toml`: `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`.
- `lean-toolchain`: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`.
- `lake-manifest.json`: `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.

Actual source definitions inspected: `YulangClosure.PaperTypes.PaperValueTyped`,
`PaperComputationTyped`, `RecordShape`, `RecordField`, `RecordPayloadsTyped`,
`TermSubstitutionTyped`, `liftTermSubstitution`, `replaceTermComputation`,
`PaperComputationTyped.termReplace`, and `.termSubstitute`. Requiredness follows
declaration coverage; runtime presence tags do not choose lookup branches.

## Constructed surface and exact failure

New source: `notes/theory/lean/YulangClosure/PaperCoreStep.lean`, SHA-256
`4b9afa131058a5bc585624d9851f251f27aa518530f90767a66bef77e9fd4b0d`.
Namespace: `YulangClosure.PaperTypes.PaperCoreStep`.
The file contains candidate `singleReplacement`, runtime `lookupRecord`, record
label/type lemmas and partial `step`. The step includes let/Ret, Force/Delay,
both union injections, unroll/roll, field presence, and lookup presence/absence.
Single replacement maps zero to the supplied value and successor indices to
predecessor variables, using R28's binder lifting through `termSubstituteComputation`.
Lookup chooses by runtime label equality and returns right payload or left unit.
Unlisted reductions/constructor mismatches return `none`; no safety/termination
meaning is assigned to `none`.

The first module check failed at `PaperCoreStep.lean:67:6`, inside fully qualified
`YulangClosure.PaperTypes.PaperCoreStep.field_required_mem`:

```text
Tactic `subst` failed: did not find equation for eliminating 'presence'

case here
r : Ty
label : Label
presence : Presence
a : Ty
label✝ : Nat
presence✝ : Presence
field✝ tail✝ : Ty
he : presence✝ = Presence.required
⊢ label✝ ∈ requiredLabels (Ty.recordCons label✝ presence✝.encode field✝ tail✝)
```

The induction branch introduces another presence binder; the proof targets the
outer name. This is an elaboration failure, not a mathematical counterexample.
The complete command-4 output, including all warnings and this goal, is frozen
in `paper-core-step-r35-r2-worker-checks.txt`, SHA-256 `505abde97919b8288b88f7099e2a7c298d387cbf98d1e05c3fa0c2f47ae61fac`.
No source repair or retry followed the failure.

No `R35Audit.lean` was created/run. No `#check`, `#print` or `#print axioms`
output exists for these candidate declarations. Earlier declarations processed
within a failed module are not delivered as audited theorems. No `sorry`, `admit`,
project axiom, checker bypass, stronger theorem premise, or circular typing
definition was added. The skill checker was not invoked because the fixed
first-failure stop rule ended verification before the audit stage.

## Commands, resources, and parent application

Read-only `elan which lake` succeeded and resolved installed native executable
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Native commands from `notes/theory/lean`, in required order:

1. `lake --version`: exit 0; Lake `5.0.0-src+eb6cafb`, Lean `4.35.0`;
   tool wall time `0.310703195` seconds.
2. `lake env lean --version`: exit 0; Lean `4.35.0`, x86_64 Linux,
   commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release;
   tool wall time `0.000014614` seconds.
3. `lake build +YulangClosure.PaperTermSubstitution`: exit 0;
   actual job times GraphWeakening `2.3s`, TermSubstitution `5.2s`.
   Full process duration UNKNOWN because the original asynchronous tool receipt
   exposes initial/poll waits rather than full process timing. Initial replay
   warning output was tool-truncated; material success output is retained.
   Commands 1–3 are conservatively charged 30 checker seconds together.
4. `lake build +YulangClosure.PaperCoreStep`: exit 1; UTC start
   `2026-10-25T18:46:19.616763+00:00`; measured monotonic
   `4.103963267` seconds, full output retained. No timeout occurred.

Calls: 4/10 worker native invocations. Conservative checker charge:
34.103963267/120 seconds. No envelope reset; primary aggregate charge remains
binding. Startup-to-receipt time is covered by the primary's earlier aggregate
charge; receipt-to-freeze wall duration is in the log. No descendants, tests,
Rust, network, installation, dependency changes, Git or shared-state edits.

No theorem applies to the parent yet. All enumerated preservation/applicability
cases remain OPEN. The first immediate construction obstacle is the displayed
binder-elimination goal; after an independently authorized continuation, the
remaining work is checked record presence/typing, then ordinary step preservation
and applicability with exact shared contexts and result index. Luna owns any
new/revised continuation lease; this worker cannot repair under r2.

Omitted parent cases include complete heap graphs, handlers, effects, primitive
semantics, recursive allocation, wrap, omitted source/native constructors and
whole-state diagram simulation. Full-language, source/native, Simple-sub A/B,
semantic-adoption and production gates remain OPEN with their existing owners.
No independent review or production promotion is claimed.

Only changed authored paths are the module, this handoff and the r2 worker log.
Generated artifacts observed since preflight lie under leased `.lake/build`
(GraphWeakening/TermSubstitution outputs and `PaperCoreStep.setup.json`).
No existing source/root import/toolchain/manifest/rule/question or r1 evidence
was changed. Construction, checker and cache writes stopped on command-4 failure;
all evidence writes stop with this handoff. Cache ownership may return to Luna
only under the primary's lease reconciliation. No descendants exist.

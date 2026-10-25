# Sprint PAPER-PERFORM-LET-FINALIZE-20261026/r49

Status: READY; Luna authorizes this final bounded construction/verification
packet. R46, R47 and R48 remain FAILED and immutable. R45 remains
CLEAN/integrated.
Branch: `research/simple-sub-intrusion`
Baseline: `a955e74ffee83560204b74b91e2154e8076f5fa1`

## Fixed outcome

Finish the existing perform-generated request propagation proof, then obtain
the complete strict audit. R48 located the 11 `Classical.choice` dependencies
in the private Nat equality simplification path through
`find_resolved → Nat.instTransOrd → ... → Classical.not_not →
Classical.propDecidable → Classical.choice`. R48 also removed the unsupported
audit `pp.width` option. Its two attempted proof builds failed at implicit
predicate inference for `List.find?_some hf`; the strict theorem audit was not
run.

This packet fixes only the explicit Nat equality witness construction in the
proof terms. Use the pinned Lean 4.35.0 `Init/Data/List/Find.lean` declaration
to pass the list predicate, candidate and list explicitly, then convert the
Boolean Nat equality witness using `Nat.eq_of_beq_eq_true` or the exact
equivalent theorem exposed by that pinned source. For example, the following
shape is a proposal to validate, not an established proof:

```lean
List.find?_some
  (p := fun entry : OperationDeclaration => entry.identity == operation)
  (a := candidate) (l := operations) hf
```

Apply the same explicit predicate/result typing at every affected Nat
comparison in the private resolver proof. Do not alter executable definitions,
all 40 theorem headers, premises, quantifiers, assumptions, response/normal
result distinction, request semantics, binder insertion, frame order or
owner-empty boundary. Audit source remains based on R48's corrected version
and must enumerate all 37 public targets with complete types and axioms,
matching BEGIN/END markers and exact whitelist `{propext, Quot.sound}`.

If the explicit witness construction does not typecheck after one repair, or
any theorem/definition/scope change is required, stop. No weakening the
whitelist or adding assumptions.

## Frozen inputs

- R48 candidate: `b70f3d35702d8ff8b28d10d850f74bcc86127b1f79c0516f7ca64a44d769bbe0`.
- R48 corrected audit: `be0a8400df0f3696791f4ae4c176738fb9d38a2ee7e7a307b7a50f8df5b09c2e`.
- R48 handoff: `f769e9e544f5bc96139009492108ebac050423c997c60919be7a4bd5cd656c6b`.
- Manuscript `docs/yulang-operational-type-safety-ja.tex`:
  `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
- `PaperTypeFormation.lean`:
  `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`.
- `PaperExecutionSyntax.lean`:
  `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`.
- `PaperExecutionTypingSubstitution.lean`:
  `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41`.
- `PaperTermSubstitution.lean`:
  `a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f`.
- `PaperCoreStep.lean`:
  `503f81c162f7b9ceb0f7d27aa9796b8d7010345653267c675267ce14214c57e9`.
- `PaperCoreControl.lean`:
  `261d6a77438eec1a32e0299b73583899204ed7c2fe0590b819ecd3fd5b89876e`.
- `PaperTupleSplitExecution.lean`:
  `7bc13a41a0333d885b91291a7fbb1ef18302a94c79a34f21469dbae19d76f84d`.
- Baseline root `YulangClosure.lean`:
  `44bc52747836a81fb3d9ae5017d935d3fd9259e2edad8f16b91b48a1c2a5cd0d`.
- `lean-toolchain`: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`.
- `lakefile.toml`: `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`.
- `lake-manifest.json`: `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.

## Worker lane

One registered `lean_prover`, no children, no Astra. Detached baseline checkout:
`/tmp/yulang-r49-perform-let-finalize`. Luna seeds the R48 candidate and
corrected audit before lease transfer. Verify every pin and seed hash before
and after work.

Exact leases in that checkout:

- `notes/theory/lean/YulangClosure/PaperPerformLetExecution.lean` (proof terms only)
- `notes/theory/lean/.lake/R49DependencyCheck.lean` (optional, one invocation)
- `notes/theory/lean/.lake/R49Audit.lean`
- `tasks/agent-loop/inbox/paper-perform-let-r49.md`
- `tasks/agent-loop/inbox/paper-perform-let-r49-worker.log`
- enumerated `paper-perform-let-r49-call-*.stdout` and `*.stderr`
- dedicated `notes/theory/lean/.lake/build`

Capture exact command, cwd, exit, monotonic duration, full raw stdout/stderr and
hash at invocation. New worker cap: **600 active seconds, 6 literal Lean/Lake
calls, 90 checker seconds**; each call at most 60 seconds. Allocate two version
queries, one repair build (one further proof-only adjustment/build may follow),
one optional dependency confirmation, and one final strict audit. A second
failed build stops the packet. Final audit failure, timeout, pin/scope mismatch
or cap also stops it, with no further checker call.

The final audit checks all 37 public theorem declaration kinds, full types,
complete axiom lists, all 37 BEGIN/END pairs, and `Lean.collectAxioms` whitelist
exactly `{propext, Quot.sound}`. No `sorry`, `admit`, project axioms,
unsafe/native bypass, assumptions, weakened claims or expected-output changes.

## Luna primary and fresh review

After worker cessation, create `/tmp/yulang-r49-perform-let-primary` at the
exact baseline. Verify pins/artifacts, copy only the candidate and audit source,
then add exactly one root import. Four calls maximum: Lake version, Lean
version, default root build, complete strict audit. Cap: **420 active seconds,
4 calls, 90 checker seconds**, at most 60 seconds per call. Capture full raw
outputs and process metadata at launch; stop on failure or cap. No Lean in the
main worktree.

Fresh independent `compiler_referee` review follows successful primary evidence
freeze; max 180 active seconds, zero checker/build/test/Git/network/write or
descendant calls. Review proof-only diff, all theorem statements/types/axioms,
root delta, authority, dependency removal, complete logs and audit coverage.
Any blocking/major finding stops integration.

Only after CLEAN review may Luna integrate the byte-identical candidate and
exact one-import root, run `python3 tools/agent_sprint.py check`, and
commit/push explicit paths. Do not stage pending questions. On failure preserve
R49 artifacts, mark FAILED, and consult the dispatcher.

## Scope boundary

No Rust change or implementation bridge is authorized (`NO_SAFE_CODE_SLICE`).
General owner/handler alpha-renaming, nonempty-owner propagation, full-state,
current-port and residual-graph simulation, source-owner closure, omitted
constructors/frames, native semantics, inference A/B, whole executor and
production remain OPEN. R44/R46/R47/R48 remain FAILED; R45 is the accepted
bounded component only.

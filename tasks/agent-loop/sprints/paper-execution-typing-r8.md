# Sprint FULL-PAPER-TYPE-SUBSTITUTION-20261025/r8 — indexed recursor transport

Status: issued by the primary for the user's continuing proof goal.
Branch / baseline: `research/simple-sub-intrusion` at
`492f48e12cbccec3b4f5d5e10b9c6a334c6bcd51`.
Authority: `docs/yulang-operational-type-safety-ja.tex:953-977`, with record
rules `:217-231` and record code lemma `:724-749`. The original arbitrary
simultaneous substitution claim and all later inference/executor/A-B obligations
remain unchanged and OPEN.

## Prior evidence and R8 objective

R5's checked partial result covers only its recorded constructors. R6 and R7
remain `FAILED_CHECK`; R7 consumed 7/8 calls and approximately 17.8 checker
seconds. Its frozen handoff is
`tasks/agent-loop/inbox/paper-typing-subst-r7.md` (SHA-256
`f93b87262c44dd56d2ed3542000c248577ad06cd4011a67718fb884b53f20f9d`). R7
verified the generated five-motive recursor and a concrete `List.attach_map_val`
record-map equality, but did not apply the recursor to the substitution proof.

R8's fixed outcome is to apply the generated mutual recursor to the record,
required-field and declared-lookup slice, with all five motives and every
environment/syntax/result index explicit. Constructor handlers must use the IHs
provided by that recursor; replace the existing mutually recursive `.subst`
proof block rather than patching its case-based calls. First isolate the
indexed-family behavior with one identity-transport probe in
`.lake/R8IndexProbe.lean`. That probe is diagnostic only and cannot substitute
for the σ transport result. If it succeeds, implement the same explicit
eliminator architecture for the arbitrary σ transport and build/audit it. If
the eliminator itself yields a concrete index mismatch, preserve the exact
motive, handler and kernel diagnostic and stop within budget.

Keep record row labels, required labels, actual fields, raw Presence tags,
declarations, and payload types distinct. Preserve required-label inclusion,
actual-label inclusion, payload typing, optional absence, required-only
`field`, and any-declared-label `lookup` with result `1 ∨ A`. Do not add a
`Formed` premise or correlate raw Presence with row Presence. The paper/Rust
field and union-lookup bridge and raw Presence interpretation remain OPEN; no
compiler change is authorized.

## Leases and resources

Primary `/root` owns:

- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`
- `tasks/agent-loop/current.json`
- this contract and `tasks/agent-loop/inbox/paper-typing-subst-r8.md`
- `notes/theory/lean/.lake/R8IndexProbe.lean` and this project's generated
  `.lake` cache, exclusively for the single verification owner

Read-only: `PaperExecutionSyntax.lean` (SHA-256
`8ad8bc4b1549eadaa73c743438b333c62b44be7bdff0346f690b7da9e6353a97`), the
R7 handoff, governing paper, and existing formation/type-substitution
references. Typing baseline SHA-256:
`647146f77ba98b997c16cc08cc735ec2e1eaaf72e0b56e262b54e25604c3529d`.
No new worker, reviewer, Astra, native/Rust build, tests, or compiler source
changes are assigned. All eight historical/foreign UNKNOWN reservations remain
quarantined.

Budget: at most 900 active seconds, 8 serial Lean/Lake invocations, and 120
cumulative checker seconds; one Lean/Lake process at a time with `-j1 -M1024`.
All R1-R7 charges remain recorded. Stop at a concrete eliminator obstruction,
a counterexample, authority/dependency/lease change, user STOP, or any budget
limit. Never use `sorry`, `admit`, generated failed declarations, project
axioms, or stronger hypotheses as a result.

## Verification and boundary

Success requires the focused typing module build to exit 0, exact types and full
axiom audits for all five transport theorems and support lemmas, no `sorryAx`,
failed declaration dependency (including `_f`), or project axiom, and an explicit
source-to-paper map of represented and omitted rules. An identity probe alone,
a green syntax build, or support lemma is not success. Fresh independent review
remains `NOT_RUN` until a safe reviewer slot exists; the parent theorem and all
downstream gates remain OPEN even if this slice succeeds.

At the boundary, freeze the exact diagnostics/artifacts in the R8 handoff,
update compact state, consult the selector, and only then decide a further
bounded packet. The primary remains the sole Git integrator.

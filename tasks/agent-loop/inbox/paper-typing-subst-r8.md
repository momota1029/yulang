# FULL-PAPER-TYPE-SUBSTITUTION-20261025/r8 — active checkpoint

Status: `ACTIVE_PRIMARY_CONSTRUCTION`, no theorem transport accepted yet.
Baseline: `492f48e12cbccec3b4f5d5e10b9c6a334c6bcd51` on
`research/simple-sub-intrusion`. Contract SHA-256
`65834569d8bdf44215a2de7201e70de3e9542063d0b7c3c18d45245144627b14`.
R7 remains frozen `FAILED_CHECK`; its receipt is preserved at
`tasks/agent-loop/inbox/paper-typing-subst-r7.md`.

## R8 work and current evidence

R8 keeps `PaperExecutionSyntax.lean` read-only. It uses the exact five-motive
recursor `RecordPayloadsTyped.rec` and writes scratch only to
`notes/theory/lean/.lake/R8IndexProbe.lean` plus the leased typing proof file.

A first probe attempt used `aesop`, which is unavailable in this project import
context; it produced no index evidence. A second `induction ... using` attempt
left the sibling motives unresolved, showing that the recursor's motives must be
supplied explicitly. Both attempts were discarded as failed scratch proofs and
are not results.

The third invocation printed the full `RecordPayloadsTyped.rec` type. Its five
motives quantify the environment and relevant syntax/result indices; the cons
handler receives separate payload and value induction hypotheses. The fourth
invocation successfully checked `payload_identity_transport` by applying that
recursor with all five motives explicitly set to their identity relations and
supplying all constructor handlers. `#print axioms payload_identity_transport`
reported no axioms. This establishes an indexed identity eliminator probe only;
it is not a σ-substitution result and does not prove the prior kernel mismatch
has been repaired for the mapped target.

The current scratch file is a successful axiom-free identity probe. No
`PaperExecutionTypingSubstitution.lean` theorem was changed during R8, and no
focused typing-substitution build or substitution axiom audit has yet run.
The paper's original substitution theorem, source/native record bridge, and all
downstream safety/inference/executor/A-B gates remain OPEN.

## Accounting and continuation

R8 consumed 4/8 serial Lean/Lake invocations and less than one checker second.
The two early failed scratch attempts are preserved in this accounting but are
not accepted results. Static tooling checks from R7 remain separate; no R8
static check or independent review is claimed. No tests, Rust/native builds, or
compiler implementation changes were made. All eight historical/foreign
UNKNOWN reservations remain quarantined; no reviewer slot is established.

Next: replace the old mutually recursive `.subst` proof block with the same
explicit five-motive eliminator architecture, using arbitrary σ target motives
and recursor-provided IHs. Use the checked record-map equality as an explicit
support lemma. Build and audit all five target transports; stop on a concrete
eliminator/index obstruction or the R8 budget boundary.

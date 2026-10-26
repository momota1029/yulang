# Independent review of the nine-module Lean lint cleanup

Date: 2026-10-27. Reviewer/adjudicator: `/root`.
Producer: `/root/soundness_hygiene`.
Verdict: **PASS for statement-preserving lint cleanup**.

The exact nine files and final SHA-256 values in
[the producer receipt](2026-10-27-lean-lint-cleanup.md) were independently
read and checked against the working tree. That receipt's frozen SHA-256 is
`a4a163aad11070ff96cd1e2b58fb570b30b9ed187d5779f83f946452ee7d66f9`.
No production compiler behavior, source restriction, theorem premise,
conclusion, dependency or linter/checker setting changes.

## Diff and declaration review

I reviewed the exact diff from `6a4933e06ecceee2cc2a00a635925f55cfc14adc`.
The simplifier changes remove precisely unused arguments from their own
invocations; other uses and the remaining argument order are preserved.
The deprecated conditional lemma names are replaced by their pinned
canonical names. Public theorem statements and all recursive computational
branches are unchanged.

The complete `PaperExecutionSyntax` diff was also checked mechanically:
undoing only the consistent local `_hmem`, `_hsmall` and `_hdefault` renames
reproduces the old source bytes exactly. The analogous local `_hv` renames
in `PaperTermSubstitution` preserve the termination evidence and its uses;
public theorem parameters named `hv` remain intact.

I inspected the unchanged origin-based before/after census harness and the
type comparison code. The census includes every originating declaration,
not only namespace-prefixed public theorems. Alpha normalization removes
only binder display names and formatting; de Bruijn indices, universes,
binder kinds, constants and expression structure remain compared.

The 2,699 before / 2,683 after declarations have 2,652 common names:
2,410 exact type representations, 117 alpha-only differences and 125
regenerated proof-helper type differences. The 47 removed and 31 added
names are also generated helpers. I independently verified that every
non-alpha changed, added or removed name has a `_proof_*` or `_simp_*`
generated suffix. No authored or non-helper interface type changes or
disappears. This does not claim identity of the compiler's auxiliary names.

Every common name retains its axiom set, and the entire post-change census
checks all new helpers. The allowed union remains exactly `propext`,
`Classical.choice`, and `Quot.sound`; the source diff adds no proof hole,
project axiom or native/kernel trust bypass.

## Independent integration

The primary's fresh focused build passed 40 jobs. After the final frozen
hash comparison, I ran the complete default project build with the pinned
Lean 4.35.0 / Lake 5.0.0-src+eb6cafb configuration. It exited 0 and completed
**131 jobs, with zero warnings and zero errors**. Informational existing
theorem-type/axiom output is retained. The actual log is
`/tmp/yulang-lint-full-integration.log`; its completion was observed and the
process exit collected explicitly.

This resolves the 668 existing warnings exposed by the earlier integration.
The nine direct source checks and full declaration comparison remain in the
producer receipt. All review inputs matched their frozen hashes at adjudication.
No further check is required for this unchanged cleanup packet.

This acceptance creates no new original whole-language semantic theorem.
The separately reviewed new execution suppliers and all four original
metatheory goals retain their own proof/source-correspondence gates.

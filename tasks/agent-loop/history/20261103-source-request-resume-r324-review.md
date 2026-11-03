# R324 — structured Request/resume evidence

Baseline `773e96901`. The native witness now exports the supported actual
R323 request, response, operation identity/signature, saved frame operands,
view/receipt and owner replay as typed data rather than Debug strings or
pointer identities. It checks the same Machine internally and rejects
unsupported frame kinds. A test-only accessor was added for receipt ordinals;
production behavior and public API are unchanged.

Independent source review passed the frozen witness and reran its focused
Cargo test (1 passed; 94 filtered) and generated Lean 4.35 data elaboration
(`-M2048`). The receipt-only mutation case was not independently tested;
other source/template/response/frame mutation controls are in the handoff.
This remains finite native evidence, not a semantic world or source proof.

The proof attempt did not construct the original Request/resume registry law
or reduce an R293/R159 premise. It first tried the inner Call by mistake, then
corrected the attempt to the actual outer Call and retained the original leaf,
resolution and precondition as unsolved. It used an earlier generated run;
the final witness below is a separate run and was not consumed by that proof.
R315/R323/R324 run-local IDs must not be treated as identical. Original source
guards/fields, dependent response domain, lawful action, full arm inventory and
independent Checking remain open.

Frozen inputs: `machine.rs` SHA-256
`7dec51aa5d57b3ef7b5217a4c772355aa75ddf3a88adffae017cdd637ee485ef`;
`receiving.rs` SHA-256
`476ef914bb11449f106c900a233e9677025830e6923cd5db6a1dc6edbcc6d613`;
generated scratch artifact SHA-256
`85e663b65a893b0acd5de46b7b1b59e940098bf5e5a7815cada4736a3e983551`.
The two R324 inbox handoffs preserve exact commands, provenance and limits.

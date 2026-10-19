# R121 implementation handoff

Status: Luna applied the batched review repair; repaired output is frozen,
fresh delta review pending. No checks, builds, CLI runs, runtime probes, or Git
actions were performed.

## Output

Added `tools/inference-playground/tests/cli_outward_root_suffix.rs` with one
serial test covering both exact contract sources. Each direct-Machine setup
compares the two scheduled expression roots, in order, with the expression
roots minted by the owning HIR items. The positive source completes at integer
7. The negative source preserves the declared `tick` operation identity and
integer payload 7; its request `SourceSite` root and occurrence are resolved
back through the owning HIR `LocalSource` Apply expression. Its retained range
equals the request site's range, and its callee resolves by declaration
identity to `tick`; no assumption is made that this application-tail range
covers the `io` head. Its saved continuation is nonempty.

The public stdin CLI cells use `--run main --steps 30000 -`. Positive requires
success, exactly `7\n`, and empty stderr. Negative requires failure, empty
stdout, and exactly the existing `unhandled runtime request at <range>` error,
where `<range>` is the retained range of the authentic LocalSource Apply
occurrence that supplies the request SourceSite. The test authenticates that
occurrence's operation callee by declaration identity; it makes no assumption
that the range covers the entire `io::tick 7` spelling. The existing error path
does not publish a completed result.

## Frozen inputs and limits

The R121 rev1 contract and all 24 listed input files were revalidated against
their pinned SHA-256 values before writing. Exact sources remain the contract's
158-byte positive and 159-byte negative inputs, both without a final LF; their
contract hashes are `11f811ba795dfc8420aadd0706221fe14f1efa9a192b902bda5b7816d627924f`
and `685aa2465d5a5b47d18447762637107b4cb0da5971d384fad7bc1ad56937448f`.

No runtime/source semantics, other tests, or expected outputs changed. No
scratch paths or child workers were created. The single permitted cargo test
remains for Luna after the required independent CLEAN reviews; this output has
not been run or independently certified.

Requested model/effort: Luna/high. Observed model/effort: UNKNOWN. Worker:
`/root/r118_implementation_lane`. The only new paths are the leased test and
this handoff. STOP.

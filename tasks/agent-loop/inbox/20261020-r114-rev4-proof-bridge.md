# R114 rev4 proof bridge: WAITING

Handoff ID: `R114-REV4-PROOF-BRIDGE-20261020`; revision **1**; **FROZEN**.
Author: `/root/r114_source_identity_proof`, sole author, no descendants.
Requested Sol/high; observed model/effort UNKNOWN/UNKNOWN (no visible routing
metadata). State: **WAITING for Luna's final review and verification gates**.
Writer state: **STOPPED**, not a resident worker awaiting another turn.

## Parent and precise result

Contract: `tasks/agent-loop/sprints/cli-wrong-family-permission-20261020-r114-rev4.md`,
verified SHA-256
`b42ac475a6e5049edd89f7ba3eda91933af61ae43324821c3cc65e8c19b30c6e`.
The unchanged parent/source is R114 rev1's exact 195-byte source, SHA-256
`91c015cf7dce0132b0d7faa5cd7d30f87eb1fe3c3cadc5bd18db1595061a771f`.

**No additional source lemma is needed for the authorized harness split.**
The exact existing proof is
`notes/theory/2026-10-20-r114-source-identity-current.md`, revision 1,
SHA-256 `2835bca1ea5612fb4a6806540a94f6a225feef1ddc38a58db896838974a36ecf`,
authored by this worker. Its sections “Constructor lemma and application to
P-ID” and “Concrete conditional Machine trace” establish the narrow identity,
permission and public error-transport argument. This receipt is a producer's
application of that reviewed work, not independent certification of it.

The rev3 compiler/source, spec and regression review transcripts are CLEAN for
that finite conditional scope. They do not establish execution. Rev3's command
failed at compilation because the integration test called crate-private
`RuntimeProgram::start_source_schedule`; no test-body runtime or CLI observation
followed. That failure remains permanent history. Rev4 grants new harness
placement and commands; it does not relabel rev3 as a successful run or retry.

## Why the witnesses compose

Let S be the exact source, and let e be the structured direct Machine error
`HandlerEvidence(original_site)`. For the common inputs `(S, "-", "main",
10_000, false)`, the two tests and the already-inspected public source compose
as follows, conditional on their future successful execution:

1. The crate unit test forms the original HIR using
   `FileKey("inference-playground", "-")`, checks syntax and ordinary candidate
   conflicts, and observes the source-scheduled direct Machine. It requires
   the actual structured HandlerEvidence variant. It then asserts that public
   `execute` returns exactly `format!("runtime unavailable: {e:?}")`.
   The expected site is derived from this original Machine error; no numeric
   source range is supplied by the test or this receipt.
2. `lib.rs::execute` (167 onward) still calls ordinary preparation, constructs
   the runtime from that HIR, and returns its formatted unavailable error
   before completed-result rendering. Relocating the direct witness into the
   crate makes the private entry callable by the harness; it adds no source
   constructor, permission rule or runtime transition.
3. The unchanged pinned `main.rs::run` (63 onward) reads stdin for path `-`,
   passes name `-`, definition `main`, steps 10,000 and scoped=false to that
   public execute path, and applies `?` before `print!`. Its `main` propagates
   that error to `eprintln!("{error}")` and returns failure. This existing
   source-to-consumer bridge supplies exact error transport plus newline and
   empty stdout when execute returns Err.
4. The integration test supplies the same S to the actual public stdin child
   with `--run main --steps 10000 -`. It observes failure, empty stdout,
   diagnostic category `runtime unavailable: HandlerEvidence(` and a final
   newline. Together with the unit's exact execute comparison and step 3's
   pinned transport, this supports the original finite diagnostic claim.

The integration assertions alone do not compare all diagnostic bytes and do
not prove the original site. The exact-site component is the direct-Machine
to public-execute equality in the unit witness, composed with the inspected
unchanged CLI transport. This is not an inference that substring containment
and a newline imply arbitrary whole-string equality. Fresh final review must
confirm the executable harness and unchanged public implementation correspond
to this composition before commands run.

The split neither creates a new semantic premise nor discharges the original
successful-preparation, bounded execution and actual public-observation gates
before execution. Source identity, `[other]` retention, S != O, Lambda bypass
exclusion and local_grant rejection reuse exactly the reviewed rev3 premises.
No broader source domain, foreign-continuation case, F1/FK1 or independent
receiver quantifier is inferred from this one route. Missing positive evidence
proves neither language rejection nor outward forwarding.

## Read and hash evidence

Rev4 contract, rev3 proof and handoff hashes matched. All immutable entries of
the complete rev3 current inventory matched their prescribed hashes. The
authorized implementation outputs were moving during reads: lib.rs already
contained the new test at the inventory check, and the integration test changed
from its original hash to the authorized split before the subsequent read.
These are declared rev4 harness outputs, not silently accepted changed theorem
dependencies. Their observed candidate hashes below require Luna's freeze and
fresh final review; no baseline identity is asserted for those new bytes.

| Observed input/output | SHA-256 |
|---|---|
| Rev3 proof handoff, this worker | `0741e0907740d9fc3e570c60bd52105762af0a7290d484f9d138e842761ac6bd` |
| Rev3 compiler/source review, `/root/r114_rev3_compiler_review`, transcribed by Luna | `750ce3cc530cf4b39b985959578bf166decdc922fb34df793c7fb98b47990067` |
| Rev3 spec review, `/root/r114_rev3_spec_review`, transcribed by Luna | `4c5eb77c719770cf948a37216139751b0b47a489cb0e93833e66f29f495011bd` |
| Rev3 regression review, `/root/r114_rev3_regression_review`, transcribed by Luna | `1d80b441315febd5bb1833cd739985568805c26129213d04c287c364bcac4e34` |
| Rev4 prospective review, `/root/r128_recovery_spec`, transcribed by Luna | `6305a1f2f9bc51dcba2151f5e005ce5e39083db6b1338466ac57a365ab165e19` |
| `src/lib.rs`, Luna's observed test output | `a0769f77feac552304f0516b0742637f51660c0bb8bf9391d18ae0f9de5e2473` |
| `tests/cli_permission_boundary.rs`, Luna's observed split output | `2f6cda6d85054a313d3f810dcbe5595494e57135b71b82e47d9235199d7fa48a` |
| Unchanged CLI owner `src/main.rs` | `75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100` |
| Unchanged package owner `Cargo.toml` | `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56` |

Paths beginning src/tests/Cargo above are relative to
`tools/inference-playground/`; review paths are under `tasks/agent-loop/inbox/`
with their corresponding `20261020-r114-...` filenames. No new direct owner
was needed. Existing historical proof failures were not reused as positive
execution evidence.

## Resources, mutual TODOs and stop

Lease cap 120 seconds, zero Astra/children/heavy work. First observed clock
`2026-10-19 15:30:05 UTC`; read/hash checkpoint `15:30:40 UTC` (35 measured
seconds plus final reads/writing). A following parent message explicitly
authorized exec_command only for cat/sed/rg/sha256sum reads and verification;
no executable compiler, test, build, CLI, formatter or Git command ran.
Handoff written with apply_patch only. Luna may conservatively retain the full
120-second reservation; no old budget is reset. No authorized work remains
after this STOP.

Next action and mutual TODO: Luna freezes the test outputs, obtains the three
fresh final reviews, and alone executes the two prescribed sequential commands
if their gates are CLEAN. Any preparation, runtime, diagnostic or command
failure retains its original falsifier and stops without retry or semantic
repair. No production implementation TODO arises. All original Simple-sub/
evaluator A/B, adoption, source-law, general hygiene and production gates stay
OPEN. WAITING names an evidence gate, not a running worker.

Only new path is this exact handoff. No scratch, code, test or prior-proof
artifact was written. Writer **STOPPED** at freeze, no pending mutation,
descendants or background process.

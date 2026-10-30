# R30 append-only stage ledger — revision 1

Sprint: EFFECT-PERMISSION-NATIVE-CALLBACK-GRANT/20261030-R30. This file records immutable gate facts; later revisions append a new section and include the previous SHA-256. It does not replace the fixed contract or authorize any gate by itself.

## Admission and intake pending

Admission receipt: tasks/agent-loop/history/effect-permission-native-callback-grant-20261030-r30-admission.md, SHA-256 e5d33278748553ea196eaf4ec1d5212b14c470f148b87f870bc26d005c395d34. Contract SHA-256 bb0b5de338c11e82d10dc9580a097d06d969f075493f0b510979271f7479f9b3. Inputs manifest SHA-256 ea0afb71f4973138ecb014f2e1843c3fe877ded976fdb0228205d3cef8b8283a. Current checkpoint before project-copy verification: cf382d2a8a401de74a6d2ed355240bee7827b440. No compiler, test, runtime, Lean, or Lake command is authorized by this entry.

## Gate 0

State: PENDING. The primary has not yet created or authenticated the isolated project copy.

## Gate 0 verified and intake incident — revision 2

Previous ledger SHA-256: `7ea91fcaf5753a19be7ce059fd876c416541fb895452fcfc298b459c11bebf0e`. The primary recorded the missing-workspace incident at `tasks/agent-loop/history/effect-permission-native-callback-grant-20261030-r30-intake-incident-r1.md`, SHA-256 `bc92edc6787b4f37a0da26506e753613e50cc3f16dd24f742c1ce10c776ae76f`.

Gate 0 state: VERIFIED. The copy receipt is `isolated/ep-native-callback-grant-r30/project-copy-r1.json`, SHA-256 `9e178b17997a37b4755d0bcd207f99886f3e2348746821b2807278c592e46c8c`. It records baseline commit `dd3d5ee22b8622f22e8db87382edaec0a466e7fd`, tree `554c82b13d9186e197a460128330c4bb0dcd53ab`, 10,411 regular files, zero mismatches or missing files, and content digest `1aa7ba512c55fd91d10eec15036f7b4b1d73110e2c8d9a5492165f0163a61ef0`. The four overlays match the R30 manifest exactly.

The exact recovered overlays and provenance are frozen in `tasks/agent-loop/history/effect-permission-native-callback-grant-20261030-r30-recovered-overlays-r1.tar.gz`, SHA-256 `5c3c991dec9e54ad3e2665a1c722a0abf2d80a9efe719664606824558351a790`. The R29 bridge is an exact recovered candidate and remains unchecked; no proof or audit closure follows from recovery. Existing R29 Rust review/compile evidence applies only to the unchanged R29 Rust bytes, not to future R30 edits.

No R30 worker, compiler, Cargo, runtime, test, Lean, or Lake process was started. The three R30 worker assignments remain WAITING. No budget, source authority, or historical lease changed or transferred. Gate 1 is the next authorized stage after this receipt and current-state checkpoint are pushed. The primary will continue in this one R30 project copy and create no additional full project copy for this sprint.

## User-directed storage reclamation — revision 3

Previous ledger SHA-256: `49c6baa4a0bade27ca65c0a92a4245e1987b2505d2734f92809d46afcbc2993d`. In response to the user's explicit storage instruction, the primary deleted only `isolated/ep-native-callback-grant-r30/project` (about 265 MiB). The small copy receipt and recovered-overlay archive remain as historical evidence. No other isolated path, quarantined lease, or workspace deletion was touched.

Gate 0 was verified before removal; that historical receipt remains accurate for the verification event. The project is now absent, so Gate 1 cannot use that copy and no current R30 source edit may start from it. No R30 worker was launched. Rust, proof, and review assignments are BLOCKED pending a storage-constrained replan. This action does not recreate a project, change the contract, transfer a lease, reset a resource allowance, or claim compiler/test/proof progress.

## R30 closeout — revision 4, CLOSED_INCOMPLETE

Previous ledger SHA-256: `9a66c567452eeb9c9c365fbed44694371be91889b3de3baabab39dde773b6ea1`. Outcome receipt: `tasks/agent-loop/history/effect-permission-native-callback-grant-20261030-r30-outcome.md`, SHA-256 `147a447798d10092cdc8ed713d77f58a29f851ce6c8d776eb01acc1e5e1d4236`.

R30 is CLOSED_INCOMPLETE. The roster contained no live R30 writer, all three planned child identities were completed, and no R30 worker launched. The absent project means Gate 1 is not authorized. Primary recovery/intake timing was not authenticated; the accounting disposition charges the maximum 1,500-second non-closeout share to that unmeasured work and the full reserved 500-second closeout share, consuming the 2,000-second primary cap. No R30 lane allocation transfers or resets. The R30-only project, scratch and handoff leases are retired; historical receipt and overlay archive leases remain FROZEN. Parent effect hygiene, soundness, principality, termination, Rust implementation and Lean application remain OPEN.

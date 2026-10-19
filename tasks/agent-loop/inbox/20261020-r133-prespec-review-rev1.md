# R133 rev1 prospective spec review

Result: **BLOCKING — contract ambiguity**

Reviewer `/root/r133_prespec`; rev1 contract SHA-256
`c911fa7a92f28e62e7fa0fbf9e65bd4b8b378752b0970110c90d163b557c2570`.

The three-result identity-only scope is justified by the original sample and
oracle. All 15 dependency pins match; the 210-byte source projection hashes to
`b4d68db12c1845f23b5c8a3231249952470868d22d9489a8590270a57de77a3f` and
matches the external sample. The oracle source hash matches the R132 pin.

Blocking ambiguity: the contract says to preserve prior smoke oracles and not
delete the countdown expectation, but the currently leased smoke executes all
four definitions against the combined source that the failed check rejected.
It did not specify how the executable countdown case would be handled while
introducing the three-value matrix. Keeping it prevents success; silently
removing it weakens protected coverage.

Closure required an explicit prospective statement that R133 supersedes only
the R132-added live combined-source smoke case, preserves its four-value
source/oracle and failure in frozen R132 records, and replaces it with a
separate exact identity-only fixture and reviewed matrix. The countdown's
expected value remains `8`; R132 remains failed and no semantics change.

Read-only review; no files, tests, builds, compiler, CLI, or Git. Elapsed about
90 seconds; requested spec-auditor role, runtime/model telemetry unavailable.
Reviewer STOPPED.

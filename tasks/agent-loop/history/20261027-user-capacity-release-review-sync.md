# User capacity release: review-lane synchronization

The user reaffirmed that the nine UNKNOWN capacity reservations may be released,
required the policy and live agents to be synchronized, and asked whether
`current.json` could be ignored as a bug. The receipt-backed policy and checker
already implement that release: capacity accounting excludes only the exact
released UNKNOWN identities while preserving their worker rows and quarantined
path leases. The release is idempotent; it does not add a tenth slot or imply
worker cessation or path release.

At this reaffirmation, the only live child was
`/root/source_owner_reification_review`. It was notified that the capacity
release changes no review assignment or read-only scope. The reviewer returned
its final report and stopped; the nine released reservations and all path
quarantines remain unchanged. Earlier live proof and implementation agents
had acknowledged the same release, as recorded in
`20261027-user-capacity-release-live-sync.md`.

No new work assignment or compiler authority was granted by the release.

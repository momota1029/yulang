# Amendment 01 — correct the frozen coverage-module dependency pin

Sprint: `PROVIDER-SOURCE-OWNER-BRIDGE-20261027/r1`
Base contract: `tasks/agent-loop/sprints/provider-source-owner-bridge-20261027-r1.md`, SHA-256 `1cf1706358a56e7e7b4836a270704c127097feff2dee4542767ca04fbd2ce359`.
Approved by: Luna, primary, at admission amendment.

## Exact correction

The base contract's coverage-module SHA-256 contains a transcription error. Its pin `62257d276004f6caf07872142e4a4369266d5205d992f2f3d56f36657ae69783` does not match the frozen module or proof handoff. The actual file and the frozen handoff both hash to `62257d276004f6caf07872142e4a4369266d5205d992f4f3d56f36657ae69783`.

For all remaining sprint work, replace only that dependency pin with the actual value above. All other contract fields, exact leases, authority, original claim, budget, stop conditions, and parent gates remain unchanged. No artifact bytes or source/semantic assumptions change. Both active lane owners are notified; proof work resumes against the verified actual frozen bytes.

The base contract remains immutable evidence of the admitted initial packet. This sequential amendment is the current dependency authority; it authorizes no widening of source scope or writer lease.

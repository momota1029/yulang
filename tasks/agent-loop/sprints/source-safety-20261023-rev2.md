# SOURCE-SAFETY-20261023, contract revision 2

Supersedes revision 1 only for the direct-dependency addition below. All original
scope, outputs, author, resource cap and open-parent boundaries remain unchanged.
Revision 1: `tasks/agent-loop/sprints/source-safety-20261023.md`, retained frozen.

At 2026-10-23 14:59:45 UTC the source-owner audit located existing reviewed
constructor work that supplies a stronger route to the original compose gap:

- `notes/design/2026-10-15-callback-identity-forwarding.md`, SHA-256
  `c544ed3c7b83686a740aa43b1db92d901de31a3b197f81f90a4c9dbdae561134`.
- `notes/theory/2026-10-15-callback-named-frame-source-bridge.md`, SHA-256
  `ed5d8407fb20324578dc649aeec4547977d9c83299bdf0992a15e92f13da82c3`.
- `notes/theory/2026-10-15-callback-identity-receiver-construction.md`, SHA-256
  `8462a7c048ff622b46d9a6486b7d0afe1abdea7589169ecfb09b9a886b73353b`.

For direct calls in a named group, the chosen source frame is the terminal
parameter frame (x in compose), not the inner f invocation. Use the exact
constructor guards and producer/consumer code at the pinned Oracle revision to
construct the bounded runtime recipe. Apply the lifetime/inventory lemmas there.
Retain the existing non-Var callee counterexample and the general source gap;
no blanket Oracle shape restriction is adopted. The forwarding authority also
explicitly leaves concrete suspension/reentry representation open: the manuscript
must describe its owner repair as a candidate realizing the prior source-owner
machine, not pretend this representation itself has user approval.

The multiple-input release interpretation is separately pending user response.
Do not invent an answer. No extra workers, runtime budget or implementation rights.
Additional writable path: this revision-2 contract only.

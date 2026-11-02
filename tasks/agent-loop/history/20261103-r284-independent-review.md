# R284 independent review — clean abstract counterexample

Reviewer: `/root/sol_r284_capture_validity_review`, registered `lean_prover`,
requested Sol/high. The independent review found **CLEAN for the stated
abstract R284 falsifier**. Charge the full 900s grant; exact CPU/RSS and active
runtime are UNKNOWN. Reviewer STOP / WRITES_STOPPED, no descendants or active
processes. No reviewer artifact writes occurred.

## Authentication, order and independent checks

- Contract-only gate matched R284 review contract SHA-256
  `e99d2cade6ee8214879a678c5b762ccfe910fe397fc33e99281244f20e4f3dfc`.
- First technical operation hashed the explicit input manifest
  `tasks/agent-loop/sprints/extrusion-capture-validity-r284-review-inputs.json`,
  SHA-256 `8407c07a92ec751aee9214c7b0c6b868eca7e50a0767fa9b451d2c620cd132d4`,
  and all 26 exact inputs. Every pin matched.
- Reviewer reconstructed `incomingJobs`, `copiedRow`, `step` and relevant
  result projections before candidate/handoff inspection.
- Candidate module SHA-256
  `6842d0af28691e18ea6c50f250ff08f14205c5cb45ced3d0c58e07178e30f49c`;
  handoff SHA-256
  `8f4d100930853d61b6d7f883f14955b67c3b79ffb170c76e87aec88d5e4b3407`;
  Work model SHA-256
  `c419675d75a2cdf03fe5b1ba8d2eef106fea0c4f5187f9f5c06999fa734edd58`;
  R283 module SHA-256
  `31c83006c8d9b411b00d045fd16c9e5875e8a73d5baead989c7a55315f3a3f10`.
- With the transferred exclusive `.lake/build` lease, the reviewer ran a
  focused Lake build of 14 jobs, direct Lean check, manual `#check @` and
  `#print axioms` for all 18 declarations, and the bundled checker. Every
  command exited 0; bundled checker reported 18 PASS entries and complete
  begin/end/type/axiom records. Lean was 4.35.0, commit
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake was
  `5.0.0-src+eb6cafb`. Temporary checker output stayed within the cache and
  was removed.
- The full per-theorem types and axiom table remain in the frozen producer
  handoff. Independent audit matched it: only `propext` and `Quot.sound` (or
  neither) occur; two frame theorems have no axioms. No `Classical.choice`,
  project axiom or `sorryAx` appeared.

## Independent mathematical finding

The candidate checks each capture's raw Effect source and its kind-separated
`qe` representative; `CapturesValid` quantifies over all capture indices.
That matches the references actually read by `incomingJobs`. The R283
`captureGap` exclusion and `Computed.rowInput` initialization follow for the
printed universal callers.

`viewTailGap` has one Effect row, empty captures, a published allowance view
7 with tail row 99, and a Visit of that allowance. It satisfies R283
`RowsValid` and R284 `CaptureComplete` because neither predicate validates
published view tails. The actual `visitStructure` path queues a canonical
Effect Visit for row 99. `step funded` returns `.next`; the Effect vector
length remains 1. The exact universal negation
`¬ StepPreservesCaptureComplete` applies to this state and funding. This is a
valid counterexample to this R284 candidate invariant.

The first necessary repair premise is validity of every published Effect
view tail and its `qe` canonical representative against the Effect store.
That premise is not yet sufficient: preservation must still cover every Work
constructor, all result projections, external and failure paths, partial
publication and finite prefixes. The candidate result is not a source/Rust
counterexample, an impossibility result for stronger invariants, or an R70
parent proof.

## Adjudication and parent edge

Luna accepts R284 as a **reviewed counterexample to its specified candidate
invariant**, not as preservation or R70 closure. Producer and independent
review both completed inside the existing 3,600s envelope; all previous R282
and R283 charges remain consumed. Parent/A/B stays 0->0; original R70,
source/native correspondence, Parent and production readiness remain OPEN;
`NO_SAFE_CODE_SLICE` remains. The next proof must include view-tail validity
and prove preservation over all actual transitions. Luna retains selector,
admission and Git ownership.

No Rust/source/Cargo/test/probe or semantic work occurred. No production code
or new theorem has been promoted to the unchanged parent.

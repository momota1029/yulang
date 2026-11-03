# R344 — scoped arm and endpoint separation

Baseline `9c084ac4f`. `OriginalAuthenticatedArmTransportR344.lean`, SHA-256
`b04974bfe936307c8e46d7d2d12487030d06c4ef0577c89e4987ba1e00393b77`,
constructs an abstract model with an exact R310 arm slot, nonidentity lawful
scope/observation action, retained `Nat → Bool` witness and a nonempty
licensed R343/R318 primitive child. In that model the scoped packet cannot be
projected to the R306 endpoint packet. The same model applies unchanged R159
inversion and rules out its required computation check, retaining both
annotation alternatives and the same extracted candidate extension.

Independent review confirmed this is stronger than R334's endpoint/key
projection example: even exact-key lookup, a primitive license and a lawful
nonidentity action do not force endpoint agreement in an arbitrary abstract
interface. The registry and `Decoded.interfaces` are constructed for this
model, not authenticated source owners; the reading ignores the environment.
It is not a counterexample to actual source IF/EI, nor proof that every scoped
consumer or authentic factorization is impossible. It does not construct the
original ArmDecl inventory, source-use relation, R306 contribution or a
positive R159 premise. The independent Bind/Delay investigation likewise
found no current source-to-Inputs operator-law producer and made no new proof
claim. Actual original source interpretation remains open.

Independent Lean 4.35 `-j1 -M2048` checking authenticated the 34-module
source cone and reused artifacts, compiled the target and audited all 56
originating constants including 31 theorems. Only standard Lean axioms
occurred. Full audit SHA-256:
`d85612b08113c919399e1426c8e851c821bf4714357760949bec3b3913e29b62`.

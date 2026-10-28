# Independent review: EFFECT-PERMISSION-SOURCE-ORIGIN-20261028/r1

Reviewer: `/root/source_origin_final_review` (`compiler_referee`), fresh and
independent of both lane authors.

Bounded verdict: the Rust correction is suitable as provisional finite
observation; Lean remains constructed but unchecked. No compiler semantic
regression was found.

## Findings

- **Blocking for proof closure:** the final Lean check fails at
  `FormalPermissionSourceOrigin.lean:163` on an unresolved impossible branch.
  The final theorem and transitive axiom audits never ran. Probe 4 concerns an
  earlier draft and does not certify final bytes. Repair under a newly admitted
  check budget, then audit all 12 declarations on the final hash.
- **Major, parent/source-native bridge remains open:** the model admits abstract
  construction histories without deriving them from successful Rust calls;
  parameter identity is definitional and discovery requests are arbitrary
  inputs. Actual constructor coverage, allocated-row witnesses, memo/allocation
  invariants, row/bound/evidence/context recurrence, canonical transport,
  node writes, endpoint arrival, and export membership are unproved.
- **Minor, trace ownership:** ordinary trace assertions search a module-wide
  event stream, so events may belong to different captures. The selected
  owner's `formal_effect_permissions()` walk independently requires its exact
  domain root and structural path, strengthening the finite observation.
- **Minor, runtime receipt:** exit, tests, elapsed time, and RSS are reported in
  the frozen Rust handoff and worker completion receipt; no raw Cargo transcript
  was retained, so the reviewer could not independently authenticate those
  figures. They fall within the stated runtime envelope.
- **Minor, contract pin typo:** the contract's manifest hash differs by one
  character from the manifest and proof handoff. Correct SHA-256:
  `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.
  No dependency mutation was found.

Verified artifact hashes:

- Contract: `4158140fa23108a9be8377527854df831044de1dc4d8a06ed063cfbf44ef7130`
- Rust handoff revision 2: `da1d12525f568a63dbc22f634a824493d571eecc71803a65f14a004423cbdd5a`
- Proof handoff: `7d4ef479f68a8865a1c3563867494dce53a4ddfe6d7f321f36850937b343e321`
- Lean source: `3e8ae8ba21cdaf47e1172a40d69f37a29247d2987a323e0c0746e7770ac58231`
- `candidate_effect.rs`: `7c8e4fe5270fd45cecece80dfbbdff81aa8f294546687938bf89212325fc146b`
- `candidate_scheme.rs`: `35c58dca3748595e273cd53bfba07da2be3fd340ec63c56f6a18adea5e514fb1`

STOP receipt: review complete; no files edited, no Git mutation, no Cargo,
tests, or Lean execution, no descendants, and no process left running.

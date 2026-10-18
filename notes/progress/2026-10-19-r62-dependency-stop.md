# R62 rev1 stop: omitted source crosswalk dependency

Date: 2026-10-19
Sprint: `whole-ascription-formation-derivation-20261019-r62`, revision 1
Contract SHA-256: `b9e2846ca4c92cf2913094297ba5817e071c10d991abefd1b7c367402f4cd4fa`
Activation baseline: `353f7b6b03e1ef3d8fa249505731a561a95bb9f5`; activation commit `686390069`; proof receipt commit `10206d4f1`.

## Stop reason and evidence

R62 rev1 stopped before either author wrote an output because Luna's source/native audit found a directly relevant unpinned `yu-core` annotation crosswalk. It is a default-off shadow module and supplies no typing judgment, but it explicitly inventories source annotations and reports typed-port/profile correspondence, annotation applicability/permission, original `Xi`, types/scopes, semantic witness, and legal whole-tuple substitution as unresolved premises. This is relevant evidence for the source-owner and underdetermination audit, so it must be part of the exact dependency set before a proof author can rely on it.

The crosswalk and boundary modules are observations only. They do not supply the missing whole-ascription judgment and do not alter selected annotation semantics. No R62 derivation, semantic underdetermination witness, implementation finding, or source exclusion was established.

The configured prover acknowledged Luna's HOLD and then STOPPED / WRITES_STOPPED / NO_DESCENDANTS. The two proof output files remain absent; no scratch paths were written. It had read the rev1 contract/current state, R61/R60 theory, pinned call-view authority and annotation policy, and pinned source sections before the HOLD; it did not inspect the newly found crosswalk. Luna had read the HIR/native source owners and `yu-core` crosswalk/boundary modules. Neither author output path was written. Reviewers remained WAITING and did not read.

## Resource and state disposition

R62 rev1's 600-second proof grant and 500-second Luna owner grant are charged in full on issuance under the sprint resource rule: **1100/1800 seconds charged**. Actual elapsed time, CPU and RSS remain UNKNOWN. The unissued review/integration allocations and the remaining 700 seconds are not carried forward. The rev1 sprint is closed as **INTERRUPTED FOR INCOMPLETE DEPENDENCY SET / NO RESEARCH RESULT**. All rev1 leases are frozen and current state records the exact stop receipts.

The R61 outcome and TODO `R61-SOURCE-ASCRIPTION-FORMATION-1` remain unchanged. Any continuation needs a fresh, versioned contract with the crosswalk sources explicitly pinned and a new resource allocation. No code, tests, builds, parser/solver/compiler execution, runtime, probes, instrumentation, semantic edits, or Git actions were performed by the stopped authors.

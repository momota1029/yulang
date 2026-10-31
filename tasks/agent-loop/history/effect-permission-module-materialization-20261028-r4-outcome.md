# Sprint outcome — EFFECT-PERMISSION-MODULE-MATERIALIZATION/r4

Status: **CLOSED_INCOMPLETE / BUDGET_EXCEEDED_BEFORE_OWNER_AUDIT**. Contract
SHA-256 `12d99e885af99a669007921e3ebc782b990c443781a9b6549962c12abd2f490f`.
Neither current supplier owner was inspected; no supplier, parent, native or
production conclusion is adopted.

## Authentication and coverage

The primary and both producers authenticated the six bootstrap entries and
all 21 manifest pins, receiving `PREFLIGHT_21_ENTRIES_ALL_MATCH`. The source
lane completed its reported bounded governance reads but inspected zero bytes
of semantic source material. The proof lane reported full page coverage for
the materialization rule, an adoption note and the parent preservation note,
but did not inspect either current supplier owner, the current birth-level
correction, or the needed admission/provenance and Rust-owner inputs. Its
authority and non-circularity discussion remains unadopted. A complete hash
preflight establishes input identity only.

## Resource and review disposition

The 150-second source reservation was fully charged; its measured elapsed
interval alone is 164.336331 seconds, at least 14.336331 seconds beyond the
cap, plus unmeasured startup. The 150-second proof reservation was fully
charged; its measured interval is 208.305920 seconds, at least 58.305920
seconds beyond the cap, plus unmeasured startup. Both are protocol overruns.

The 100-second review reservation is fully charged. The independent review
found the semantic audit incomplete, confirmed both cap overruns, and noted
that handoff page ledgers do not independently authenticate actual inspection.
The reviewer also exceeded the 4,096-byte page limit on initial reads, then
re-read all three artifacts in bounded pages through EOF. That deviation
remains recorded; full reviewer protocol compliance is not claimed.

Conservative ledger: r1/r2 1,400 seconds + full r3 700-second reservation +
full r4 500-second grant = **2,600 / 7,200 seconds charged**, leaving 4,600
seconds. No time refund or reuse is claimed. No Lean/Lake, theorem, axiom
audit, Cargo, tests, build, Git, source/compiler edit or child-agent work
occurred in this sprint beyond the named producer/reviewer grants.

## Frozen evidence and gates

| Artifact | SHA-256 |
|---|---|
| R4 contract | `12d99e885af99a669007921e3ebc782b990c443781a9b6549962c12abd2f490f` |
| Primary preflight receipt | `e1ce2d408fb9e5ef2aa042f505526011787611d60342b865f779b10e6f7fb0ae` |
| Source receipt | `4434dccb11598e88b6fa38c38895b19cfd7686f52b833df0698c683df632ea43` |
| Proof receipt | `7459262c38286729a68d56ae1f920ac3a7616ed1382d4673dd2f750d9652375a` |
| Independent review | `a20ad75a1356f6c759e6750667c7836c55a9e2b4a1cd511c411b8fab32772060` |

Preserve both supplier obligations, original parent quantifiers and shared
witnesses, callback → Call result → tuple `left`, and all source/native and
production obligations as OPEN. Keep all prior UNKNOWN identities/quarantines
and `DELTA_AUTH_UNRESOLVED / NO_SAFE_CODE_SLICE`. No source or expected-output
change is authorized. The next source continuation must retain the frozen r4
coverage, reauthenticate inputs, and have adequate bounded grants; a different
proof lane must perform its own required governance reading. No further code
or source work was admitted by this closure.

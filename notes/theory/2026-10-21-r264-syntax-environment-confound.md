# R264 — parser environment confounds the R262 diagnostic totals

R262 parsed the line-comment-projected Y2 files with `SyntaxEnvironment::empty()`.
That does not provide the imported operator capabilities the sources request.
The resulting 474 diagnostics / recoveries are observed output, but are not a
clean measure of Y2/Y3 grammar incompatibility.

A primary-only control built one `SyntaxEnvironment` from all 40 scanned
headers, with a provenance entry per pinned source, then parsed all 40
comment-projected files. This is deliberately only a broad control: it gives
each source operators from unrelated modules and is not the per-module import
environment. It produced 500 syntax diagnostics and 464 structural recoveries
across 34 modules. `std::core::ops` had 35 diagnostics but one structural
recovery, and `std::testing` acquired two diagnostics with no structural
recovery, consistent with the global table introducing irrelevant collisions.

The control therefore confirms the environment matters and does not validate
R262's count as a dialect falsifier. Nor does the all-header environment
resolve the issue. A proper per-module environment must be derived from each
source's authenticated imports. Independently, `pub mod name;` in the pinned
Y2 sources receives Missing recoveries under the current Y3 `ModDeclaration`
shape; the same diagnostic persists under both empty and all-header
environments. This is direct evidence of an external-module syntax gap, but it
does not classify all the other diagnostics.

The temporary control test was removed. Its Cargo test passed the probe's
round-trip and projection assertions; it was not a compatibility test. R260
remains conditional and no Y2 root set is established. See R264 contract.

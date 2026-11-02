# R274 frozen producer handoff

Handoff ID: `R274-SOL-SOURCE-ACCEPTANCE-1`; revision: `1`. Freeze is the SHA-256 of this file reported to Luna with the theory artifact digest.

Producer: `/root/sol_r274_source_acceptance`; coordination session `01a1873a-a93b-7dc3-a8ce-028a7b543a80`; requested Sol/high, observed model/effort UNKNOWN. **STOPPED INCOMPLETE** within the 2,400-second grant. No descendants.

Parent: inference/effects soundness → R70 → `R71-RAW-CANONICAL-FIBER-COVERAGE-1`; original quantifiers, Simple-sub A/B, source/native correspondence, F1/FK1 and foreign continuations unchanged. Parent/A/B 0→0; `Need_D` and R71 coverage OPEN.

All authorized gates passed: contract `ec875f9705324e9aab328ee8aebd9bc028ab8dafffed3578d3db9fd910a72b27`, ranges `4df81d44a22a22c7ea7d56d19f49bd75c6ed6061bbd06fc777cd80cfafa2debf`, source view `e1e03aaa65ec15e45ca25c9998b29d366b4b6f8ef16e2d2290ea7dd03935cb2e`, 229 distinct input entries, three origin manifest digests, R268 `719497ad1921be23329a8df790e942ba5c63170ed2bae4880c9656634389ad72` and R269-r4 `a5f3bd1f3bc701ce75191ec234b72264d0dd9e73d7dfd31b88f0b8da0c6009ec`, 28 whole-file hashes, 28 interval hashes and 28 view byte equalities.

First missing implication: `H = yu_syntax::scan_header(S)` must imply `Arc::ptr_eq(&S, &H.source)` and that `H` is the header discovery result. `R274-E001` gives the fixture and call identity; `R274-E009` requires the pointer equality as the first `parse_file` assert; `R274-E008` shows only the conditional `HeaderDiscovery::into_header_info(self, source)` constructor. The public `yu_syntax::scan_header` owner is absent from the source view. Stop under the contract's omitted-owner rule. This is no observed failure of the assert, accepted fixture, counterexample, or parent application. `crate::declaration::next_use_item_lex` is a further missing header-classifier owner if the first bridge is supplied.

Source excerpts used: `R274-E001`, `R274-E002`, `R274-E003`, `R274-E004`, `R274-E008`, `R274-E009`, `R274-E010`; no original source body was displayed for technical use. Prior R272 conditional trace and R273 stopped producer outputs were rejected as premises. Earlier R268/R269 contracts were used only for inherited semantic bounds.

Next in-scope step for Luna: issue a new exact range for the public `yu_syntax::scan_header` constructor/forwarding law, with hash and view correspondence, then retry the first normal-return premise. No code TODO is warranted. No tests/builds/probes/Cargo/Lean/network/scratch, source edits, or production writes. Exclusive new paths: this handoff and `notes/theory/2026-11-03-source-acceptance-r274.md`; no other paths written.

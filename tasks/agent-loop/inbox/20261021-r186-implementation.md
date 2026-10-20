Sprint-ID: source-emission-and-option-b-stage1-20261021-r186
Contract SHA-256: 41d2241083e3443918b730cd457428d5128b5abe73896e0ed23aae17390664d3
Handoff revision: 2
Parent gate: R183-FRONTIER-COVERAGE-1 and original A/B/source-native/production gates remain OPEN.
Baseline: ef15618375343b5bfef0ba4aa3a7fbfbe5606d74; exact 50 committed pins in sprint contract.
Role/owner: Luna primary; design lane max 600s; code still inactive.
Outcome: staged design candidate for ordinary non-record braced `if` expression sequences.
Semantics: source-order exactly-once items; last item provides value; effects accumulate across all items; continuation preserves unrun suffix; no-else remains Unit after evaluating selected body. Existing colon/indented/inline behavior and unchanged fixture protected.
Deferred: empty/record field/spread semantics, duplicates, precedence, lookup, rendering, mixed spread, malformed execution.
Exact path set: see `notes/design/2026-10-21-r186-option-b-implementation-contract.md`; only a justified subset may activate. Dirty solver owners and fixture/lib.rs excluded.
Checks: none; no tests/builds/probes before code activation.
Review: revision 1 received MAJOR finding (about 110/120s charged): primitive certification must cover every retained definition/arm/dependency, including unused objects. Revision 2 states the universal condition. No review budget remains in this sprint, so no code lease or activation; a separately budgeted fresh review is required.
Remaining premise: the revised universal certification wording still requires fresh independent review before code authority. Verify all constructors/consumers remain in the exact source manifest and path list.

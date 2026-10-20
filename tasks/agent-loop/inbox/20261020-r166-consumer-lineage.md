# R166 native consumer-lineage proof handoff

- Sprint: `native-consumer-lineage-and-runtime-completion-20261020-r166`; contract SHA-256 recorded after freeze.
- Assignment: `R166-NATIVE-CONSUMER-LINEAGE`, revision 1; prospective only, no lease or launch yet.
- Parent: original computation-forwarding preservation §§1, 6–7; preserve original source domain, shared assignment, provider/witness identities, ordered dependencies, arbitrary finite chains, repeated calls, simultaneous entries and independent quantifiers.
- Baseline: proposed `dbdf179986ac80608347dfc72c95d90b5ab9dfb7`; R165 frozen note `ac8f211679cb8c44d7834069d821e0a774f83fdc379845ca9ad110eb3b14b9aa`.
- Objective: trace an authentic required witness backward from its actual relation-local Function AE/RE consumer to source admission, then prove its constructor lineage forward through Capture, FreshUse, extrusion, qualifying merge/recapture and Replay; or identify the exact source-qualified obstruction/counterexample.
- Exact output leases: `notes/theory/2026-10-20-r166-consumer-lineage.md` and this handoff only.
- Exclusions: solver edits, tests/builds/probes/compiler/sample/runtime execution, instrumentation, all Yulang2 activity, semantic changes, source restrictions, production promotion.
- Falsifier: accepted source history with exact required witness/provider/use and current residual/scoped payload, where every admissible lineage fails to reach the actual consumer. Endpoint/count/sibling/hand-built evidence is insufficient.
- Dependencies: original theorem, R70/R71, R165, exact current source pins; re-pin and stop on mismatch.
- Budget: proposed 900s proof within R166 2520s total; no carryover or descendants. No work starts before CLEAN prospective review and Luna's fresh launch/lease receipt.
- Review: fresh independent result review after freeze; author cannot self-certify.
- Writer stop: prospective; no current worker assigned and no writes authorized.

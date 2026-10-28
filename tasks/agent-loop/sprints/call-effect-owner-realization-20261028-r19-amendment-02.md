# R19 amendment 02 — frozen implementation overlay and budget stop

Base contract: `CALL-EFFECT-OWNER-REALIZATION/20261028-r19`, revision 2, SHA-256 `9400d07a47cb48043983fa4ae43c41962a581a97a732d181c92cdd2a090e6bd7`. Amendment 01 remains in force except where this amendment adds the candidate-overlay disposition and stop rule below. The original theorem, quantifiers, source domain, semantics, dependencies and 2,100-second aggregate grant do not change. No worker grant or verification attempt is renewed.

## Frozen candidate overlay

The original input manifest remains unchanged at SHA-256 `f287059a08410cf644644be214ba622de92d3e2d10c4897441cbb360c91ca22d`. The primary changed one leased candidate path before the Sol lane completed authentication. This is recorded as a sequencing error; it invalidated the source lane's exact input pin for that path.

The one-hunk primary edit is frozen separately in [candidate overlay 01](call-effect-owner-realization-20261028-r19-candidate-overlay-01.md), SHA-256 `8292a917f07a2c2b509ed5875d734e193d6da798bff325a36015039da6da4e4a`:

- baseline `candidate_scheme.rs`: `3eb9ba3b414dd0e40f49957e0ee2b9de1ba21fd86dff718111d1b5030ccac6b7`;
- candidate `candidate_scheme.rs`: `985ea301fbca632ecabe494f4324326759477608c0bf1a81e297c9e8b41cd37c`;
- implementation handoff: [R19 implementation](../inbox/call-effect-owner-realization-r19-impl.md), SHA-256 `3ada7346900ea9d013771e6eb864f3ffc845464bbf971116a6bd511aedee39a2`.

This overlay supplements the original pins without rewriting the manifest or claiming the edited candidate was among its authenticated bytes. It adds no constructor provenance or source/native law.

## Source receipt correction and disposition

The frozen Sol receipt [R19 source](../inbox/call-effect-owner-realization-r19-source.md), SHA-256 `5708927ca95ab623979d3580704bd0b2be13a13fda07c324b74c45971252dd4c`, transcribes the contract hash with an extra leading zero (`09400d07…`). The authoritative contract hash is `9400d07a47cb48043983fa4ae43c41962a581a97a732d181c92cdd2a090e6bd7`, independently recomputed from the pinned contract bytes. Preserve the original receipt unchanged; this amendment is its correction record.

The source lane stopped after 726/727 file pins matched and all 11 parent pins matched. It read no source body, completed no row join, and establishes no source conclusion. Its requested 250-second grant is spent/unknown for accounting; no restart is authorized by this amendment.

## Runtime and verification boundary

Astra's proof lane and the Lean lane are frozen at their separate handoffs. They establish missing same-route Function ownership/typed-port/Call equations and no supported Lean theorem type. Their remaining times and observed execution metadata stay UNKNOWN where not measured. All parent, source/native, effect-hygiene and production gates remain **OPEN**.

Primary residual closeout time is not authenticated. Therefore this amendment authorizes **no Cargo, test, formatter, build or Lean command** and no retry. The only remaining action is a fresh independent read-only review of the frozen R19 proof, Lean, source-stop and implementation-overlay artifacts using the existing 250-second review allocation. The reviewer must account for the original manifest/candidate overlay distinction, the source pin mismatch, selection equivalence, allocation/traversal cost, and every still-open parent premise. No pre-run ACCEPT from that review will trigger Cargo under this amendment.

After that review, close R19 **CLOSED_INCOMPLETE**, record the exact frozen hashes and the primary sequencing error, preserve the original parent quantifiers, and keep every parent and production gate OPEN. No scope, lease, source or budget expansion is implied.

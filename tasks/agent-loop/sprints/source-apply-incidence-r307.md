# R307 — authenticate source Apply and child incidence

Baseline `ef1b11a91`. The unchanged goal is actual source Union → catalogue →
original child/result correspondence and R159 application. R306 computes a
conditional graph lookup but does not construct source registration. The next
concrete source-owned edge is the missing Apply parent-to-child incidence: the
existing owner reification records physical occurrences but its `.app` case
does not authenticate that its independently translated children are the
actual `LocalSourceForm::Apply` children.

Implementation lane: extend the existing authentic HIR source extractor to
emit every Apply's actual owner, application occurrence/source key, raw callee
and argument occurrence/source key from the same `LocalSourceIndex`, and enough
original group/route information to avoid replacing physical incidence with a
guessed unwrapped child. Preserve occurrence identities separately from source
keys: empty-call Unit and Apply can share a key/range but not an occurrence.
Emit Lean-readable data for genuine source, include a nested computed-call and
same-position/empty-call fixture, and exercise deterministic extraction. Do not
infer EI arms, a logical admission, or a semantic interpretation from syntax.
Exclusive files: `tools/inline-authentic-extraction/src/bin/source_signature_r300.rs`,
`tasks/agent-loop/inbox/source-apply-extraction-r307.md`, and
`/tmp/yulang-r307-extract`. Offline locked checks, 1800s; no Git or children.

Proof lane: build a source-incidence relation that checks the emitted exact Apply
row against the parent and both real child occurrences, then use existing
`OriginalSourceOwnerReification.TableToSource.app` and the unchanged R159
consumer with actual fields where feasible. Preserve group paths, every source
occurrence, duplicate positions, and both children. Never supply a desired
catalogue, EI meaning, admission or child judgment as a disguised output. Apply
the result to a genuine extractor-produced fixture and report exact remaining
premises and how far it reaches the parent. No finite fixture proves general
Rust–Lean equivalence. Exclusive files:
`notes/theory/lean/YulangClosure/OriginalSourceApplyIncidenceR307.lean`,
`tasks/agent-loop/inbox/source-apply-incidence-r307.md`,
`/tmp/yulang-r307-proof`. Pinned Lean 4.35, per-theorem type/axiom audits,
2400s; no Git or children. Wait for frozen source schema before consuming it.

The independent review must reject swapped children, a missing group, and
conflation of distinct occurrences sharing a source position, and check that
actual source rows are used. No new language semantics or production behavior
is authorized. All independent arms, authentic EI interpretation, q_c
registration, original checking/admission, arbitrary source coverage and R159
closure remain open unless separately proved. Primary owns Git and review;
unknown historical leases remain quarantined.

Input SHA-256: extractor `e72138e1982bebe2ca6fe1e867b4cc8d70126524b1946875e05deb8a7cc35c18`;
existing owner extractor `4921d14f813e931cb064ecc87d8120734b69d1eedaf48fe0bd36deb014e862e9`;
existing owner Lean `95d9749ce93ecfc82d6423ba193a261f2725178a7e62cea469b57ae316af3d7e`;
R159 `5e948a1f8a3aab66028f885ebf16b6ffeed81999039e8a5a4e9c3caf84464408`.

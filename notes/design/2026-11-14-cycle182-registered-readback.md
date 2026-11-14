# Cycle 182: registered equation readback

Status: Draft, additive local proof support for the original centered ground boundary.

For every centered state and assignment satisfying its Models predicate, every registered plan supplies its head, input, named, and every declared-child schema equations. Every actual use in any of those schemas therefore gives Same between its observation origin and that plan's allocated binder. Arbitrary observed values are Equivalent to the binder's interpretation. For origins renamed along recorded source equalities, the same conclusion follows by the existing root-alias transport theorem. These implications require no execution path: Models includes registered equations directly.

Capture-only membership supplies Fits in its recorded interval, not an actual-origin equality. Registered centered sites, registered plan input sites and registered child sites similarly supply their own Fits. The public API keeps these statements separate.

No theorem produces schema membership, origin linkage, registered root aliases or candidate-to-old binder equality from reachability. No EvidenceNode field or successor V6 composition closes. The original I-30 target remains GeneralNominalCenteredGroundBoundary.groundBoundary.

## Full-support typed provenance

GeneralNominalSupportProvenance182 defines exact typed origin predicates, not new semantic assumptions. `full_iff` states that fullSources membership is equivalent to a raw journal component, a registered centered site's lower/upper/center source, or a registered plan's input, capture, schema or child-site source. A schema source is a test origin or a use's origin, actual binder, or nonactual capture endpoint/output. `variable_iff`, `schema_iff`, `site_iff`, `capture_iff`, and `plan_iff` establish the subordinate exact membership classifications. `ActualBinder` identifies one particular actual-binder branch. `actual_member`, `actual_same`, and `actual_readback` connect that branch to support membership and the registered readback theorem. Other branches are not automatically actual binders. In particular raw historical reports and raw observed sites are retained, not discarded by the ordinary current-context freshness lemma.

## Reachable site producer

GeneralNominalSiteOrigin182 proves `site_origin` for every actual centered trace from any state: every final registered site either was initially registered or belongs to an actually registered final plan's emitted list. `initial_site_origin` specializes this to rootSite starts. `plan_seed` proves that all registered plans share the initial context's seed. `root_not_eight` excludes every purpose-eight allocated name from every initial rootSite center using source linkage and namespace separation; it needs InitialSource but not groundness, point roots or model inhabitation.

`purpose_eight_site_binder` combines these results: for every InitialSource, actual trace, final registered site and argument index, if that site's center is an allocated purpose-eight name at the initial seed, there exist a final registered plan and binder name whose binder equals this center. It is derived by trace induction and the emitted child's normalized pattern. Compound child centers have purpose nine and are excluded; the remaining child is a bare binder. The conclusion does not assert a head actual-use, candidate origin match, capture-needed condition, or fullSources purpose-eight classification. It is one genuinely produced provenance case, not the unrestricted EvidenceNode theorem.

## Validation

Three new modules compiled independently with Lean 4.35.0, -j1 --trust=0 -DwarningAsError=true. All 23 public theorems passed explicit axiom inspection, with only propext, Classical.choice and Quot.sound dependencies. The first provenance compile failed on a reserved local name and an implicit-schema name collision; the first site producer compile failed on a shadowed variable and incorrect pattern constructor alternatives. These were corrected before the successful builds. No full project build was run.

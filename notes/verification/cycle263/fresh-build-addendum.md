# Final focused rebuild accounting

Primary final rebuild: 141 distinct modules, exit0, source closure1857, 20:09–20:13UTC.
The final InitialBoundary audit then added an unchanged historical dependency,
GeneralNominalVersionedMixedPlanLedger235. It was built freshly with
LEAN_PATH=lean/.lake/cycle263-final lean --trust=0 -DwarningAsError=true -o ...
(exit0; ledger235-fresh.txt). Its prerequisites had already been verified.
The final dependency-source-sha256.json and fresh-modules.txt therefore contain
1858 dependency sources and142 distinct freshly verified modules (30 new263 and112
historical sources not in the previous cycle262 verified dependency manifest).
No frozen dependency in the previous manifest changed.

One audit runner had created its build-path links just before this last historical
olean appeared, so InitialBoundary initially failed with a missing object file.
The direct primary audit succeeded. Relinking all verified artifacts and rerunning
all standalone audits fixes that environment timing issue; see final audit-runs.txt.
The initial missing-link output is preserved separately. Do not mistake this for
a full-repository build or a kernel proof failure. No whole lake build was run.

A final ProspectiveEffect263 module was built separately at20:18UTC, exit0 (prospective-effect-primary.txt), with all imported dependencies already in the verified closure. Final distinct fresh total is143=31new+112historical, final dependency manifest1859. Final standalone run includes19audits after this addition.

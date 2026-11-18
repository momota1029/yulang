# Deeper focused rebuild

Rebuilt182 actual dependency-closure modules numbered240–257 in a separate fresh
cache, dependency order, under --trust=0 and warningAsError=true. Start13:43:10,
completion13:46:57 UTC, exit0, bounded by timeout5m. Includes the14 then-existing
cycle257 modules; the later Known/Point/Report/BinderGap files are separately
focused built and must be included in final fresh cycle257 build. Source list and
full transcript are critical-layer-modules.txt and critical-layer-build.txt.
Older dependencies outside the selected layer were reused with source hashes
checked. Not whole repo build and not an independent-worker rebuild.

A second, separate final critical-layer rebuild was started at14:10:04 UTC,
selecting193 modules from the complete final closure. Unlike the first run it
includes all25 cycle257 modules. See final-critical-build.txt for actual outcome;
do not infer PASS from starting the command. Older dependencies are still
reused with checked source hashes, not claimed independently rebuilt.

Final critical layer completed14:14:00 UTC, exit0:193 modules, including all25
cycle257 modules, fresh cache; no duplicate selected module. This strengthens
the final dependency check but remains focused (not all1615 closure modules).

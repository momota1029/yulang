# MODULE-SUPPLIER-NATIVE-SLICES/r2 page preparation

Primary-owned transport preparation only; no source/proof semantic conclusion and no producer grant.

- Corrected generator `tasks/agent-loop/sprints/module-supplier-native-slices-r2-pagegen.py`, SHA-256 `9e555f3f83d9f7153ad1972dbd5e8f66e951317fb41e0ae78da49f4dffc27d4a`.
- Consumer `tasks/agent-loop/sprints/module-supplier-native-slices-r2-pagecat.py`, SHA-256 `41a350c97634b2025d8b4dcd98643e9c3938a720e2acbc57089f43fcbf2c0ff0`.
- Frozen page manifest `tasks/agent-loop/sprints/module-supplier-native-slices-r2-pages/manifest.json`, SHA-256 `4c5db2314c74ac5f42a81ef05eda17be4524de970f90baaf4a6ba842669676fe`.
- Governing r1 scope contract SHA-256 `6ab211856d460e4c31fdcadd0f4c0576444444630eb9bcd380a53e4aec7f7435`.
- Owner pins remain the four r1 hashes for `candidate_source.rs`, `lib.rs`, `candidate_scheme.rs`, and `shadow_apply.rs`.

The r2 manifest contains 18 pages and 32,185 unique source bytes. Before staging, the generator authenticates all four owner hashes, validates every range and unit/context classification, checks overlap per owner, and checks aggregate/page caps. It writes into a private sibling staging directory, verifies each page and manifest there, then renames the completed directory to the fresh r2 destination. The rejected unreviewed first r2 page directory is preserved as `tasks/agent-loop/sprints/module-supplier-native-slices-r2-initial-unreviewed-pages`; r1 artifacts remain untouched.

Boundary repairs: `instantiate_candidate_graph` now includes line 4800; `definition_use` begins with its documentation and full declaration at 3230–3253. The three `lib.rs` ranges identified as incomplete are explicitly `context_fragment`; they are not represented as complete functions. The Name arm includes surrounding context but identifies its complete unit as 1766–1807. The other corrected complete ranges are recorded with kind `unit` in the manifest. No other owner or source tail is included.

Primary verification independently rechecked all 18 page hashes/sizes/headers, exact original source offsets and range reconstruction, per-unit contiguous page continuation, and nonoverlap. All passed; maximum emitted page is 3,779 bytes including its header. The prescribed command `python3 tasks/agent-loop/sprints/module-supplier-native-slices-r2-pagecat.py page-014.txt` ran with an 8,192-token output allowance, exit 0, and returned the full 3,779-byte page including its closing bytes. This verifies transport only; source facts remain unadopted.

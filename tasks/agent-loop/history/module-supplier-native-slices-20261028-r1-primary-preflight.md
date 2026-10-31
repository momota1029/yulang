# MODULE-SUPPLIER-NATIVE-SLICES/r1 primary preflight

- Contract: `tasks/agent-loop/sprints/module-supplier-native-slices-20261028-r1.md`
- Contract SHA-256: `6ab211856d460e4c31fdcadd0f4c0576444444630eb9bcd380a53e4aec7f7435`
- Baseline: `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`; worktree `yulang3`.
- Exact manifest: `tasks/agent-loop/sprints/effect-permission-module-materialization-r3-manifest.json`, SHA-256 `aee1a5e3c06e9c72348e45676157bdb56b57f0dc5673ddcffe58b30a8fb16f11`.
- Exact script: `tasks/agent-loop/sprints/effect-permission-module-materialization-r3-preflight.py`, SHA-256 `7ef05dc938c7f44cbbcd08004cc5fc9b306677b58415cc4276c21330a832d133`.
- Literal command: `python3 tasks/agent-loop/sprints/effect-permission-module-materialization-r3-preflight.py tasks/agent-loop/sprints/effect-permission-module-materialization-r3-manifest.json`
- Result: exit 0; all 21 entries MATCH; `PREFLIGHT_21_ENTRIES_ALL_MATCH`.
- No body reads preceded the primary preflight. Both lanes must independently repeat contract/manifest/script and 21-entry authentication before any body read.
- The exact governed functions and read caps are in the frozen contract. No source, proof, compiler, or expected-output edits authorized.

# R19 implementation candidate overlay 01

Status: **FROZEN**. This overlay supplements, and does not modify, the original R19 input manifest.

- Sprint: `CALL-EFFECT-OWNER-REALIZATION/20261028-r19`, contract SHA-256 `9400d07a47cb48043983fa4ae43c41962a581a97a732d181c92cdd2a090e6bd7`.
- Sole changed input path: `isolated/call-effect-owner-realization-r19/rust/crates/yu-solver/src/candidate_scheme.rs`.
- Pinned baseline SHA-256: `3eb9ba3b414dd0e40f49957e0ee2b9de1ba21fd86dff718111d1b5030ccac6b7`.
- Frozen candidate SHA-256: `985ea301fbca632ecabe494f4324326759477608c0bf1a81e297c9e8b41cd37c`.
- The other two assigned Rust paths remain byte-identical to their manifest pins.
- Implementation handoff SHA-256: `3ada7346900ea9d013771e6eb864f3ffc845464bbf971116a6bd511aedee39a2`.
- Writer: `/root`; writer STOPPED after freezing the candidate and handoff. No source, build, Cargo, test, Lean or Git operation occurred in the implementation lane.

## Authorized one-hunk delta

The existing same-route selector matched only a retained term and collapsed zero and multiple matches into one `None`. The frozen delta maps each candidate node through `mapped_endpoint_at(graph, mapped_rows, retained, node)` and compares the resulting typed endpoint with the full Replay lower or upper endpoint. It reports distinct zero-match and multiple-match rejection stages; exactly one positive and one negative node continue to the existing typed-port checks.

```diff
-            let find_function = |term: Term, polarity: Polarity| {
-                let mut found = None;
-                for (index, node) in graph.nodes.iter().enumerate() {
-                    if !matches!(node, Node::Function { polarity: actual, .. } if *actual == polarity)
-                        || retained.terms.get(index).copied().flatten() != Some(term) { continue; }
-                    if found.replace(index).is_some() { return None; }
-                }
-                found
-            };
-            let Some(positive_node) = find_function(positive_root, Polarity::Positive) else { rejected!("positive-function-node-absent"); };
-            let Some(negative_node) = find_function(negative_root, Polarity::Negative) else { rejected!("negative-function-node-absent"); };
+            let find_function_nodes = |expected: ExtrusionEndpoint, polarity: Polarity| {
+                graph.nodes.iter().enumerate().filter_map(|(index, node)| {
+                    if !matches!(node, Node::Function { polarity: actual, .. } if *actual == polarity)
+                        || mapped_endpoint_at(graph, mapped_rows, retained, index) != Some(expected)
+                    {
+                        return None;
+                    }
+                    Some(index)
+                }).collect::<Vec<_>>()
+            };
+            let positive_nodes = find_function_nodes(row.lower_input.2, Polarity::Positive);
+            let positive_node = match positive_nodes.as_slice() {
+                [] => rejected!("positive-function-node-zero-matches"),
+                [node] => *node,
+                _ => rejected!("positive-function-node-multiple-matches"),
+            };
+            let negative_nodes = find_function_nodes(row.upper_input.2, Polarity::Negative);
+            let negative_node = match negative_nodes.as_slice() {
+                [] => rejected!("negative-function-node-zero-matches"),
+                [node] => *node,
+                _ => rejected!("negative-function-node-multiple-matches"),
+            };
```

This is a test-only observer selection change. It adds no independent constructor provenance or ordered-port ownership. The retained endpoint helper derives Function endpoints from polarity and retained term; the route row map is used for row endpoints. The four original R18 rows and all original theorem quantifiers remain unchanged.

## Input mismatch and disposition

During the Sol lane's authentication, the primary had already changed the candidate path. The lane correctly stopped on the 1/727 mismatch before source-body reads; all 11 parent pins matched. The frozen source receipt is `tasks/agent-loop/inbox/call-effect-owner-realization-r19-source.md`, SHA-256 `5708927ca95ab623979d3580704bd0b2be13a13fda07c324b74c45971252dd4c`. It records that no source audit or four-row join was completed. No source claim is inferred from that lane.

The primary therefore keeps the original input manifest and records this separate immutable candidate overlay. The candidate is not evidence of an authenticated owner-consumer relation. Parent, native, effect-hygiene and production gates remain **OPEN**. Cargo is not run because the primary's remaining closeout reserve is not authenticated; no fresh test or retry is authorized by this overlay.

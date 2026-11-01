# R142 source handoff — corrected sibling-module visibility patch

Sprint / contract: `EFFECT-PERMISSION-SNAPSHOT-VISIBILITY-FIX/20261102-R142`, revision 1, contract SHA-256 `41f0f3383dedb7812affa1ec4c2b36cae6c339071773fd12a5ef00e5f8c17cc7`.
Admission: `tasks/agent-loop/history/effect-permission-snapshot-visibility-fix-20261102-r142-admission.md`, SHA-256 `c0857063b04029af0d9f82f5ee45660c8de1d4df61efbf936e2dd36c4d0bcc17`.
Assignment / handoff revision: `R142-TWO-TYPE-VISIBILITY-PATCH`, revision 1.
Parent: `YulangClosure.SourceProblem.InferenceSoundness` and effect-hygiene H; both remain OPEN.

## Frozen inputs and patch evidence

- Immutable baseline commit: `a88e405b1b1c1b99a6c38e6180c977454b2507e6`.
- Baseline `crates/yu-solver/src/candidate_effect.rs`: 301873 bytes, SHA-256 `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01`.
- Frozen R141 handoff revision 1: 25181 bytes, SHA-256 `65c3d181b50c45f1716092e94a519aaa74a40f93a863bf1f264d1f1da12be76f`.
- Frozen R141 review: SHA-256 `be08b8fa589aa0d2a91bd0468b92620e141093873e094c3412854d4de717f650` (B1 requires sibling-visible result types).
- Corrected complete unified patch: 17469 bytes, SHA-256 `0cbeb277433288d3cb6e56469bf453f57bdf36c31ef2219180c1142304211484`.
- In-memory target `crates/yu-solver/src/candidate_effect.rs`: 318120 bytes, SHA-256 `8fb4c52b89069f4ffcf203c50204869fed91d1fb5b3fa7738d10592b1cb072ce`.

R141 v1 is preserved unchanged. This patch changes exactly the visibility of `SnapshotError` and `Snapshot` from private to `pub(super)`; all fields remain private. The existing `pub(super) one_successful_call` can therefore return an accessible `Result` to the parent-module sibling fixture. The fixture continues to consume the result via inferred `.expect(...)`; no public fields or type annotations are needed.

## Applicability and scope

The corrected patch was reconstructed from the pinned Git blob and frozen R141 patch entirely in memory. Both original hunks' old lines and declared line counts matched the baseline; after the two visibility substitutions, the reconstructed target was diffed against that same baseline to produce the full patch below. No patch was applied to a worktree and no source or scratch file was materialized. The diff consists of the R141 fixture call replacement plus appended comparator module, with only those two visibility modifiers corrected.

The sibling fixture is the existing parent-module test in `candidate_effect.rs`; it can call the accessible helper and consume its `Result` through `.expect`. Snapshot fields remain private, and the fixture does not access them. `SnapshotError` variants remain private.

This resolves only the static privacy seam. The fixture is an internal-producer test, not accepted-source evidence. Source/native equality beyond the exact fixture, the parent theorem, H/A/B and production remain OPEN. No compile/type confirmation is claimed.

## Full corrected unified patch against the immutable baseline blob

```diff
--- a/crates/yu-solver/src/candidate_effect.rs
+++ b/crates/yu-solver/src/candidate_effect.rs
@@ -3739,9 +3739,9 @@
         let SourceAnnotationValue::Function { result: rr_effect_node, .. } = &rr_function.value else { panic!("RRR Function"); };
         let rr_row = rr_effect_node.effects.as_ref().expect("RRR effect row");
 
-        session.with_route_transaction(|session| {
-            session.candidate_formal_annotation(&annotation, parameter, &occurrence, &scope)
-        }).unwrap();
+        let _snapshot = r140_ordered_snapshot_candidate::one_successful_call(
+            &mut session, &annotation, parameter, &occurrence, &scope,
+        ).expect("same-call ordered snapshot matches the retained native suffix");
 
         let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
         assert_eq!(state.formal_permissions.len(), 2);
@@ -5226,3 +5226,318 @@
         assert_eq!(session.effect_bounds.len(), old_rows);
     }
 }
+
+#[cfg(test)]
+mod r140_ordered_snapshot_candidate {
+    use super::*;
+
+    #[derive(Clone, Debug, Eq, Hash, PartialEq)]
+    enum TaggedKey {
+        Owner(SourceRootId),
+        Occurrence(HirOccurrenceId),
+        Formal(yu_hir::HirParameterId),
+        FormalPosition { owner: SourceRootId, parameter: usize },
+        Scope(AnnotationScope),
+        Node(SourceNodeKey),
+        Effect(SourceEffectId),
+        Symbol { scope: AnnotationScope, spelling: Box<str> },
+    }
+
+    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
+    enum Polarity { Positive, Negative }
+
+    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
+    pub(super) enum SnapshotError { Exhausted, Unsupported, MissingKey,
+        Divergence { index: usize, field: &'static str } }
+
+    #[derive(Default)]
+    struct IdTable { by_key: HashMap<TaggedKey, u32>, by_code: Vec<TaggedKey> }
+
+    impl IdTable {
+        fn intern(&mut self, key: TaggedKey) -> Result<u32, SnapshotError> {
+            if let Some(&id) = self.by_key.get(&key) { return Ok(id); }
+            let id = u32::try_from(self.by_code.len()).map_err(|_| SnapshotError::Exhausted)?;
+            self.by_key.try_reserve(1).map_err(|_| SnapshotError::Exhausted)?;
+            self.by_code.try_reserve(1).map_err(|_| SnapshotError::Exhausted)?;
+            // HashMap uses full Eq after hash selection. Clone allocation for
+            // Symbol(Box<str>) is infallible; it is not called Exhausted here.
+            self.by_key.insert(key.clone(), id);
+            self.by_code.push(key);
+            Ok(id)
+        }
+        fn lookup(&self, key: &TaggedKey) -> Result<u32, SnapshotError> {
+            self.by_key.get(key).copied().ok_or(SnapshotError::MissingKey)
+        }
+    }
+
+    #[derive(Clone, Debug, Eq, PartialEq)]
+    struct PermissionImage {
+        parameter: usize,
+        formal_position: u32,
+        occurrence: u32,
+        owner: u32,
+        scope: u32,
+        path: Vec<FormalPortStep>,
+        source_row: u32,
+        concrete: Vec<u32>,
+    }
+
+    // Separate record shape: root-entry permission is never a nested port.
+    #[derive(Clone, Debug, Eq, PartialEq)]
+    struct EntryImage {
+        registration: usize,
+        parameter: usize,
+        formal: u32,
+        formal_position: u32,
+        occurrence: u32,
+        owner: u32,
+        scope: u32,
+        annotation_position: u32,
+        source_row: u32,
+        entry_effect: u32, // State-local only; never compared across snapshots.
+        concrete: Vec<u32>,
+    }
+
+    struct Complete;
+    pub(super) struct Snapshot {
+        table: IdTable,
+        root_entries_before: Vec<EntryImage>,
+        nested_suffix: Vec<PermissionImage>,
+        _complete: Complete,
+    }
+
+    fn key(table: &mut IdTable, key: TaggedKey) -> Result<u32, SnapshotError> {
+        table.intern(key)
+    }
+
+    fn copy_path(path: &[FormalPortStep]) -> Result<Vec<FormalPortStep>, SnapshotError> {
+        let mut result = Vec::new();
+        result.try_reserve_exact(path.len()).map_err(|_| SnapshotError::Exhausted)?;
+        result.extend_from_slice(path);
+        Ok(result)
+    }
+
+    fn append_step<T>(path: &mut Vec<FormalPortStep>, step: FormalPortStep,
+        f: impl FnOnce(&mut Vec<FormalPortStep>) -> Result<T, SnapshotError>)
+        -> Result<T, SnapshotError> {
+        path.try_reserve(1).map_err(|_| SnapshotError::Exhausted)?;
+        path.push(step);
+        let result = f(path);
+        path.pop();
+        result
+    }
+
+    fn valid_pair(row: Option<&SourceEffectRow>, polarity: Polarity) -> bool {
+        row.is_none_or(|row| row.variables.len() <= 1 && match polarity {
+            Polarity::Positive => true,
+            Polarity::Negative => (row.concrete.is_empty() && row.variables.len() == 1)
+                || (!row.concrete.is_empty() && row.variables.is_empty()),
+        })
+    }
+
+    fn context_ids(table: &mut IdTable, owner_key: &SourceRootId,
+        parameter: usize, occurrence: &HirOccurrenceId, scope: &AnnotationScope)
+        -> Result<(u32, u32, u32, u32), SnapshotError> {
+        Ok((key(table, TaggedKey::FormalPosition {
+                owner: owner_key.clone(), parameter })?,
+            key(table, TaggedKey::Occurrence(occurrence.clone()))?,
+            key(table, TaggedKey::Owner(owner_key.clone()))?,
+            key(table, TaggedKey::Scope(scope.clone()))?))
+    }
+
+    fn emit_port(table: &mut IdTable, expected: &mut Vec<PermissionImage>,
+        annotation: &SourceAnnotation, parameter: usize, occurrence: &HirOccurrenceId,
+        scope: &AnnotationScope, polarity: Polarity, path: &[FormalPortStep],
+        row: Option<&SourceEffectRow>) -> Result<(), SnapshotError> {
+        let Some(row) = row else { return Ok(()); };
+        if row.variables.len() > 1 { return Err(SnapshotError::Unsupported); }
+        if polarity == Polarity::Negative
+            && !(row.concrete.is_empty() && row.variables.len() == 1
+                || !row.concrete.is_empty() && row.variables.is_empty()) {
+            return Err(SnapshotError::Unsupported);
+        }
+        // Native candidate_formal_effect_port emits exactly this filtered case.
+        if polarity != Polarity::Negative || row.concrete.is_empty() || !row.variables.is_empty() {
+            for name in &row.variables {
+                let _ = key(table, TaggedKey::Symbol { scope: scope.clone(), spelling: name.clone() })?;
+            }
+            return Ok(());
+        }
+        let (formal_position, occurrence_id, owner, scope_id) =
+            context_ids(table, &annotation.owner, parameter, occurrence, scope)?;
+        let source_row = key(table, TaggedKey::Node(row.position.clone()))?;
+        let mut concrete = Vec::new();
+        concrete.try_reserve_exact(row.concrete.len()).map_err(|_| SnapshotError::Exhausted)?;
+        for effect in &row.concrete {
+            concrete.push(key(table, TaggedKey::Effect(effect.clone()))?);
+        }
+        let mut vars = Vec::new();
+        vars.try_reserve_exact(row.variables.len()).map_err(|_| SnapshotError::Exhausted)?;
+        for name in &row.variables {
+            vars.push(key(table, TaggedKey::Symbol { scope: scope.clone(), spelling: name.clone() })?);
+        }
+        // For emitted rows vars is necessarily empty; retain the loop above
+        // explicitly so any filter change remains visible to review.
+        if !vars.is_empty() { return Err(SnapshotError::Unsupported); }
+        expected.try_reserve(1).map_err(|_| SnapshotError::Exhausted)?;
+        expected.push(PermissionImage { parameter, formal_position, occurrence: occurrence_id,
+            owner, scope: scope_id, path: copy_path(path)?, source_row, concrete });
+        Ok(())
+    }
+
+    fn walk_pair(table: &mut IdTable, expected: &mut Vec<PermissionImage>,
+        annotation: &SourceAnnotation, parameter: usize, occurrence: &HirOccurrenceId,
+        scope: &AnnotationScope, ty: &SourceAnnotationType, polarity: Polarity,
+        path: &mut Vec<FormalPortStep>) -> Result<(), SnapshotError> {
+        if !valid_pair(ty.effects.as_ref(), polarity) { return Err(SnapshotError::Unsupported); }
+        walk_value(table, expected, annotation, parameter, occurrence, scope,
+            &ty.value, polarity, path)
+    }
+
+    fn walk_value(table: &mut IdTable, expected: &mut Vec<PermissionImage>,
+        annotation: &SourceAnnotation, parameter: usize, occurrence: &HirOccurrenceId,
+        scope: &AnnotationScope, value: &SourceAnnotationValue, polarity: Polarity,
+        path: &mut Vec<FormalPortStep>) -> Result<(), SnapshotError> {
+        match value {
+            SourceAnnotationValue::Function { argument, result } => {
+                let reverse = if polarity == Polarity::Positive { Polarity::Negative } else { Polarity::Positive };
+                append_step(path, FormalPortStep::Argument, |path| walk_pair(table, expected,
+                    annotation, parameter, occurrence, scope, argument, reverse, path))?;
+                append_step(path, FormalPortStep::Result, |path| walk_pair(table, expected,
+                    annotation, parameter, occurrence, scope, result, polarity, path))?;
+                append_step(path, FormalPortStep::Argument, |path| emit_port(table, expected,
+                    annotation, parameter, occurrence, scope, reverse, path, argument.effects.as_ref()))?;
+                append_step(path, FormalPortStep::Result, |path| emit_port(table, expected,
+                    annotation, parameter, occurrence, scope, polarity, path, result.effects.as_ref()))?;
+                Ok(())
+            }
+            SourceAnnotationValue::Tuple(elements) => {
+                if elements.is_empty() || elements.iter().any(|element| element.effects.is_some()) {
+                    return Err(SnapshotError::Unsupported);
+                }
+                for (index, element) in elements.iter().enumerate() {
+                    append_step(path, FormalPortStep::Element(index), |path| walk_value(table,
+                        expected, annotation, parameter, occurrence, scope, &element.value,
+                        polarity, path))?;
+                }
+                Ok(())
+            }
+            SourceAnnotationValue::Variable(name) => {
+                let _ = key(table, TaggedKey::Symbol { scope: scope.clone(), spelling: name.clone() })?;
+                Ok(())
+            }
+            SourceAnnotationValue::Hole(node) => {
+                let _ = key(table, TaggedKey::Node(node.clone()))?;
+                Ok(())
+            }
+            SourceAnnotationValue::Unit | SourceAnnotationValue::Int
+            | SourceAnnotationValue::Bool | SourceAnnotationValue::Str => Ok(()),
+        }
+    }
+
+    fn source_rows(table: &mut IdTable, annotation: &SourceAnnotation, parameter: usize,
+        occurrence: &HirOccurrenceId, scope: &AnnotationScope)
+        -> Result<Vec<PermissionImage>, SnapshotError> {
+        let _ = key(table, TaggedKey::Owner(annotation.owner.clone()))?;
+        let _ = key(table, TaggedKey::Node(annotation.position.clone()))?;
+        let _ = key(table, TaggedKey::Scope(scope.clone()))?;
+        let _ = key(table, TaggedKey::FormalPosition { owner: annotation.owner.clone(), parameter })?;
+        let _ = key(table, TaggedKey::Occurrence(occurrence.clone()))?;
+        let mut expected = Vec::new();
+        let mut path = Vec::new();
+        // CandidateFormalAnnotation calls candidate_formal_value_pair on the
+        // root value directly. The root row is exclusively FormalEntry input.
+        walk_value(table, &mut expected, annotation, parameter, occurrence, scope,
+            &annotation.ty.value, Polarity::Negative, &mut path)?;
+        Ok(expected)
+    }
+
+    fn image_native(table: &mut IdTable, p: &FormalPermission)
+        -> Result<PermissionImage, SnapshotError> {
+        let (formal_position, occurrence, owner, scope) = context_ids(table,
+            &p.source_owner, p.parameter, &p.occurrence, &p.scope)?;
+        let source_row = key(table, TaggedKey::Node(p.source_row.clone()))?;
+        let mut path = copy_path(&p.path)?;
+        let mut concrete = Vec::new();
+        concrete.try_reserve_exact(p.concrete.len()).map_err(|_| SnapshotError::Exhausted)?;
+        for effect in &p.concrete { concrete.push(key(table, TaggedKey::Effect(effect.clone()))?); }
+        Ok(PermissionImage { parameter: p.parameter, formal_position, occurrence, owner,
+            scope, path: std::mem::take(&mut path), source_row, concrete })
+    }
+
+    fn image_entry(table: &mut IdTable, p: &FormalEntryPermission)
+        -> Result<EntryImage, SnapshotError> {
+        let formal = key(table, TaggedKey::Formal(p.formal.clone()))?;
+        let formal_position = key(table, TaggedKey::FormalPosition {
+            owner: p.source_owner.clone(), parameter: p.parameter })?;
+        let occurrence = key(table, TaggedKey::Occurrence(p.occurrence.clone()))?;
+        let owner = key(table, TaggedKey::Owner(p.source_owner.clone()))?;
+        let scope = key(table, TaggedKey::Scope(p.scope.clone()))?;
+        let annotation_position = key(table, TaggedKey::Node(p.annotation_position.clone()))?;
+        let source_row = key(table, TaggedKey::Node(p.source_row.clone()))?;
+        let mut concrete = Vec::new();
+        concrete.try_reserve_exact(p.concrete.len()).map_err(|_| SnapshotError::Exhausted)?;
+        for effect in &p.concrete { concrete.push(key(table, TaggedKey::Effect(effect.clone()))?); }
+        Ok(EntryImage { registration: p.registration, parameter: p.parameter, formal,
+            formal_position, occurrence, owner, scope, annotation_position, source_row,
+            entry_effect: p.entry_effect, concrete })
+    }
+
+    fn first_difference(expected: &[PermissionImage], actual: &[PermissionImage])
+        -> Option<(usize, &'static str)> {
+        for (i, (e, a)) in expected.iter().zip(actual).enumerate() {
+            if e.parameter != a.parameter { return Some((i, "parameter")); }
+            if e.formal_position != a.formal_position { return Some((i, "formal-position")); }
+            if e.occurrence != a.occurrence { return Some((i, "occurrence")); }
+            if e.owner != a.owner { return Some((i, "owner")); }
+            if e.scope != a.scope { return Some((i, "scope")); }
+            if e.path != a.path { return Some((i, "path")); }
+            if e.source_row != a.source_row { return Some((i, "source-row")); }
+            if e.concrete != a.concrete { return Some((i, "concrete-order-or-multiplicity")); }
+        }
+        (expected.len() != actual.len()).then_some((expected.len().min(actual.len()), "length"))
+    }
+
+    pub(super) fn one_successful_call(session: &mut InferenceSession, annotation: &SourceAnnotation,
+        parameter: usize, occurrence: &HirOccurrenceId, scope: &AnnotationScope)
+        -> Result<Snapshot, SnapshotError> {
+        let mut table = IdTable::default();
+        let expected = source_rows(&mut table, annotation, parameter, occurrence, scope)?;
+        let graph = session.candidate_graph.as_ref().ok_or(SnapshotError::Unsupported)?;
+        let state = &graph.intrusion.effect_algebra;
+        let mut root_entries_before = Vec::new();
+        root_entries_before.try_reserve_exact(state.formal_entry_permissions.len())
+            .map_err(|_| SnapshotError::Exhausted)?;
+        for entry in &state.formal_entry_permissions {
+            root_entries_before.push(image_entry(&mut table, entry)?);
+        }
+        let before = state.formal_permissions.len();
+        // This is the one selected constructor call. An error returns before a
+        // Snapshot exists; route transaction rollback is owned by this caller.
+        session.with_route_transaction(|session| session.candidate_formal_annotation(
+            annotation, parameter, occurrence, scope)).map_err(|_| SnapshotError::Unsupported)?;
+
+        let graph = session.candidate_graph.as_ref().ok_or(SnapshotError::Unsupported)?;
+        let state = &graph.intrusion.effect_algebra;
+        let suffix = state.formal_permissions.get(before..).ok_or(SnapshotError::Unsupported)?;
+        let mut actual = Vec::new();
+        actual.try_reserve_exact(suffix.len()).map_err(|_| SnapshotError::Exhausted)?;
+        for permission in suffix { actual.push(image_native(&mut table, permission)?); }
+        if let Some((index, field)) = first_difference(&expected, &actual) {
+            return Err(SnapshotError::Divergence { index, field });
+        }
+        let mut root_entries_after = Vec::new();
+        root_entries_after.try_reserve_exact(state.formal_entry_permissions.len())
+            .map_err(|_| SnapshotError::Exhausted)?;
+        for entry in &state.formal_entry_permissions {
+            root_entries_after.push(image_entry(&mut table, entry)?);
+        }
+        if root_entries_after != root_entries_before {
+            return Err(SnapshotError::Divergence { index: 0, field: "separate-root-entry-output" });
+        }
+        // Snapshot publication is the final operation. Clone/allocation aborts
+        // are not reported as Exhausted; explicit reservations and u32 width
+        // failures are. No partial Snapshot escapes any returned Err path.
+        Ok(Snapshot { table, root_entries_before, nested_suffix: actual, _complete: Complete })
+    }
+}
```

## Packet receipt

- Role / worker / session: requested `gpt-6-luna/high`; worker `/root/r142_source`; session `EFFECT-PERMISSION-SNAPSHOT-VISIBILITY-FIX/20261102-R142`. Effective observed model/effort: UNKNOWN (no runtime observation available in this worker context).
- Exact lease: only `tasks/agent-loop/inbox/effect-permission-snapshot-visibility-fix-r142-source.md`; no descendants, generated source, or scratch.
- Outcome class: provisional patch-only correction.
- Parent application: sibling fixture's helper result types are now visible at the call boundary; no parent theorem or accepted-source claim follows.
- Checks: frozen R141 handoff byte/hash verification; immutable baseline blob byte/hash verification; in-memory application of both unified-diff hunks with old-line/count matching; corrected target and patch byte/hash calculation. No build, Cargo, tests, Lean/Lake, source materialization, patch application, or environment/scratch creation.
- Mutual TODOs retained from R141: `R140-SOURCE-ACCEPTED-KEY-UNIQUENESS-1` (source owner/Luna); `R140-FORMAL-INDEX-CORRESPONDENCE-1` (source owner/Luna); `R140-RUST-LEAN-ORDER-BRIDGE-1` (proof owner). No TODO is closed by this patch.
- Next related step: the separately leased fresh compiler-referee reviewer checks this frozen patch against the immutable baseline and exact R141 inputs, focusing on B1 and the unchanged integration surface; Luna adjudicates. No further producer write is authorized in this packet.
- Worker state: **STOPPED_WRITING** after this handoff is frozen; no outstanding descendants or scratch.
- Review/integration: frozen candidate awaiting independent review; not approved or commit-ready.

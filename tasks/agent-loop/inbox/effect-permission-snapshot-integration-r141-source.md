# R141 source handoff — same-call comparator in the committed AAR/RRR fixture

Sprint / contract: `EFFECT-PERMISSION-SNAPSHOT-INTEGRATION/20261102-R141`, revision 1, contract SHA-256 `7d74760aaa32e97bcced1c6574871ca5e2b4d8fd975c4db44e04bd2f05e56d40`.
Assignment / handoff revision: `R141-IMMUTABLE-BASELINE-RUST-PATCH`, revision 1.
Parent: `YulangClosure.SourceProblem.InferenceSoundness` and effect-hygiene H; both remain OPEN.

## Frozen inputs and exact patch target

- Baseline commit: `a88e405b1b1c1b99a6c38e6180c977454b2507e6` (`origin/yulang3` per admission).
- Baseline source: `crates/yu-solver/src/candidate_effect.rs`, 301873 bytes, SHA-256 `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01`; immutable Git blob only.
- R140 comparator input: `tasks/agent-loop/inbox/effect-permission-ordered-snapshot-r140-source.md`, 28566 bytes, SHA-256 `3335922fa8b259a1f4dea95bbf72e4ee6db8a99d7dd22fce25b3909e91aa8f56`.
- R140 independent static review: `tasks/agent-loop/history/effect-permission-ordered-snapshot-20261102-r140-review.md`, SHA-256 `d3a66d051dacb2cca835325adaf081865e08987fe253aed56d89f30f2c531624` (PASS for bounded static candidate only).
- R140 Lean candidate SHA-256 `da3baeabd61ff8fd30d078a4481f4a6c62ef5801cdb670f634e4d7c827add985` remains CONSTRUCTED_BUT_UNCHECKED and is not an acceptance premise.
- Patch target `crates/yu-solver/src/candidate_effect.rs`: 318098 bytes, SHA-256 `c476a352bda63d3401913e7142928e005b3602ac252bf8faf175443cd579140b`.
- Unified patch: 17447 bytes. It is reproduced in full below and is not materialized or applied.

The baseline target shape matched the R140 fixture description. I replaced only its first successful `with_route_transaction(... candidate_formal_annotation ...)` expression with the comparator call and appended the R140 module at file end. The remaining test body—including AAR/RRR path order, parameter/occurrence/source-owner/scope equality, distinct source-row assertion, equal concrete family, exact source-row/member pairing, duplicate refusal, both failure injection rollback checks and subsequent capture assertions—remains byte-for-byte unchanged. The existing fixture's duplicate/failure calls remain intentionally present; the comparator makes exactly one selected successful constructor invocation and does not add a second successful invocation.

## One-call, transaction and publication boundary

The fixture creates one `InferenceSession` and extracts one `Action::FormalAnnotation`. The new `one_successful_call` first builds the expected source projection and images preexisting root-entry records. It captures `before = state.formal_permissions.len()` from that session's current `State`, then invokes `candidate_formal_annotation` exactly once inside the same `with_route_transaction` boundary as the original successful fixture call. Constructor failure maps to a comparator error and the transaction wrapper owns rollback. Only after successful return does the helper reacquire the same session graph/state, read `formal_permissions[before..]`, encode those native records through the same identity table, compare ordered fields and compare the separately imaged root-entry vector. It returns `Snapshot` only after all checks pass; no partial Snapshot is returned on any reported error.

The comparator itself does not wrap post-call comparison in a transaction. A divergence after a completed constructor call would fail the fixture while leaving that successful call's state as the native behavior dictates; this is not presented as rollback evidence. Existing test rollback assertions continue to exercise constructor failures inside their preexisting transactions.

## Visibility and type fit

`candidate_effect.rs` imports `SourceAnnotation`, `SourceAnnotationType`, `SourceAnnotationValue`, `SourceEffectId`, `SourceEffectRow`, and `SourceNodeKey` at module scope. The appended `#[cfg(test)]` child module uses `super::*`, so it sees the private constructor and types (`InferenceSession`, `FormalPermission`, `FormalEntryPermission`, `FormalPortStep`, `AnnotationScope`, and `HashMap`) in the baseline module. The existing fixture is a parent-module test; therefore the sole helper it calls is raised to `pub(super)`. Its `Snapshot`/`SnapshotError` internals remain child-private and are only consumed through inferred `Result::expect`. The helper argument types match the fixture's extracted action (`parameter: usize`, `&SourceAnnotation`, `&HirOccurrenceId`, `&AnnotationScope`). No constructor API, production code, imports, test expectation or semantic rule is changed.

## Scope and evidence limits

This is static source/patch evidence only. No Rust source was written or materialized, and no build, Cargo, test, Lean, Lake, toolchain, or environment command ran. No source preflight is added: the selected regression explicitly uses an internal producer and bypasses accepted-source checks. The artifact does not prove accepted-source behavior, SourceNodeKey injectivity, FormalPosition-to-HirParameterId equality, all-source/native identity/order, parent inference soundness, effect hygiene H, A/B, consumer/execution behavior or production readiness. The R140 modeled traversal/filter and equality table are reused as a candidate; no unchecked R140 Lean proposition is used as proof evidence.

## Full patch against the immutable baseline blob

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
+    enum SnapshotError { Exhausted, Unsupported, MissingKey,
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
+    struct Snapshot {
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

- Role / worker / session: requested `gpt-6-luna/high`; worker `/root/r141_source`; session `EFFECT-PERMISSION-SNAPSHOT-INTEGRATION/20261102-R141`. Effective observed model/effort: UNKNOWN (no runtime observation available in this worker context).
- Exact lease / authors: only `tasks/agent-loop/inbox/effect-permission-snapshot-integration-r141-source.md`; author `/root/r141_source`; no descendants; no generated source, scratch or build output.
- Outcome class: provisional source-native-evidence patch candidate, in-memory only; no implementation integration.
- Parent application: the exact two-row AAR/RRR fixture can now compare its source projection to one successful same-call native suffix, retaining all prior focused assertions. Parent theorem and source/native generality remain OPEN.
- Checks: static read of admitted contract/admission, immutable baseline blob, frozen R140 handoff and review; in-memory fixture-shape replacement and SHA/diff construction. No compile/test/check execution was authorized or run. Resource use stayed within the 600-second packet; no CPU/RSS measurement.
- Mutual TODOs: `R140-SOURCE-ACCEPTED-KEY-UNIQUENESS-1` — source owner/Luna, prove accepted-source uniqueness or report supported collision using exact parser/HIR owner paths; `R140-FORMAL-INDEX-CORRESPONDENCE-1` — source owner/Luna, connect native `parameter: usize` to source formal identity or preserve the mismatch using registration/owner maps; `R140-RUST-LEAN-ORDER-BRIDGE-1` — proof owner, instantiate the order/filter bridge without assuming native equality and check the exact AAR/RRR path/context/row/member sequence. These requests do not grant this lane new writes or close any premise.
- Worker state: STOPPED_WRITING after freezing this handoff; no outstanding descendants or scratch.
- Review/integration: frozen patch candidate awaiting the single fresh review leased by Luna; not commit-ready source integration and not independently certified by its author.

## Next related step inside the admitted sprint

The fresh compiler-referee reviewer checks only the frozen handoff and the exact immutable baseline/R140 inputs, without applying or compiling the patch. Luna adjudicates that review and records the sprint outcome. Any accepted-source or theorem work remains with its named owners and authority.

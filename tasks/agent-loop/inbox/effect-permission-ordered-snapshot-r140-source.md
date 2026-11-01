# R140 source handoff — same-call ordered formal-permission suffix

Sprint / contract: `EFFECT-PERMISSION-ORDERED-SNAPSHOT/20261102-R140`, revision 1, SHA-256 `e81ff2ddd7cda47bfb60bc1738e0c5bc3bfce4eb9effc183dd725003b4db06d0`.

Assignment: `R140-SOURCE-AND-ORDERED-SNAPSHOT`, handoff revision 1. Baseline: `4c1d58a646a1101c080659ebfed6ae7862d8aded`. Parent: `YulangClosure.SourceProblem.InferenceSoundness` and effect-hygiene H; both remain OPEN.

## Exact constructor call and append boundary

I used the committed `negative_concrete_formal_permission_recovers_its_shared_port_and_rolls_back` regression fixture in `crates/yu-solver/src/candidate_effect.rs` as the exact invocation trace. It obtains one `Action::FormalAnnotation` for this source:

```text
act io
my bridge (consume: ((int -> [io] ()) -> ()) -> (() -> (int -> [io] ()))) = consume
```

The test passes that action's *same* `annotation`, `parameter`, `occurrence`, and `scope` to one call:

```rust
session.with_route_transaction(|session| {
    session.candidate_formal_annotation(&annotation, parameter, &occurrence, &scope)
}).unwrap();
```

The native constructor creates local `permissions`, recursively visits the annotation, then on success reserves `state.formal_permissions` for the whole local suffix and executes `state.formal_permissions.extend(permissions.drain(..))`. A later `sample_f4_resources` is still inside the method; only its final `Ok(())` is a successful call. The candidate below captures `before = state.formal_permissions.len()` immediately before that call, then reads `state.formal_permissions[before..]` from that same `State` only after `Ok`. If the method returns `Err`, or comparison fails, it returns an error and constructs no completed `Snapshot`.

The committed test asserts the successful suffix has two records in this exact order:

1. `Argument, Argument, Result`, source row at the `io` annotation in the first nested function result (AAR).
2. `Result, Result, Result`, source row at the second nested function result (RRR).

Both records retain the same `SourceEffectId` for `io`, but different source row keys and paths; they are not merged. Existing test assertions also check common `parameter`, `occurrence`, `source_owner`, and `scope`, then pair records in order with the two source rows. The test's source comment calls out that function effect annotations attach to the result child. This is direct committed evidence of a successful same-call suffix for the chosen nested fixture, not a claim that this fixture proves accepted-source uniqueness or the parent theorem.

## Source traversal, filtering, context and R136 bridge

The precise source projection starts at `annotation.ty.value` with `Polarity::Negative` and an empty path. It does **not** treat `annotation.ty.effects` as a nested permission port: the root annotation's entry row belongs to `FormalEntryPermission` and its separate `candidate_formal_entry_annotation` call.

At each Function, it visits argument value with flipped polarity and `Argument` appended; then result value with unchanged polarity and `Result` appended; then the immediate argument effect port at flipped polarity; then the immediate result effect port at unchanged polarity. This is the same order as `candidate_formal_value_pair` and `candidate_formal_effect_port`. It is not preorder over all rows. Tuple children are visited by source index with `Element(index)` appended; the native constructor first rejects an empty tuple or any tuple child whose `effects.is_some()`, then visits the child values in index order.

The source projection also copies the native admission filter exactly. The initial formal call bypasses `candidate_formal_pair` for the root, but every recursive Function argument/result call passes through `candidate_formal_pair` before visiting the child's value. That check rejects any row with more than one variable, and rejects a negative row unless it is either empty concrete with exactly one variable, or nonempty concrete with no variables. At each Function's immediate port, native emission occurs only for a negative row with nonempty concrete members and zero variables. `None`, positive rows, the one-variable negative row, and empty rows emit no `FormalPermission`; unsupported rows fail. Concrete-plus-tail is rejected on nested negative paths, even though the HIR parser can represent one symbolic tail alongside concrete members.

The R136 structural mapping is:

| Native `FormalPermission` | R136 model | Exact projection |
| --- | --- | --- |
| `parameter`, `occurrence`, `source_owner`, `scope` | `Context` / `Metadata` | Same context is attached to every emitted row; it is not inferred from an effect row. |
| `path: Vec<FormalPortStep>` | `Permission.path: List PortStep` | Exact Function steps and tuple index are retained. |
| `source_row` | `Row.position` | Full opaque `SourceNodeKey` is interned as a table key; no injectivity claim is made. |
| `concrete` | `Row.concrete` | Full `SourceEffectId`s are interned in order; duplicate members remain repeated output codes. |
| negative/nonempty/zero-variable emission rule | `emit` | Same predicate: negative, nonempty concrete sequence, no symbolic variables. |
| successful append order | `inventory` / `inventory_exact` | Argument subtree, result subtree, argument effect port, result effect port; tuples preserve index order. |

R136's `ports` deliberately inventories every port; `inventory`/`flatMap emit` filters that order to exactly the emitted records. R140's source traversal uses that inventory/filter bridge, then compares it to the successful native suffix. R136's `EntryPermission` / `constructEntry` remains a distinct root-entry projection, not an element of the nested `FormalPermission` suffix. The selected committed fixture has no root annotation row, so its separate root-entry vector is empty and unchanged across this call. The candidate preserves a nonempty preexisting root-entry inventory separately if one exists in the same State; it never concatenates that vector into the nested suffix.

## In-memory test-only candidate

Suggested target: a `#[cfg(test)]` child module at the end of `crates/yu-solver/src/candidate_effect.rs`, where the existing regression helpers and private fields are in scope. This is a handoff candidate only; no Rust source file was edited. The in-memory wrapper takes the source action values from the existing regression and one existing `InferenceSession`; the `entry_before`/`entry_after` outputs are separate from nested permission suffixes.

The eight key tags remain disjoint. `FormalPosition` is `(SourceRootId, parameter usize)` because `FormalPermission` does not retain a `HirParameterId`; no relation between that index and an independently retained formal identity is asserted. `Formal(HirParameterId)` is used only for the separate root-entry records that actually retain that value. `SourceNodeKey` uses its exact Rust `Eq` (parse brand, green-node identity, start offset), but that equality is **not injective into source syntax occurrences**: committed `source_node_keys_expose_shared_zero_width_ambiguity` explicitly gives distinct zero-width siblings equal keys. That test uses a modified parse and is not a supported-source counterexample; accepted-source uniqueness stays OPEN.

```rust
#[cfg(test)]
mod r140_ordered_snapshot_candidate {
    use super::*;

    #[derive(Clone, Debug, Eq, Hash, PartialEq)]
    enum TaggedKey {
        Owner(SourceRootId),
        Occurrence(HirOccurrenceId),
        Formal(yu_hir::HirParameterId),
        FormalPosition { owner: SourceRootId, parameter: usize },
        Scope(AnnotationScope),
        Node(SourceNodeKey),
        Effect(SourceEffectId),
        Symbol { scope: AnnotationScope, spelling: Box<str> },
    }

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Polarity { Positive, Negative }

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum SnapshotError { Exhausted, Unsupported, MissingKey,
        Divergence { index: usize, field: &'static str } }

    #[derive(Default)]
    struct IdTable { by_key: HashMap<TaggedKey, u32>, by_code: Vec<TaggedKey> }

    impl IdTable {
        fn intern(&mut self, key: TaggedKey) -> Result<u32, SnapshotError> {
            if let Some(&id) = self.by_key.get(&key) { return Ok(id); }
            let id = u32::try_from(self.by_code.len()).map_err(|_| SnapshotError::Exhausted)?;
            self.by_key.try_reserve(1).map_err(|_| SnapshotError::Exhausted)?;
            self.by_code.try_reserve(1).map_err(|_| SnapshotError::Exhausted)?;
            // HashMap uses full Eq after hash selection. Clone allocation for
            // Symbol(Box<str>) is infallible; it is not called Exhausted here.
            self.by_key.insert(key.clone(), id);
            self.by_code.push(key);
            Ok(id)
        }
        fn lookup(&self, key: &TaggedKey) -> Result<u32, SnapshotError> {
            self.by_key.get(key).copied().ok_or(SnapshotError::MissingKey)
        }
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    struct PermissionImage {
        parameter: usize,
        formal_position: u32,
        occurrence: u32,
        owner: u32,
        scope: u32,
        path: Vec<FormalPortStep>,
        source_row: u32,
        concrete: Vec<u32>,
    }

    // Separate record shape: root-entry permission is never a nested port.
    #[derive(Clone, Debug, Eq, PartialEq)]
    struct EntryImage {
        registration: usize,
        parameter: usize,
        formal: u32,
        formal_position: u32,
        occurrence: u32,
        owner: u32,
        scope: u32,
        annotation_position: u32,
        source_row: u32,
        entry_effect: u32, // State-local only; never compared across snapshots.
        concrete: Vec<u32>,
    }

    struct Complete;
    struct Snapshot {
        table: IdTable,
        root_entries_before: Vec<EntryImage>,
        nested_suffix: Vec<PermissionImage>,
        _complete: Complete,
    }

    fn key(table: &mut IdTable, key: TaggedKey) -> Result<u32, SnapshotError> {
        table.intern(key)
    }

    fn copy_path(path: &[FormalPortStep]) -> Result<Vec<FormalPortStep>, SnapshotError> {
        let mut result = Vec::new();
        result.try_reserve_exact(path.len()).map_err(|_| SnapshotError::Exhausted)?;
        result.extend_from_slice(path);
        Ok(result)
    }

    fn append_step<T>(path: &mut Vec<FormalPortStep>, step: FormalPortStep,
        f: impl FnOnce(&mut Vec<FormalPortStep>) -> Result<T, SnapshotError>)
        -> Result<T, SnapshotError> {
        path.try_reserve(1).map_err(|_| SnapshotError::Exhausted)?;
        path.push(step);
        let result = f(path);
        path.pop();
        result
    }

    fn valid_pair(row: Option<&SourceEffectRow>, polarity: Polarity) -> bool {
        row.is_none_or(|row| row.variables.len() <= 1 && match polarity {
            Polarity::Positive => true,
            Polarity::Negative => (row.concrete.is_empty() && row.variables.len() == 1)
                || (!row.concrete.is_empty() && row.variables.is_empty()),
        })
    }

    fn context_ids(table: &mut IdTable, owner_key: &SourceRootId,
        parameter: usize, occurrence: &HirOccurrenceId, scope: &AnnotationScope)
        -> Result<(u32, u32, u32, u32), SnapshotError> {
        Ok((key(table, TaggedKey::FormalPosition {
                owner: owner_key.clone(), parameter })?,
            key(table, TaggedKey::Occurrence(occurrence.clone()))?,
            key(table, TaggedKey::Owner(owner_key.clone()))?,
            key(table, TaggedKey::Scope(scope.clone()))?))
    }

    fn emit_port(table: &mut IdTable, expected: &mut Vec<PermissionImage>,
        annotation: &SourceAnnotation, parameter: usize, occurrence: &HirOccurrenceId,
        scope: &AnnotationScope, polarity: Polarity, path: &[FormalPortStep],
        row: Option<&SourceEffectRow>) -> Result<(), SnapshotError> {
        let Some(row) = row else { return Ok(()); };
        if row.variables.len() > 1 { return Err(SnapshotError::Unsupported); }
        if polarity == Polarity::Negative
            && !(row.concrete.is_empty() && row.variables.len() == 1
                || !row.concrete.is_empty() && row.variables.is_empty()) {
            return Err(SnapshotError::Unsupported);
        }
        // Native candidate_formal_effect_port emits exactly this filtered case.
        if polarity != Polarity::Negative || row.concrete.is_empty() || !row.variables.is_empty() {
            for name in &row.variables {
                let _ = key(table, TaggedKey::Symbol { scope: scope.clone(), spelling: name.clone() })?;
            }
            return Ok(());
        }
        let (formal_position, occurrence_id, owner, scope_id) =
            context_ids(table, &annotation.owner, parameter, occurrence, scope)?;
        let source_row = key(table, TaggedKey::Node(row.position.clone()))?;
        let mut concrete = Vec::new();
        concrete.try_reserve_exact(row.concrete.len()).map_err(|_| SnapshotError::Exhausted)?;
        for effect in &row.concrete {
            concrete.push(key(table, TaggedKey::Effect(effect.clone()))?);
        }
        let mut vars = Vec::new();
        vars.try_reserve_exact(row.variables.len()).map_err(|_| SnapshotError::Exhausted)?;
        for name in &row.variables {
            vars.push(key(table, TaggedKey::Symbol { scope: scope.clone(), spelling: name.clone() })?);
        }
        // For emitted rows vars is necessarily empty; retain the loop above
        // explicitly so any filter change remains visible to review.
        if !vars.is_empty() { return Err(SnapshotError::Unsupported); }
        expected.try_reserve(1).map_err(|_| SnapshotError::Exhausted)?;
        expected.push(PermissionImage { parameter, formal_position, occurrence: occurrence_id,
            owner, scope: scope_id, path: copy_path(path)?, source_row, concrete });
        Ok(())
    }

    fn walk_pair(table: &mut IdTable, expected: &mut Vec<PermissionImage>,
        annotation: &SourceAnnotation, parameter: usize, occurrence: &HirOccurrenceId,
        scope: &AnnotationScope, ty: &SourceAnnotationType, polarity: Polarity,
        path: &mut Vec<FormalPortStep>) -> Result<(), SnapshotError> {
        if !valid_pair(ty.effects.as_ref(), polarity) { return Err(SnapshotError::Unsupported); }
        walk_value(table, expected, annotation, parameter, occurrence, scope,
            &ty.value, polarity, path)
    }

    fn walk_value(table: &mut IdTable, expected: &mut Vec<PermissionImage>,
        annotation: &SourceAnnotation, parameter: usize, occurrence: &HirOccurrenceId,
        scope: &AnnotationScope, value: &SourceAnnotationValue, polarity: Polarity,
        path: &mut Vec<FormalPortStep>) -> Result<(), SnapshotError> {
        match value {
            SourceAnnotationValue::Function { argument, result } => {
                let reverse = if polarity == Polarity::Positive { Polarity::Negative } else { Polarity::Positive };
                append_step(path, FormalPortStep::Argument, |path| walk_pair(table, expected,
                    annotation, parameter, occurrence, scope, argument, reverse, path))?;
                append_step(path, FormalPortStep::Result, |path| walk_pair(table, expected,
                    annotation, parameter, occurrence, scope, result, polarity, path))?;
                append_step(path, FormalPortStep::Argument, |path| emit_port(table, expected,
                    annotation, parameter, occurrence, scope, reverse, path, argument.effects.as_ref()))?;
                append_step(path, FormalPortStep::Result, |path| emit_port(table, expected,
                    annotation, parameter, occurrence, scope, polarity, path, result.effects.as_ref()))?;
                Ok(())
            }
            SourceAnnotationValue::Tuple(elements) => {
                if elements.is_empty() || elements.iter().any(|element| element.effects.is_some()) {
                    return Err(SnapshotError::Unsupported);
                }
                for (index, element) in elements.iter().enumerate() {
                    append_step(path, FormalPortStep::Element(index), |path| walk_value(table,
                        expected, annotation, parameter, occurrence, scope, &element.value,
                        polarity, path))?;
                }
                Ok(())
            }
            SourceAnnotationValue::Variable(name) => {
                let _ = key(table, TaggedKey::Symbol { scope: scope.clone(), spelling: name.clone() })?;
                Ok(())
            }
            SourceAnnotationValue::Hole(node) => {
                let _ = key(table, TaggedKey::Node(node.clone()))?;
                Ok(())
            }
            SourceAnnotationValue::Unit | SourceAnnotationValue::Int
            | SourceAnnotationValue::Bool | SourceAnnotationValue::Str => Ok(()),
        }
    }

    fn source_rows(table: &mut IdTable, annotation: &SourceAnnotation, parameter: usize,
        occurrence: &HirOccurrenceId, scope: &AnnotationScope)
        -> Result<Vec<PermissionImage>, SnapshotError> {
        let _ = key(table, TaggedKey::Owner(annotation.owner.clone()))?;
        let _ = key(table, TaggedKey::Node(annotation.position.clone()))?;
        let _ = key(table, TaggedKey::Scope(scope.clone()))?;
        let _ = key(table, TaggedKey::FormalPosition { owner: annotation.owner.clone(), parameter })?;
        let _ = key(table, TaggedKey::Occurrence(occurrence.clone()))?;
        let mut expected = Vec::new();
        let mut path = Vec::new();
        // CandidateFormalAnnotation calls candidate_formal_value_pair on the
        // root value directly. The root row is exclusively FormalEntry input.
        walk_value(table, &mut expected, annotation, parameter, occurrence, scope,
            &annotation.ty.value, Polarity::Negative, &mut path)?;
        Ok(expected)
    }

    fn image_native(table: &mut IdTable, p: &FormalPermission)
        -> Result<PermissionImage, SnapshotError> {
        let (formal_position, occurrence, owner, scope) = context_ids(table,
            &p.source_owner, p.parameter, &p.occurrence, &p.scope)?;
        let source_row = key(table, TaggedKey::Node(p.source_row.clone()))?;
        let mut path = copy_path(&p.path)?;
        let mut concrete = Vec::new();
        concrete.try_reserve_exact(p.concrete.len()).map_err(|_| SnapshotError::Exhausted)?;
        for effect in &p.concrete { concrete.push(key(table, TaggedKey::Effect(effect.clone()))?); }
        Ok(PermissionImage { parameter: p.parameter, formal_position, occurrence, owner,
            scope, path: std::mem::take(&mut path), source_row, concrete })
    }

    fn image_entry(table: &mut IdTable, p: &FormalEntryPermission)
        -> Result<EntryImage, SnapshotError> {
        let formal = key(table, TaggedKey::Formal(p.formal.clone()))?;
        let formal_position = key(table, TaggedKey::FormalPosition {
            owner: p.source_owner.clone(), parameter: p.parameter })?;
        let occurrence = key(table, TaggedKey::Occurrence(p.occurrence.clone()))?;
        let owner = key(table, TaggedKey::Owner(p.source_owner.clone()))?;
        let scope = key(table, TaggedKey::Scope(p.scope.clone()))?;
        let annotation_position = key(table, TaggedKey::Node(p.annotation_position.clone()))?;
        let source_row = key(table, TaggedKey::Node(p.source_row.clone()))?;
        let mut concrete = Vec::new();
        concrete.try_reserve_exact(p.concrete.len()).map_err(|_| SnapshotError::Exhausted)?;
        for effect in &p.concrete { concrete.push(key(table, TaggedKey::Effect(effect.clone()))?); }
        Ok(EntryImage { registration: p.registration, parameter: p.parameter, formal,
            formal_position, occurrence, owner, scope, annotation_position, source_row,
            entry_effect: p.entry_effect, concrete })
    }

    fn first_difference(expected: &[PermissionImage], actual: &[PermissionImage])
        -> Option<(usize, &'static str)> {
        for (i, (e, a)) in expected.iter().zip(actual).enumerate() {
            if e.parameter != a.parameter { return Some((i, "parameter")); }
            if e.formal_position != a.formal_position { return Some((i, "formal-position")); }
            if e.occurrence != a.occurrence { return Some((i, "occurrence")); }
            if e.owner != a.owner { return Some((i, "owner")); }
            if e.scope != a.scope { return Some((i, "scope")); }
            if e.path != a.path { return Some((i, "path")); }
            if e.source_row != a.source_row { return Some((i, "source-row")); }
            if e.concrete != a.concrete { return Some((i, "concrete-order-or-multiplicity")); }
        }
        (expected.len() != actual.len()).then_some((expected.len().min(actual.len()), "length"))
    }

    fn one_successful_call(session: &mut InferenceSession, annotation: &SourceAnnotation,
        parameter: usize, occurrence: &HirOccurrenceId, scope: &AnnotationScope)
        -> Result<Snapshot, SnapshotError> {
        let mut table = IdTable::default();
        let expected = source_rows(&mut table, annotation, parameter, occurrence, scope)?;
        let graph = session.candidate_graph.as_ref().ok_or(SnapshotError::Unsupported)?;
        let state = &graph.intrusion.effect_algebra;
        let mut root_entries_before = Vec::new();
        root_entries_before.try_reserve_exact(state.formal_entry_permissions.len())
            .map_err(|_| SnapshotError::Exhausted)?;
        for entry in &state.formal_entry_permissions {
            root_entries_before.push(image_entry(&mut table, entry)?);
        }
        let before = state.formal_permissions.len();
        // This is the one selected constructor call. An error returns before a
        // Snapshot exists; route transaction rollback is owned by this caller.
        session.with_route_transaction(|session| session.candidate_formal_annotation(
            annotation, parameter, occurrence, scope)).map_err(|_| SnapshotError::Unsupported)?;

        let graph = session.candidate_graph.as_ref().ok_or(SnapshotError::Unsupported)?;
        let state = &graph.intrusion.effect_algebra;
        let suffix = state.formal_permissions.get(before..).ok_or(SnapshotError::Unsupported)?;
        let mut actual = Vec::new();
        actual.try_reserve_exact(suffix.len()).map_err(|_| SnapshotError::Exhausted)?;
        for permission in suffix { actual.push(image_native(&mut table, permission)?); }
        if let Some((index, field)) = first_difference(&expected, &actual) {
            return Err(SnapshotError::Divergence { index, field });
        }
        let mut root_entries_after = Vec::new();
        root_entries_after.try_reserve_exact(state.formal_entry_permissions.len())
            .map_err(|_| SnapshotError::Exhausted)?;
        for entry in &state.formal_entry_permissions {
            root_entries_after.push(image_entry(&mut table, entry)?);
        }
        if root_entries_after != root_entries_before {
            return Err(SnapshotError::Divergence { index: 0, field: "separate-root-entry-output" });
        }
        // Snapshot publication is the final operation. Clone/allocation aborts
        // are not reported as Exhausted; explicit reservations and u32 width
        // failures are. No partial Snapshot escapes any returned Err path.
        Ok(Snapshot { table, root_entries_before, nested_suffix: actual, _complete: Complete })
    }
}
```

The candidate is statically complete enough to compare the exact fields retained by this constructor. It makes no claim that every allocation is fallible: table key cloning of `Symbol(Box<str>)` and any remaining derived `Clone` allocation can abort; only explicit `try_reserve` and checked `u32` conversion map to `Exhausted`. No returned error exposes the local table or partial output. A process abort is not relabeled as `EncodeError`/`SnapshotError`.

## Review corrections, dependencies and limits

- R139 review SHA-256 `f40a05d3c791cdf4d10c98f283938e9347a5f1dbc68e6943d70a956c86d6b508` is applied: this handoff makes no `SourceNodeKey` injectivity claim; it limits fallible-allocation language to explicit reservations and checked widths; it uses the current R138 outcome digest `2cfe94f5dd822c4df4619fa194186c2537393c1c3ed8340e244f56b6e93ac480`.
- R138 remains only the audited failed-session discard/publication envelope. It does not prove this constructor call's source/native order equality or transaction rollback for every internal observer.
- R139's proof remains `CONSTRUCTED_BUT_UNCHECKED`; its abstract table result is not source/native evidence.
- R137's structural HIR-decoder record is named by R140 contract at SHA-256 `82fd775010eb1b865928510bed1d34d282c0d46768f6ee93054ca0d670748231`, but that path is not present in the pinned baseline tree, so I did not read any working-tree copy. The R136 committed structural inventory is the order/filter bridge used here.

| Immutable baseline dependency | Git blob | Bytes |
| --- | --- | ---: |
| `crates/yu-solver/src/candidate_effect.rs` | `18a4cafb4a1bb6466686d82aa825e28318f91a72` | 301,873 |
| `crates/yu-solver/src/candidate_source.rs` | `b43f37f4cca246a072b73329aed84e89aef4ebe1` | 212,732 |
| `crates/yu-hir/src/module/source_annotation.rs` | `bd65e9f50e63cdbab53ee3b3c8f25958813b1ef5` | 35,724 |
| `crates/yu-syntax/src/full_parse.rs` | `9e07c1546d36561d2a24192ced2c7ebbffd6d798` | 36,778 |
| `FormalPermissionConstructorR136.lean` | `2265896c38a8febf7fd41d10c9a49f9f4a1bc340` | 10,356 |

Actual `Eq` correspondence is separate evidence. `SourceNodeKey`'s equality retains parse brand, green pointer and offset, but same-key equality does not show one source constructor per syntax occurrence. The selected test's own `assert_ne!` for its two row keys is local evidence only. Accepted-source uniqueness, all-source owner coverage, source-to-Lean instantiation, FormalPosition-to-HirParameterId correspondence, actual consumer/arrival/copy/capture, effect hygiene H, `SourceProblem.InferenceSoundness`, A/B and production remain OPEN.

## Frozen packet receipt

- Role / worker / session: Luna/high source lane requested; worker `/root/r139_source`; session R140. Requested model/effort `gpt-6-luna/high`; observed model/effort `UNKNOWN` in available state evidence; no separate runtime launch receipt was provided.
- Exact lease / authors: only `tasks/agent-loop/inbox/effect-permission-ordered-snapshot-r140-source.md`; author `/root/r139_source`; no descendants.
- Outcome class: source-native-evidence candidate, provisional. It is a static in-memory candidate, not an implementation patch or theorem.
- Parent application: a source traversal can be compared to one exact same-call successful native suffix in the candidate; the existing committed fixture already exhibits the two-row sequence. Parent source/native equality and all consumers remain unproved.
- Source -> constraints -> propagation -> consumer/native path: this packet ends at the constructor's retained `FormalPermission` vector. It does not change constraints, propagation, consumers, native execution or solver admission.
- Checks/resources: immutable baseline blob inspection and prior frozen evidence only; no tests, build, Cargo, Lean, checker, Git mutation, scratch or generated files. Within the 900-second packet.
- Next related step: independent R140 review against these exact source blobs and the proof lane's matching order/filter model. Stop on the first unequal row field; keep source accepted-domain uniqueness OPEN.
- Mutual TODOs: `R140-SOURCE-ACCEPTED-KEY-UNIQUENESS-1` — Luna/source owner, original parent; prove accepted-source uniqueness needed to interpret SourceNodeKey keys, using exact parser/HIR owner paths; output requires a separately leased source trace; falsifier is a supported distinct-source collision. `R140-FORMAL-INDEX-CORRESPONDENCE-1` — Luna/source owner, same parent; connect native `parameter: usize` to a source formal identity or preserve the mismatch; use the exact registration and owner maps; falsifier is any nonmatching owner/index. `R140-RUST-LEAN-ORDER-BRIDGE-1` — proof lane, same parent; map the exact AAR/RRR order and filter without assuming native equality; output its already leased proof handoff; falsifier is missing polarity, path, context, row, member order or multiplicity.
- Worker state: STOPPED_WRITING; no outstanding descendants, generated outputs or scratch leases.
- Integration/review: pending Luna intake and the exact independent R140 review; no commit-ready source change.

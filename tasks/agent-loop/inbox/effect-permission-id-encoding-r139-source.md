# R139 source handoff — snapshot-local identity table

Contract: `tasks/agent-loop/sprints/effect-permission-id-encoding-20261102-r139.md`, SHA-256 `717acc2e9c3bd70f19a0b74854802952ab0eea6ccf62fab104c5075997ee4afb`.

Baseline: `4c1d58a646a1101c080659ebfed6ae7862d8aded`. This handoff is based only on immutable blobs from that commit. No Rust file was changed, and no build, test, Lean check, or Git mutation was run.

## Finding

A test-only table can retain the identity-bearing Rust values and use their complete `Eq` without reducing identities to offsets, ordinals, strings, debug output, or pointers chosen by this table. `HashMap` hashes are only bucket selectors; key lookup still checks `Eq`. Cloning the identity values preserves the custom equality of their cloned `Arc` brands.

The applicable concrete source fields are:

| Table identity | Exact source expression | Equality carried by the source type |
| --- | --- | --- |
| Owner | `annotation.owner`; `permission.source_owner` | `SourceRootId` tags Definition / Expression / Member. Definition compares artifact `Arc::ptr_eq` plus `DefId`; expression compares its `HirOccurrenceId`; member compares artifact pointer, `ModuleId`, declaration and member `SourceNodeKey`s, and `SourceMemberKind`. |
| Occurrence | `permission.occurrence` | `HirOccurrenceId`: ordinal **and** `Arc::ptr_eq` on its HIR artifact token. |
| Formal ID | `entry.formal` | `HirParameterId`: full `SourceRootId` and parameter ordinal. The existing entry record also has a separate `entry.parameter: usize`; retain it as `FormalPosition { owner, parameter }`, not as a global ordinal. |
| Annotation scope | `scope` / `entry.scope` | `AnnotationScope` has disjoint Definition / Source / Local / Expression variants. Payload Eq is the full root/local identity or `LocalSourceIndex` (root plus local ordinal). |
| Source node | `annotation.position`, each `SourceEffectRow.position`, `permission.source_row`, `entry.annotation_position` | `SourceNodeKey`: parse-brand `Arc::ptr_eq`, green-node pointer identity, and start offset. It distinguishes same-offset nodes and equal-looking nodes from separately branded parses. |
| Effect declaration | each `row.concrete[i]`, `permission.concrete[i]`, `entry.concrete[i]` | `SourceEffectId`: `ModuleId` plus full declaration `SourceNodeKey`. The declaration key is not a declaration ordinal or spelling. |
| Annotation symbol | each `SourceAnnotationValue::Variable(name)` and `SourceEffectRow.variables[i]` | Use `Symbol { scope, spelling }`; spelling alone is not a table key. This matches the source's scoped variable identity in `annotation_values` / `annotation_effects`. |

The source defines `Eq` for each value above (including manual full `Eq` where artifact identity uses pointer brands). `SourceAnnotation`, `SourceAnnotationType`, and `SourceAnnotationValue` themselves do not derive `Eq`; that is not a blocker because the table encodes only their explicit identity fields and recursively visits their constructors. `SourceNodeKey` is intentionally opaque but its committed implementation gives complete `Eq`; its Debug implementation is deliberately non-injective and must not be used as a key.

`FormalPermission` does **not** retain a `HirParameterId`; its source representation is the pair `(source_owner, parameter)` plus its occurrence. The candidate preserves exactly that available identity as `FormalPosition`. `FormalEntryPermission` retains both the pair and `formal`, so it encodes both and does not assert the relationship between them. Recovering/validating that relation is outside this table-only packet.

## Candidate patch

Suggested exact insertion target: test-only child module at the end of `crates/yu-solver/src/candidate_effect.rs`, inside the existing module so private `State`, `AnnotationScope`, `FormalPermission`, and `FormalEntryPermission` are in scope. This is a candidate only; no source edit is authorized by R139.

Target blob at the baseline: `crates/yu-solver/src/candidate_effect.rs`, Git blob `18a4cafb4a1bb6466686d82aa825e28318f91a72`, 301,873 bytes. The handoff output itself is the only written path; its final SHA-256/size are reported below.

Immutable input blob manifest (all from the pinned baseline):

| Path | Git blob | Bytes |
| --- | --- | ---: |
| `crates/yu-hir/src/module.rs` | `9e28e05a7ab31db09accebc8925b8e4bbab8472e` | 222,888 |
| `crates/yu-hir/src/module/source_annotation.rs` | `bd65e9f50e63cdbab53ee3b3c8f25958813b1ef5` | 35,724 |
| `crates/yu-syntax/src/full_parse.rs` | `9e07c1546d36561d2a24192ced2c7ebbffd6d798` | 36,778 |
| `crates/yu-solver/src/candidate_effect.rs` | `18a4cafb4a1bb6466686d82aa825e28318f91a72` | 301,873 |
| `crates/yu-solver/src/candidate_source.rs` | `b43f37f4cca246a072b73329aed84e89aef4ebe1` | 212,732 |

```rust
#[cfg(test)]
mod r139_identity_snapshot_candidate {
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

    #[derive(Debug)]
    enum EncodeError { Exhausted, MissingKey }

    #[derive(Default)]
    struct IdTable {
        by_key: HashMap<TaggedKey, u32>,
        by_code: Vec<TaggedKey>,
    }

    impl IdTable {
        fn intern(&mut self, key: TaggedKey) -> Result<u32, EncodeError> {
            if let Some(&code) = self.by_key.get(&key) { return Ok(code); }
            let code = u32::try_from(self.by_code.len()).map_err(|_| EncodeError::Exhausted)?;
            // Reserve both sides before publishing either side. The local table
            // is not observable until the complete Snapshot is returned.
            self.by_key.try_reserve(1).map_err(|_| EncodeError::Exhausted)?;
            self.by_code.try_reserve(1).map_err(|_| EncodeError::Exhausted)?;
            self.by_key.insert(key.clone(), code);
            self.by_code.push(key);
            Ok(code)
        }

        fn lookup(&self, key: &TaggedKey) -> Result<u32, EncodeError> {
            self.by_key.get(key).copied().ok_or(EncodeError::MissingKey)
        }
    }

    #[derive(Debug)]
    struct EncodedType {
        owner: u32,
        annotation: u32,
        nodes: Vec<u32>,
        symbols: Vec<u32>,
        effects_in_source_order: Vec<u32>,
    }

    #[derive(Debug)]
    struct EncodedPermission {
        owner: u32,
        occurrence: u32,
        formal: Option<u32>,
        formal_position: u32,
        scope: u32,
        nodes: Vec<u32>,
        effects_in_source_order: Vec<u32>,
    }

    // Private construction result: callers get it only after all source and
    // retained-native rows have encoded successfully. It is not solver input.
    struct Snapshot {
        table: IdTable,
        source: Vec<EncodedType>,
        native: Vec<EncodedPermission>,
        _complete: Complete,
    }
    struct Complete;

    fn id(table: &mut IdTable, key: TaggedKey) -> Result<u32, EncodeError> {
        table.intern(key)
    }

    fn encode_type(
        table: &mut IdTable,
        annotation: &SourceAnnotation,
        scope: &AnnotationScope,
    ) -> Result<EncodedType, EncodeError> {
        let owner = id(table, TaggedKey::Owner(annotation.owner.clone()))?;
        let annotation_id = id(table, TaggedKey::Scope(scope.clone()))?;
        let mut out = EncodedType { owner, annotation: annotation_id,
            nodes: Vec::new(), symbols: Vec::new(), effects_in_source_order: Vec::new() };
        fn walk(table: &mut IdTable, scope: &AnnotationScope, ty: &SourceAnnotationType,
                out: &mut EncodedType) -> Result<(), EncodeError> {
            if let Some(row) = &ty.effects {
                out.nodes.push(id(table, TaggedKey::Node(row.position.clone()))?);
                for effect in &row.concrete {
                    // Push every occurrence in order, including repeated IDs.
                    out.effects_in_source_order.push(id(table, TaggedKey::Effect(effect.clone()))?);
                }
                for name in &row.variables {
                    out.symbols.push(id(table, TaggedKey::Symbol {
                        scope: scope.clone(), spelling: name.clone() })?);
                }
            }
            match &ty.value {
                SourceAnnotationValue::Hole(position) =>
                    out.nodes.push(id(table, TaggedKey::Node(position.clone()))?),
                SourceAnnotationValue::Variable(name) =>
                    out.symbols.push(id(table, TaggedKey::Symbol {
                        scope: scope.clone(), spelling: name.clone() })?),
                SourceAnnotationValue::Tuple(elements) => {
                    for element in elements { walk(table, scope, element, out)?; }
                }
                SourceAnnotationValue::Function { argument, result } => {
                    walk(table, scope, argument, out)?;
                    walk(table, scope, result, out)?;
                }
                SourceAnnotationValue::Unit | SourceAnnotationValue::Int
                | SourceAnnotationValue::Bool | SourceAnnotationValue::Str => {}
            }
            Ok(())
        }
        out.nodes.push(id(table, TaggedKey::Node(annotation.position.clone()))?);
        walk(table, scope, &annotation.ty, &mut out)?;
        Ok(out)
    }

    fn encode_native(
        table: &mut IdTable,
        permissions: &[FormalPermission],
        entries: &[FormalEntryPermission],
    ) -> Result<Vec<EncodedPermission>, EncodeError> {
        let mut out = Vec::new();
        out.try_reserve(permissions.len().checked_add(entries.len()).ok_or(EncodeError::Exhausted)?)
            .map_err(|_| EncodeError::Exhausted)?;
        for p in permissions {
            let owner = id(table, TaggedKey::Owner(p.source_owner.clone()))?;
            let occurrence = id(table, TaggedKey::Occurrence(p.occurrence.clone()))?;
            let formal_position = id(table, TaggedKey::FormalPosition {
                owner: p.source_owner.clone(), parameter: p.parameter })?;
            let scope = id(table, TaggedKey::Scope(p.scope.clone()))?;
            let node = id(table, TaggedKey::Node(p.source_row.clone()))?;
            let mut nodes = Vec::new();
            nodes.try_reserve_exact(1).map_err(|_| EncodeError::Exhausted)?;
            nodes.push(node);
            let mut effects = Vec::new();
            effects.try_reserve(p.concrete.len()).map_err(|_| EncodeError::Exhausted)?;
            for effect in &p.concrete {
                effects.push(id(table, TaggedKey::Effect(effect.clone()))?);
            }
            out.push(EncodedPermission { owner, occurrence, formal: None,
                formal_position, scope, nodes, effects_in_source_order: effects });
        }
        for p in entries {
            let owner = id(table, TaggedKey::Owner(p.source_owner.clone()))?;
            let occurrence = id(table, TaggedKey::Occurrence(p.occurrence.clone()))?;
            let formal = id(table, TaggedKey::Formal(p.formal.clone()))?;
            let formal_position = id(table, TaggedKey::FormalPosition {
                owner: p.source_owner.clone(), parameter: p.parameter })?;
            let scope = id(table, TaggedKey::Scope(p.scope.clone()))?;
            let annotation_node = id(table, TaggedKey::Node(p.annotation_position.clone()))?;
            let row_node = id(table, TaggedKey::Node(p.source_row.clone()))?;
            let mut nodes = Vec::new();
            nodes.try_reserve_exact(2).map_err(|_| EncodeError::Exhausted)?;
            nodes.extend([annotation_node, row_node]);
            let mut effects = Vec::new();
            effects.try_reserve(p.concrete.len()).map_err(|_| EncodeError::Exhausted)?;
            for effect in &p.concrete {
                effects.push(id(table, TaggedKey::Effect(effect.clone()))?);
            }
            out.push(EncodedPermission { owner, occurrence, formal: Some(formal),
                formal_position, scope, nodes,
                effects_in_source_order: effects });
        }
        Ok(out)
    }

    fn build_snapshot(
        source: &[(&SourceAnnotation, &AnnotationScope)],
        native: &State,
    ) -> Result<Snapshot, EncodeError> {
        let mut table = IdTable::default();
        let mut encoded_source = Vec::new();
        encoded_source.try_reserve(source.len()).map_err(|_| EncodeError::Exhausted)?;
        for (annotation, scope) in source {
            encoded_source.push(encode_type(&mut table, annotation, scope)?);
        }
        let encoded_native = encode_native(&mut table,
            &native.formal_permissions, &native.formal_entry_permissions)?;
        // No intermediate table or output vector escaped. The completion
        // marker is created only after every reservation, lookup and row pass.
        Ok(Snapshot { table, source: encoded_source, native: encoded_native,
            _complete: Complete })
    }
}
```

Both source annotations and native retained permissions call `IdTable::intern` on the same table instance in `build_snapshot`; concrete members are traversed and appended one by one, never deduplicated in the output vectors. Equal concrete keys reuse a numeric code, while each occurrence remains present in its source order. Different `Snapshot` values own independent tables, so codes are explicitly snapshot-local and must never be compared across snapshots. A follow-up use of `lookup` that misses returns `MissingKey`; it cannot produce a snapshot. Every `try_reserve`, code-width check, recursive walk, and row encoding error returns before `Snapshot` construction; all partial state is stack-local and dropped.

For source signatures, pass the scope already paired with the annotation by `SignatureContext::Annotation(annotation, scope)`; for standalone source owners use the established `AnnotationScope::for_source(annotation.owner.clone())`. The candidate does not rederive scope from a spelling or position.

The candidate purposefully does not encode solver handles (`registration`, `entry_effect`, view indices, `FormalPortStep`, or `State` brands): those are native execution bookkeeping, not any of the requested source identities. It does not call solver admission, add a consumer, or assert effect hygiene. The returned test value has no public API and no path into solver state.

## Prior evidence reused and limits

- R138 outcome `tasks/agent-loop/history/effect-permission-formal-publication-envelope-20261102-r138-outcome.md` (SHA-256 `080b15b31f4231611143279e6604f88285dd0ce29940fd28fd8f728e06bacd64`) closes only the audited failed-session discard/publication envelope. It explicitly leaves source identity encoding, native inventory equality, effect hygiene, and production OPEN. Reused as a boundary, not treated as identity proof.
- `module.rs` defines artifact-branded `DefinitionRootId`, `SourceMemberRootId`, `SourceRootId`, `HirLocalId`, `HirParameterId`, and `HirOccurrenceId` equality. In particular the occurrence ordinal is paired with its artifact pointer; it is not used alone.
- `full_parse.rs` implements `SourceNodeKey` equality with parse brand, green identity, and start. Existing `source_node_keys_preserve_clone_brand_and_reject_reused_green_root` and `source_node_keys_expose_shared_zero_width_ambiguity` fixtures support retaining the whole key; they reject offset-only identity. The HIR `occurrence_ids_remain_distinct_for_equal_zero_width_error_ranges` fixture likewise rejects range-only occurrence identity.
- `source_annotation.rs` carries annotation and row positions and concrete `SourceEffectId`s as source-owned values. Its recursive value representation has no whole-tree `Eq`, so this proposal never derives an ID from Debug or serialized output.
- `candidate_effect.rs` retains `FormalPermission` and `FormalEntryPermission` fields described above; its existing scoped maps use `(AnnotationScope, SourceNodeKey)` and `(AnnotationScope, Box<str>)`, consistent with the proposed scoped symbol identity. Source signature handling carries scope in `SignatureContext::Annotation(annotation, scope)`. `candidate_source.rs` retains source annotation actions and their source owner/occurrence; it supplies no evidence that numeric codes are currently used for admission.

No equality was inferred from tests alone; Rust source implementations provide the Eq premise. The table demonstrates only a candidate representation. Actual source/native inventory equality, source-to-Lean correspondence, parser/owner closure, parent `SourceProblem.InferenceSoundness`, effect-hygiene H, consumer/arrival/Catch behavior, and production approval remain OPEN. The table's completion marker is provisional test-only evidence, not theorem closure or a cutover authorization.

## Packet receipt

- Sprint / contract revision: `EFFECT-PERMISSION-ID-ENCODING/20261102-R139`, contract SHA-256 `717acc2e9c3bd70f19a0b74854802952ab0eea6ccf62fab104c5075997ee4afb`.
- Assignment / handoff revision: `R139-SOURCE-AND-CONSTRUCTIVE-TABLE-PROOF`, revision 1.
- Parent gate: `SourceProblem.InferenceSoundness` and effect-hygiene H; both remain OPEN.
- Baseline and direct dependencies: `4c1d58a646a1101c080659ebfed6ae7862d8aded`; relevant immutable blobs and hashes/sizes are recorded above for module, source annotation, full parse, candidate effect and candidate source.
- Role / worker / session: Luna/high source lane requested; worker identity `/root/r139_source`; session `R139`; requested model/effort `gpt-6-luna/high`, observed model/effort `UNKNOWN` from the available state receipt. No separate launch receipt was available in the assigned inputs.
- Exact write lease: only this inbox path. Authors/contributors: `/root/r139_source`; no descendants.
- Outcome class: source-native-evidence candidate, provisional and test-only.
- Parent application: equal retained keys can be represented by one snapshot-local code table; no parent theorem follows. Exact unresolved premise: independently establish the source/native identity correspondence and apply it to the original source-owner theorem. Owner: Luna/proof lane under R139; no source production authority is transferred.
- Source to constraints to execution: source `SourceAnnotation` identity fields and native `FormalPermission` / `FormalEntryPermission` fields can be encoded through the same table. No constraints, propagation, consumer, native execution, or solver admission path is changed.
- Artifact target: proposed test-only child module in `crates/yu-solver/src/candidate_effect.rs`, pinned blob `18a4cafb4a1bb6466686d82aa825e28318f91a72` (301,873 bytes). No implementation patch or review snapshot exists.
- Checks / resources: immutable blob and prior-outcome inspection only; no build/tests/Lean. No scratch/generated paths. Within the 900-second packet; no heavy process.
- Next related in-envelope step: source lane is complete; Luna can compare this exact mapping against the proof lane's finite tagged table. Keep source/native equality and production gates OPEN.
- Mutual TODOs (requests only; no authority or extra lease):
  - `R139-TABLE-PROPERTIES-1`, proof lane, original R139 parent gate: prove table-only same-key lookup, distinct tagged-key codes, append preservation, and failed-construction nonpublication from the definition; inputs are this handoff and R139 contract; output is the already leased R139 proof handoff; falsifier is any claim needing Rust Eq correspondence or native-output equality as an axiom.
  - `R139-SOURCE-NATIVE-COVERAGE-1`, Luna/source owner, original `SourceProblem.InferenceSoundness`: establish that the selected source annotation inventory and all intended native retained records traverse these same encoders in the exact caller; inputs are pinned source blobs and this candidate; output is an owner-path source trace under Luna's existing authority; falsifier is an identity-bearing constructor/consumer omitted from the traversal or codes compared across snapshots.
  - `R139-FORMAL-POSITION-CORRESPONDENCE-1`, Luna/source owner, original formal permission owner path: establish or leave explicitly open the relation between `FormalPermission.parameter: usize` and source `HirParameterId`; this handoff does not infer it. Inputs are the source owner and ordered formal registration paths; output is a source-owner equation; falsifier is a disagreement between stored index, formal identity, and owner.
- Worker state / stop: STOPPED_WRITING; no descendants or scratch leases.
- Commit/integration: pending Luna intake and the frozen independent review assigned by the sprint.

//! Immutable full-fixity operator definitions and chasa trie traversal.

use std::{cmp::Ordering, collections::BTreeMap, ops::Range};

use chasa::parser::trie::TrieState as ChasaTrieState;

use crate::{BindingPower as HeaderBindingPower, HeaderOperator, SyntaxDependencySlot};

pub(crate) use crate::OperatorFixity;

/// A parse-session operator table compiled before full parsing starts.
#[derive(Debug)]
pub struct OperatorTable {
    entries: Vec<OperatorEntry>,
    sites: Vec<OperatorFixitySites>,
    trie: OperatorTrie,
}

impl OperatorTable {
    pub fn empty() -> Self {
        Self {
            entries: Vec::new(),
            sites: Vec::new(),
            trie: OperatorTrie::new(),
        }
    }

    pub(crate) fn from_declarations(
        declarations: impl IntoIterator<Item = OperatorDeclaration>,
    ) -> Result<Self, OperatorTableBuildError> {
        Ok(OperatorTableBuilder::from_declarations(declarations)?.build())
    }

    /// Compiles declaration-local header facts into spelling-level fixities.
    pub(crate) fn from_header_operators(
        operators: impl IntoIterator<Item = HeaderOperator>,
    ) -> Result<Self, OperatorTableBuildError> {
        Self::from_declarations(
            operators
                .into_iter()
                .map(OperatorDeclaration::from_header_operator),
        )
    }

    pub(crate) fn get(&self, spelling: &str) -> Option<&OperatorEntry> {
        let entry = self.trie.find(spelling)?;
        self.entries.get(entry)
    }

    pub(crate) fn state(&self) -> OperatorTrieState<'_> {
        OperatorTrieState {
            table: self,
            node: Some(0),
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub(crate) fn entries_with_sites(
        &self,
    ) -> impl ExactSizeIterator<Item = (&OperatorEntry, &OperatorFixitySites)> {
        debug_assert_eq!(self.entries.len(), self.sites.len());
        self.entries.iter().zip(&self.sites)
    }
}

impl Default for OperatorTable {
    fn default() -> Self {
        Self::empty()
    }
}

/// One declaration input; repeated spellings merge non-conflicting fixities.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct OperatorDeclaration {
    spelling: Box<str>,
    fixities: OperatorFixities,
    origin: OperatorOrigin,
    range: Range<usize>,
}

impl OperatorDeclaration {
    pub(crate) fn new(spelling: impl Into<Box<str>>, fixities: OperatorFixities) -> Self {
        Self::at_range(spelling, fixities, 0..0)
    }

    pub(crate) fn at_range(
        spelling: impl Into<Box<str>>,
        fixities: OperatorFixities,
        range: Range<usize>,
    ) -> Self {
        Self {
            spelling: spelling.into(),
            fixities,
            origin: OperatorOrigin::Local,
            range,
        }
    }

    pub(crate) fn imported_at_range(
        spelling: impl Into<Box<str>>,
        fixities: OperatorFixities,
        dependency: SyntaxDependencySlot,
        range: Range<usize>,
    ) -> Self {
        Self {
            spelling: spelling.into(),
            fixities,
            origin: OperatorOrigin::Imported(dependency),
            range,
        }
    }

    fn from_header_operator(header: HeaderOperator) -> Self {
        let fixities = match header.fixity() {
            OperatorFixity::Prefix => {
                OperatorFixities::new().with_prefix(binding_power_from_header(
                    header
                        .binding_power()
                        .right()
                        .expect("prefix header facts require a right binding power"),
                ))
            }
            OperatorFixity::Infix => OperatorFixities::new().with_infix(
                binding_power_from_header(
                    header
                        .binding_power()
                        .left()
                        .expect("infix header facts require a left binding power"),
                ),
                binding_power_from_header(
                    header
                        .binding_power()
                        .right()
                        .expect("infix header facts require a right binding power"),
                ),
            ),
            OperatorFixity::Suffix => {
                OperatorFixities::new().with_suffix(binding_power_from_header(
                    header
                        .binding_power()
                        .left()
                        .expect("suffix header facts require a left binding power"),
                ))
            }
            OperatorFixity::Nullfix => OperatorFixities::new().with_nullfix(),
        };
        Self::at_range(header.name(), fixities, header.range().clone())
    }
}

/// The source relative to a full parse where an operator declaration originated.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum OperatorOrigin {
    Local,
    Imported(SyntaxDependencySlot),
}

/// Cold metadata identifying the declaration that supplied one fixity capability.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct OperatorDeclarationSite {
    origin: OperatorOrigin,
    range: Range<usize>,
}

impl OperatorDeclarationSite {
    fn from_declaration(declaration: &OperatorDeclaration) -> Self {
        Self {
            origin: declaration.origin,
            range: declaration.range.clone(),
        }
    }

    pub(crate) fn origin(&self) -> OperatorOrigin {
        self.origin
    }

    pub(crate) fn range(&self) -> &Range<usize> {
        &self.range
    }
}

/// One declaration site per present fixity in an operator spelling entry.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct OperatorFixitySites {
    prefix: Option<OperatorDeclarationSite>,
    infix: Option<OperatorDeclarationSite>,
    suffix: Option<OperatorDeclarationSite>,
    nullfix: Option<OperatorDeclarationSite>,
}

impl OperatorFixitySites {
    pub(crate) fn site(&self, fixity: OperatorFixity) -> Option<&OperatorDeclarationSite> {
        match fixity {
            OperatorFixity::Prefix => self.prefix.as_ref(),
            OperatorFixity::Infix => self.infix.as_ref(),
            OperatorFixity::Suffix => self.suffix.as_ref(),
            OperatorFixity::Nullfix => self.nullfix.as_ref(),
        }
    }
}

fn binding_power_from_header(power: &HeaderBindingPower) -> BindingPower {
    let (first, rest) = power
        .components()
        .split_first()
        .expect("header binding powers are never empty");
    BindingPower::new(*first, rest.iter().copied())
}

/// One spelling and every fixity capability declared for it.
#[derive(Debug, Eq, PartialEq)]
pub(crate) struct OperatorEntry {
    spelling: Box<str>,
    fixities: OperatorFixities,
}

impl OperatorEntry {
    pub(crate) fn spelling(&self) -> &str {
        &self.spelling
    }

    pub(crate) fn fixities(&self) -> &OperatorFixities {
        &self.fixities
    }
}

/// Yulang2 `BpVec`-equivalent capability set for a single spelling.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct OperatorFixities {
    prefix: Option<PrefixFixity>,
    infix: Option<InfixFixity>,
    suffix: Option<SuffixFixity>,
    nullfix: bool,
}

impl OperatorFixities {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn with_prefix(mut self, right: BindingPower) -> Self {
        self.prefix = Some(PrefixFixity { right });
        self
    }

    pub(crate) fn with_infix(mut self, left: BindingPower, right: BindingPower) -> Self {
        self.infix = Some(InfixFixity { left, right });
        self
    }

    pub(crate) fn with_suffix(mut self, left: BindingPower) -> Self {
        self.suffix = Some(SuffixFixity { left });
        self
    }

    pub(crate) fn with_nullfix(mut self) -> Self {
        self.nullfix = true;
        self
    }

    pub(crate) fn prefix(&self) -> Option<&PrefixFixity> {
        self.prefix.as_ref()
    }

    pub(crate) fn infix(&self) -> Option<&InfixFixity> {
        self.infix.as_ref()
    }

    pub(crate) fn suffix(&self) -> Option<&SuffixFixity> {
        self.suffix.as_ref()
    }

    pub(crate) fn is_nullfix(&self) -> bool {
        self.nullfix
    }

    pub(crate) fn kinds(&self) -> OperatorKindSet {
        let mut kinds = OperatorKindSet::empty();
        if self.prefix.is_some() {
            kinds.insert(OperatorKindSet::PREFIX);
        }
        if self.infix.is_some() {
            kinds.insert(OperatorKindSet::INFIX);
        }
        if self.suffix.is_some() {
            kinds.insert(OperatorKindSet::SUFFIX);
        }
        if self.nullfix {
            kinds.insert(OperatorKindSet::NULLFIX);
        }
        kinds
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PrefixFixity {
    right: BindingPower,
}

impl PrefixFixity {
    pub(crate) fn right_binding_power(&self) -> &BindingPower {
        &self.right
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct InfixFixity {
    left: BindingPower,
    right: BindingPower,
}

impl InfixFixity {
    pub(crate) fn left_binding_power(&self) -> &BindingPower {
        &self.left
    }

    pub(crate) fn right_binding_power(&self) -> &BindingPower {
        &self.right
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SuffixFixity {
    left: BindingPower,
}

impl SuffixFixity {
    pub(crate) fn left_binding_power(&self) -> &BindingPower {
        &self.left
    }
}

/// Lexicographically ordered binding-power components, with implicit trailing zeroes.
#[derive(Clone, Debug)]
pub(crate) struct BindingPower(Box<[i8]>);

impl BindingPower {
    pub(crate) fn scalar(value: i8) -> Self {
        Self(Box::new([value]))
    }

    pub(crate) fn new(first: i8, rest: impl IntoIterator<Item = i8>) -> Self {
        let mut components = vec![first];
        components.extend(rest);
        Self(components.into_boxed_slice())
    }

    pub(crate) fn components(&self) -> &[i8] {
        &self.0
    }
}

impl Ord for BindingPower {
    fn cmp(&self, other: &Self) -> Ordering {
        let component_count = self.0.len().max(other.0.len());
        (0..component_count)
            .map(|index| {
                let left = self.0.get(index).copied().unwrap_or(0);
                let right = other.0.get(index).copied().unwrap_or(0);
                left.cmp(&right)
            })
            .find(|ordering| *ordering != Ordering::Equal)
            .unwrap_or(Ordering::Equal)
    }
}

impl PartialOrd for BindingPower {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for BindingPower {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for BindingPower {}

/// Compact full-fixity flags used by the future NUD/LED judge table.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct OperatorKindSet(u8);

impl OperatorKindSet {
    pub(crate) const PREFIX: Self = Self(1 << 0);
    pub(crate) const INFIX: Self = Self(1 << 1);
    pub(crate) const SUFFIX: Self = Self(1 << 2);
    pub(crate) const NULLFIX: Self = Self(1 << 3);

    pub(crate) const fn empty() -> Self {
        Self(0)
    }

    pub(crate) fn contains(self, required: Self) -> bool {
        self.0 & required.0 == required.0
    }

    fn insert(&mut self, kind: Self) {
        self.0 |= kind.0;
    }
}

impl std::ops::BitOr for OperatorKindSet {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum OperatorTableBuildError {
    EmptySpelling {
        range: Range<usize>,
    },
    ConflictingFixity {
        spelling: Box<str>,
        fixity: OperatorFixity,
        first_origin: OperatorOrigin,
        first_range: Range<usize>,
        second_origin: OperatorOrigin,
        second_range: Range<usize>,
    },
}

#[derive(Default)]
struct AccumulatedOperator {
    fixities: OperatorFixities,
    sites: OperatorFixitySites,
}

impl AccumulatedOperator {
    fn merge(&mut self, declaration: &OperatorDeclaration) -> Result<(), OperatorTableBuildError> {
        let site = OperatorDeclarationSite::from_declaration(declaration);
        merge_capability(
            &mut self.fixities.prefix,
            &declaration.fixities.prefix,
            &mut self.sites.prefix,
            &declaration.spelling,
            OperatorFixity::Prefix,
            &site,
        )?;
        merge_capability(
            &mut self.fixities.infix,
            &declaration.fixities.infix,
            &mut self.sites.infix,
            &declaration.spelling,
            OperatorFixity::Infix,
            &site,
        )?;
        merge_capability(
            &mut self.fixities.suffix,
            &declaration.fixities.suffix,
            &mut self.sites.suffix,
            &declaration.spelling,
            OperatorFixity::Suffix,
            &site,
        )?;
        if declaration.fixities.nullfix {
            if let Some(first_site) = &self.sites.nullfix {
                return Err(OperatorTableBuildError::ConflictingFixity {
                    spelling: declaration.spelling.clone(),
                    fixity: OperatorFixity::Nullfix,
                    first_origin: first_site.origin,
                    first_range: first_site.range.clone(),
                    second_origin: site.origin,
                    second_range: site.range,
                });
            }
            self.fixities.nullfix = true;
            self.sites.nullfix = Some(site);
        }
        Ok(())
    }
}

fn merge_capability<T: Clone>(
    current: &mut Option<T>,
    incoming: &Option<T>,
    first_site: &mut Option<OperatorDeclarationSite>,
    spelling: &str,
    fixity: OperatorFixity,
    second_site: &OperatorDeclarationSite,
) -> Result<(), OperatorTableBuildError> {
    let Some(incoming) = incoming else {
        return Ok(());
    };
    if let Some(first_site) = first_site {
        return Err(OperatorTableBuildError::ConflictingFixity {
            spelling: spelling.into(),
            fixity,
            first_origin: first_site.origin,
            first_range: first_site.range.clone(),
            second_origin: second_site.origin,
            second_range: second_site.range.clone(),
        });
    }
    *current = Some(incoming.clone());
    *first_site = Some(second_site.clone());
    Ok(())
}

/// Compiles the immutable full-parse table without modifying the imported table.
pub(crate) fn compile_full_parse_operators(
    imported: &OperatorTable,
    local: &[HeaderOperator],
) -> Result<OperatorTable, OperatorTableBuildError> {
    let mut builder = OperatorTableBuilder::default();
    builder.seed_imported(imported)?;
    builder.extend(
        local
            .iter()
            .cloned()
            .map(OperatorDeclaration::from_header_operator),
    )?;
    Ok(builder.build())
}

/// The deterministic, degraded full-parse table and every rejected duplicate
/// capability encountered while building it.
pub(crate) struct FullParseOperatorCompilation {
    pub(crate) table: OperatorTable,
    pub(crate) rejected_conflicts: Vec<RejectedOperatorFixity>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RejectedOperatorFixity {
    pub(crate) spelling: Box<str>,
    pub(crate) fixity: OperatorFixity,
    pub(crate) first_origin: OperatorOrigin,
    pub(crate) first_range: Range<usize>,
    pub(crate) second_origin: OperatorOrigin,
    pub(crate) second_range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum FullParseOperatorConstructionError {
    EmptySpelling {
        origin: OperatorOrigin,
        range: Range<usize>,
    },
}

/// Compiles the full-parse table in one builder pass, retaining the first
/// accepted capability for a duplicate fixity and recording the rejected one.
pub(crate) fn compile_full_parse_operators_recovering(
    imported: &OperatorTable,
    local: &[HeaderOperator],
) -> Result<FullParseOperatorCompilation, FullParseOperatorConstructionError> {
    let mut builder = OperatorTableBuilder::default();
    let mut rejected_conflicts = Vec::new();

    for (entry, sites) in imported.entries_with_sites() {
        for fixity in [
            OperatorFixity::Prefix,
            OperatorFixity::Infix,
            OperatorFixity::Suffix,
            OperatorFixity::Nullfix,
        ] {
            let Some(site) = sites.site(fixity) else {
                continue;
            };
            merge_full_parse_operator_recovering(
                &mut builder,
                OperatorDeclaration {
                    spelling: entry.spelling.clone(),
                    fixities: fixities_for(entry.fixities(), fixity),
                    origin: site.origin,
                    range: site.range.clone(),
                },
                &mut rejected_conflicts,
            )?;
        }
    }
    for header in local.iter().cloned() {
        merge_full_parse_operator_recovering(
            &mut builder,
            OperatorDeclaration::from_header_operator(header),
            &mut rejected_conflicts,
        )?;
    }

    Ok(FullParseOperatorCompilation {
        table: builder.build(),
        rejected_conflicts,
    })
}

fn merge_full_parse_operator_recovering(
    builder: &mut OperatorTableBuilder,
    declaration: OperatorDeclaration,
    rejected_conflicts: &mut Vec<RejectedOperatorFixity>,
) -> Result<(), FullParseOperatorConstructionError> {
    let origin = declaration.origin;
    let range = declaration.range.clone();
    match builder.merge(declaration) {
        Ok(()) => Ok(()),
        Err(OperatorTableBuildError::ConflictingFixity {
            spelling,
            fixity,
            first_origin,
            first_range,
            second_origin,
            second_range,
        }) => {
            rejected_conflicts.push(RejectedOperatorFixity {
                spelling,
                fixity,
                first_origin,
                first_range,
                second_origin,
                second_range,
            });
            Ok(())
        }
        Err(OperatorTableBuildError::EmptySpelling { .. }) => {
            Err(FullParseOperatorConstructionError::EmptySpelling { origin, range })
        }
    }
}

#[derive(Default)]
struct OperatorTableBuilder {
    definitions: BTreeMap<Box<str>, AccumulatedOperator>,
}

impl OperatorTableBuilder {
    fn from_declarations(
        declarations: impl IntoIterator<Item = OperatorDeclaration>,
    ) -> Result<Self, OperatorTableBuildError> {
        let mut builder = Self::default();
        builder.extend(declarations)?;
        Ok(builder)
    }

    fn extend(
        &mut self,
        declarations: impl IntoIterator<Item = OperatorDeclaration>,
    ) -> Result<(), OperatorTableBuildError> {
        for declaration in declarations {
            self.merge(declaration)?;
        }
        Ok(())
    }

    fn merge(&mut self, declaration: OperatorDeclaration) -> Result<(), OperatorTableBuildError> {
        if declaration.spelling.is_empty() {
            return Err(OperatorTableBuildError::EmptySpelling {
                range: declaration.range,
            });
        }

        self.definitions
            .entry(declaration.spelling.clone())
            .or_default()
            .merge(&declaration)
    }

    fn seed_imported(&mut self, imported: &OperatorTable) -> Result<(), OperatorTableBuildError> {
        for (entry, sites) in imported.entries_with_sites() {
            for fixity in [
                OperatorFixity::Prefix,
                OperatorFixity::Infix,
                OperatorFixity::Suffix,
                OperatorFixity::Nullfix,
            ] {
                let Some(site) = sites.site(fixity) else {
                    continue;
                };
                let fixities = fixities_for(entry.fixities(), fixity);
                self.merge(OperatorDeclaration {
                    spelling: entry.spelling.clone(),
                    fixities,
                    origin: site.origin,
                    range: site.range.clone(),
                })?;
            }
        }
        Ok(())
    }

    fn build(self) -> OperatorTable {
        let mut table = OperatorTable::empty();
        for (spelling, definition) in self.definitions {
            debug_assert!(matching_presence(&definition.fixities, &definition.sites));
            let entry_index = table.entries.len();
            table.trie.insert(&spelling, entry_index);
            table.entries.push(OperatorEntry {
                spelling,
                fixities: definition.fixities,
            });
            table.sites.push(definition.sites);
        }
        debug_assert_eq!(table.entries.len(), table.sites.len());
        table
    }
}

fn fixities_for(fixities: &OperatorFixities, fixity: OperatorFixity) -> OperatorFixities {
    match fixity {
        OperatorFixity::Prefix => OperatorFixities::new().with_prefix(
            fixities
                .prefix
                .as_ref()
                .expect("operator site and fixity presence must agree")
                .right
                .clone(),
        ),
        OperatorFixity::Infix => {
            let infix = fixities
                .infix
                .as_ref()
                .expect("operator site and fixity presence must agree");
            OperatorFixities::new().with_infix(infix.left.clone(), infix.right.clone())
        }
        OperatorFixity::Suffix => OperatorFixities::new().with_suffix(
            fixities
                .suffix
                .as_ref()
                .expect("operator site and fixity presence must agree")
                .left
                .clone(),
        ),
        OperatorFixity::Nullfix => OperatorFixities::new().with_nullfix(),
    }
}

fn matching_presence(fixities: &OperatorFixities, sites: &OperatorFixitySites) -> bool {
    (fixities.prefix.is_some() == sites.prefix.is_some())
        && (fixities.infix.is_some() == sites.infix.is_some())
        && (fixities.suffix.is_some() == sites.suffix.is_some())
        && (fixities.nullfix == sites.nullfix.is_some())
}

/// Borrowing traversal state consumed directly by chasa's trie parser.
#[derive(Clone, Copy, Debug)]
pub(crate) struct OperatorTrieState<'table> {
    table: &'table OperatorTable,
    node: Option<usize>,
}

impl<'table> ChasaTrieState for OperatorTrieState<'table> {
    type Item = char;
    type Value = &'table OperatorEntry;

    fn step(&mut self, character: Self::Item) -> bool {
        let Some(node) = self.node else {
            return false;
        };
        self.node = self.table.trie.nodes[node]
            .children
            .get(&character)
            .copied();
        self.node.is_some()
    }

    fn value(&self) -> Option<Self::Value> {
        let entry = self.table.trie.nodes[self.node?].entry?;
        self.table.entries.get(entry)
    }
}

#[derive(Debug)]
struct OperatorTrie {
    nodes: Vec<OperatorTrieNode>,
}

impl OperatorTrie {
    fn new() -> Self {
        Self {
            nodes: vec![OperatorTrieNode::default()],
        }
    }

    fn insert(&mut self, spelling: &str, entry: usize) {
        let mut node = 0;
        for character in spelling.chars() {
            if let Some(next) = self.nodes[node].children.get(&character).copied() {
                node = next;
                continue;
            }

            let next = self.nodes.len();
            self.nodes.push(OperatorTrieNode::default());
            self.nodes[node].children.insert(character, next);
            node = next;
        }
        self.nodes[node].entry = Some(entry);
    }

    fn find(&self, spelling: &str) -> Option<usize> {
        let mut node = 0;
        for character in spelling.chars() {
            node = *self.nodes[node].children.get(&character)?;
        }
        self.nodes[node].entry
    }
}

#[derive(Debug, Default)]
struct OperatorTrieNode {
    children: BTreeMap<char, usize>,
    entry: Option<usize>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        BindingPower as HeaderBindingPower, BindingPowers, HeaderOperator, Visibility,
        input::SourceInput,
    };
    use chasa::Input;

    #[test]
    fn preserves_all_fixities_and_bpvec_binding_powers() {
        let prefix = BindingPower::scalar(70);
        let infix_left = BindingPower::scalar(40);
        let infix_right = BindingPower::new(40, [1]);
        let suffix = BindingPower::scalar(80);
        let table = OperatorTable::from_declarations([OperatorDeclaration::new(
            "..",
            OperatorFixities::new()
                .with_prefix(prefix.clone())
                .with_infix(infix_left.clone(), infix_right.clone())
                .with_suffix(suffix.clone())
                .with_nullfix(),
        )])
        .expect("full-fixity declaration should build");

        let definition = table.get("..").expect("operator should exist");
        let kinds = definition.fixities().kinds();
        assert!(kinds.contains(
            OperatorKindSet::PREFIX
                | OperatorKindSet::INFIX
                | OperatorKindSet::SUFFIX
                | OperatorKindSet::NULLFIX
        ));
        assert_eq!(
            definition
                .fixities()
                .prefix()
                .expect("prefix")
                .right_binding_power(),
            &prefix
        );
        assert_eq!(
            definition
                .fixities()
                .infix()
                .expect("infix")
                .left_binding_power(),
            &infix_left
        );
        assert_eq!(
            definition
                .fixities()
                .infix()
                .expect("infix")
                .right_binding_power(),
            &infix_right
        );
        assert_eq!(
            definition
                .fixities()
                .suffix()
                .expect("suffix")
                .left_binding_power(),
            &suffix
        );
        assert!(definition.fixities().is_nullfix());
        assert_eq!(BindingPower::scalar(40), BindingPower::new(40, [0]));
    }

    #[test]
    fn compiles_separate_header_declarations_into_one_full_fixity_entry() {
        let headers = [
            HeaderOperator::new(
                0..20,
                "..".to_owned(),
                OperatorFixity::Nullfix,
                Visibility::Public,
                false,
                BindingPowers::nullfix(),
            ),
            HeaderOperator::new(
                21..48,
                "..".to_owned(),
                OperatorFixity::Prefix,
                Visibility::Public,
                false,
                BindingPowers::prefix(HeaderBindingPower::from_components([8, 0, 0])),
            ),
            HeaderOperator::new(
                49..76,
                "..".to_owned(),
                OperatorFixity::Suffix,
                Visibility::Public,
                false,
                BindingPowers::suffix(HeaderBindingPower::from_components([8, 0, 0])),
            ),
            HeaderOperator::new(
                77..112,
                "..".to_owned(),
                OperatorFixity::Infix,
                Visibility::Public,
                false,
                BindingPowers::infix(
                    HeaderBindingPower::from_components([4, 0, 0]),
                    HeaderBindingPower::from_components([4, 0, 1]),
                ),
            ),
        ];

        let table = OperatorTable::from_header_operators(headers)
            .expect("distinct fixities for one spelling should aggregate");
        let entry = table.get("..").expect("aggregated spelling should exist");
        assert!(entry.fixities().kinds().contains(
            OperatorKindSet::PREFIX
                | OperatorKindSet::INFIX
                | OperatorKindSet::SUFFIX
                | OperatorKindSet::NULLFIX
        ));
        assert_eq!(
            entry
                .fixities()
                .infix()
                .expect("infix capability")
                .right_binding_power()
                .components(),
            &[4, 0, 1]
        );
    }

    #[test]
    fn rejects_redeclaring_the_same_fixity_with_both_source_ranges() {
        let error = OperatorTable::from_declarations([
            OperatorDeclaration::at_range(
                "+",
                OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
                3..18,
            ),
            OperatorDeclaration::at_range(
                "+",
                OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
                42..57,
            ),
        ])
        .expect_err("a repeated prefix declaration must not silently overwrite");

        assert_eq!(
            error,
            OperatorTableBuildError::ConflictingFixity {
                spelling: "+".into(),
                fixity: OperatorFixity::Prefix,
                first_origin: OperatorOrigin::Local,
                first_range: 3..18,
                second_origin: OperatorOrigin::Local,
                second_range: 42..57,
            }
        );
    }

    #[test]
    fn full_parse_merge_preserves_imported_sites_and_adds_local_fixities() {
        let dependency = SyntaxDependencySlot::from_index(0).expect("first slot fits");
        let imported = OperatorTable::from_declarations([OperatorDeclaration::imported_at_range(
            "<+>",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
            dependency,
            8..21,
        )])
        .expect("imported prefix should build");
        let local = [HeaderOperator::new(
            30..48,
            "<+>".to_owned(),
            OperatorFixity::Infix,
            Visibility::Private,
            false,
            BindingPowers::infix(
                HeaderBindingPower::from_components([40]),
                HeaderBindingPower::from_components([41]),
            ),
        )];

        let merged = compile_full_parse_operators(&imported, &local)
            .expect("distinct imported and local fixities should aggregate");
        let entry = merged.get("<+>").expect("merged spelling should exist");
        assert_eq!(
            entry
                .fixities()
                .prefix()
                .expect("imported prefix")
                .right_binding_power(),
            &BindingPower::scalar(70)
        );
        assert_eq!(
            entry
                .fixities()
                .infix()
                .expect("local infix")
                .left_binding_power(),
            &BindingPower::scalar(40)
        );

        let (_, sites) = merged
            .entries_with_sites()
            .next()
            .expect("one merged entry");
        assert_eq!(
            sites.site(OperatorFixity::Prefix),
            Some(&OperatorDeclarationSite {
                origin: OperatorOrigin::Imported(dependency),
                range: 8..21,
            })
        );
        assert_eq!(
            sites.site(OperatorFixity::Infix),
            Some(&OperatorDeclarationSite {
                origin: OperatorOrigin::Local,
                range: 30..48,
            })
        );

        let (_, imported_sites) = imported
            .entries_with_sites()
            .next()
            .expect("imported entry remains available");
        assert_eq!(
            imported_sites.site(OperatorFixity::Prefix),
            Some(&OperatorDeclarationSite {
                origin: OperatorOrigin::Imported(dependency),
                range: 8..21,
            })
        );
        assert!(imported_sites.site(OperatorFixity::Infix).is_none());
    }

    #[test]
    fn full_parse_merge_reports_imported_fixity_before_local_conflict() {
        let dependency = SyntaxDependencySlot::from_index(0).expect("first slot fits");
        let imported = OperatorTable::from_declarations([OperatorDeclaration::imported_at_range(
            "<+>",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
            dependency,
            8..21,
        )])
        .expect("imported prefix should build");
        let local = [HeaderOperator::new(
            30..47,
            "<+>".to_owned(),
            OperatorFixity::Prefix,
            Visibility::Private,
            false,
            BindingPowers::prefix(HeaderBindingPower::from_components([71])),
        )];

        let error = compile_full_parse_operators(&imported, &local)
            .expect_err("same fixity must retain imported declaration as first conflict");
        assert_eq!(
            error,
            OperatorTableBuildError::ConflictingFixity {
                spelling: "<+>".into(),
                fixity: OperatorFixity::Prefix,
                first_origin: OperatorOrigin::Imported(dependency),
                first_range: 8..21,
                second_origin: OperatorOrigin::Local,
                second_range: 30..47,
            }
        );
    }

    #[test]
    fn recovering_full_parse_merge_retains_first_local_fixity_and_later_capabilities() {
        let local = [
            HeaderOperator::new(
                0..15,
                "+".to_owned(),
                OperatorFixity::Prefix,
                Visibility::Private,
                false,
                BindingPowers::prefix(HeaderBindingPower::from_components([70])),
            ),
            HeaderOperator::new(
                16..31,
                "+".to_owned(),
                OperatorFixity::Prefix,
                Visibility::Private,
                false,
                BindingPowers::prefix(HeaderBindingPower::from_components([71])),
            ),
            HeaderOperator::new(
                32..49,
                "+".to_owned(),
                OperatorFixity::Infix,
                Visibility::Private,
                false,
                BindingPowers::infix(
                    HeaderBindingPower::from_components([40]),
                    HeaderBindingPower::from_components([41]),
                ),
            ),
        ];

        let compilation = compile_full_parse_operators_recovering(&OperatorTable::empty(), &local)
            .expect("duplicate fixity is recoverable");
        let entry = compilation.table.get("+").expect("accepted spelling");
        assert_eq!(
            entry
                .fixities()
                .prefix()
                .expect("first prefix remains accepted")
                .right_binding_power(),
            &BindingPower::scalar(70)
        );
        assert!(entry.fixities().infix().is_some());
        assert_eq!(
            compilation.rejected_conflicts,
            [RejectedOperatorFixity {
                spelling: "+".into(),
                fixity: OperatorFixity::Prefix,
                first_origin: OperatorOrigin::Local,
                first_range: 0..15,
                second_origin: OperatorOrigin::Local,
                second_range: 16..31,
            }]
        );
    }

    #[test]
    fn recovering_full_parse_merge_retains_imported_first_fixity() {
        let dependency = SyntaxDependencySlot::from_index(0).expect("slot fits");
        let imported = OperatorTable::from_declarations([OperatorDeclaration::imported_at_range(
            "+",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
            dependency,
            4..18,
        )])
        .expect("imported table");
        let local = [HeaderOperator::new(
            20..35,
            "+".to_owned(),
            OperatorFixity::Prefix,
            Visibility::Private,
            false,
            BindingPowers::prefix(HeaderBindingPower::from_components([71])),
        )];

        let compilation = compile_full_parse_operators_recovering(&imported, &local)
            .expect("duplicate fixity is recoverable");
        assert_eq!(
            compilation.rejected_conflicts[0].first_origin,
            OperatorOrigin::Imported(dependency)
        );
        assert_eq!(compilation.rejected_conflicts[0].first_range, 4..18);
        assert_eq!(compilation.rejected_conflicts[0].second_range, 20..35);
    }

    #[test]
    fn longest_match_then_can_fall_back_from_long_to_short_spelling() {
        let table = OperatorTable::from_declarations([
            OperatorDeclaration::new(
                "+",
                OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
            ),
            OperatorDeclaration::new(
                "+!",
                OperatorFixities::new()
                    .with_infix(BindingPower::scalar(50), BindingPower::new(50, [1])),
            ),
            OperatorDeclaration::new(
                "!",
                OperatorFixities::new()
                    .with_prefix(BindingPower::scalar(80))
                    .with_nullfix(),
            ),
        ])
        .expect("operator declarations should build");

        let mut longest_input = SourceInput::new("+!a");
        let longest = longest_input.test(
            table
                .state()
                .longest_match_then(|_, candidate, _| Some(candidate.spelling())),
        );
        assert_eq!(longest, Some("+!"));
        assert_eq!(longest_input.pos(), 2);

        let mut candidates = Vec::new();
        let mut fallback_input = SourceInput::new("+!a");
        let fallback = fallback_input.test(table.state().longest_match_then(|_, candidate, _| {
            candidates.push(candidate.spelling());
            (!candidate
                .fixities()
                .kinds()
                .contains(OperatorKindSet::INFIX))
            .then(|| candidate.spelling())
        }));

        assert_eq!(candidates, ["+!", "+"]);
        assert_eq!(fallback, Some("+"));
        assert_eq!(fallback_input.pos(), 1);
        assert_eq!(fallback_input.next(), Some('!'));
        let bang = table.get("!").expect("bang operator should exist");
        assert!(
            bang.fixities()
                .kinds()
                .contains(OperatorKindSet::PREFIX | OperatorKindSet::NULLFIX)
        );
    }
}

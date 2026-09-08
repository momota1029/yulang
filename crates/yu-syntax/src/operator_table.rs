//! Immutable full-fixity operator definitions and source matching.

use std::{cmp::Ordering, collections::BTreeMap, ops::Range};

use unicode_ident::is_xid_continue;

use crate::SyntaxDependencySlot;

pub(crate) use crate::OperatorFixity;

/// A parse-session operator table compiled before full parsing starts.
#[derive(Debug)]
pub struct OperatorTable {
    entries: Vec<OperatorEntry>,
    sites: Vec<OperatorFixitySites>,
    trie: OperatorTrie,
    value_start_trie: OperatorTrie,
}

impl OperatorTable {
    pub fn empty() -> Self {
        Self {
            entries: Vec::new(),
            sites: Vec::new(),
            trie: OperatorTrie::new(),
            value_start_trie: OperatorTrie::new(),
        }
    }

    #[cfg(test)]
    pub(crate) fn from_declarations(
        declarations: impl IntoIterator<Item = OperatorDeclaration>,
    ) -> Result<Self, OperatorTableBuildError> {
        Ok(OperatorTableBuilder::from_declarations(declarations)?.build())
    }

    #[cfg(test)]
    pub(crate) fn get(&self, spelling: &str) -> Option<&OperatorEntry> {
        let entry = self.trie.find(spelling)?;
        self.entries.get(entry)
    }

    /// Traverses the frozen all-spelling trie directly from source. Terminal
    /// candidates are offered longest first; rejecting one continues at the
    /// next shorter terminal without retaining source-specific matcher state.
    pub(crate) fn longest_source_match_then<T>(
        &self,
        source: &str,
        mut accept: impl FnMut(char, &OperatorEntry, usize) -> Option<T>,
    ) -> Option<(T, usize)> {
        self.trie
            .longest_source_match_then(&self.entries, source, &mut accept)
    }

    /// Greedily recognizes a boundary-valid spelling whose final merged entry
    /// has both Prefix and Nullfix capability. The filtered trie is frozen with
    /// the canonical trie and borrows the canonical entry storage.
    pub(crate) fn value_start_source_len(&self, source: &str) -> Option<usize> {
        self.value_start_trie
            .longest_source_match_then(&self.entries, source, &mut |last_character, _entry, end| {
                operator_boundary_source(last_character, &source[end..]).then_some(())
            })
            .map(|((), end)| end)
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
    pub(crate) fn from_site(
        spelling: &str,
        fixities: OperatorFixities,
        site: &OperatorDeclarationSite,
    ) -> Self {
        Self {
            spelling: spelling.into(),
            fixities,
            origin: site.origin,
            range: site.range.clone(),
        }
    }

    pub(crate) fn origin(&self) -> OperatorOrigin {
        self.origin
    }

    #[cfg(test)]
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

    #[cfg(test)]
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
    #[cfg(test)]
    pub(crate) fn scalar(value: i8) -> Self {
        Self(Box::new([value]))
    }

    pub(crate) fn new(first: i8, rest: impl IntoIterator<Item = i8>) -> Self {
        let mut components = vec![first];
        components.extend(rest);
        Self(components.into_boxed_slice())
    }

    #[cfg(test)]
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

#[derive(Default)]
pub(crate) struct OperatorTableBuilder {
    definitions: BTreeMap<Box<str>, AccumulatedOperator>,
}

impl OperatorTableBuilder {
    #[cfg(test)]
    fn from_declarations(
        declarations: impl IntoIterator<Item = OperatorDeclaration>,
    ) -> Result<Self, OperatorTableBuildError> {
        let mut builder = Self::default();
        builder.extend(declarations)?;
        Ok(builder)
    }

    #[cfg(test)]
    pub(crate) fn extend(
        &mut self,
        declarations: impl IntoIterator<Item = OperatorDeclaration>,
    ) -> Result<(), OperatorTableBuildError> {
        for declaration in declarations {
            self.merge(declaration)?;
        }
        Ok(())
    }

    pub(crate) fn merge(
        &mut self,
        declaration: OperatorDeclaration,
    ) -> Result<(), OperatorTableBuildError> {
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

    pub(crate) fn build(self) -> OperatorTable {
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
            if table.entries[entry_index]
                .fixities()
                .kinds()
                .contains(OperatorKindSet::PREFIX | OperatorKindSet::NULLFIX)
            {
                table
                    .value_start_trie
                    .insert(table.entries[entry_index].spelling(), entry_index);
            }
        }
        debug_assert_eq!(table.entries.len(), table.sites.len());
        table
    }
}

fn matching_presence(fixities: &OperatorFixities, sites: &OperatorFixitySites) -> bool {
    (fixities.prefix.is_some() == sites.prefix.is_some())
        && (fixities.infix.is_some() == sites.infix.is_some())
        && (fixities.suffix.is_some() == sites.suffix.is_some())
        && (fixities.nullfix == sites.nullfix.is_some())
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

    #[cfg(test)]
    fn find(&self, spelling: &str) -> Option<usize> {
        let mut node = 0;
        for character in spelling.chars() {
            node = *self.nodes[node].children.get(&character)?;
        }
        self.nodes[node].entry
    }

    fn longest_source_match_then<T>(
        &self,
        entries: &[OperatorEntry],
        source: &str,
        accept: &mut impl FnMut(char, &OperatorEntry, usize) -> Option<T>,
    ) -> Option<(T, usize)> {
        self.longest_source_match_from(entries, source, 0, 0, None, accept)
    }

    fn longest_source_match_from<T>(
        &self,
        entries: &[OperatorEntry],
        source: &str,
        node: usize,
        offset: usize,
        last_character: Option<char>,
        accept: &mut impl FnMut(char, &OperatorEntry, usize) -> Option<T>,
    ) -> Option<(T, usize)> {
        if let Some(character) = source[offset..].chars().next()
            && let Some(next) = self.nodes[node].children.get(&character).copied()
        {
            let next_offset = offset + character.len_utf8();
            if let Some(accepted) = self.longest_source_match_from(
                entries,
                source,
                next,
                next_offset,
                Some(character),
                accept,
            ) {
                return Some(accepted);
            }
        }

        let entry = self.nodes[node].entry?;
        let accepted = accept(last_character?, entries.get(entry)?, offset)?;
        Some((accepted, offset))
    }
}

fn operator_boundary_source(last_character: char, remainder: &str) -> bool {
    !is_xid_continue(last_character)
        || remainder
            .chars()
            .next()
            .is_none_or(|character| !is_xid_continue(character))
}

#[derive(Debug, Default)]
struct OperatorTrieNode {
    children: BTreeMap<char, usize>,
    entry: Option<usize>,
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn filtered_value_start_trie_is_built_after_capability_merge() {
        let table = OperatorTable::from_declarations([
            OperatorDeclaration::new(
                "!",
                OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
            ),
            OperatorDeclaration::new("!", OperatorFixities::new().with_nullfix()),
            OperatorDeclaration::new(
                "!?",
                OperatorFixities::new().with_prefix(BindingPower::scalar(80)),
            ),
            OperatorDeclaration::new(
                "λ",
                OperatorFixities::new()
                    .with_prefix(BindingPower::scalar(60))
                    .with_nullfix(),
            ),
        ])
        .expect("distinct merged capabilities build one filtered terminal");

        assert_eq!(table.value_start_source_len("!?operand"), Some(1));
        assert_eq!(
            table.value_start_source_len("λx"),
            None,
            "identifier-like terminal observes its following XID boundary"
        );
        assert_eq!(table.value_start_source_len("λ+"), Some("λ".len()));
        assert_eq!(
            table.value_start_source_len("!?"),
            Some(1),
            "the longer Prefix-only spelling is absent, not a qualifying split"
        );
    }

    #[test]
    fn direct_source_traversal_offers_longest_terminal_then_shorter_terminal() {
        let table = OperatorTable::from_declarations([
            OperatorDeclaration::new("+", OperatorFixities::new().with_nullfix()),
            OperatorDeclaration::new("+!", OperatorFixities::new().with_nullfix()),
        ])
        .expect("overlap table");
        let mut offered = Vec::new();
        let accepted = table.longest_source_match_then("+!tail", |_, entry, _| {
            offered.push(entry.spelling().to_owned());
            (entry.spelling() == "+").then(|| entry.spelling().to_owned())
        });
        assert_eq!(offered, ["+!", "+"]);
        assert_eq!(accepted, Some(("+".to_owned(), 1)));
    }
}

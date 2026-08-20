//! Immutable full-fixity operator definitions and chasa trie traversal.

use std::{cmp::Ordering, collections::BTreeMap, ops::Range};

use chasa::parser::trie::TrieState as ChasaTrieState;

use crate::{BindingPower as HeaderBindingPower, HeaderOperator};

pub(crate) use crate::OperatorFixity;

/// A parse-session operator table compiled before full parsing starts.
#[derive(Debug)]
pub(crate) struct OperatorTable {
    entries: Vec<OperatorEntry>,
    trie: OperatorTrie,
}

impl OperatorTable {
    pub(crate) fn empty() -> Self {
        Self {
            entries: Vec::new(),
            trie: OperatorTrie::new(),
        }
    }

    pub(crate) fn from_declarations(
        declarations: impl IntoIterator<Item = OperatorDeclaration>,
    ) -> Result<Self, OperatorTableBuildError> {
        let mut definitions = BTreeMap::<Box<str>, AccumulatedOperator>::new();

        for declaration in declarations {
            if declaration.spelling.is_empty() {
                return Err(OperatorTableBuildError::EmptySpelling {
                    range: declaration.range,
                });
            }

            let spelling = declaration.spelling.clone();
            definitions
                .entry(spelling)
                .or_default()
                .merge(&declaration)?;
        }

        let mut table = Self::empty();
        for (spelling, definition) in definitions {
            let entry_index = table.entries.len();
            table.trie.insert(&spelling, entry_index);
            table.entries.push(OperatorEntry {
                spelling,
                fixities: definition.fixities,
            });
        }
        Ok(table)
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
        first_range: Range<usize>,
        second_range: Range<usize>,
    },
}

#[derive(Default)]
struct AccumulatedOperator {
    fixities: OperatorFixities,
    prefix_range: Option<Range<usize>>,
    infix_range: Option<Range<usize>>,
    suffix_range: Option<Range<usize>>,
    nullfix_range: Option<Range<usize>>,
}

impl AccumulatedOperator {
    fn merge(&mut self, declaration: &OperatorDeclaration) -> Result<(), OperatorTableBuildError> {
        merge_capability(
            &mut self.fixities.prefix,
            &declaration.fixities.prefix,
            &mut self.prefix_range,
            &declaration.spelling,
            OperatorFixity::Prefix,
            &declaration.range,
        )?;
        merge_capability(
            &mut self.fixities.infix,
            &declaration.fixities.infix,
            &mut self.infix_range,
            &declaration.spelling,
            OperatorFixity::Infix,
            &declaration.range,
        )?;
        merge_capability(
            &mut self.fixities.suffix,
            &declaration.fixities.suffix,
            &mut self.suffix_range,
            &declaration.spelling,
            OperatorFixity::Suffix,
            &declaration.range,
        )?;
        if declaration.fixities.nullfix {
            if let Some(first_range) = &self.nullfix_range {
                return Err(OperatorTableBuildError::ConflictingFixity {
                    spelling: declaration.spelling.clone(),
                    fixity: OperatorFixity::Nullfix,
                    first_range: first_range.clone(),
                    second_range: declaration.range.clone(),
                });
            }
            self.fixities.nullfix = true;
            self.nullfix_range = Some(declaration.range.clone());
        }
        Ok(())
    }
}

fn merge_capability<T: Clone>(
    current: &mut Option<T>,
    incoming: &Option<T>,
    first_range: &mut Option<Range<usize>>,
    spelling: &str,
    fixity: OperatorFixity,
    second_range: &Range<usize>,
) -> Result<(), OperatorTableBuildError> {
    let Some(incoming) = incoming else {
        return Ok(());
    };
    if let Some(first_range) = first_range {
        return Err(OperatorTableBuildError::ConflictingFixity {
            spelling: spelling.into(),
            fixity,
            first_range: first_range.clone(),
            second_range: second_range.clone(),
        });
    }
    *current = Some(incoming.clone());
    *first_range = Some(second_range.clone());
    Ok(())
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
                first_range: 3..18,
                second_range: 42..57,
            }
        );
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

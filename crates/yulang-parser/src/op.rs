use smallvec::SmallVec;

#[derive(Debug, Clone, Default)]
pub struct BpVec(pub SmallVec<[i8; 4]>);

impl BpVec {
    pub fn new(items: impl Into<SmallVec<[i8; 4]>>) -> Self {
        Self(items.into())
    }

    pub fn parse(raw: &str) -> Option<Self> {
        if raw.is_empty() {
            return None;
        }
        let mut out = SmallVec::<[i8; 4]>::new();
        for part in raw.split('.') {
            if part.is_empty() {
                return None;
            }
            let value = part.parse::<i8>().ok()?;
            out.push(value);
        }
        Some(Self(out))
    }
}

impl Ord for BpVec {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let max_len = self.0.len().max(other.0.len());
        for i in 0..max_len {
            let a = self.0.get(i).copied().unwrap_or(0);
            let b = other.0.get(i).copied().unwrap_or(0);
            match a.cmp(&b) {
                std::cmp::Ordering::Equal => {}
                non_eq => return non_eq,
            }
        }
        std::cmp::Ordering::Equal
    }
}

impl PartialOrd for BpVec {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for BpVec {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == std::cmp::Ordering::Equal
    }
}

impl Eq for BpVec {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpUse {
    Prefix,
    Infix,
    Suffix,
    Nullfix,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct OpKindSet {
    bits: u8,
}

impl OpKindSet {
    pub const PREFIX: Self = Self { bits: 1 << 0 };
    pub const INFIX: Self = Self { bits: 1 << 1 };
    pub const SUFFIX: Self = Self { bits: 1 << 2 };
    pub const NULLFIX: Self = Self { bits: 1 << 3 };

    pub fn contains(self, other: Self) -> bool {
        (self.bits & other.bits) == other.bits
    }
}

impl std::ops::SubAssign for OpKindSet {
    fn sub_assign(&mut self, rhs: Self) {
        self.bits &= !rhs.bits;
    }
}

impl std::ops::BitOr for OpKindSet {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self::Output {
        Self {
            bits: self.bits | rhs.bits,
        }
    }
}

impl std::ops::BitOrAssign for OpKindSet {
    fn bitor_assign(&mut self, rhs: Self) {
        self.bits |= rhs.bits;
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct OpDef {
    pub prefix: Option<BpVec>,
    pub infix: Option<(BpVec, BpVec)>,
    pub suffix: Option<BpVec>,
    pub nullfix: bool,
}

impl OpDef {
    pub fn kinds(&self) -> OpKindSet {
        let mut kinds = OpKindSet::default();
        if self.prefix.is_some() {
            kinds |= OpKindSet::PREFIX;
        }
        if self.infix.is_some() {
            kinds |= OpKindSet::INFIX;
        }
        if self.suffix.is_some() {
            kinds |= OpKindSet::SUFFIX;
        }
        if self.nullfix {
            kinds |= OpKindSet::NULLFIX;
        }
        kinds
    }
}

pub mod trie {
    use chasa::parser::trie::TrieState as ChasaTrieState;
    use qp_trie::{Trie as QpTrie, wrapper::BString};

    pub type Trie<V> = QpTrie<BString, V>;

    #[derive(Debug)]
    pub struct TrieState<'a, V> {
        trie: &'a Trie<V>,
        path: Vec<u8>,
        dead: bool,
    }

    impl<'a, V> TrieState<'a, V> {
        pub fn new(trie: &'a Trie<V>) -> Self {
            Self {
                trie,
                path: Vec::new(),
                dead: false,
            }
        }

        pub fn step(&mut self, ch: char) -> bool {
            if self.dead {
                return false;
            }
            let mut buf = [0u8; 4];
            let bytes = ch.encode_utf8(&mut buf).as_bytes();
            self.path.extend_from_slice(bytes);
            let has_prefix = self.trie.iter_prefix(self.path.as_slice()).next().is_some();
            if !has_prefix {
                self.dead = true;
                false
            } else {
                true
            }
        }

        pub fn value(&self) -> Option<&V> {
            if self.dead {
                None
            } else {
                self.trie.get(self.path.as_slice())
            }
        }
    }

    impl<'a, V: Clone> ChasaTrieState for TrieState<'a, V> {
        type Item = char;
        type Value = V;

        fn step(&mut self, ch: Self::Item) -> bool {
            self.step(ch)
        }

        fn value(&self) -> Option<Self::Value> {
            self.value().cloned()
        }
    }
}

#[derive(Debug, Clone)]
pub struct OpTable(pub trie::Trie<OpDef>);

impl Default for OpTable {
    fn default() -> Self {
        standard_op_table()
    }
}

impl OpTable {
    pub fn new() -> Self {
        Self(trie::Trie::new())
    }

    pub fn state(&self) -> trie::TrieState<'_, OpDef> {
        trie::TrieState::new(&self.0)
    }
}

fn bp(value: i8) -> BpVec {
    BpVec::new(vec![value])
}

fn bp_r(value: i8) -> BpVec {
    BpVec::new(vec![value, 1])
}

pub fn standard_op_table() -> OpTable {
    let mut table = OpTable::new();

    macro_rules! add {
        ($sym:expr, prefix: $p:expr) => {{
            let mut def = OpDef::default();
            def.prefix = Some(bp($p));
            table.0.insert($sym.into(), def);
        }};
        ($sym:expr, prefix: $p:expr, nullfix) => {{
            let mut def = OpDef::default();
            def.prefix = Some(bp($p));
            def.nullfix = true;
            table.0.insert($sym.into(), def);
        }};
        ($sym:expr, infix: ($l:expr, $r:expr)) => {{
            let mut def = OpDef::default();
            let _ = $r;
            def.infix = Some((bp($l), bp_r($l)));
            table.0.insert($sym.into(), def);
        }};
        ($sym:expr, prefix: $p:expr, infix: ($l:expr, $r:expr)) => {{
            let mut def = OpDef::default();
            let _ = $r;
            def.prefix = Some(bp($p));
            def.infix = Some((bp($l), bp_r($l)));
            table.0.insert($sym.into(), def);
        }};
        ($sym:expr, prefix: $p:expr, infix: ($l:expr, $r:expr), suffix: $s:expr, nullfix) => {{
            let mut def = OpDef::default();
            let _ = $r;
            def.prefix = Some(bp($p));
            def.infix = Some((bp($l), bp_r($l)));
            def.suffix = Some(bp($s));
            def.nullfix = true;
            table.0.insert($sym.into(), def);
        }};
    }

    add!("not", prefix: 70);
    add!("last", prefix: 80, nullfix);
    add!("next", prefix: 80, nullfix);
    add!("redo", prefix: 80, nullfix);
    add!("return", prefix: 1, nullfix);
    add!("+", prefix: 70, infix: (50, 50));
    add!("-", prefix: 70, infix: (50, 50));
    add!("*", infix: (60, 60));
    add!("/", infix: (60, 60));
    add!("%", infix: (60, 60));
    add!("..", prefix: 70, infix: (40, 40), suffix: 70, nullfix);
    add!("==", infix: (30, 30));
    add!("!=", infix: (30, 30));
    add!("<", infix: (30, 30));
    add!("<=", infix: (30, 30));
    add!(">", infix: (30, 30));
    add!(">=", infix: (30, 30));
    add!("and", infix: (20, 20));
    add!("or", infix: (10, 10));

    table
}

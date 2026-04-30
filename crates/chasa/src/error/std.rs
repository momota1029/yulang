use std::borrow::Cow;
use std::cmp::Ordering;
use std::fmt;

use crate::error::MergeErrors;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum StdErr<Item> {
    Expected(Expected<()>),
    Unexpected(Unexpected<Item>),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Expected<E> {
    pub start: u64,
    pub label: Cow<'static, str>,
    pub err: E,
}

impl<E> Expected<E> {
    pub fn new(start: u64, label: impl Into<Cow<'static, str>>, err: E) -> Self {
        Self {
            start,
            label: label.into(),
            err,
        }
    }
}

impl<E> fmt::Display for Expected<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.label.as_ref())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Unexpected<Item> {
    EndOfInput,
    Item(Item),
}

pub struct UnexpectedEndOfInput;
pub struct UnexpectedItem<Item>(pub Item);

impl<Item> From<UnexpectedEndOfInput> for Unexpected<Item> {
    fn from(_: UnexpectedEndOfInput) -> Self {
        Unexpected::EndOfInput
    }
}

impl<Item> From<UnexpectedItem<Item>> for Unexpected<Item> {
    fn from(value: UnexpectedItem<Item>) -> Self {
        Unexpected::Item(value.0)
    }
}

impl<Item: fmt::Debug> fmt::Display for Unexpected<Item> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Unexpected::EndOfInput => f.write_str("end of input"),
            Unexpected::Item(item) => write!(f, "{item:?}"),
        }
    }
}

impl<Item, E> From<Expected<E>> for StdErr<Item> {
    fn from(value: Expected<E>) -> Self {
        StdErr::Expected(Expected {
            start: value.start,
            label: value.label,
            err: (),
        })
    }
}

impl<Item> From<Unexpected<Item>> for StdErr<Item> {
    fn from(value: Unexpected<Item>) -> Self {
        StdErr::Unexpected(value)
    }
}

impl<Item> From<UnexpectedItem<Item>> for StdErr<Item> {
    fn from(value: UnexpectedItem<Item>) -> Self {
        StdErr::Unexpected(Unexpected::from(value))
    }
}

impl<Item> From<UnexpectedEndOfInput> for StdErr<Item> {
    fn from(value: UnexpectedEndOfInput) -> Self {
        StdErr::Unexpected(Unexpected::from(value))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StdSummary<Item> {
    pub unexpected: Option<Unexpected<Item>>,
    pub expected: Vec<Expected<()>>,
}

impl<Item> StdSummary<Item> {
    pub fn is_empty(&self) -> bool {
        self.unexpected.is_none() && self.expected.is_empty()
    }
}

impl<Item: Clone> MergeErrors for StdErr<Item> {
    type Output = StdSummary<Item>;

    fn merge(errors: &[Self]) -> Self::Output {
        let mut unexpected = None;
        let mut expected: Vec<Expected<()>> = Vec::new();
        let mut max_start: Option<u64> = None;

        for e in errors {
            match e {
                StdErr::Unexpected(u) => {
                    if unexpected.is_none() {
                        unexpected = Some(u.clone());
                    }
                }
                StdErr::Expected(x) => match max_start {
                    None => {
                        max_start = Some(x.start);
                        expected.push(x.clone());
                    }
                    Some(cur) => match x.start.cmp(&cur) {
                        Ordering::Less => {}
                        Ordering::Equal => expected.push(x.clone()),
                        Ordering::Greater => {
                            max_start = Some(x.start);
                            expected.clear();
                            expected.push(x.clone());
                        }
                    },
                },
            }
        }

        let mut dedup = Vec::<Expected<()>>::new();
        for x in expected {
            if dedup.iter().any(|y| y.label == x.label) {
                continue;
            }
            dedup.push(x);
        }

        StdSummary {
            unexpected,
            expected: dedup,
        }
    }
}

impl<Item: fmt::Debug> fmt::Display for StdSummary<Item> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            return f.write_str("<no error>");
        }

        if let Some(u) = &self.unexpected {
            write!(f, "unexpected {u}")?;
        }

        if !self.expected.is_empty() {
            if self.unexpected.is_some() {
                f.write_str(", ")?;
            }
            f.write_str("expecting ")?;
            for (i, e) in self.expected.iter().enumerate() {
                if i > 0 {
                    f.write_str(" or ")?;
                }
                write!(f, "{e}")?;
            }
        }

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Name(pub String);

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct Path {
    pub segments: Vec<Name>,
}

impl Path {
    pub fn new(segments: Vec<Name>) -> Self {
        Self { segments }
    }

    pub fn from_name(name: Name) -> Self {
        Self {
            segments: vec![name],
        }
    }

    pub fn push(&mut self, name: Name) {
        self.segments.push(name);
    }
}

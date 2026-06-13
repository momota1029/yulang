//! `mono` から軽量 control 表現へ下げて実行する VM crate。
//!
//! ここは本命 VM の置き場である。最初は `mono-runtime` で契約を検証し、その後にこの crate へ
//! control lowering と frame machine を移す。

#![forbid(unsafe_code)]

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Program {
    pub roots: Vec<Root>,
    pub instances: Vec<Instance>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Root {
    Instance(u32),
    Expr(u32),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Instance {
    pub id: u32,
    pub entry: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LowerError {
    UnsupportedMonoShape,
}

pub fn lower(program: &mono::Program) -> Result<Program, LowerError> {
    if program.roots.is_empty() && program.instances.is_empty() {
        return Ok(Program::default());
    }
    Err(LowerError::UnsupportedMonoShape)
}

#[cfg(test)]
mod tests {
    use super::{Program, lower};

    #[test]
    fn lowers_empty_program() {
        assert_eq!(lower(&mono::Program::default()), Ok(Program::default()));
    }
}

use yulang_core_ir as core_ir;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeModule {
    pub functions: Vec<NativeFunction>,
    pub roots: Vec<NativeFunction>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeFunction {
    pub name: String,
    pub params: Vec<ValueId>,
    pub blocks: Vec<NativeBlock>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeBlock {
    pub id: BlockId,
    pub params: Vec<ValueId>,
    pub stmts: Vec<NativeStmt>,
    pub terminator: NativeTerminator,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeStmt {
    Literal {
        dest: ValueId,
        literal: NativeLiteral,
    },
    Primitive {
        dest: ValueId,
        op: core_ir::PrimitiveOp,
        args: Vec<ValueId>,
    },
    DirectCall {
        dest: ValueId,
        target: String,
        args: Vec<ValueId>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeTerminator {
    Return(ValueId),
    Jump {
        target: BlockId,
        args: Vec<ValueId>,
    },
    Branch {
        cond: ValueId,
        then_block: BlockId,
        else_block: BlockId,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeLiteral {
    Int(String),
    Float(String),
    String(String),
    Bool(bool),
    Unit,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ValueId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BlockId(pub usize);

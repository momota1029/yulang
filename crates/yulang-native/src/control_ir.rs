use yulang_typed_ir as typed_ir;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeModule {
    pub functions: Vec<NativeFunction>,
    pub roots: Vec<NativeFunction>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeFunction {
    pub name: String,
    pub captures: Vec<ValueId>,
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
        op: typed_ir::PrimitiveOp,
        args: Vec<ValueId>,
    },
    DirectCall {
        dest: ValueId,
        target: String,
        args: Vec<ValueId>,
    },
    Tuple {
        dest: ValueId,
        items: Vec<ValueId>,
    },
    Record {
        dest: ValueId,
        base: Option<ValueId>,
        fields: Vec<NativeRecordField>,
    },
    Variant {
        dest: ValueId,
        tag: typed_ir::Name,
        value: Option<ValueId>,
    },
    Select {
        dest: ValueId,
        base: ValueId,
        field: typed_ir::Name,
    },
    TupleGet {
        dest: ValueId,
        tuple: ValueId,
        index: usize,
    },
    VariantTagEq {
        dest: ValueId,
        variant: ValueId,
        tag: typed_ir::Name,
    },
    VariantPayload {
        dest: ValueId,
        variant: ValueId,
    },
    MakeClosure {
        dest: ValueId,
        target: String,
        captures: Vec<ValueId>,
    },
    ClosureCall {
        dest: ValueId,
        callee: ValueId,
        args: Vec<ValueId>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeRecordField {
    pub name: typed_ir::Name,
    pub value: ValueId,
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

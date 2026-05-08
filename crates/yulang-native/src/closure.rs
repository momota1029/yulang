use crate::control_ir::{NativeFunction, NativeModule, ValueId};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeClosureModule {
    pub functions: Vec<NativeClosureFunction>,
    pub roots: Vec<NativeClosureFunction>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeClosureFunction {
    pub name: String,
    pub params: Vec<ValueId>,
    pub environment: NativeClosureEnvironment,
    pub code: NativeFunction,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeClosureEnvironment {
    pub slots: Vec<NativeClosureSlot>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NativeClosureSlot {
    pub index: usize,
    pub value: ValueId,
}

pub fn closure_convert_module(module: &NativeModule) -> NativeClosureModule {
    NativeClosureModule {
        functions: module
            .functions
            .iter()
            .map(closure_convert_function)
            .collect(),
        roots: module.roots.iter().map(closure_convert_function).collect(),
    }
}

fn closure_convert_function(function: &NativeFunction) -> NativeClosureFunction {
    let environment_slots = function
        .captures
        .iter()
        .copied()
        .enumerate()
        .map(|(index, value)| NativeClosureSlot { index, value })
        .collect();
    let params = function
        .params
        .iter()
        .copied()
        .filter(|param| !function.captures.contains(param))
        .collect();
    NativeClosureFunction {
        name: function.name.clone(),
        params,
        environment: NativeClosureEnvironment {
            slots: environment_slots,
        },
        code: function.clone(),
    }
}

#[cfg(test)]
mod tests {
    use crate::control_ir::{
        BlockId, NativeBlock, NativeFunction, NativeLiteral, NativeModule, NativeStmt,
        NativeTerminator, ValueId,
    };

    use super::*;

    #[test]
    fn converts_first_order_function_to_empty_environment_closure() {
        let function = NativeFunction {
            name: "root".to_string(),
            captures: Vec::new(),
            params: vec![ValueId(0)],
            blocks: vec![NativeBlock {
                id: BlockId(0),
                params: vec![ValueId(0)],
                stmts: vec![NativeStmt::Literal {
                    dest: ValueId(1),
                    literal: NativeLiteral::Int("1".to_string()),
                }],
                terminator: NativeTerminator::Return(ValueId(1)),
            }],
        };
        let module = NativeModule {
            functions: Vec::new(),
            roots: vec![function.clone()],
        };

        let converted = closure_convert_module(&module);

        assert_eq!(
            converted.roots,
            vec![NativeClosureFunction {
                name: "root".to_string(),
                params: vec![ValueId(0)],
                environment: NativeClosureEnvironment { slots: Vec::new() },
                code: function,
            }]
        );
    }

    #[test]
    fn separates_capture_params_into_environment_slots() {
        let function = NativeFunction {
            name: "root#lambda0".to_string(),
            captures: vec![ValueId(0)],
            params: vec![ValueId(0), ValueId(1)],
            blocks: vec![NativeBlock {
                id: BlockId(0),
                params: vec![ValueId(0), ValueId(1)],
                stmts: Vec::new(),
                terminator: NativeTerminator::Return(ValueId(1)),
            }],
        };
        let module = NativeModule {
            functions: vec![function.clone()],
            roots: Vec::new(),
        };

        let converted = closure_convert_module(&module);

        assert_eq!(converted.functions[0].params, vec![ValueId(1)]);
        assert_eq!(
            converted.functions[0].environment,
            NativeClosureEnvironment {
                slots: vec![NativeClosureSlot {
                    index: 0,
                    value: ValueId(0),
                }]
            }
        );
        assert_eq!(converted.functions[0].code, function);
    }
}

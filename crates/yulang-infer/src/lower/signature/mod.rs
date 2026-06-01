use rowan::TextRange;

use crate::ids::{NegId, PosId};
use crate::symbols::Name;

mod compact;
mod lower;
mod parse;
mod scope;

pub use compact::{
    collect_all_sig_vars, compact_sig_pattern_type, render_concrete_sig_type, sig_type_head,
};
pub use lower::{
    lower_function_sig_shape, lower_pure_sig_neg_id, lower_pure_sig_neg_type,
    lower_pure_sig_pos_id, lower_pure_sig_type, lower_sig_effect_arg, lower_sig_neg_id,
    lower_sig_pos_id, lower_sig_row_neg_id, lower_sig_row_pos_id,
};
pub(crate) use parse::parse_sig_row_literal_type_expr;
pub use parse::parse_sig_type_expr;
pub use scope::{act_type_param_names, fresh_type_scope, ordered_act_type_vars, ordered_type_vars};

#[derive(Debug, Clone)]
pub enum SigType {
    Prim {
        path: crate::symbols::Path,
        span: TextRange,
    },
    Apply {
        path: crate::symbols::Path,
        args: Vec<SigType>,
        span: TextRange,
    },
    Var(SigVar),
    Unit {
        span: TextRange,
    },
    Tuple {
        items: Vec<SigType>,
        span: TextRange,
    },
    Record {
        fields: Vec<SigRecordField>,
        span: TextRange,
    },
    RecordTailSpread {
        fields: Vec<SigRecordField>,
        tail: Box<SigType>,
        span: TextRange,
    },
    RecordHeadSpread {
        tail: Box<SigType>,
        fields: Vec<SigRecordField>,
        span: TextRange,
    },
    Fun {
        arg: Box<SigType>,
        ret_eff: Option<SigRow>,
        ret: Box<SigType>,
        span: TextRange,
    },
    /// `'[row]` の形。associated type が effect row 自体を値として束縛する
    /// `type throws = '[E]` のような注釈で使う。
    Row {
        row: SigRow,
        span: TextRange,
    },
    /// `[row] T` の形。引数を持たず、戻り型 `T` に effect row `row` を被せる
    /// 注釈シェイプ。role の `our e.method: [row] T` のような、受け手を暗黙化した
    /// メソッド注釈で使う。
    EffectPrefixed {
        eff: SigRow,
        ret: Box<SigType>,
        span: TextRange,
    },
}

impl SigType {
    pub fn span(&self) -> TextRange {
        match self {
            SigType::Prim { span, .. }
            | SigType::Apply { span, .. }
            | SigType::Unit { span }
            | SigType::Tuple { span, .. }
            | SigType::Record { span, .. }
            | SigType::RecordTailSpread { span, .. }
            | SigType::RecordHeadSpread { span, .. }
            | SigType::Fun { span, .. }
            | SigType::Row { span, .. }
            | SigType::EffectPrefixed { span, .. } => *span,
            SigType::Var(var) => var.span,
        }
    }
}

#[derive(Debug, Clone)]
pub struct SigRow {
    pub items: Vec<SigType>,
    pub tail: Option<SigVar>,
}

#[derive(Debug, Clone)]
pub struct SigVar {
    pub name: String,
    pub span: TextRange,
}

#[derive(Debug, Clone)]
pub struct SigRecordField {
    pub name: Name,
    pub ty: SigType,
    pub optional: bool,
}

#[derive(Debug, Clone)]
pub struct LoweredFunctionSigShape {
    pub arg_pos: PosId,
    pub arg_neg: NegId,
    pub ret_pos: PosId,
    pub ret_neg: NegId,
    pub ret_eff_pos: PosId,
    pub ret_eff_neg: NegId,
    pub effect_hint: bool,
}

//! Declaration-family grammar entered through statement admission or header discovery.
//! These owners do not classify statement starts or select header phases.

pub(super) mod act_decl;
pub(super) mod binding;
pub(super) mod cast_decl;
pub(super) mod declaration_companion;
pub(super) mod declaration_variant;
pub(super) mod derives;
pub(super) mod enum_decl;
pub(super) mod error_decl;
pub(super) mod fields;
pub(super) mod impl_decl;
mod impl_tail;
pub(super) mod mod_decl;
pub(super) mod operator_header;
pub(super) mod role_decl;
pub(super) mod struct_decl;
pub(super) mod type_decl;
pub(super) mod use_decl;

// Explicit entry surface for statement admission and header discovery.
pub(super) use act_decl::act_declaration_normalized;
pub(super) use act_decl::act_declaration_selected_lexical;
pub(super) use binding::binding_statement_normalized;
pub(super) use binding::binding_statement_selected_lexical;
pub(super) use binding::is_binding_visibility;
pub(super) use cast_decl::cast_declaration_normalized;
pub(super) use cast_decl::cast_declaration_selected_lexical;
pub(super) use enum_decl::enum_declaration_normalized;
pub(super) use enum_decl::enum_declaration_selected_lexical;
pub(super) use error_decl::error_declaration_normalized;
pub(super) use error_decl::error_declaration_selected_lexical;
pub(super) use impl_decl::impl_declaration_normalized;
pub(super) use impl_decl::impl_declaration_selected_lexical;
pub(super) use mod_decl::mod_declaration_normalized;
pub(super) use mod_decl::mod_declaration_selected_lexical;
pub(super) use operator_header::operator_header_normalized;
pub(super) use role_decl::role_declaration_normalized;
pub(super) use role_decl::role_declaration_selected_lexical;
pub(super) use struct_decl::struct_declaration_normalized;
pub(super) use struct_decl::struct_declaration_selected_lexical;
pub(super) use type_decl::type_declaration_normalized;
pub(super) use type_decl::type_declaration_selected_lexical;
pub(super) use use_decl::next_use_item_lex;
pub(super) use use_decl::use_declaration_header_normalized;
pub(super) use use_decl::use_declaration_normalized;
pub(super) use use_decl::use_declaration_selected_lexical;
pub(super) use use_decl::use_declaration_selected_normalized;

use std::collections::HashSet;

use yulang_parser::lex::SyntaxKind;

use crate::lower::SyntaxNode;

pub(crate) fn binding_sig_var_names(header: &SyntaxNode) -> Vec<String> {
    let mut out = Vec::new();
    for type_expr in header
        .descendants()
        .filter(|child| child.kind() == SyntaxKind::TypeExpr)
    {
        let Some(sig) = crate::lower::signature::parse_sig_type_expr(&type_expr) else {
            continue;
        };
        let mut vars = HashSet::new();
        crate::lower::signature::collect_all_sig_vars(&sig, &mut vars);
        let mut vars = vars.into_iter().collect::<Vec<_>>();
        vars.sort();
        for name in vars {
            if name != "_" && !out.contains(&name) {
                out.push(name);
            }
        }
    }
    out
}

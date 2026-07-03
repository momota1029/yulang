use super::*;

impl<'a, 'paths> TypeFormatter<'a, 'paths> {
    pub(super) fn new(arena: &'a TypeArena, namer: TypeVarNamer) -> Self {
        Self {
            arena,
            namer,
            path_rewriter: None,
            style: TypeFormatStyle::Debug,
            redactions: 0,
            truncations: 0,
            public_budget: PublicTypeBudget::default(),
            public_stack_boundary_count: 0,
        }
    }

    pub(super) fn new_with_path_rewriter(
        arena: &'a TypeArena,
        namer: TypeVarNamer,
        path_rewriter: PathRewriter<'paths>,
    ) -> Self {
        Self {
            arena,
            namer,
            path_rewriter: Some(path_rewriter),
            style: TypeFormatStyle::Debug,
            redactions: 0,
            truncations: 0,
            public_budget: PublicTypeBudget::default(),
            public_stack_boundary_count: 0,
        }
    }

    pub(super) fn new_public(arena: &'a TypeArena, namer: TypeVarNamer) -> Self {
        Self {
            arena,
            namer,
            path_rewriter: None,
            style: TypeFormatStyle::Public,
            redactions: 0,
            truncations: 0,
            public_budget: PublicTypeBudget::default(),
            public_stack_boundary_count: 0,
        }
    }

    pub(super) fn new_public_with_path_rewriter(
        arena: &'a TypeArena,
        namer: TypeVarNamer,
        path_rewriter: PathRewriter<'paths>,
    ) -> Self {
        Self {
            arena,
            namer,
            path_rewriter: Some(path_rewriter),
            style: TypeFormatStyle::Public,
            redactions: 0,
            truncations: 0,
            public_budget: PublicTypeBudget::default(),
            public_stack_boundary_count: 0,
        }
    }

    pub(super) fn format_scheme(mut self, scheme: &Scheme) -> String {
        self.format_scheme_text(scheme)
    }

    pub(super) fn format_scheme_public(mut self, scheme: &Scheme) -> PublicTypeDisplay {
        self.public_stack_boundary_count =
            PublicStackBoundaryScanner::new(self.arena).count_scheme(scheme);
        let text = self.format_scheme_text(scheme);
        PublicTypeDisplay {
            text,
            redactions: self.redactions,
            truncations: self.truncations,
        }
    }

    pub(super) fn format_neg_public(mut self, id: NegId) -> PublicTypeDisplay {
        self.public_stack_boundary_count =
            PublicStackBoundaryScanner::new(self.arena).count_neg(id);
        let text = self.neg(id, Context::Free);
        PublicTypeDisplay {
            text,
            redactions: self.redactions,
            truncations: self.truncations,
        }
    }

    fn format_scheme_text(&mut self, scheme: &Scheme) -> String {
        let mut body = self.pos(scheme.predicate, Context::Free);
        self.charge_public_text(&body);
        let mut predicates = Vec::new();
        for predicate in &scheme.role_predicates {
            if self.should_truncate_public_sequence_tail() {
                self.push_public_string_sequence_truncation(&mut predicates, ", ");
                break;
            }
            let rendered = self.role_predicate(predicate);
            self.push_public_string_sequence_part(&mut predicates, rendered, ", ");
        }
        if !predicates.is_empty() {
            let facts = predicates.join(", ");
            body.push_str(" where ");
            body.push_str(&facts);
        }
        body
    }

    pub(super) fn role_predicate(&mut self, predicate: &RolePredicate) -> String {
        let role = self.path_name(&predicate.role);
        let mut inputs = predicate
            .inputs
            .iter()
            .map(|arg| self.render_role_predicate_arg(*arg))
            .collect::<Vec<_>>();
        let associated = predicate
            .associated
            .iter()
            .map(|associated| {
                format!(
                    "{} = {}",
                    associated.name,
                    self.neu(associated.value, Context::Free)
                )
            })
            .collect::<Vec<_>>();

        if inputs.is_empty() {
            return self.role_call(role, inputs, associated);
        }

        if inputs[0].has_bare_space {
            return self.role_call(role, inputs, associated);
        }

        let subject = inputs.remove(0).in_context(Context::FunctionArg);
        let role = self.role_call(role, inputs, associated);
        format!("{subject}: {role}")
    }

    pub(super) fn render_role_predicate_arg(&mut self, arg: RolePredicateArg) -> Rendered {
        match arg {
            RolePredicateArg::Covariant(pos) => self.render_pos(pos),
            RolePredicateArg::Contravariant(neg) => self.render_neg(neg),
            RolePredicateArg::Invariant(neu) => self.render_neu(neu),
        }
    }

    pub(super) fn role_call(
        &mut self,
        role: String,
        args: Vec<Rendered>,
        associated: Vec<String>,
    ) -> String {
        if args.is_empty() && associated.is_empty() {
            return role;
        }

        if associated.is_empty() && !args.iter().any(|arg| arg.has_bare_space) {
            let mut parts = vec![role];
            parts.extend(args.into_iter().map(|arg| arg.in_context(Context::MlArg)));
            return parts.join(" ");
        }

        let mut parts = args.into_iter().map(|arg| arg.text).collect::<Vec<_>>();
        parts.extend(associated);
        format!("{}({})", role, parts.join(", "))
    }

    pub(super) fn subtractability_head(&mut self, path: &[String], args: &[NeuId]) -> String {
        let rendered = self.render_subtractability_con(path, args);
        if rendered.has_bare_space {
            format!("[{}]", rendered.in_context(Context::Free))
        } else {
            rendered.in_context(Context::Free)
        }
    }

    pub(super) fn render_subtractability_con(
        &mut self,
        path: &[String],
        args: &[NeuId],
    ) -> Rendered {
        let name = self.subtractability_path_name(path);
        if args.is_empty() {
            return Rendered::atom(name);
        }

        let args = args
            .iter()
            .map(|arg| self.render_neu(*arg))
            .collect::<Vec<_>>();
        if args.iter().any(|arg| arg.has_bare_space) {
            let args = args
                .into_iter()
                .map(|arg| arg.text)
                .collect::<Vec<_>>()
                .join(", ");
            Rendered::apply_c(format!("{name}({args})"))
        } else {
            let mut parts = Vec::with_capacity(args.len() + 1);
            parts.push(name);
            parts.extend(args.into_iter().map(|arg| arg.in_context(Context::MlArg)));
            Rendered::apply_ml(parts.join(" "))
        }
    }

    pub(super) fn pos(&mut self, id: PosId, context: Context) -> String {
        self.render_pos(id).in_context(context)
    }

    pub(super) fn neg(&mut self, id: NegId, context: Context) -> String {
        self.render_neg(id).in_context(context)
    }

    pub(super) fn neu(&mut self, id: NeuId, context: Context) -> String {
        self.render_neu(id).in_context(context)
    }

    pub(super) fn render_pos(&mut self, id: PosId) -> Rendered {
        if let Some(rendered) = self.enter_public_subtree() {
            return rendered;
        }
        let rendered = self.render_pos_node(id);
        self.exit_public_subtree();
        rendered
    }

    fn render_pos_node(&mut self, id: PosId) -> Rendered {
        match self.arena.pos(id) {
            Pos::Bot => Rendered::atom("never"),
            Pos::Var(var) => Rendered::atom(self.namer.name(*var)),
            Pos::Con(path, args) => self.render_con(path, args, NeuPolarity::Positive),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => self.render_pos_fun(*arg, *arg_eff, *ret_eff, *ret),
            Pos::Record(fields) => {
                Rendered::atom(self.record(fields, |this, id| this.pos(id, Context::Free)))
            }
            Pos::RecordTailSpread { fields, tail } => {
                Rendered::atom(self.record_spread_tail(fields, *tail))
            }
            Pos::RecordHeadSpread { tail, fields } => {
                Rendered::atom(self.record_spread_head(*tail, fields))
            }
            Pos::PolyVariant(items) => {
                Rendered::atom(self.variant(items, |this, id| this.pos(id, Context::MlArg)))
            }
            Pos::Tuple(items) => {
                Rendered::atom(self.tuple(items, |this, id| this.pos(id, Context::Free)))
            }
            Pos::Row(items) => Rendered::atom(format!("'{}", self.pos_row_items(items))),
            Pos::Stack { inner, weight } => {
                if self.style == TypeFormatStyle::Public {
                    let inner = self.render_pos(*inner);
                    return self.render_public_stack_postfix(inner, weight);
                }
                if is_hidden_quantifier_stack(weight) {
                    return self.render_pos(*inner);
                }
                let inner = self.render_pos(*inner);
                if let Some(rendered) = self.render_stack_postfix(inner.clone(), weight) {
                    rendered
                } else {
                    let inner = inner.in_context(Context::Free);
                    Rendered::apply_c(format!("stack({inner}, {})", self.stack_weight(weight)))
                }
            }
            Pos::NonSubtract(pos, weight) => {
                if self.style == TypeFormatStyle::Public {
                    let inner = self.render_pos(*pos);
                    return self.render_public_stack_postfix(inner, weight);
                }
                let inner = self.render_pos(*pos);
                if let Some(rendered) = self.render_stack_postfix(inner.clone(), weight) {
                    rendered
                } else {
                    let inner = self.postfix_inner(inner);
                    Rendered::atom(format!("{inner}{}", self.stack_weight(weight)))
                }
            }
            Pos::Union(left, right) => {
                let parts = self.flatten_pos_union(*left, *right);
                Rendered::union(parts.join(" | "))
            }
        }
    }

    pub(super) fn render_neg(&mut self, id: NegId) -> Rendered {
        if let Some(rendered) = self.enter_public_subtree() {
            return rendered;
        }
        let rendered = self.render_neg_node(id);
        self.exit_public_subtree();
        rendered
    }

    fn render_neg_node(&mut self, id: NegId) -> Rendered {
        match self.arena.neg(id) {
            Neg::Top => Rendered::atom("any"),
            Neg::Bot => Rendered::atom("never"),
            Neg::Var(var) => Rendered::atom(self.namer.name(*var)),
            Neg::Con(path, args) => self.render_con(path, args, NeuPolarity::Negative),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => self.render_neg_fun(*arg, *arg_eff, *ret_eff, *ret),
            Neg::Record(fields) => {
                Rendered::atom(self.record(fields, |this, id| this.neg(id, Context::Free)))
            }
            Neg::PolyVariant(items) => {
                Rendered::atom(self.variant(items, |this, id| this.neg(id, Context::MlArg)))
            }
            Neg::Tuple(items) => {
                Rendered::atom(self.tuple(items, |this, id| this.neg(id, Context::Free)))
            }
            Neg::Row(items, tail) => Rendered::atom(format!("'{}", self.neg_row(items, *tail))),
            Neg::Stack { inner, weight } => {
                if self.style == TypeFormatStyle::Public {
                    let inner = self.render_neg(*inner);
                    return self.render_public_stack_postfix(inner, weight);
                }
                if is_hidden_quantifier_stack(weight) {
                    return self.render_neg(*inner);
                }
                let inner = self.render_neg(*inner);
                if let Some(rendered) = self.render_stack_postfix(inner.clone(), weight) {
                    rendered
                } else {
                    let inner = inner.in_context(Context::Free);
                    Rendered::apply_c(format!("stack({inner}, {})", self.stack_weight(weight)))
                }
            }
            Neg::Intersection(left, right) => {
                let parts = self.flatten_neg_intersection(*left, *right);
                Rendered::intersection(parts.join(" & "))
            }
        }
    }

    pub(super) fn render_neu(&mut self, id: NeuId) -> Rendered {
        if let Some(rendered) = self.enter_public_subtree() {
            return rendered;
        }
        let rendered = self.render_neu_node(id);
        self.exit_public_subtree();
        rendered
    }

    fn render_neu_node(&mut self, id: NeuId) -> Rendered {
        match self.arena.neu(id) {
            Neu::Bounds(lower, upper) => {
                let center = self.bounds_center(*lower, *upper);
                if let Some(var) = center {
                    if self.is_plain_bounds(*lower, var, *upper) {
                        return Rendered::atom(self.namer.name(var));
                    }
                    if let Some(rendered) =
                        self.render_directional_bounds(*lower, var, *upper, NeuPolarity::Neutral)
                    {
                        return rendered;
                    }
                    return self.render_bounds(*lower, var, *upper);
                }
                self.render_centerless_bounds(*lower, *upper)
            }
            Neu::Con(path, args) => self.render_con(path, args, NeuPolarity::Neutral),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => self.render_neu_fun(*arg, *arg_eff, *ret_eff, *ret),
            Neu::Record(fields) => {
                Rendered::atom(self.record(fields, |this, id| this.neu(id, Context::Free)))
            }
            Neu::PolyVariant(items) => {
                Rendered::atom(self.variant(items, |this, id| this.neu(id, Context::MlArg)))
            }
            Neu::Tuple(items) => {
                Rendered::atom(self.tuple(items, |this, id| this.neu(id, Context::Free)))
            }
        }
    }

    pub(super) fn render_neu_with_polarity(
        &mut self,
        id: NeuId,
        polarity: NeuPolarity,
    ) -> Rendered {
        if let Some(rendered) = self.enter_public_subtree() {
            return rendered;
        }
        let rendered = self.render_neu_with_polarity_node(id, polarity);
        self.exit_public_subtree();
        rendered
    }

    fn render_neu_with_polarity_node(&mut self, id: NeuId, polarity: NeuPolarity) -> Rendered {
        match self.arena.neu(id) {
            Neu::Bounds(lower, upper) => {
                let center = self.bounds_center(*lower, *upper);
                if let Some(var) = center {
                    if self.is_plain_bounds(*lower, var, *upper) {
                        return Rendered::atom(self.namer.name(var));
                    }
                    if let Some(rendered) =
                        self.render_directional_bounds(*lower, var, *upper, polarity)
                    {
                        return rendered;
                    }
                    return self.render_bounds(*lower, var, *upper);
                }
                self.render_centerless_bounds(*lower, *upper)
            }
            Neu::Con(path, args) => self.render_con(path, args, polarity),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => self.render_neu_fun(*arg, *arg_eff, *ret_eff, *ret),
            Neu::Record(fields) => {
                Rendered::atom(self.record(fields, |this, id| this.neu(id, Context::Free)))
            }
            Neu::PolyVariant(items) => {
                Rendered::atom(self.variant(items, |this, id| this.neu(id, Context::MlArg)))
            }
            Neu::Tuple(items) => {
                Rendered::atom(self.tuple(items, |this, id| this.neu(id, Context::Free)))
            }
        }
    }

    pub(super) fn render_con(
        &mut self,
        path: &[String],
        args: &[NeuId],
        polarity: NeuPolarity,
    ) -> Rendered {
        if args.is_empty() && matches!(path, [name] if name == "unit") {
            return Rendered::atom("()");
        }
        let name = self.path_name(path);
        if args.is_empty() {
            return Rendered::atom(name);
        }

        let mut rendered_args = Vec::new();
        for arg in args {
            if self.should_truncate_public_sequence_tail() {
                self.push_public_rendered_sequence_truncation(&mut rendered_args, ", ");
                break;
            }
            let rendered = self.render_neu_with_polarity(*arg, polarity);
            self.push_public_rendered_sequence_part(&mut rendered_args, rendered, ", ");
        }
        let args = rendered_args;
        if args.iter().any(|arg| arg.has_bare_space) {
            let args = args
                .into_iter()
                .map(|arg| arg.text)
                .collect::<Vec<_>>()
                .join(", ");
            Rendered::apply_c(format!("{name}({args})"))
        } else {
            let mut parts = Vec::with_capacity(args.len() + 1);
            parts.push(name);
            parts.extend(args.into_iter().map(|arg| arg.in_context(Context::MlArg)));
            Rendered::apply_ml(parts.join(" "))
        }
    }

    pub(super) fn render_pos_fun(
        &mut self,
        arg: NegId,
        arg_eff: NegId,
        ret_eff: PosId,
        ret: PosId,
    ) -> Rendered {
        let arg = self.neg(arg, Context::FunctionArg);
        let arg_eff = self.neg_row_inline(arg_eff);
        let ret_eff = self.pos_row_inline(ret_eff);
        let ret = self.pos(ret, Context::Free);
        Rendered::arrow(fun_text(arg, arg_eff, ret_eff, ret))
    }

    pub(super) fn render_neg_fun(
        &mut self,
        arg: PosId,
        arg_eff: PosId,
        ret_eff: NegId,
        ret: NegId,
    ) -> Rendered {
        let arg = self.pos(arg, Context::FunctionArg);
        let arg_eff = self.pos_row_inline(arg_eff);
        let ret_eff = self.neg_row_inline(ret_eff);
        let ret = self.neg(ret, Context::Free);
        Rendered::arrow(fun_text(arg, arg_eff, ret_eff, ret))
    }

    pub(super) fn render_neu_fun(
        &mut self,
        arg: NeuId,
        arg_eff: NeuId,
        ret_eff: NeuId,
        ret: NeuId,
    ) -> Rendered {
        let arg = self.neu(arg, Context::FunctionArg);
        let arg_eff = Some(self.neu(arg_eff, Context::Free));
        let ret_eff = Some(self.neu(ret_eff, Context::Free));
        let ret = self.neu(ret, Context::Free);
        Rendered::arrow(fun_text(arg, arg_eff, ret_eff, ret))
    }

    pub(super) fn record<Id: Copy>(
        &mut self,
        fields: &[RecordField<Id>],
        mut format: impl FnMut(&mut Self, Id) -> String,
    ) -> String {
        let mut fields_text = Vec::new();
        for field in fields {
            if self.should_truncate_public_sequence_tail() {
                self.push_public_string_sequence_truncation(&mut fields_text, ", ");
                break;
            }
            let rendered = self.record_field(field, &mut format);
            self.push_public_string_sequence_part(&mut fields_text, rendered, ", ");
        }
        let fields = fields_text.join(", ");
        format!("{{{fields}}}")
    }

    pub(super) fn record_field<Id: Copy>(
        &mut self,
        field: &RecordField<Id>,
        format: &mut impl FnMut(&mut Self, Id) -> String,
    ) -> String {
        format!(
            "{}{}: {}",
            self.surface_name(&field.name),
            if field.optional { "?" } else { "" },
            format(self, field.value)
        )
    }

    pub(super) fn record_spread_tail(
        &mut self,
        fields: &[RecordField<PosId>],
        tail: PosId,
    ) -> String {
        let mut items = Vec::new();
        let mut sequence_truncated = false;
        for field in fields {
            if self.should_truncate_public_sequence_tail() {
                self.push_public_string_sequence_truncation(&mut items, ", ");
                sequence_truncated = true;
                break;
            }
            let rendered = self.record_field(field, &mut |this, id| this.pos(id, Context::Free));
            self.push_public_string_sequence_part(&mut items, rendered, ", ");
        }
        if sequence_truncated {
            return format!("{{{}}}", items.join(", "));
        }
        if !self.should_truncate_public_sequence_tail() {
            let rendered = format!("..{}", self.pos(tail, Context::Free));
            self.push_public_string_sequence_part(&mut items, rendered, ", ");
        } else {
            self.push_public_string_sequence_truncation(&mut items, ", ");
        }
        format!("{{{}}}", items.join(", "))
    }

    pub(super) fn record_spread_head(
        &mut self,
        tail: PosId,
        fields: &[RecordField<PosId>],
    ) -> String {
        let mut items = Vec::new();
        let tail_truncated = if self.should_truncate_public_sequence_tail() {
            self.push_public_string_sequence_truncation(&mut items, ", ");
            true
        } else {
            let rendered = format!("..{}", self.pos(tail, Context::Free));
            self.push_public_string_sequence_part(&mut items, rendered, ", ");
            false
        };
        if !tail_truncated {
            for field in fields {
                if self.should_truncate_public_sequence_tail() {
                    self.push_public_string_sequence_truncation(&mut items, ", ");
                    break;
                }
                let rendered =
                    self.record_field(field, &mut |this, id| this.pos(id, Context::Free));
                self.push_public_string_sequence_part(&mut items, rendered, ", ");
            }
        }
        format!("{{{}}}", items.join(", "))
    }

    pub(super) fn variant<Id: Copy>(
        &mut self,
        items: &[(String, Vec<Id>)],
        mut format: impl FnMut(&mut Self, Id) -> String,
    ) -> String {
        let mut item_texts = Vec::new();
        for (name, payloads) in items {
            if self.should_truncate_public_sequence_tail() {
                self.push_public_string_sequence_truncation(&mut item_texts, ", ");
                break;
            }
            let rendered = if payloads.is_empty() {
                self.surface_name(name)
            } else {
                let mut payload_texts = Vec::new();
                for payload in payloads {
                    if self.should_truncate_public_sequence_tail() {
                        self.push_public_string_sequence_truncation(&mut payload_texts, " ");
                        break;
                    }
                    let rendered = format(self, *payload);
                    self.push_public_string_sequence_part(&mut payload_texts, rendered, " ");
                }
                format!("{} {}", self.surface_name(name), payload_texts.join(" "))
            };
            self.push_public_string_sequence_part(&mut item_texts, rendered, ", ");
        }
        let items = item_texts.join(", ");
        format!(":{{{items}}}")
    }

    pub(super) fn tuple<Id: Copy>(
        &mut self,
        items: &[Id],
        mut format: impl FnMut(&mut Self, Id) -> String,
    ) -> String {
        match items {
            [] => "()".to_string(),
            [only] => format!("({},)", format(self, *only)),
            _ => {
                let mut item_texts = Vec::new();
                for item in items {
                    if self.should_truncate_public_sequence_tail() {
                        self.push_public_string_sequence_truncation(&mut item_texts, ", ");
                        break;
                    }
                    let rendered = format(self, *item);
                    self.push_public_string_sequence_part(&mut item_texts, rendered, ", ");
                }
                format!("({})", item_texts.join(", "))
            }
        }
    }

    fn rewritten_path(&self, path: &[String]) -> Vec<String> {
        self.path_rewriter
            .map(|rewrite| rewrite(path))
            .unwrap_or_else(|| path.to_vec())
    }

    fn path_name(&mut self, path: &[String]) -> String {
        self.rewritten_path(path)
            .iter()
            .map(|segment| self.surface_name(segment))
            .collect::<Vec<_>>()
            .join("::")
    }

    fn subtractability_path_name(&mut self, path: &[String]) -> String {
        self.rewritten_path(path)
            .iter()
            .map(|segment| self.subtractability_surface_name(segment))
            .collect::<Vec<_>>()
            .join("::")
    }

    fn surface_name(&mut self, name: &str) -> String {
        match self.style {
            TypeFormatStyle::Debug => surface_name(name),
            TypeFormatStyle::Public if public_name_needs_redaction(name, false) => self.redact(),
            TypeFormatStyle::Public => name.to_string(),
        }
    }

    fn subtractability_surface_name(&mut self, name: &str) -> String {
        match self.style {
            TypeFormatStyle::Debug => subtractability_surface_name(name),
            TypeFormatStyle::Public if public_name_needs_redaction(name, true) => self.redact(),
            TypeFormatStyle::Public => name.to_string(),
        }
    }

    fn redact(&mut self) -> String {
        self.redactions = self.redactions.saturating_add(1);
        PUBLIC_REDACTION.to_string()
    }

    fn redacted_rendered(&mut self) -> Rendered {
        Rendered::atom(self.redact())
    }

    fn enter_public_subtree(&mut self) -> Option<Rendered> {
        if self.style != TypeFormatStyle::Public {
            return None;
        }
        if self.public_budget.depth > PUBLIC_MAX_RENDER_DEPTH
            || self.public_budget.rendered_chars > PUBLIC_MAX_RENDERED_CHARS
        {
            return Some(self.public_truncation_rendered());
        }
        self.public_budget.depth += 1;
        None
    }

    fn exit_public_subtree(&mut self) {
        if self.style == TypeFormatStyle::Public {
            self.public_budget.depth = self.public_budget.depth.saturating_sub(1);
        }
    }

    fn should_truncate_public_sequence_tail(&self) -> bool {
        self.style == TypeFormatStyle::Public
            && self.public_budget.rendered_chars > PUBLIC_MAX_RENDERED_CHARS
    }

    fn public_truncation_text(&mut self) -> String {
        self.truncations = self.truncations.saturating_add(1);
        PUBLIC_REDACTION.to_string()
    }

    fn public_truncation_rendered(&mut self) -> Rendered {
        let rendered = Rendered::atom(self.public_truncation_text());
        self.charge_public_text(&rendered.text);
        rendered
    }

    fn push_public_string_sequence_part(
        &mut self,
        parts: &mut Vec<String>,
        part: String,
        separator: &str,
    ) {
        if !parts.is_empty() {
            self.charge_public_text(separator);
        }
        self.charge_public_text(&part);
        parts.push(part);
    }

    fn push_public_string_sequence_truncation(&mut self, parts: &mut Vec<String>, separator: &str) {
        if parts.last().is_some_and(|part| part == PUBLIC_REDACTION) {
            return;
        }
        let part = self.public_truncation_text();
        self.push_public_string_sequence_part(parts, part, separator);
    }

    fn push_public_rendered_sequence_part(
        &mut self,
        parts: &mut Vec<Rendered>,
        part: Rendered,
        separator: &str,
    ) {
        if !parts.is_empty() {
            self.charge_public_text(separator);
        }
        self.charge_public_text(&part.text);
        parts.push(part);
    }

    fn push_public_rendered_sequence_truncation(
        &mut self,
        parts: &mut Vec<Rendered>,
        separator: &str,
    ) {
        if parts
            .last()
            .is_some_and(|part| part.text == PUBLIC_REDACTION)
        {
            return;
        }
        let part = Rendered::atom(self.public_truncation_text());
        self.push_public_rendered_sequence_part(parts, part, separator);
    }

    fn charge_public_text(&mut self, text: &str) {
        if self.style == TypeFormatStyle::Public {
            self.public_budget.rendered_chars = self
                .public_budget
                .rendered_chars
                .saturating_add(text.chars().count());
        }
    }

    pub(super) fn neg_row_inline(&mut self, id: NegId) -> Option<String> {
        self.render_neg_row_inline(id).map(|rendered| rendered.text)
    }

    pub(super) fn render_neg_row_inline(&mut self, id: NegId) -> Option<Rendered> {
        match self.arena.neg(id) {
            Neg::Top => None,
            Neg::Bot => None,
            Neg::Row(items, tail) => self.render_neg_row_inline_items(items, *tail),
            Neg::Intersection(left, right) => {
                let mut parts = Vec::new();
                if let Some(left) = self.render_neg_row_intersection_part(*left) {
                    parts.push(left);
                }
                if let Some(right) = self.render_neg_row_intersection_part(*right) {
                    parts.push(right);
                }
                (!parts.is_empty()).then(|| Rendered::intersection(parts.join(" & ")))
            }
            _ => Some(self.render_neg(id)),
        }
    }

    pub(super) fn render_neg_row_intersection_part(&mut self, id: NegId) -> Option<String> {
        let rendered = match self.arena.neg(id) {
            Neg::Intersection(left, right) => {
                let mut parts = Vec::new();
                if let Some(left) = self.render_neg_row_intersection_part(*left) {
                    parts.push(left);
                }
                if let Some(right) = self.render_neg_row_intersection_part(*right) {
                    parts.push(right);
                }
                (!parts.is_empty()).then(|| Rendered::intersection(parts.join(" & ")))?
            }
            Neg::Row(items, tail) => self.render_neg_row_inline_items(items, *tail)?,
            _ => self.render_neg_row_inline(id)?,
        };
        if rendered.has_bare_space {
            Some(format!("[{}]", rendered.text))
        } else {
            Some(rendered.text)
        }
    }

    pub(super) fn render_neg_row_inline_items(
        &mut self,
        items: &[NegId],
        tail: NegId,
    ) -> Option<Rendered> {
        let mut rendered_items = Vec::new();
        for item in items {
            if self.should_truncate_public_sequence_tail() {
                self.push_public_rendered_sequence_truncation(&mut rendered_items, ", ");
                break;
            }
            let rendered = self.render_neg(*item);
            self.push_public_rendered_sequence_part(&mut rendered_items, rendered, ", ");
        }
        let item_has_bare_space = rendered_items.iter().any(|item| item.has_bare_space);
        let item_texts = rendered_items
            .into_iter()
            .map(|item| item.in_context(Context::Free))
            .collect::<Vec<_>>();
        match self.arena.neg(tail) {
            Neg::Top if item_texts.is_empty() => None,
            Neg::Top => {
                let text = item_texts.join(", ");
                Some(Rendered {
                    text,
                    prec: Prec::Atom,
                    has_bare_space: item_has_bare_space || item_texts.len() > 1,
                })
            }
            _ => {
                let tail = self
                    .render_neg_row_inline(tail)
                    .unwrap_or_else(|| self.render_neg(tail));
                if item_texts.is_empty() {
                    Some(tail)
                } else {
                    Some(Rendered {
                        text: format!("{}; {}", item_texts.join(", "), tail.text),
                        prec: Prec::Atom,
                        has_bare_space: true,
                    })
                }
            }
        }
    }

    pub(super) fn neg_row(&mut self, items: &[NegId], tail: NegId) -> String {
        self.render_neg_row_inline_items(items, tail)
            .map(|items| format!("[{}]", items.text))
            .unwrap_or_else(|| "[]".to_string())
    }

    pub(super) fn pos_row_inline(&mut self, id: PosId) -> Option<String> {
        let parts = self.collect_pos_row_parts(id);
        if parts.is_empty() {
            return None;
        }
        let mut items = Vec::new();
        let mut tails = Vec::new();
        for part in parts {
            match part {
                PosRowPart::Item(item) => {
                    if self.should_truncate_public_sequence_tail() {
                        self.push_public_string_sequence_truncation(&mut items, ", ");
                        break;
                    }
                    self.push_public_string_sequence_part(&mut items, item, ", ");
                }
                PosRowPart::Tail(tail) => tails.push(tail),
            }
        }
        for tail in tails {
            if self.should_truncate_public_sequence_tail() {
                self.push_public_string_sequence_truncation(&mut items, ", ");
                break;
            }
            self.push_public_string_sequence_part(&mut items, tail, ", ");
        }
        Some(items.join(", "))
    }

    pub(super) fn pos_row_items(&mut self, items: &[PosId]) -> String {
        let mut rendered_items = Vec::new();
        'outer: for item in items {
            for part in self.collect_pos_row_parts(*item) {
                if self.should_truncate_public_sequence_tail() {
                    self.push_public_string_sequence_truncation(&mut rendered_items, ", ");
                    break 'outer;
                }
                let rendered = match part {
                    PosRowPart::Item(item) | PosRowPart::Tail(item) => item,
                };
                self.push_public_string_sequence_part(&mut rendered_items, rendered, ", ");
            }
        }
        if rendered_items.is_empty() {
            "[]".to_string()
        } else {
            format!("[{}]", rendered_items.join(", "))
        }
    }

    pub(super) fn collect_pos_row_parts(&mut self, id: PosId) -> Vec<PosRowPart> {
        match self.arena.pos(id) {
            Pos::Bot => Vec::new(),
            Pos::Row(items) => {
                let mut parts = Vec::new();
                for item in items.clone() {
                    parts.extend(self.collect_pos_row_parts(item));
                }
                parts
            }
            Pos::Union(left, right) => {
                let mut parts = self.collect_pos_row_parts(*left);
                parts.extend(self.collect_pos_row_parts(*right));
                parts
            }
            Pos::Var(var) => vec![PosRowPart::Tail(self.namer.name(*var))],
            _ => vec![PosRowPart::Item(self.pos(id, Context::Free))],
        }
    }

    pub(super) fn flatten_pos_union(&mut self, left: PosId, right: PosId) -> Vec<String> {
        let mut parts = Vec::new();
        self.push_pos_union(left, &mut parts);
        self.push_pos_union(right, &mut parts);
        parts
    }

    pub(super) fn push_pos_union(&mut self, id: PosId, out: &mut Vec<String>) {
        if self.should_truncate_public_sequence_tail() {
            self.push_public_string_sequence_truncation(out, " | ");
            return;
        }
        match self.arena.pos(id) {
            Pos::Union(left, right) => {
                self.push_pos_union(*left, out);
                self.push_pos_union(*right, out);
            }
            _ => {
                let rendered = self.pos(id, Context::FunctionArg);
                self.push_public_string_sequence_part(out, rendered, " | ");
            }
        }
    }

    pub(super) fn flatten_neg_intersection(&mut self, left: NegId, right: NegId) -> Vec<String> {
        let mut parts = Vec::new();
        self.push_neg_intersection(left, &mut parts);
        self.push_neg_intersection(right, &mut parts);
        parts
    }

    pub(super) fn push_neg_intersection(&mut self, id: NegId, out: &mut Vec<String>) {
        if self.should_truncate_public_sequence_tail() {
            self.push_public_string_sequence_truncation(out, " & ");
            return;
        }
        match self.arena.neg(id) {
            Neg::Intersection(left, right) => {
                self.push_neg_intersection(*left, out);
                self.push_neg_intersection(*right, out);
            }
            _ => {
                let rendered = self.neg(id, Context::FunctionArg);
                self.push_public_string_sequence_part(out, rendered, " & ");
            }
        }
    }

    /// 不変な変数の仕様記法。共変部と反変部の2つ組を、共有変数を1つ選んで
    /// `lower|α&upper` と書く（spec/2026-06-02-role-system.md）。
    /// var 自身が両端の top-level union / intersection に現れる場合は重複して書かない。
    pub(super) fn render_bounds(&mut self, lower: PosId, var: TypeVar, upper: NegId) -> Rendered {
        let mut lower_parts = Vec::new();
        self.bounds_lower_parts(lower, var, &mut lower_parts);
        let mut upper_parts = Vec::new();
        self.bounds_upper_parts(upper, var, &mut upper_parts);

        if lower_parts.len() == 1 && lower_parts == upper_parts {
            return lower_parts.remove(0);
        }

        let mut text = if lower_parts.is_empty() {
            self.namer.name(var)
        } else {
            format!(
                "{} | {}",
                join_rendered_text(&lower_parts, " | "),
                self.namer.name(var)
            )
        };
        if !upper_parts.is_empty() {
            text.push_str(" & ");
            text.push_str(&join_rendered_text(&upper_parts, " & "));
        }
        if !lower_parts.is_empty() {
            Rendered::union(text)
        } else if !upper_parts.is_empty() {
            Rendered::intersection(text)
        } else {
            Rendered::atom(text)
        }
    }

    pub(super) fn render_centerless_bounds(&mut self, lower: PosId, upper: NegId) -> Rendered {
        let mut lower_parts = Vec::new();
        self.bounds_lower_parts_without_center(lower, &mut lower_parts);
        let mut upper_parts = Vec::new();
        self.bounds_upper_parts_without_center(upper, &mut upper_parts);

        if lower_parts.len() == 1 && lower_parts == upper_parts {
            return lower_parts.remove(0);
        }
        if upper_parts.is_empty() {
            return Rendered::union(join_rendered_text(&lower_parts, " | "));
        }
        if lower_parts.is_empty() {
            return Rendered::intersection(join_rendered_text(&upper_parts, " & "));
        }
        if self.style == TypeFormatStyle::Public {
            return self.redacted_rendered();
        }
        Rendered {
            text: format!(
                "{} <: {}",
                join_rendered_text(&lower_parts, " | "),
                join_rendered_text(&upper_parts, " & ")
            ),
            prec: Prec::Atom,
            has_bare_space: true,
        }
    }

    pub(super) fn bounds_center(&self, lower: PosId, upper: NegId) -> Option<TypeVar> {
        let mut lower_vars = Vec::new();
        self.bounds_lower_top_vars(lower, &mut lower_vars);
        lower_vars.sort_by_key(|var| var.0);
        lower_vars.dedup();
        let mut upper_vars = Vec::new();
        self.bounds_upper_top_vars(upper, &mut upper_vars);
        upper_vars.sort_by_key(|var| var.0);
        upper_vars.dedup();
        let common = lower_vars
            .into_iter()
            .filter(|var| upper_vars.contains(var))
            .collect::<Vec<_>>();
        (common.len() == 1).then(|| common[0])
    }

    pub(super) fn bounds_lower_top_vars(&self, id: PosId, out: &mut Vec<TypeVar>) {
        match self.arena.pos(id) {
            Pos::Var(var) => out.push(*var),
            Pos::Stack { inner, weight } if is_hidden_quantifier_stack(weight) => {
                self.bounds_lower_top_vars(*inner, out);
            }
            Pos::Union(left, right) => {
                self.bounds_lower_top_vars(*left, out);
                self.bounds_lower_top_vars(*right, out);
            }
            _ => {}
        }
    }

    pub(super) fn bounds_upper_top_vars(&self, id: NegId, out: &mut Vec<TypeVar>) {
        match self.arena.neg(id) {
            Neg::Var(var) => out.push(*var),
            Neg::Stack { inner, weight } if is_hidden_quantifier_stack(weight) => {
                self.bounds_upper_top_vars(*inner, out);
            }
            Neg::Intersection(left, right) => {
                self.bounds_upper_top_vars(*left, out);
                self.bounds_upper_top_vars(*right, out);
            }
            _ => {}
        }
    }

    pub(super) fn bounds_lower_parts(&mut self, id: PosId, var: TypeVar, out: &mut Vec<Rendered>) {
        if self.pos_is_plain_bounds_var(id, var) {
            return;
        }
        match self.arena.pos(id) {
            Pos::Union(left, right) => {
                let (left, right) = (*left, *right);
                self.bounds_lower_parts(left, var, out);
                self.bounds_lower_parts(right, var, out);
            }
            Pos::Bot => {}
            _ => {
                if self.should_truncate_public_sequence_tail() {
                    self.push_public_rendered_sequence_truncation(out, " | ");
                } else {
                    let rendered = self.render_pos(id).into_context(Context::FunctionArg);
                    self.push_public_rendered_sequence_part(out, rendered, " | ");
                }
            }
        }
    }

    pub(super) fn bounds_upper_parts(&mut self, id: NegId, var: TypeVar, out: &mut Vec<Rendered>) {
        if self.neg_is_plain_bounds_var(id, var) {
            return;
        }
        match self.arena.neg(id) {
            Neg::Intersection(left, right) => {
                let (left, right) = (*left, *right);
                self.bounds_upper_parts(left, var, out);
                self.bounds_upper_parts(right, var, out);
            }
            Neg::Top => {}
            _ => {
                if self.should_truncate_public_sequence_tail() {
                    self.push_public_rendered_sequence_truncation(out, " & ");
                } else {
                    let rendered = self.render_neg(id).into_context(Context::FunctionArg);
                    self.push_public_rendered_sequence_part(out, rendered, " & ");
                }
            }
        }
    }

    pub(super) fn bounds_lower_parts_without_center(&mut self, id: PosId, out: &mut Vec<Rendered>) {
        match self.arena.pos(id) {
            Pos::Union(left, right) => {
                let (left, right) = (*left, *right);
                self.bounds_lower_parts_without_center(left, out);
                self.bounds_lower_parts_without_center(right, out);
            }
            Pos::Bot => {}
            _ => {
                if self.should_truncate_public_sequence_tail() {
                    self.push_public_rendered_sequence_truncation(out, " | ");
                } else {
                    let rendered = self.render_pos(id).into_context(Context::FunctionArg);
                    self.push_public_rendered_sequence_part(out, rendered, " | ");
                }
            }
        }
    }

    pub(super) fn bounds_upper_parts_without_center(&mut self, id: NegId, out: &mut Vec<Rendered>) {
        match self.arena.neg(id) {
            Neg::Intersection(left, right) => {
                let (left, right) = (*left, *right);
                self.bounds_upper_parts_without_center(left, out);
                self.bounds_upper_parts_without_center(right, out);
            }
            Neg::Top => {}
            _ => {
                if self.should_truncate_public_sequence_tail() {
                    self.push_public_rendered_sequence_truncation(out, " & ");
                } else {
                    let rendered = self.render_neg(id).into_context(Context::FunctionArg);
                    self.push_public_rendered_sequence_part(out, rendered, " & ");
                }
            }
        }
    }

    pub(super) fn is_plain_bounds(&self, lower: PosId, var: TypeVar, upper: NegId) -> bool {
        matches!(self.arena.pos(lower), Pos::Bot) && matches!(self.arena.neg(upper), Neg::Top)
            || self.pos_is_plain_bounds_var(lower, var) && self.neg_is_plain_bounds_var(upper, var)
    }

    pub(super) fn pos_is_plain_bounds_var(&self, id: PosId, var: TypeVar) -> bool {
        match self.arena.pos(id) {
            Pos::Var(found) => *found == var,
            Pos::Stack { inner, weight } if is_hidden_quantifier_stack(weight) => {
                self.pos_is_plain_bounds_var(*inner, var)
            }
            _ => false,
        }
    }

    pub(super) fn neg_is_plain_bounds_var(&self, id: NegId, var: TypeVar) -> bool {
        match self.arena.neg(id) {
            Neg::Var(found) => *found == var,
            Neg::Stack { inner, weight } if is_hidden_quantifier_stack(weight) => {
                self.neg_is_plain_bounds_var(*inner, var)
            }
            _ => false,
        }
    }

    pub(super) fn render_directional_bounds(
        &mut self,
        lower: PosId,
        var: TypeVar,
        upper: NegId,
        polarity: NeuPolarity,
    ) -> Option<Rendered> {
        match polarity {
            NeuPolarity::Negative
                if matches!(self.arena.pos(lower), Pos::Var(lower_var) if *lower_var == var)
                    && neg_contains_var(self.arena, upper, var)
                    && !matches!(self.arena.neg(upper), Neg::Var(upper_var) if *upper_var == var) =>
            {
                Some(self.render_neg(upper))
            }
            NeuPolarity::Positive
                if matches!(self.arena.neg(upper), Neg::Var(upper_var) if *upper_var == var)
                    && pos_contains_var(self.arena, lower, var)
                    && !matches!(self.arena.pos(lower), Pos::Var(lower_var) if *lower_var == var) =>
            {
                Some(self.render_pos(lower))
            }
            NeuPolarity::Neutral | NeuPolarity::Positive | NeuPolarity::Negative => None,
        }
    }

    pub(super) fn stack_weight(&mut self, weight: &StackWeight) -> String {
        if weight.is_empty() {
            return "@0".to_string();
        }
        let filter = if weight.has_filter() {
            Some(format!(
                "filter[{}]",
                self.stack_subtractability(weight.filter_set())
            ))
        } else {
            None
        };
        let entries = weight
            .entries()
            .iter()
            .map(|entry| {
                let id = self.namer.subtract_id(entry.id);
                let floor = entry
                    .floor
                    .iter()
                    .map(|subtractability| self.stack_subtractability(subtractability))
                    .collect::<Vec<_>>()
                    .join(", ");
                let stack = entry
                    .stack
                    .iter()
                    .map(|subtractability| self.stack_subtractability(subtractability))
                    .collect::<Vec<_>>()
                    .join(", ");
                if entry.floor.is_empty() {
                    format!("#{id} -> pop({})[{}]", entry.pops, stack)
                } else {
                    format!("#{id} -> floor[{floor}] pop({})[{stack}]", entry.pops)
                }
            })
            .collect::<Vec<_>>()
            .join(", ");
        let entries = match (filter, entries.is_empty()) {
            (Some(filter), true) => filter,
            (Some(filter), false) => format!("{filter}, {entries}"),
            (None, _) => entries,
        };
        format!("{{ {entries} }}")
    }

    pub(super) fn render_stack_postfix(
        &mut self,
        inner: Rendered,
        weight: &StackWeight,
    ) -> Option<Rendered> {
        let suffix = self.stack_weight_suffix(weight)?;
        let inner = self.postfix_inner(inner);
        Some(Rendered::atom(format!("{inner}{suffix}")))
    }

    fn render_public_stack_postfix(&mut self, inner: Rendered, weight: &StackWeight) -> Rendered {
        match self.public_stack_weight_suffix(weight) {
            PublicStackSuffix::Empty => inner,
            PublicStackSuffix::Rendered(suffix) => {
                let inner = self.postfix_inner(inner);
                Rendered::atom(format!("{inner}{suffix}"))
            }
            PublicStackSuffix::Redacted => {
                let inner = self.postfix_inner(inner);
                let redaction = self.redact();
                Rendered::atom(format!("{inner}{redaction}"))
            }
        }
    }

    fn postfix_inner(&self, inner: Rendered) -> String {
        if inner.prec == Prec::Atom && !inner.has_bare_space {
            inner.text
        } else {
            format!("({})", inner.text)
        }
    }

    fn stack_weight_suffix(&mut self, weight: &StackWeight) -> Option<String> {
        if weight.has_filter() {
            return None;
        }
        let [entry] = weight.entries() else {
            return None;
        };
        if !entry.floor.is_empty() || entry.pops == u32::MAX {
            return None;
        }
        if entry.pops == 0 && entry.stack.is_empty() {
            return None;
        }

        let id = self.namer.subtract_id(entry.id);
        let mut suffix = format!("#{id}");
        if entry.pops > 0 && !(entry.pops == 1 && entry.stack.is_empty()) {
            suffix.push_str(&format!("({})", entry.pops));
        }
        if !entry.stack.is_empty() {
            let stack = entry
                .stack
                .iter()
                .map(|subtractability| self.stack_subtractability(subtractability))
                .collect::<Vec<_>>()
                .join(", ");
            suffix.push_str(&format!("[{stack}]"));
        }
        Some(suffix)
    }

    fn public_stack_weight_suffix(&mut self, weight: &StackWeight) -> PublicStackSuffix {
        if weight.is_empty() || is_hidden_quantifier_stack(weight) {
            return PublicStackSuffix::Empty;
        }
        if weight.has_filter() {
            return PublicStackSuffix::Redacted;
        }
        let [entry] = weight.entries() else {
            return PublicStackSuffix::Redacted;
        };
        if !entry.floor.is_empty() || entry.pops == u32::MAX {
            return PublicStackSuffix::Redacted;
        }
        if entry.pops == 0 && entry.stack.is_empty() {
            return PublicStackSuffix::Empty;
        }

        let mut suffix = "@".to_string();
        if self.public_stack_boundary_count != 1 {
            suffix.push_str(&self.namer.subtract_id(entry.id).to_string());
        }
        if entry.pops > 0 && !(entry.pops == 1 && entry.stack.is_empty()) {
            suffix.push_str(&format!("({})", entry.pops));
        }
        for subtractability in &entry.stack {
            suffix.push_str(&self.public_stack_subtractability(subtractability));
        }
        PublicStackSuffix::Rendered(suffix)
    }

    fn public_stack_subtractability(&mut self, subtractability: &Subtractability) -> String {
        let omit_id = self.public_stack_boundary_count == 1;
        match subtractability {
            Subtractability::Empty if omit_id => "∅".to_string(),
            Subtractability::Empty => "(∅)".to_string(),
            Subtractability::All if omit_id => "∀".to_string(),
            Subtractability::All => "(∀)".to_string(),
            Subtractability::Set(path, args) => {
                format!("[{}]", self.public_subtractability_head(path, args))
            }
            Subtractability::SetMany(families) => {
                format!("[{}]", self.public_subtractability_heads(families))
            }
            Subtractability::AllExcept(path, args) => {
                format!(
                    "(except [{}])",
                    self.public_subtractability_head(path, args)
                )
            }
            Subtractability::AllExceptMany(families) => {
                format!("(except [{}])", self.public_subtractability_heads(families))
            }
        }
    }

    fn public_subtractability_heads(&mut self, families: &[(Vec<String>, Vec<NeuId>)]) -> String {
        families
            .iter()
            .map(|(path, args)| self.public_subtractability_head(path, args))
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn public_subtractability_head(&mut self, path: &[String], args: &[NeuId]) -> String {
        self.render_subtractability_con(path, args)
            .in_context(Context::Free)
    }

    pub(super) fn stack_subtractability(&mut self, subtractability: &Subtractability) -> String {
        match subtractability {
            Subtractability::Empty => "Empty".to_string(),
            Subtractability::All => "All".to_string(),
            Subtractability::Set(path, args) => self.subtractability_head(path, args),
            Subtractability::SetMany(families) => families
                .iter()
                .map(|(path, args)| self.subtractability_head(path, args))
                .collect::<Vec<_>>()
                .join(", "),
            Subtractability::AllExcept(path, args) => {
                format!("AllExcept({})", self.subtractability_head(path, args))
            }
            Subtractability::AllExceptMany(families) => {
                let heads = families
                    .iter()
                    .map(|(path, args)| self.subtractability_head(path, args))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("AllExcept({heads})")
            }
        }
    }
}

use super::*;

mod substitution;
pub(crate) use substitution::normalize_var_substitutions;
pub(super) use substitution::*;

pub(super) struct FreshCompactVars;

impl FreshCompactVars {
    pub(super) fn new(_root: &CompactRoot) -> Self {
        Self
    }
}
#[derive(Default)]
pub(super) struct VarPolarities {
    pub(super) positive: FxHashSet<TypeVar>,
    pub(super) negative: FxHashSet<TypeVar>,
}

impl VarPolarities {
    pub(super) fn record(&mut self, var: TypeVar, polarity: Polarity) {
        match polarity {
            Polarity::Positive => {
                self.positive.insert(var);
            }
            Polarity::Negative => {
                self.negative.insert(var);
            }
        }
    }

    pub(super) fn is_bipolar(&self, var: TypeVar) -> bool {
        self.positive.contains(&var) && self.negative.contains(&var)
    }
}
#[derive(Default)]
pub(super) struct VarPolarityCounts {
    positive: FxHashMap<TypeVar, usize>,
    negative: FxHashMap<TypeVar, usize>,
}

impl VarPolarityCounts {
    pub(super) fn record(&mut self, var: TypeVar, polarity: Polarity) {
        let table = match polarity {
            Polarity::Positive => &mut self.positive,
            Polarity::Negative => &mut self.negative,
        };
        *table.entry(var).or_default() += 1;
    }

    pub(super) fn count(&self, var: TypeVar, polarity: Polarity) -> usize {
        let table = match polarity {
            Polarity::Positive => &self.positive,
            Polarity::Negative => &self.negative,
        };
        table.get(&var).copied().unwrap_or(0)
    }
}

pub(super) fn collect_var_polarities(
    root: &CompactRoot,
    roles: &[CompactRoleConstraint],
) -> VarPolarities {
    let mut out = VarPolarities::default();
    visit_type_polarity(&root.root, Polarity::Positive, &mut out);
    for rec in &root.rec_vars {
        visit_bounds_polarity(&rec.bounds, Polarity::Positive, &mut out);
    }
    for role in roles {
        visit_role_polarity(role, &mut out);
    }
    out
}

pub(super) fn collect_var_polarity_counts(
    root: &CompactRoot,
    roles: &[CompactRoleConstraint],
) -> VarPolarityCounts {
    let mut out = VarPolarityCounts::default();
    visit_type_polarity_counts(&root.root, Polarity::Positive, &mut out);
    for rec in &root.rec_vars {
        visit_bounds_polarity_counts(&rec.bounds, Polarity::Positive, &mut out);
    }
    for role in roles {
        visit_role_polarity_counts(role, &mut out);
    }
    out
}

pub(super) fn collect_main_var_polarities(root: &CompactRoot) -> VarPolarities {
    let mut out = VarPolarities::default();
    visit_type_polarity(&root.root, Polarity::Positive, &mut out);
    for rec in &root.rec_vars {
        visit_bounds_polarity(&rec.bounds, Polarity::Positive, &mut out);
    }
    out
}

pub(super) fn visit_role_polarity(role: &CompactRoleConstraint, out: &mut VarPolarities) {
    for input in &role.inputs {
        visit_role_arg_polarity(input, Polarity::Positive, out);
    }
    for associated in &role.associated {
        visit_bounds_polarity(&associated.value.bounds, Polarity::Positive, out);
    }
}

pub(super) fn visit_role_arg_polarity(
    arg: &CompactRoleArg,
    polarity: Polarity,
    out: &mut VarPolarities,
) {
    match (&arg.bounds, arg.polarity) {
        (CompactBounds::Interval { lower, upper: _ }, CompactRoleArgPolarity::Covariant) => {
            visit_type_polarity(lower, polarity, out)
        }
        (CompactBounds::Interval { lower: _, upper }, CompactRoleArgPolarity::Contravariant) => {
            visit_type_polarity(upper, polarity.flipped(), out)
        }
        (_, CompactRoleArgPolarity::Invariant)
        | (_, CompactRoleArgPolarity::Covariant | CompactRoleArgPolarity::Contravariant) => {
            visit_bounds_polarity(&arg.bounds, polarity, out);
        }
    }
}

pub(super) fn visit_role_polarity_counts(
    role: &CompactRoleConstraint,
    out: &mut VarPolarityCounts,
) {
    for input in &role.inputs {
        visit_bounds_polarity_counts(&input.bounds, Polarity::Positive, out);
    }
    for associated in &role.associated {
        visit_bounds_polarity_counts(&associated.value.bounds, Polarity::Positive, out);
    }
}

pub(super) fn visit_type_polarity(ty: &CompactType, polarity: Polarity, out: &mut VarPolarities) {
    for var in &ty.vars {
        out.record(var.var, polarity);
    }
    for args in ty.cons.values() {
        for arg in args {
            visit_bounds_polarity(arg, polarity, out);
        }
    }
    for fun in &ty.funs {
        visit_type_polarity(&fun.arg, polarity.flipped(), out);
        visit_type_polarity(&fun.arg_eff, polarity.flipped(), out);
        visit_type_polarity(&fun.ret_eff, polarity, out);
        visit_type_polarity(&fun.ret, polarity, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            visit_type_polarity(&field.value, polarity, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            visit_type_polarity(&field.value, polarity, out);
        }
        visit_type_polarity(&spread.tail, polarity, out);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                visit_type_polarity(payload, polarity, out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            visit_type_polarity(item, polarity, out);
        }
    }
    for row in &ty.rows {
        for args in row.items.values() {
            for arg in args {
                visit_bounds_polarity(arg, polarity, out);
            }
        }
        visit_type_polarity(&row.tail, polarity, out);
    }
}

pub(super) fn visit_type_polarity_counts(
    ty: &CompactType,
    polarity: Polarity,
    out: &mut VarPolarityCounts,
) {
    for var in &ty.vars {
        out.record(var.var, polarity);
    }
    for args in ty.cons.values() {
        for arg in args {
            visit_bounds_polarity_counts(arg, polarity, out);
        }
    }
    for fun in &ty.funs {
        visit_type_polarity_counts(&fun.arg, polarity.flipped(), out);
        visit_type_polarity_counts(&fun.arg_eff, polarity.flipped(), out);
        visit_type_polarity_counts(&fun.ret_eff, polarity, out);
        visit_type_polarity_counts(&fun.ret, polarity, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            visit_type_polarity_counts(&field.value, polarity, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            visit_type_polarity_counts(&field.value, polarity, out);
        }
        visit_type_polarity_counts(&spread.tail, polarity, out);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                visit_type_polarity_counts(payload, polarity, out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            visit_type_polarity_counts(item, polarity, out);
        }
    }
    for row in &ty.rows {
        for args in row.items.values() {
            for arg in args {
                visit_bounds_polarity_counts(arg, polarity, out);
            }
        }
        visit_type_polarity_counts(&row.tail, polarity, out);
    }
}

pub(super) fn visit_bounds_polarity(
    bounds: &CompactBounds,
    polarity: Polarity,
    out: &mut VarPolarities,
) {
    match bounds {
        CompactBounds::Interval { lower, upper } => {
            visit_type_polarity(lower, polarity, out);
            visit_type_polarity(upper, polarity.flipped(), out);
        }
        CompactBounds::Con { args, .. } => {
            for arg in args {
                visit_bounds_polarity(arg, polarity, out);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            visit_bounds_polarity(arg, polarity.flipped(), out);
            visit_bounds_polarity(arg_eff, polarity.flipped(), out);
            visit_bounds_polarity(ret_eff, polarity, out);
            visit_bounds_polarity(ret, polarity, out);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                visit_bounds_polarity(&field.value, polarity, out);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    visit_bounds_polarity(payload, polarity, out);
                }
            }
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                visit_bounds_polarity(item, polarity, out);
            }
        }
    }
}

pub(super) fn visit_bounds_polarity_counts(
    bounds: &CompactBounds,
    polarity: Polarity,
    out: &mut VarPolarityCounts,
) {
    match bounds {
        CompactBounds::Interval { lower, upper } => {
            visit_type_polarity_counts(lower, polarity, out);
            visit_type_polarity_counts(upper, polarity.flipped(), out);
        }
        CompactBounds::Con { args, .. } => {
            for arg in args {
                visit_bounds_polarity_counts(arg, polarity, out);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            visit_bounds_polarity_counts(arg, polarity.flipped(), out);
            visit_bounds_polarity_counts(arg_eff, polarity.flipped(), out);
            visit_bounds_polarity_counts(ret_eff, polarity, out);
            visit_bounds_polarity_counts(ret, polarity, out);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                visit_bounds_polarity_counts(&field.value, polarity, out);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    visit_bounds_polarity_counts(payload, polarity, out);
                }
            }
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                visit_bounds_polarity_counts(item, polarity, out);
            }
        }
    }
}
#[derive(Default)]
pub(super) struct CoOccurrences {
    pub(super) positive: FxHashMap<TypeVar, FxHashSet<AlongItem>>,
    pub(super) negative: FxHashMap<TypeVar, FxHashSet<AlongItem>>,
    pub(super) interval_equalities: Vec<(TypeVar, TypeVar)>,
}

impl CoOccurrences {
    /// 不変区間 `[lower, upper]` は instantiation ごとに `lower ≤ 実型 ≤ upper` を要求するので、
    /// 両側に現れる変数は実型と等しく確定する。他の出現位置での同伴に関係なく、
    /// この区間単独を根拠に互いに（中心があれば中心と）併合できる。
    /// 具体型との等値は変数の除去になり他出現を壊すため、ここでは変数同士に限る。
    pub(super) fn record_interval_equalities(&mut self, lower: &CompactType, upper: &CompactType) {
        let upper_vars = upper
            .vars
            .iter()
            .map(|var| var.var)
            .collect::<FxHashSet<_>>();
        let mut both = lower
            .vars
            .iter()
            .map(|var| var.var)
            .filter(|var| upper_vars.contains(var))
            .collect::<Vec<_>>();
        both.sort_by_key(|var| var.0);
        both.dedup();
        for pair in both.windows(2) {
            self.interval_equalities.push((pair[0], pair[1]));
        }
    }

    pub(super) fn record_group(&mut self, group: FxHashSet<AlongItem>, polarity: Polarity) {
        let mut vars = group
            .iter()
            .filter_map(|item| match item {
                AlongItem::Var(var) => Some(*var),
                AlongItem::Exact(_) => None,
            })
            .collect::<Vec<_>>();
        vars.sort_by_key(|var| var.0);
        vars.dedup();
        if vars.is_empty() {
            return;
        }

        let table = match polarity {
            Polarity::Positive => &mut self.positive,
            Polarity::Negative => &mut self.negative,
        };
        for var in vars {
            match table.get_mut(&var) {
                Some(existing) => existing.retain(|item| group.contains(item)),
                None => {
                    table.insert(var, group.clone());
                }
            }
        }
    }

    pub(super) fn substitution(
        &self,
        machine: &ConstraintMachine,
        boundary: TypeLevel,
        non_generic: &FxHashSet<TypeVar>,
    ) -> VarSubstitution {
        let mut union = VarUnion::default();
        let mut removals = FxHashSet::default();
        for (alpha, beta) in &self.interval_equalities {
            register_co_occurrence_pair(*alpha, *beta, machine, boundary, non_generic, &mut union);
        }
        register_co_occurrence_table(
            &self.positive,
            &self.negative,
            machine,
            boundary,
            non_generic,
            &mut union,
        );
        register_co_occurrence_table(
            &self.negative,
            &self.positive,
            machine,
            boundary,
            non_generic,
            &mut union,
        );
        register_sandwich_flattening(
            &self.positive,
            &self.negative,
            machine,
            boundary,
            non_generic,
            &mut union,
            &mut removals,
        );
        register_sandwich_flattening(
            &self.negative,
            &self.positive,
            machine,
            boundary,
            non_generic,
            &mut union,
            &mut removals,
        );
        union.into_substitution(removals)
    }
}

pub(super) fn register_co_occurrence_table(
    table: &FxHashMap<TypeVar, FxHashSet<AlongItem>>,
    opposite: &FxHashMap<TypeVar, FxHashSet<AlongItem>>,
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    non_generic: &FxHashSet<TypeVar>,
    union: &mut VarUnion,
) {
    let mut vars = table.keys().copied().collect::<Vec<_>>();
    vars.sort_by_key(|var| var.0);
    for alpha in vars {
        let Some(items) = table.get(&alpha) else {
            continue;
        };
        let mut items = items.iter().cloned().collect::<Vec<_>>();
        items.sort_by_key(along_item_sort_key);
        for beta in items {
            let AlongItem::Var(beta) = beta else {
                continue;
            };
            if alpha == beta {
                continue;
            }
            if !table
                .get(&beta)
                .is_some_and(|beta_items| beta_items.contains(&AlongItem::Var(alpha)))
            {
                continue;
            }
            if !opposite_co_occurrence_compatible(alpha, beta, opposite) {
                continue;
            }
            register_co_occurrence_pair(alpha, beta, machine, boundary, non_generic, union);
        }
    }
}

pub(super) fn register_sandwich_flattening(
    table: &FxHashMap<TypeVar, FxHashSet<AlongItem>>,
    opposite: &FxHashMap<TypeVar, FxHashSet<AlongItem>>,
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    non_generic: &FxHashSet<TypeVar>,
    union: &mut VarUnion,
    removals: &mut FxHashSet<TypeVar>,
) {
    let mut vars = table.keys().copied().collect::<Vec<_>>();
    vars.sort_by_key(|var| var.0);
    for alpha in vars {
        if !is_simplification_candidate(machine, boundary, alpha, non_generic) {
            continue;
        }
        if union.find(alpha) != alpha {
            continue;
        }
        let (Some(items), Some(opposite_items)) = (table.get(&alpha), opposite.get(&alpha)) else {
            continue;
        };
        let mut sandwiches = items
            .iter()
            .filter(|item| **item != AlongItem::Var(alpha) && opposite_items.contains(item))
            .cloned()
            .collect::<Vec<_>>();
        sandwiches.sort_by_key(along_item_sort_key);
        let Some(sandwich) = sandwiches.into_iter().next() else {
            continue;
        };
        match sandwich {
            AlongItem::Var(beta) => {
                register_co_occurrence_pair(alpha, beta, machine, boundary, non_generic, union);
            }
            AlongItem::Exact(_) => {
                removals.insert(alpha);
            }
        }
    }
}

pub(super) fn opposite_co_occurrence_compatible(
    alpha: TypeVar,
    beta: TypeVar,
    opposite: &FxHashMap<TypeVar, FxHashSet<AlongItem>>,
) -> bool {
    let alpha_items = opposite.get(&alpha);
    let beta_items = opposite.get(&beta);
    if alpha_items == beta_items {
        return true;
    }
    let (Some(alpha_items), Some(beta_items)) = (alpha_items, beta_items) else {
        return false;
    };
    without_var(alpha_items, alpha) == *beta_items || without_var(beta_items, beta) == *alpha_items
}

pub(super) fn without_var(items: &FxHashSet<AlongItem>, var: TypeVar) -> FxHashSet<AlongItem> {
    items
        .iter()
        .filter(|item| **item != AlongItem::Var(var))
        .cloned()
        .collect()
}

pub(super) fn along_item_sort_key(item: &AlongItem) -> (u8, u32) {
    match item {
        AlongItem::Var(var) => (0, var.0),
        AlongItem::Exact(exact) => (1, exact.sort_key()),
    }
}

pub(super) fn register_co_occurrence_pair(
    alpha: TypeVar,
    beta: TypeVar,
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    non_generic: &FxHashSet<TypeVar>,
    union: &mut VarUnion,
) {
    let alpha_candidate = is_simplification_candidate(machine, boundary, alpha, non_generic);
    let beta_candidate = is_simplification_candidate(machine, boundary, beta, non_generic);
    if !alpha_candidate && !beta_candidate {
        return;
    }

    let rep = [alpha, beta]
        .into_iter()
        .min_by_key(|var| (machine.level_of(*var), var.0))
        .expect("pair should be non-empty");
    if alpha_candidate {
        union.union_to(rep, alpha);
    }
    if beta_candidate {
        union.union_to(rep, beta);
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum AlongItem {
    Var(TypeVar),
    Exact(ExactKey),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum ExactKey {
    Builtin(BuiltinType),
    Con(Vec<String>, usize),
    Fun,
    Record(Vec<(String, bool)>),
    RecordSpread(Vec<(String, bool)>),
    PolyVariant(Vec<(String, usize)>),
    Tuple(usize),
    Row(Vec<ExactKey>),
}

impl ExactKey {
    pub(super) fn sort_key(&self) -> u32 {
        match self {
            ExactKey::Builtin(_) => 0,
            ExactKey::Con(_, _) => 1,
            ExactKey::Fun => 2,
            ExactKey::Record(_) => 3,
            ExactKey::RecordSpread(_) => 4,
            ExactKey::PolyVariant(_) => 5,
            ExactKey::Tuple(_) => 6,
            ExactKey::Row(_) => 7,
        }
    }
}

pub(super) fn collect_co_occurrences(
    root: &CompactRoot,
    roles: &[CompactRoleConstraint],
) -> CoOccurrences {
    let mut out = CoOccurrences::default();
    let rec_vars = root.rec_vars.iter().map(|rec| rec.var).collect::<Vec<_>>();
    // Recursive center vars are counted through their Interval bounds via `extra_vars`.
    // Counting their root/role occurrences as ordinary singleton groups would prevent
    // the center from coalescing with the bounds that always sandwich it.
    visit_type_co_occurrence(&root.root, Polarity::Positive, &[], &rec_vars, &mut out);
    for rec in &root.rec_vars {
        visit_bounds_co_occurrence(&rec.bounds, Polarity::Positive, &[], &mut out);
    }
    for role in roles {
        visit_role_co_occurrence(role, &rec_vars, &mut out);
    }
    out
}

pub(super) fn visit_role_co_occurrence(
    role: &CompactRoleConstraint,
    ignored_vars: &[TypeVar],
    out: &mut CoOccurrences,
) {
    for input in &role.inputs {
        visit_role_arg_co_occurrence(input, Polarity::Positive, ignored_vars, out);
    }
    for associated in &role.associated {
        visit_bounds_co_occurrence(
            &associated.value.bounds,
            Polarity::Positive,
            ignored_vars,
            out,
        );
    }
}

pub(super) fn visit_role_arg_co_occurrence(
    arg: &CompactRoleArg,
    polarity: Polarity,
    ignored_vars: &[TypeVar],
    out: &mut CoOccurrences,
) {
    match (&arg.bounds, arg.polarity) {
        (CompactBounds::Interval { lower, upper: _ }, CompactRoleArgPolarity::Covariant) => {
            visit_type_co_occurrence(lower, polarity, &[], ignored_vars, out)
        }
        (CompactBounds::Interval { lower: _, upper }, CompactRoleArgPolarity::Contravariant) => {
            visit_type_co_occurrence(upper, polarity.flipped(), &[], ignored_vars, out)
        }
        (_, CompactRoleArgPolarity::Invariant)
        | (_, CompactRoleArgPolarity::Covariant | CompactRoleArgPolarity::Contravariant) => {
            visit_bounds_co_occurrence(&arg.bounds, polarity, ignored_vars, out);
        }
    }
}

pub(super) fn visit_type_co_occurrence(
    ty: &CompactType,
    polarity: Polarity,
    extra_vars: &[TypeVar],
    ignored_vars: &[TypeVar],
    out: &mut CoOccurrences,
) {
    out.record_group(along_group(ty, extra_vars, ignored_vars), polarity);

    for args in ty.cons.values() {
        for arg in args {
            visit_bounds_co_occurrence(arg, polarity, ignored_vars, out);
        }
    }
    for fun in &ty.funs {
        visit_type_co_occurrence(&fun.arg, polarity.flipped(), &[], ignored_vars, out);
        visit_type_co_occurrence(&fun.arg_eff, polarity.flipped(), &[], ignored_vars, out);
        visit_type_co_occurrence(&fun.ret_eff, polarity, &[], ignored_vars, out);
        visit_type_co_occurrence(&fun.ret, polarity, &[], ignored_vars, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            visit_type_co_occurrence(&field.value, polarity, &[], ignored_vars, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            visit_type_co_occurrence(&field.value, polarity, &[], ignored_vars, out);
        }
        visit_type_co_occurrence(&spread.tail, polarity, &[], ignored_vars, out);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                visit_type_co_occurrence(payload, polarity, &[], ignored_vars, out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            visit_type_co_occurrence(item, polarity, &[], ignored_vars, out);
        }
    }
    for row in &ty.rows {
        let group = row_along_group(row, ignored_vars);
        visit_row_tail_vars(&row.tail, polarity, Some(&group), ignored_vars, out);
        for args in row.items.values() {
            for arg in args {
                visit_bounds_co_occurrence(arg, polarity, ignored_vars, out);
            }
        }
        visit_type_co_occurrence(&row.tail, polarity, &[], ignored_vars, out);
    }
}

pub(super) fn visit_row_tail_vars(
    ty: &CompactType,
    polarity: Polarity,
    group: Option<&FxHashSet<AlongItem>>,
    ignored_vars: &[TypeVar],
    out: &mut CoOccurrences,
) {
    if let Some(group) = group {
        out.record_group(group.clone(), polarity);
    }
    for row in &ty.rows {
        visit_row_tail_vars(&row.tail, polarity, group, ignored_vars, out);
    }
}

pub(super) fn along_group(
    ty: &CompactType,
    extra_vars: &[TypeVar],
    ignored_vars: &[TypeVar],
) -> FxHashSet<AlongItem> {
    let mut group = FxHashSet::default();
    group.extend(
        ty.vars
            .iter()
            .filter(|var| !ignored_vars.contains(&var.var))
            .map(|var| AlongItem::Var(var.var)),
    );
    group.extend(extra_vars.iter().copied().map(AlongItem::Var));
    group.extend(exact_group(ty).into_iter().map(AlongItem::Exact));
    group
}

pub(super) fn row_along_group(row: &CompactRow, ignored_vars: &[TypeVar]) -> FxHashSet<AlongItem> {
    let mut group = FxHashSet::default();
    collect_row_tail_vars(&row.tail, ignored_vars, &mut group);
    let mut item_keys = compact_row_item_entries(&row.items)
        .into_iter()
        .map(|item| ExactKey::Con(item.path, item.args.len()))
        .collect::<Vec<_>>();
    item_keys.sort_by_key(ExactKey::sort_key);
    item_keys.dedup();
    group.extend(item_keys.into_iter().map(AlongItem::Exact));
    group
}

pub(super) fn collect_row_tail_vars(
    ty: &CompactType,
    ignored_vars: &[TypeVar],
    out: &mut FxHashSet<AlongItem>,
) {
    out.extend(
        ty.vars
            .iter()
            .filter(|var| !ignored_vars.contains(&var.var))
            .map(|var| AlongItem::Var(var.var)),
    );
    for row in &ty.rows {
        collect_row_tail_vars(&row.tail, ignored_vars, out);
    }
}

pub(super) fn exact_group(ty: &CompactType) -> Vec<ExactKey> {
    let mut group = Vec::new();
    group.extend(ty.builtins.iter().copied().map(ExactKey::Builtin));
    group.extend(
        ty.cons
            .iter()
            .map(|(path, args)| ExactKey::Con(path.clone(), args.len())),
    );
    if !ty.funs.is_empty() {
        group.push(ExactKey::Fun);
    }
    group.extend(ty.records.iter().map(|record| {
        ExactKey::Record(
            record
                .fields
                .iter()
                .map(|field| (field.name.clone(), field.optional))
                .collect(),
        )
    }));
    group.extend(ty.record_spreads.iter().map(|spread| {
        ExactKey::RecordSpread(
            spread
                .fields
                .iter()
                .map(|field| (field.name.clone(), field.optional))
                .collect(),
        )
    }));
    group.extend(ty.poly_variants.iter().map(|variant| {
        ExactKey::PolyVariant(
            variant
                .items
                .iter()
                .map(|(name, payloads)| (name.clone(), payloads.len()))
                .collect(),
        )
    }));
    group.extend(
        ty.tuples
            .iter()
            .map(|tuple| ExactKey::Tuple(tuple.items.len())),
    );
    group.extend(ty.rows.iter().map(|row| {
        let mut item_keys = compact_row_item_entries(&row.items)
            .into_iter()
            .map(|item| ExactKey::Con(item.path, item.args.len()))
            .collect::<Vec<_>>();
        item_keys.sort_by_key(ExactKey::sort_key);
        item_keys.dedup();
        ExactKey::Row(item_keys)
    }));
    group
}

pub(super) fn visit_bounds_co_occurrence(
    bounds: &CompactBounds,
    polarity: Polarity,
    ignored_vars: &[TypeVar],
    out: &mut CoOccurrences,
) {
    match bounds {
        CompactBounds::Interval { lower, upper } => {
            out.record_interval_equalities(lower, upper);
            if !lower.is_empty() {
                visit_type_co_occurrence(lower, polarity, &[], ignored_vars, out);
            }
            if !upper.is_empty() {
                visit_type_co_occurrence(upper, polarity.flipped(), &[], ignored_vars, out);
            }
        }
        CompactBounds::Con { args, .. } => {
            for arg in args {
                visit_bounds_co_occurrence(arg, polarity, ignored_vars, out);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            visit_bounds_co_occurrence(arg, polarity.flipped(), ignored_vars, out);
            visit_bounds_co_occurrence(arg_eff, polarity.flipped(), ignored_vars, out);
            visit_bounds_co_occurrence(ret_eff, polarity, ignored_vars, out);
            visit_bounds_co_occurrence(ret, polarity, ignored_vars, out);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                visit_bounds_co_occurrence(&field.value, polarity, ignored_vars, out);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    visit_bounds_co_occurrence(payload, polarity, ignored_vars, out);
                }
            }
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                visit_bounds_co_occurrence(item, polarity, ignored_vars, out);
            }
        }
    }
}

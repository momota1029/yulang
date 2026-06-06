//! グローバル sandwich：不変型の中心変数が「主型全体で例外なく同じ単一コンストラクタ K と
//! 共起」していれば K を lift し中心変数を捨てる。詳細 spec/2026-06-06-invariant-type-sandwich.md。
//!
//! - 共起判定はスキーマ（1 def の主型）全体で行う（局所判定では `(int,int)|α&(int,int) -> α`
//!   の ret に裸 α がいるケースを誤って lift してしまう）。
//! - lift 後の子をもう一度 sandwich（さらに潰れうるため fixpoint）。

use std::collections::HashMap;

use crate::ids::TypeVar;
use crate::symbols::Path;

use super::compact::{CompactBounds, CompactCon, CompactType, CompactTypeScheme};

/// lift 対象になりうるコンストラクタ種。同種（path+arity が一致）なら同じ kind。
/// Fun/Record/Variant/Row は今は lift しない（= NonLiftable 扱いで保守的に共起判定だけ参加）。
#[derive(Clone, PartialEq, Eq, Debug)]
enum ConKind {
    Con(Path, usize),
    Tuple(usize),
    /// 今は lift しないが「裸ではない」コンストラクタとして共起判定に出る種。
    NonLiftable,
}

/// 各 CompactType が表に持つコンストラクタ種を集める。空なら「裸（コンストラクタ無し）」。
fn type_con_kinds(ty: &CompactType) -> Vec<ConKind> {
    let mut kinds = Vec::new();
    for con in &ty.cons {
        kinds.push(ConKind::Con(con.path.clone(), con.args.len()));
    }
    for tuple in &ty.tuples {
        kinds.push(ConKind::Tuple(tuple.len()));
    }
    if !ty.prims.is_empty()
        || !ty.funs.is_empty()
        || !ty.records.is_empty()
        || !ty.record_spreads.is_empty()
        || !ty.variants.is_empty()
        || !ty.rows.is_empty()
    {
        kinds.push(ConKind::NonLiftable);
    }
    kinds
}

/// 中心変数 α の「共起判定」の途中状態。
#[derive(Clone)]
enum Verdict {
    /// まだ矛盾なく、この単一 kind と共起している。
    Single(ConKind),
    /// 裸出現・複数 kind・矛盾 → lift しない。
    NoLift,
}

/// スキーマ全体を走査し、各型変数が「全出現で同じ単一 liftable kind と共起し、一度も裸で
/// 出ない」かを判定する。lift 可能な変数→kind のみ返す。
fn compute_lift_verdicts(scheme: &CompactTypeScheme) -> HashMap<TypeVar, ConKind> {
    let mut verdicts: HashMap<TypeVar, Verdict> = HashMap::new();
    visit_bounds_for_verdict(&scheme.cty, &mut verdicts);
    for bounds in scheme.rec_vars.values() {
        visit_bounds_for_verdict(bounds, &mut verdicts);
    }
    verdicts
        .into_iter()
        // μ束縛変数（rec_vars のキー）は lift しない。lift すると再帰型を無限展開してしまう
        // （`list<α>` の中心 α を lift → 子にまた α → 無限再帰）。再帰型は Interval のまま残す。
        .filter(|(tv, _)| !scheme.rec_vars.contains_key(tv))
        .filter_map(|(tv, v)| match v {
            Verdict::Single(kind @ (ConKind::Con(..) | ConKind::Tuple(_))) => Some((tv, kind)),
            _ => None,
        })
        .collect()
}

fn record_var_occurrence(verdicts: &mut HashMap<TypeVar, Verdict>, tv: TypeVar, kinds: &[ConKind]) {
    // この出現で α が共起する kind は、kinds がちょうど 1 種なら Single、0 種（裸）or 複数なら NoLift。
    let this = if kinds.len() == 1 {
        Verdict::Single(kinds[0].clone())
    } else {
        Verdict::NoLift
    };
    let merged = match (verdicts.get(&tv), &this) {
        (None, _) => this.clone(),
        (Some(Verdict::NoLift), _) | (_, Verdict::NoLift) => Verdict::NoLift,
        (Some(Verdict::Single(a)), Verdict::Single(b)) => {
            if a == b {
                Verdict::Single(a.clone())
            } else {
                Verdict::NoLift
            }
        }
    };
    verdicts.insert(tv, merged);
}

fn visit_type_for_verdict(ty: &CompactType, verdicts: &mut HashMap<TypeVar, Verdict>) {
    let kinds = type_con_kinds(ty);
    for &tv in &ty.vars {
        record_var_occurrence(verdicts, tv, &kinds);
    }
    // ネストした不変位置（con args）も走査。
    for con in &ty.cons {
        for arg in &con.args {
            visit_bounds_for_verdict(arg, verdicts);
        }
    }
    // tuple 成分・fun・record 等の CompactType もたどる（変数の出現を拾うため）。
    for tuple in &ty.tuples {
        for item in tuple {
            visit_type_for_verdict(item, verdicts);
        }
    }
    for fun in &ty.funs {
        visit_type_for_verdict(&fun.arg, verdicts);
        visit_type_for_verdict(&fun.arg_eff, verdicts);
        visit_type_for_verdict(&fun.ret_eff, verdicts);
        visit_type_for_verdict(&fun.ret, verdicts);
    }
    for record in &ty.records {
        for field in &record.fields {
            visit_type_for_verdict(&field.value, verdicts);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            visit_type_for_verdict(&field.value, verdicts);
        }
        visit_type_for_verdict(&spread.tail, verdicts);
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                visit_type_for_verdict(payload, verdicts);
            }
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            visit_type_for_verdict(item, verdicts);
        }
        visit_type_for_verdict(&row.tail, verdicts);
    }
}

fn visit_bounds_for_verdict(bounds: &CompactBounds, verdicts: &mut HashMap<TypeVar, Verdict>) {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            // self_var は共変・反変の両方向に現れる中心として扱う（lower/upper と同じ kind 集合で判定）。
            if let Some(sv) = self_var {
                let lk = type_con_kinds(lower);
                let uk = type_con_kinds(upper);
                record_var_occurrence(verdicts, *sv, &lk);
                record_var_occurrence(verdicts, *sv, &uk);
            }
            visit_type_for_verdict(lower, verdicts);
            visit_type_for_verdict(upper, verdicts);
        }
        CompactBounds::Con { args, .. } => {
            for arg in args {
                visit_bounds_for_verdict(arg, verdicts);
            }
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                visit_bounds_for_verdict(item, verdicts);
            }
        }
    }
}

/// スキーマに sandwich を適用する。
pub(crate) fn sandwich_scheme(scheme: &mut CompactTypeScheme) {
    // verdict は lift で構造が変わると変わりうるので fixpoint で回す。各パスで実際に lift が
    // 起きたかを `changed` フラグで追い、起きなければ収束として打ち切る（scheme の clone /
    // 等価比較は巨大型で O(size) になり重いので避ける）。lift は不変中心を 1 つ消すので
    // 反復は有限だが、念のため上限も置く。
    for _ in 0..MAX_SANDWICH_PASSES {
        let verdicts = compute_lift_verdicts(scheme);
        if verdicts.is_empty() {
            break;
        }
        let mut changed = false;
        scheme.cty = sandwich_spine(std::mem::take(&mut scheme.cty), &verdicts, &mut changed);
        let rec_vars = std::mem::take(&mut scheme.rec_vars);
        scheme.rec_vars = rec_vars
            .into_iter()
            .map(|(tv, b)| (tv, sandwich_spine(b, &verdicts, &mut changed)))
            .collect();
        if !changed {
            break;
        }
    }
}

/// fixpoint の反復上限（不変中心は有限なので通常はネスト深さ分で収束する）。
const MAX_SANDWICH_PASSES: usize = 64;

/// 中心変数 `center` が `lower`/`upper` の双方で kind `K` と共起しているなら、その K を lift して
/// 中心を捨てた `CompactBounds`（lift 変種）を返す。できなければ None。
fn try_lift_interval(
    self_var: Option<TypeVar>,
    lower: &CompactType,
    upper: &CompactType,
    verdicts: &HashMap<TypeVar, ConKind>,
) -> Option<CompactBounds> {
    // 中心候補 = lower.vars ∩ upper.vars、または self_var。verdict を持つものを選ぶ。
    let center = self_var
        .filter(|tv| verdicts.contains_key(tv))
        .or_else(|| {
            lower
                .vars
                .iter()
                .find(|tv| upper.vars.contains(tv) && verdicts.contains_key(tv))
                .copied()
        })?;
    let kind = verdicts.get(&center)?.clone();
    // lower/upper の双方に同種コンストラクタがちょうど 1 つあること。
    match kind {
        ConKind::Tuple(n) => {
            let l = single_tuple(lower, n)?;
            let u = single_tuple(upper, n)?;
            let items = l
                .iter()
                .zip(u)
                .map(|(li, ui)| CompactBounds::Interval {
                    self_var: None,
                    lower: li.clone(),
                    upper: ui.clone(),
                })
                .collect();
            Some(CompactBounds::Tuple { items })
        }
        ConKind::Con(path, n) => {
            let l = single_con(lower, &path, n)?;
            let u = single_con(upper, &path, n)?;
            // con args は既に CompactBounds（不変区間）。lower 側 con と upper 側 con の対応引数を
            // 区間として組む：covariant の引数は lower の lower/upper をそのまま、という単純化は
            // できないので、各引数の (+,-) を「lower-con-arg と upper-con-arg のマージ」で作る。
            let args = l
                .iter()
                .zip(u)
                .map(|(la, ua)| merge_arg_bounds(la, ua))
                .collect();
            Some(CompactBounds::Con { path, args })
        }
        ConKind::NonLiftable => None,
    }
}

/// con 引数（不変区間）を lower 側出現と upper 側出現から1つに合流する。
/// lower 側の con arg は「正の側に現れた不変引数」、upper 側は「負の側に現れた不変引数」。
/// 不変なので両者の lower どうし・upper どうしを取る（= 同じ中心の (+,-) を保つ）。
fn merge_arg_bounds(l: &CompactBounds, u: &CompactBounds) -> CompactBounds {
    match (l, u) {
        (
            CompactBounds::Interval {
                self_var: ls,
                lower: ll,
                upper: lu,
            },
            CompactBounds::Interval {
                lower: ul,
                upper: uu,
                ..
            },
        ) => CompactBounds::Interval {
            self_var: *ls,
            lower: super::compact::merge_compact_types(true, ll.clone(), ul.clone()),
            upper: super::compact::merge_compact_types(false, lu.clone(), uu.clone()),
        },
        // すでに lift 済みの引数はそのまま lower 側を採用（保守的）。
        _ => l.clone(),
    }
}

fn single_tuple(ty: &CompactType, n: usize) -> Option<&Vec<CompactType>> {
    if ty.tuples.len() == 1 && ty.tuples[0].len() == n && ty.cons.is_empty() {
        Some(&ty.tuples[0])
    } else {
        None
    }
}

fn single_con<'a>(ty: &'a CompactType, path: &Path, n: usize) -> Option<&'a Vec<CompactBounds>> {
    if ty.cons.len() == 1
        && ty.cons[0].path == *path
        && ty.cons[0].args.len() == n
        && ty.tuples.is_empty()
    {
        Some(&ty.cons[0].args)
    } else {
        None
    }
}

/// スパイン（root cty / rec_var の top）を sandwich する。**その interval 自体は lift しない**
/// （binding の型そのものを表す位置なので lift すると coalesce 経路が `.lower()` で壊れる）。
/// con-arg などネストした不変位置だけ `sandwich_type` 経由で lift する。
fn sandwich_spine(
    bounds: CompactBounds,
    verdicts: &HashMap<TypeVar, ConKind>,
    changed: &mut bool,
) -> CompactBounds {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => CompactBounds::Interval {
            self_var,
            lower: sandwich_type(lower, verdicts, changed),
            upper: sandwich_type(upper, verdicts, changed),
        },
        // スパインが既に lift 済み（通常起きない）なら子へ降りるだけ。
        CompactBounds::Con { path, args } => CompactBounds::Con {
            path,
            args: args
                .into_iter()
                .map(|a| sandwich_spine(a, verdicts, changed))
                .collect(),
        },
        CompactBounds::Tuple { items } => CompactBounds::Tuple {
            items: items
                .into_iter()
                .map(|a| sandwich_spine(a, verdicts, changed))
                .collect(),
        },
    }
}

/// bounds を sandwich 変換する。lift できれば lift し（`changed` を立てる）、できなければネストへ再帰。
fn sandwich_bounds(
    bounds: CompactBounds,
    verdicts: &HashMap<TypeVar, ConKind>,
    changed: &mut bool,
) -> CompactBounds {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            if let Some(lifted) = try_lift_interval(self_var, &lower, &upper, verdicts) {
                *changed = true;
                sandwich_bounds(lifted, verdicts, changed)
            } else {
                CompactBounds::Interval {
                    self_var,
                    lower: sandwich_type(lower, verdicts, changed),
                    upper: sandwich_type(upper, verdicts, changed),
                }
            }
        }
        CompactBounds::Con { path, args } => CompactBounds::Con {
            path,
            args: args
                .into_iter()
                .map(|a| sandwich_bounds(a, verdicts, changed))
                .collect(),
        },
        CompactBounds::Tuple { items } => CompactBounds::Tuple {
            items: items
                .into_iter()
                .map(|a| sandwich_bounds(a, verdicts, changed))
                .collect(),
        },
    }
}

/// CompactType 内のネストした不変位置（con args）を sandwich する。
fn sandwich_type(
    mut ty: CompactType,
    verdicts: &HashMap<TypeVar, ConKind>,
    changed: &mut bool,
) -> CompactType {
    ty.cons = ty
        .cons
        .into_iter()
        .map(|con| CompactCon {
            path: con.path,
            args: con
                .args
                .into_iter()
                .map(|a| sandwich_bounds(a, verdicts, changed))
                .collect(),
        })
        .collect();
    ty
}

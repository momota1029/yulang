//! Environment-gated tracing for constraint propagation.

use std::sync::OnceLock;

use poly::types::{Neg, NegId, Pos, PosId, TypeArena, TypeVar};

use crate::time::{Duration, Instant};

use super::{ConstraintMachine, ConstraintWork, VarBounds};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConstraintTraceMode {
    Off,
    Summary,
    Verbose,
}

pub(super) struct ConstraintDrainTrace {
    mode: ConstraintTraceMode,
    start: Instant,
    steps: usize,
    subtype_steps: usize,
    subtract_steps: usize,
    initial_queue: usize,
    initial_seen: usize,
    initial_events: usize,
    next_report: usize,
}

impl ConstraintDrainTrace {
    pub(super) fn from_env(machine: &ConstraintMachine) -> Self {
        Self {
            mode: constraint_trace_mode(),
            start: Instant::now(),
            steps: 0,
            subtype_steps: 0,
            subtract_steps: 0,
            initial_queue: machine.queue.len(),
            initial_seen: machine.canonical_constraint_count(),
            initial_events: machine.events.len(),
            next_report: 10_000,
        }
    }

    pub(super) fn work(&mut self, work: &ConstraintWork, machine: &ConstraintMachine) {
        if self.mode == ConstraintTraceMode::Off {
            return;
        }
        self.steps += 1;
        match work {
            ConstraintWork::Subtype(_) => self.subtype_steps += 1,
            ConstraintWork::SubtractFact(_) => self.subtract_steps += 1,
        }
        if self.mode == ConstraintTraceMode::Verbose {
            eprintln!(
                "[constraints] work {}: {} {:?} queue={} seen={} events={} elapsed={}",
                self.steps,
                constraint_work_kind(work),
                work,
                machine.queue.len(),
                machine.canonical_constraint_count(),
                machine.events.len().saturating_sub(self.initial_events),
                format_constraint_duration(self.start.elapsed())
            );
        } else if self.steps >= self.next_report {
            self.print("progress", machine);
            self.next_report += 10_000;
        }
    }

    pub(super) fn finish(&self, machine: &ConstraintMachine) {
        if self.mode == ConstraintTraceMode::Off {
            return;
        }
        let elapsed = self.start.elapsed();
        if self.mode == ConstraintTraceMode::Verbose
            || elapsed >= Duration::from_millis(50)
            || self.steps >= 10_000
        {
            self.print("finish", machine);
        }
    }

    fn print(&self, label: &str, machine: &ConstraintMachine) {
        eprintln!(
            "[constraints] {label}: steps={} subtype={} subtract={} queue={} initial_queue={} seen_delta={} events_delta={} bounds_vars={} elapsed={}",
            self.steps,
            self.subtype_steps,
            self.subtract_steps,
            machine.queue.len(),
            self.initial_queue,
            machine
                .canonical_constraint_count()
                .saturating_sub(self.initial_seen),
            machine.events.len().saturating_sub(self.initial_events),
            machine.bounds.vars.len(),
            format_constraint_duration(self.start.elapsed())
        );
    }
}

pub(super) fn trace_bound_replay_start(kind: &str, var: TypeVar, total: usize) {
    let mode = constraint_trace_mode();
    if mode == ConstraintTraceMode::Off {
        return;
    }
    if mode == ConstraintTraceMode::Verbose || total >= 1_000 {
        eprintln!("[constraints] replay {kind}: var={var:?} total={total}");
    }
}

pub(super) fn trace_bound_replay_progress(kind: &str, var: TypeVar, index: usize) {
    let mode = constraint_trace_mode();
    if mode == ConstraintTraceMode::Off {
        return;
    }
    if index > 0 && index % 1_000 == 0 {
        eprintln!("[constraints] replay {kind}: var={var:?} done={index}");
    }
}

pub(super) fn trace_var_bounds(
    label: &str,
    var: TypeVar,
    bounds: Option<&VarBounds>,
    types: &TypeArena,
) {
    if !trace_var_bounds_requested(var) {
        return;
    }
    let Some(bounds) = bounds else {
        return;
    };
    let limit = trace_var_bound_limit();
    eprintln!(
        "[constraints] var-bounds {label}: var={var:?} lowers={} uppers={}",
        bounds.lowers.len(),
        bounds.uppers.len()
    );
    for (index, lower) in bounds.lowers.iter().take(limit).enumerate() {
        eprintln!(
            "[constraints] var-bounds {label}: lower[{index}] pos={:?} {} weights={:?}",
            lower.pos,
            format_pos_id(types, lower.pos, 4),
            lower.weights
        );
    }
    for (index, upper) in bounds.uppers.iter().take(limit).enumerate() {
        eprintln!(
            "[constraints] var-bounds {label}: upper[{index}] neg={:?} {} weights={:?}",
            upper.neg,
            format_neg_id(types, upper.neg, 4),
            upper.weights
        );
    }
}

fn constraint_trace_mode() -> ConstraintTraceMode {
    static MODE: OnceLock<ConstraintTraceMode> = OnceLock::new();
    *MODE.get_or_init(|| match std::env::var("YULANG_CONSTRAINT_TIMING") {
        Ok(value) if value == "verbose" => ConstraintTraceMode::Verbose,
        Ok(value) if !value.is_empty() && value != "0" => ConstraintTraceMode::Summary,
        _ => ConstraintTraceMode::Off,
    })
}

fn constraint_work_kind(work: &ConstraintWork) -> &'static str {
    match work {
        ConstraintWork::Subtype(_) => "subtype",
        ConstraintWork::SubtractFact(_) => "subtract-fact",
    }
}

fn format_constraint_duration(duration: Duration) -> String {
    if duration.as_secs() > 0 {
        format!("{:.3}s", duration.as_secs_f64())
    } else {
        format!("{:.3}ms", duration.as_secs_f64() * 1000.0)
    }
}

fn trace_var_bounds_requested(var: TypeVar) -> bool {
    let Ok(value) = std::env::var("YULANG_TRACE_VAR_BOUNDS") else {
        return false;
    };
    value
        .split(',')
        .any(|part| part.trim().parse::<u32>().is_ok_and(|id| id == var.0))
}

fn trace_var_bound_limit() -> usize {
    std::env::var("YULANG_TRACE_VAR_BOUND_LIMIT")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .filter(|limit| *limit > 0)
        .unwrap_or(6)
}

fn format_pos_id(types: &TypeArena, id: PosId, depth: usize) -> String {
    if depth == 0 {
        return format!("{id:?}");
    }
    match types.pos(id) {
        Pos::Bot => "Bot".to_string(),
        Pos::Var(var) => format!("Var({var:?})"),
        Pos::Con(path, args) => format!("Con({}, {} args)", path.join("::"), args.len()),
        Pos::Row(items) => format!(
            "Row([{}])",
            items
                .iter()
                .map(|item| format_pos_id(types, *item, depth - 1))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Pos::Stack { inner, weight } => {
            format!(
                "Stack({}, {weight:?})",
                format_pos_id(types, *inner, depth - 1)
            )
        }
        Pos::NonSubtract(inner, subtract) => {
            format!(
                "NonSubtract({}, {subtract:?})",
                format_pos_id(types, *inner, depth - 1)
            )
        }
        Pos::Union(left, right) => format!(
            "Union({}, {})",
            format_pos_id(types, *left, depth - 1),
            format_pos_id(types, *right, depth - 1)
        ),
        other => format!("{other:?}"),
    }
}

fn format_neg_id(types: &TypeArena, id: NegId, depth: usize) -> String {
    if depth == 0 {
        return format!("{id:?}");
    }
    match types.neg(id) {
        Neg::Top => "Top".to_string(),
        Neg::Bot => "Bot".to_string(),
        Neg::Var(var) => format!("Var({var:?})"),
        Neg::Con(path, args) => format!("Con({}, {} args)", path.join("::"), args.len()),
        Neg::Row(items, tail) => format!(
            "Row([{}], tail: {})",
            items
                .iter()
                .map(|item| format_neg_id(types, *item, depth - 1))
                .collect::<Vec<_>>()
                .join(", "),
            format_neg_id(types, *tail, depth - 1)
        ),
        Neg::Stack { inner, weight } => {
            format!(
                "Stack({}, {weight:?})",
                format_neg_id(types, *inner, depth - 1)
            )
        }
        Neg::Intersection(left, right) => format!(
            "Intersection({}, {})",
            format_neg_id(types, *left, depth - 1),
            format_neg_id(types, *right, depth - 1)
        ),
        other => format!("{other:?}"),
    }
}

//! Environment-gated tracing for the analysis coordinator.
//!
//! The coordinator should not carry logging policy inline. This module owns the
//! environment variables, counters, and formatting used while routing work.

use poly::expr::{DefId, SelectId};

use crate::constraints::ConstraintEvent;
use crate::scc::SccInput;
use crate::time::{Duration, Instant};

use super::AnalysisWork;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum AnalysisTraceMode {
    Off,
    Summary,
    Verbose,
}

pub(super) struct AnalysisDrainTrace {
    pub(super) mode: AnalysisTraceMode,
    start: Instant,
    processed: usize,
    max_queue: usize,
    role_passes: usize,
    resolve_ref: usize,
    probe_select: usize,
    apply_ref: usize,
    apply_select: usize,
    scc_register: usize,
    scc_finish: usize,
    scc_use: usize,
    scc_dependency: usize,
    scc_method_dependency: usize,
    scc_fetch: usize,
}

impl AnalysisDrainTrace {
    pub(super) fn from_env(initial_queue: usize) -> Self {
        let mode = analysis_trace_mode();
        Self {
            mode,
            start: Instant::now(),
            processed: 0,
            max_queue: initial_queue,
            role_passes: 0,
            resolve_ref: 0,
            probe_select: 0,
            apply_ref: 0,
            apply_select: 0,
            scc_register: 0,
            scc_finish: 0,
            scc_use: 0,
            scc_dependency: 0,
            scc_method_dependency: 0,
            scc_fetch: 0,
        }
    }

    pub(super) fn work(&mut self, work: &AnalysisWork, queue_len: usize) {
        if self.mode == AnalysisTraceMode::Off {
            return;
        }
        self.processed += 1;
        self.max_queue = self.max_queue.max(queue_len);
        let kind = analysis_work_kind(work);
        match work {
            AnalysisWork::ResolveRef(_) => self.resolve_ref += 1,
            AnalysisWork::ProbeSelect(_) => self.probe_select += 1,
            AnalysisWork::ApplyRefResolution { .. } => self.apply_ref += 1,
            AnalysisWork::ApplySelectionResolution { .. } => self.apply_select += 1,
            AnalysisWork::Scc(input) => match input {
                SccInput::RegisterDef { .. } => self.scc_register += 1,
                SccInput::DefFinished { .. } => self.scc_finish += 1,
                SccInput::UseResolved { .. } => self.scc_use += 1,
                SccInput::DependencyAdded { .. } => self.scc_dependency += 1,
                SccInput::MethodDependencyAdded { .. }
                | SccInput::MethodDependencyResolved { .. } => self.scc_method_dependency += 1,
                SccInput::DefFetchRecorded { .. } => self.scc_fetch += 1,
            },
        }
        if self.mode == AnalysisTraceMode::Verbose {
            eprintln!(
                "[analysis] work {}: {kind} {:?} queue={} elapsed={}",
                self.processed,
                work,
                queue_len,
                format_analysis_duration(self.start.elapsed())
            );
        }
        if self.processed % 500 == 0 {
            self.print("progress", queue_len);
        }
    }

    pub(super) fn route(&self, elapsed: Duration, queue_len: usize) {
        if self.mode == AnalysisTraceMode::Off {
            return;
        }
        if self.mode == AnalysisTraceMode::Verbose || elapsed >= Duration::from_millis(50) {
            eprintln!(
                "[analysis] route constraints: queue={} elapsed={} total={}",
                queue_len,
                format_analysis_duration(elapsed),
                format_analysis_duration(self.start.elapsed())
            );
        }
    }

    pub(super) fn work_done(&self, kind: &str, elapsed: Duration, queue_len: usize) {
        if self.mode == AnalysisTraceMode::Off {
            return;
        }
        if self.mode == AnalysisTraceMode::Verbose || elapsed >= Duration::from_millis(50) {
            eprintln!(
                "[analysis] work done: kind={kind} queue={} elapsed={} total={}",
                queue_len,
                format_analysis_duration(elapsed),
                format_analysis_duration(self.start.elapsed())
            );
        }
    }

    pub(super) fn before_role_pass(&mut self, unresolved_selections: usize, queue_len: usize) {
        if self.mode == AnalysisTraceMode::Off || unresolved_selections == 0 {
            return;
        }
        self.role_passes += 1;
        eprintln!(
            "[analysis] role pass {} start: unresolved_selects={} queue={} elapsed={}",
            self.role_passes,
            unresolved_selections,
            queue_len,
            format_analysis_duration(self.start.elapsed())
        );
    }

    pub(super) fn after_role_pass(
        &mut self,
        progressed: bool,
        unresolved_selections: usize,
        queue_len: usize,
    ) {
        if self.mode == AnalysisTraceMode::Off || self.role_passes == 0 {
            return;
        }
        eprintln!(
            "[analysis] role pass {} done: progressed={} unresolved_selects={} queue={}",
            self.role_passes, progressed, unresolved_selections, queue_len
        );
    }

    pub(super) fn route_start(&self) {
        if self.mode != AnalysisTraceMode::Off && self.processed == 0 {
            eprintln!(
                "[analysis] route constraint events start: elapsed={}",
                format_analysis_duration(self.start.elapsed())
            );
        }
    }

    pub(super) fn route_done(&self, queue_len: usize) {
        if self.mode != AnalysisTraceMode::Off && self.processed == 0 {
            eprintln!(
                "[analysis] route constraint events done: queue={} elapsed={}",
                queue_len,
                format_analysis_duration(self.start.elapsed())
            );
        }
    }

    pub(super) fn finish(&mut self, queue_len: usize) {
        if self.mode != AnalysisTraceMode::Off {
            self.print("finish", queue_len);
        }
    }

    fn print(&self, label: &str, queue_len: usize) {
        eprintln!(
            "[analysis] {label}: processed={} queue={} max_queue={} roles={} elapsed={} \
resolve_ref={} probe_select={} apply_ref={} apply_select={} \
scc_register={} scc_finish={} scc_use={} scc_dep={} scc_method_dep={} scc_fetch={}",
            self.processed,
            queue_len,
            self.max_queue,
            self.role_passes,
            format_analysis_duration(self.start.elapsed()),
            self.resolve_ref,
            self.probe_select,
            self.apply_ref,
            self.apply_select,
            self.scc_register,
            self.scc_finish,
            self.scc_use,
            self.scc_dependency,
            self.scc_method_dependency,
            self.scc_fetch
        );
    }
}

pub(super) fn analysis_trace_mode() -> AnalysisTraceMode {
    match std::env::var("YULANG_ANALYSIS_TIMING") {
        Ok(value) if value == "verbose" => AnalysisTraceMode::Verbose,
        Ok(value) if !value.is_empty() && value != "0" => AnalysisTraceMode::Summary,
        _ => AnalysisTraceMode::Off,
    }
}

pub(super) fn analysis_work_kind(work: &AnalysisWork) -> &'static str {
    match work {
        AnalysisWork::ResolveRef(_) => "resolve-ref",
        AnalysisWork::ProbeSelect(_) => "probe-select",
        AnalysisWork::ApplyRefResolution { .. } => "apply-ref",
        AnalysisWork::ApplySelectionResolution { .. } => "apply-select",
        AnalysisWork::Scc(input) => match input {
            SccInput::RegisterDef { .. } => "scc-register-def",
            SccInput::DefFinished { .. } => "scc-def-finished",
            SccInput::UseResolved { .. } => "scc-use-resolved",
            SccInput::DependencyAdded { .. } => "scc-dependency-added",
            SccInput::MethodDependencyAdded { .. } => "scc-method-dependency-added",
            SccInput::MethodDependencyResolved { .. } => "scc-method-dependency-resolved",
            SccInput::DefFetchRecorded { .. } => "scc-def-fetch-recorded",
        },
    }
}

pub(super) fn trace_constraint_events(events: &[ConstraintEvent]) {
    if events.is_empty()
        || !std::env::var("YULANG_CONSTRAINT_EVENT_TIMING")
            .is_ok_and(|value| !value.is_empty() && value != "0")
    {
        return;
    }

    let mut lower = 0usize;
    let mut upper = 0usize;
    let mut subtract = 0usize;
    let mut cast = 0usize;
    let mut filter = 0usize;
    for event in events {
        match event {
            ConstraintEvent::LowerBoundAdded { .. } => lower += 1,
            ConstraintEvent::UpperBoundAdded { .. } => upper += 1,
            ConstraintEvent::SubtractFactAdded { .. } => subtract += 1,
            ConstraintEvent::NominalCastNeeded { .. } => cast += 1,
            ConstraintEvent::EffectFilterViolation { .. } => filter += 1,
        }
    }
    eprintln!(
        "[analysis] route constraint events: total={} lower={} upper={} subtract={} cast={} filter={}",
        events.len(),
        lower,
        upper,
        subtract,
        cast,
        filter
    );
}

pub(super) fn trace_select_requested(select_id: SelectId) -> bool {
    let Ok(value) = std::env::var("YULANG_TRACE_SELECTS") else {
        return false;
    };
    value
        .split(',')
        .any(|part| part.trim().parse::<u32>().is_ok_and(|id| id == select_id.0))
}

pub(super) fn trace_select_bound_limit() -> usize {
    std::env::var("YULANG_TRACE_SELECT_BOUND_LIMIT")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .filter(|limit| *limit > 0)
        .unwrap_or(8)
}

pub(super) fn trace_scheme_requested(def: DefId) -> bool {
    let Ok(value) = std::env::var("YULANG_TRACE_SCHEME_DEFS") else {
        return false;
    };
    value
        .split(',')
        .any(|part| part.trim().parse::<u32>().is_ok_and(|id| id == def.0))
}

pub(super) fn trace_instantiate_phase(
    mode: AnalysisTraceMode,
    label: &str,
    parent: DefId,
    target: DefId,
    elapsed: Duration,
    total_start: Instant,
) {
    if mode == AnalysisTraceMode::Off {
        return;
    }
    if mode == AnalysisTraceMode::Verbose || elapsed >= Duration::from_millis(50) {
        eprintln!(
            "[analysis] instantiate use {label}: parent={parent:?} target={target:?} elapsed={} total={}",
            format_analysis_duration(elapsed),
            format_analysis_duration(total_start.elapsed())
        );
    }
}

fn format_analysis_duration(duration: Duration) -> String {
    if duration.as_secs() > 0 {
        format!("{:.3}s", duration.as_secs_f64())
    } else {
        format!("{:.3}ms", duration.as_secs_f64() * 1000.0)
    }
}

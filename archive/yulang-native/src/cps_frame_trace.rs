use std::cell::RefCell;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CpsFrameTraceLayer {
    CpsEval,
    CpsRepr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsFrameTraceSlot {
    pub target: usize,
    pub value: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CpsFrameTraceEvent {
    HandlerEnvRead {
        layer: CpsFrameTraceLayer,
        function: String,
        handler: usize,
        entry: usize,
        values: Vec<CpsFrameTraceSlot>,
    },
    HandlerEnvOverlay {
        layer: CpsFrameTraceLayer,
        function: String,
        handler: usize,
        entries: Vec<usize>,
        values: Vec<CpsFrameTraceSlot>,
    },
}

thread_local! {
    static CPS_FRAME_TRACE: RefCell<Option<Vec<CpsFrameTraceEvent>>> = const { RefCell::new(None) };
}

pub fn with_cps_frame_trace<T>(f: impl FnOnce() -> T) -> (T, Vec<CpsFrameTraceEvent>) {
    let previous = CPS_FRAME_TRACE.with(|trace| trace.replace(Some(Vec::new())));
    let result = f();
    let events = CPS_FRAME_TRACE
        .with(|trace| trace.replace(previous))
        .unwrap_or_default();
    (result, events)
}

pub(crate) fn push_cps_frame_trace_event(event: CpsFrameTraceEvent) {
    CPS_FRAME_TRACE.with(|trace| {
        if let Some(events) = trace.borrow_mut().as_mut() {
            events.push(event);
        }
    });
}

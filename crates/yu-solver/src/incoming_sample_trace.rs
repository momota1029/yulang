//! Test-only causal ledger for incoming-route resource samples.

use std::{cell::RefCell, collections::BTreeMap};

#[derive(Clone, Debug)]
struct Event {
    attempt: usize,
    owner: String,
    lane: String,
    old_capacity: usize,
    new_capacity: usize,
}

enum AwaitingSample {
    Event((String, String), Event),
    Named(String),
}

#[derive(Clone, Copy, Debug)]
pub(super) struct EventSample {
    pub(super) value_levels_bytes: usize,
    pub(super) semantic_retained_bytes: usize,
    pub(super) session_retained_bytes: usize,
    pub(super) nested_bound_bytes: usize,
    pub(super) semantic_peak_bytes: usize,
    pub(super) session_peak_bytes: usize,
}

#[derive(Debug)]
pub(super) struct CompletedEvent {
    pub(super) owner: String,
    pub(super) lane: String,
    pub(super) old_capacity: usize,
    pub(super) new_capacity: usize,
    pub(super) sample: EventSample,
}

#[derive(Default)]
struct Trace {
    active_attempt: Option<usize>,
    attempts: usize,
    pending: Vec<Event>,
    events: BTreeMap<(String, String), usize>,
    reasons: BTreeMap<String, usize>,
    matched: usize,
    recorded: usize,
    event_samples: usize,
    samples: usize,
    next_reason: Option<&'static str>,
    awaiting_sample: Option<AwaitingSample>,
    completed_event_samples: BTreeMap<(String, String), Vec<EventSample>>,
    completed_events: Vec<CompletedEvent>,
    completed_named_samples: BTreeMap<String, Vec<EventSample>>,
}

pub(super) struct Summary {
    pub(super) attempts: usize,
    pub(super) matched_events: usize,
    pub(super) event_samples: usize,
    pub(super) samples: usize,
    pub(super) event_lanes: BTreeMap<(String, String), usize>,
    pub(super) named_samples: BTreeMap<String, usize>,
    pub(super) completed_event_samples: BTreeMap<(String, String), Vec<EventSample>>,
    pub(super) completed_events: Vec<CompletedEvent>,
    pub(super) completed_named_samples: BTreeMap<String, Vec<EventSample>>,
}

thread_local! { static TRACE: RefCell<Option<Trace>> = const { RefCell::new(None) }; }

pub(super) fn start() {
    TRACE.with(|trace| assert!(trace.replace(Some(Trace::default())).is_none()));
}

pub(super) fn in_attempt() -> bool {
    TRACE.with(|slot| {
        slot.borrow()
            .as_ref()
            .is_some_and(|trace| trace.active_attempt.is_some())
    })
}

pub(super) fn begin_attempt() {
    TRACE.with(|trace| {
        if let Some(trace) = trace.borrow_mut().as_mut() {
            assert!(trace.active_attempt.is_none());
            trace.attempts += 1;
            trace.active_attempt = Some(trace.attempts);
        }
    });
}

pub(super) fn end_attempt() {
    TRACE.with(|trace| {
        if let Some(trace) = trace.borrow_mut().as_mut() {
            assert!(trace.active_attempt.is_some());
            assert!(
                trace.pending.is_empty(),
                "incoming attempt ended with unmatched events: {:?}",
                trace.pending
            );
            assert!(trace.next_reason.is_none());
            trace.active_attempt = None;
        }
    });
}

pub(super) fn reason(reason: &'static str) {
    TRACE.with(|slot| {
        if let Some(trace) = slot.borrow_mut().as_mut() {
            assert!(trace.next_reason.replace(reason).is_none());
        }
    });
}

pub(super) fn event(
    owner: impl FnOnce() -> String,
    lane: impl FnOnce() -> String,
    old: usize,
    new: usize,
) {
    if old == new {
        return;
    }
    TRACE.with(|trace| {
        let mut trace = trace.borrow_mut();
        let Some(trace) = trace.as_mut() else { return };
        let attempt = trace
            .active_attempt
            .expect("capacity event outside incoming attempt");
        trace.recorded += 1;
        trace.pending.push(Event {
            attempt,
            owner: owner(),
            lane: lane(),
            old_capacity: old,
            new_capacity: new,
        });
    });
}

pub(super) fn sample() {
    TRACE.with(|trace| {
        let mut trace = trace.borrow_mut();
        let Some(trace) = trace.as_mut() else { return };
        // A fallible aggregate can return before the completion hook runs.
        // Its event remains matched, but it has no completed snapshot.
        trace.awaiting_sample = None;
        trace.samples += 1;
        if !trace.pending.is_empty() {
            assert!(
                trace.next_reason.is_none(),
                "named boundary has pending capacity events"
            );
            // Some owners (notably the Term arena) publish one fixed-size
            // snapshot per lane change after a constructor finishes. Consume
            // those samples and their already-recorded events in that same
            // order rather than attributing the whole batch to one sample.
            let event = trace.pending.remove(0);
            trace.event_samples += 1;
            assert_eq!(
                trace.active_attempt,
                Some(event.attempt),
                "event/sample attempt mismatch: {event:?}"
            );
            assert_ne!(event.old_capacity, event.new_capacity);
            let owner_group = if event.owner.starts_with("typed-pair-") {
                "typed-pair".to_owned()
            } else {
                event.owner.split("-row-").next().unwrap().to_owned()
            };
            let key = (owner_group, event.lane.clone());
            *trace.events.entry(key.clone()).or_default() += 1;
            trace.awaiting_sample = Some(AwaitingSample::Event(key, event));
            trace.matched += 1;
        } else {
            let reason = trace
                .next_reason
                .take()
                .expect("incoming sample without event or named call-site reason");
            *trace.reasons.entry(reason.to_owned()).or_default() += 1;
            trace.awaiting_sample = Some(AwaitingSample::Named(reason.to_owned()));
        }
    });
}

pub(super) fn completed_sample(
    value_levels_bytes: usize,
    semantic_retained_bytes: usize,
    session_retained_bytes: usize,
    nested_bound_bytes: usize,
    semantic_peak_bytes: usize,
    session_peak_bytes: usize,
) {
    TRACE.with(|slot| {
        if let Some(trace) = slot.borrow_mut().as_mut() {
            if let Some(awaiting) = trace.awaiting_sample.take() {
                let sample = EventSample {
                    value_levels_bytes,
                    semantic_retained_bytes,
                    session_retained_bytes,
                    nested_bound_bytes,
                    semantic_peak_bytes,
                    session_peak_bytes,
                };
                match awaiting {
                    AwaitingSample::Event(key, event) => {
                        trace
                            .completed_event_samples
                            .entry(key)
                            .or_default()
                            .push(sample);
                        trace.completed_events.push(CompletedEvent {
                            owner: event.owner,
                            lane: event.lane,
                            old_capacity: event.old_capacity,
                            new_capacity: event.new_capacity,
                            sample,
                        });
                    }
                    AwaitingSample::Named(reason) => trace
                        .completed_named_samples
                        .entry(reason)
                        .or_default()
                        .push(sample),
                }
            }
        }
    });
}

pub(super) fn finish(name: &str, definitions: usize) -> Summary {
    TRACE.with(|slot| {
        let trace = slot.replace(None).expect("trace enabled");
        assert!(trace.active_attempt.is_none());
        assert!(trace.next_reason.is_none());
        assert!(trace.pending.is_empty(), "unmatched incoming capacity events: {:?}", trace.pending);
        assert_eq!(
            trace.samples,
            trace.event_samples + trace.reasons.values().sum::<usize>()
        );
        assert_eq!(trace.recorded, trace.matched, "every capacity event must have one sample");
        eprintln!("incoming trace {name}/{definitions}: attempts={} matched_events={} event_samples={} samples={} event_lanes={:?} named_samples={:?}", trace.attempts, trace.matched, trace.event_samples, trace.samples, trace.events, trace.reasons);
        Summary { attempts: trace.attempts, matched_events: trace.matched, event_samples: trace.event_samples, samples: trace.samples, event_lanes: trace.events, named_samples: trace.reasons, completed_event_samples: trace.completed_event_samples, completed_events: trace.completed_events, completed_named_samples: trace.completed_named_samples }
    })
}

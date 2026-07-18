//! Resident, bounded lazy Yumark doc rendering.

use std::collections::HashMap;
use std::fmt;
use std::io;
use std::sync::mpsc::{self, SyncSender};

use infer::doc_comment_render_input::{DocCommentRenderInput, DocCommentRenderInputKey};

use crate::yumark_eval::{
    YumarkLiteralEvaluationError, evaluate_doc_comment_render_input_markdown_with_embedded_std,
};

pub const DEFAULT_DOC_COMMENT_RENDER_CACHE_CAPACITY: usize = 128;

const DOC_COMMENT_RENDER_QUEUE_CAPACITY: usize = 32;
const DOC_COMMENT_RENDER_WORKER_STACK_BYTES: usize = 16 * 1024 * 1024;

/// Cloneable request handle for one resident Yumark rendering thread.
///
/// The worker owns both the embedded-std thread-local warm prefix and the
/// rendered-content cache. Calls may originate on arbitrary threads; all
/// compilation and evaluation remains pinned to the worker's OS thread.
#[derive(Clone)]
pub struct DocCommentRenderWorker {
    jobs: SyncSender<DocCommentRenderJob>,
}

impl DocCommentRenderWorker {
    pub fn start() -> io::Result<Self> {
        Self::start_with_cache_capacity(DEFAULT_DOC_COMMENT_RENDER_CACHE_CAPACITY)
    }

    pub fn start_with_cache_capacity(cache_capacity: usize) -> io::Result<Self> {
        start_worker_with_renderer(
            cache_capacity,
            evaluate_doc_comment_render_input_markdown_with_embedded_std,
        )
    }

    /// Render one owned safe-subset doc input, blocking until the resident
    /// worker replies. Later LSP wiring may call this from a blocking task.
    pub fn render(
        &self,
        input: DocCommentRenderInput,
    ) -> Result<String, DocCommentRenderWorkerError> {
        let (reply, result) = mpsc::sync_channel(1);
        self.jobs
            .send(DocCommentRenderJob { input, reply })
            .map_err(|_| DocCommentRenderWorkerError::WorkerUnavailable)?;
        result
            .recv()
            .map_err(|_| DocCommentRenderWorkerError::WorkerUnavailable)?
    }
}

#[derive(Debug)]
pub enum DocCommentRenderWorkerError {
    WorkerUnavailable,
    Evaluation(String),
}

impl fmt::Display for DocCommentRenderWorkerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WorkerUnavailable => f.write_str("Yumark doc render worker is unavailable"),
            Self::Evaluation(message) => write!(f, "Yumark doc render failed: {message}"),
        }
    }
}

impl std::error::Error for DocCommentRenderWorkerError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::WorkerUnavailable | Self::Evaluation(_) => None,
        }
    }
}

type DocRenderer =
    dyn FnMut(&DocCommentRenderInput) -> Result<String, YumarkLiteralEvaluationError> + Send;

struct DocCommentRenderJob {
    input: DocCommentRenderInput,
    reply: SyncSender<Result<String, DocCommentRenderWorkerError>>,
}

fn start_worker_with_renderer(
    cache_capacity: usize,
    renderer: impl FnMut(&DocCommentRenderInput) -> Result<String, YumarkLiteralEvaluationError>
    + Send
    + 'static,
) -> io::Result<DocCommentRenderWorker> {
    if cache_capacity == 0 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "Yumark doc render cache capacity must be non-zero",
        ));
    }

    let (jobs, requests) = mpsc::sync_channel(DOC_COMMENT_RENDER_QUEUE_CAPACITY);
    std::thread::Builder::new()
        .name("yulang-yumark-doc-render".to_string())
        .stack_size(DOC_COMMENT_RENDER_WORKER_STACK_BYTES)
        .spawn(move || run_worker(requests, cache_capacity, Box::new(renderer)))?;
    Ok(DocCommentRenderWorker { jobs })
}

fn run_worker(
    requests: mpsc::Receiver<DocCommentRenderJob>,
    cache_capacity: usize,
    mut renderer: Box<DocRenderer>,
) {
    let mut cache = RenderedDocCache::new(cache_capacity);
    while let Ok(job) = requests.recv() {
        // Lookup, evaluation, and insertion share this one serial owner. A
        // queued duplicate therefore observes the first job's insertion and
        // cannot begin a second evaluation for the same key concurrently.
        let result = if let Some(rendered) = cache.get(job.input.key()) {
            Ok(rendered)
        } else {
            match renderer(&job.input) {
                Ok(rendered) => {
                    cache.insert(job.input.key().clone(), rendered.clone());
                    Ok(rendered)
                }
                Err(error) => Err(DocCommentRenderWorkerError::Evaluation(error.to_string())),
            }
        };
        let _ = job.reply.send(result);
    }
}

struct RenderedDocCache {
    capacity: usize,
    generation: u64,
    entries: HashMap<DocCommentRenderInputKey, RenderedDocCacheEntry>,
}

struct RenderedDocCacheEntry {
    rendered: String,
    last_used: u64,
}

impl RenderedDocCache {
    fn new(capacity: usize) -> Self {
        Self {
            capacity,
            generation: 0,
            entries: HashMap::with_capacity(capacity),
        }
    }

    fn get(&mut self, key: &DocCommentRenderInputKey) -> Option<String> {
        self.generation = self.generation.wrapping_add(1);
        let entry = self.entries.get_mut(key)?;
        entry.last_used = self.generation;
        Some(entry.rendered.clone())
    }

    fn insert(&mut self, key: DocCommentRenderInputKey, rendered: String) {
        if self.entries.len() == self.capacity && !self.entries.contains_key(&key) {
            let oldest = self
                .entries
                .iter()
                .min_by_key(|(_, entry)| entry.last_used)
                .map(|(key, _)| key.clone())
                .expect("a full non-zero-capacity cache has an eviction candidate");
            self.entries.remove(&oldest);
        }
        self.generation = self.generation.wrapping_add(1);
        self.entries.insert(
            key,
            RenderedDocCacheEntry {
                rendered,
                last_used: self.generation,
            },
        );
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::{Arc, Barrier, Mutex};

    use sources::Name;

    use super::*;

    #[test]
    fn caches_successful_render_hits_and_evaluates_misses() {
        let calls = Arc::new(AtomicUsize::new(0));
        let worker = counting_worker(4, calls.clone());
        let alpha = render_input("-- alpha\nmy x = 1\n");
        let beta = render_input("-- beta\nmy x = 1\n");

        assert_eq!(worker.render(alpha.clone()).unwrap(), " alpha");
        assert_eq!(worker.render(alpha).unwrap(), " alpha");
        assert_eq!(worker.render(beta).unwrap(), " beta");
        assert_eq!(calls.load(Ordering::SeqCst), 2);
    }

    #[test]
    fn concurrent_same_key_requests_are_single_flight() {
        const REQUESTS: usize = 8;

        let calls = Arc::new(AtomicUsize::new(0));
        let renderer_calls = calls.clone();
        let worker = start_worker_with_renderer(4, move |input| {
            renderer_calls.fetch_add(1, Ordering::SeqCst);
            std::thread::sleep(std::time::Duration::from_millis(25));
            Ok(rendered_body(input))
        })
        .unwrap();
        let input = render_input("-- shared\nmy x = 1\n");
        let barrier = Arc::new(Barrier::new(REQUESTS + 1));
        let clients = (0..REQUESTS)
            .map(|_| {
                let worker = worker.clone();
                let input = input.clone();
                let barrier = barrier.clone();
                std::thread::spawn(move || {
                    barrier.wait();
                    worker.render(input).unwrap()
                })
            })
            .collect::<Vec<_>>();

        barrier.wait();
        for client in clients {
            assert_eq!(client.join().unwrap(), " shared");
        }
        assert_eq!(calls.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn evicts_the_least_recently_used_entry_at_capacity() {
        let calls = Arc::new(AtomicUsize::new(0));
        let worker = counting_worker(2, calls.clone());
        let alpha = render_input("-- alpha\nmy x = 1\n");
        let beta = render_input("-- beta\nmy x = 1\n");
        let gamma = render_input("-- gamma\nmy x = 1\n");

        worker.render(alpha.clone()).unwrap();
        worker.render(beta.clone()).unwrap();
        worker.render(alpha.clone()).unwrap();
        worker.render(gamma).unwrap();
        worker.render(alpha).unwrap();
        worker.render(beta).unwrap();

        assert_eq!(calls.load(Ordering::SeqCst), 4);
    }

    #[test]
    fn identical_doc_content_at_different_source_positions_reuses_the_cache() {
        let calls = Arc::new(AtomicUsize::new(0));
        let worker = counting_worker(4, calls.clone());
        let first = render_input("-- shared content\nmy x = 1\n");
        let moved = render_input("my before = 0\n-- shared content\nmy x = 1\n");

        assert_eq!(first.key(), moved.key());
        assert_eq!(worker.render(first).unwrap(), " shared content");
        assert_eq!(worker.render(moved).unwrap(), " shared content");
        assert_eq!(calls.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn real_evaluation_jobs_remain_on_one_resident_os_thread() {
        let worker_thread_ids = Arc::new(Mutex::new(Vec::new()));
        let observed_ids = worker_thread_ids.clone();
        let worker = start_worker_with_renderer(4, move |input| {
            observed_ids
                .lock()
                .unwrap()
                .push(std::thread::current().id());
            evaluate_doc_comment_render_input_markdown_with_embedded_std(input)
        })
        .unwrap();
        let caller_thread = std::thread::current().id();

        let alpha = worker.render(render_input("-- alpha\nmy x = 1\n")).unwrap();
        let beta = worker.render(render_input("-- beta\nmy x = 1\n")).unwrap();

        assert_eq!(alpha, "alpha\n\n");
        assert_eq!(beta, "beta\n\n");
        let ids = worker_thread_ids.lock().unwrap();
        assert_eq!(ids.len(), 2);
        assert_eq!(ids[0], ids[1]);
        assert_ne!(ids[0], caller_thread);
    }

    fn counting_worker(capacity: usize, calls: Arc<AtomicUsize>) -> DocCommentRenderWorker {
        start_worker_with_renderer(capacity, move |input| {
            calls.fetch_add(1, Ordering::SeqCst);
            Ok(rendered_body(input))
        })
        .unwrap()
    }

    fn rendered_body(input: &DocCommentRenderInput) -> String {
        input
            .units()
            .iter()
            .map(|unit| unit.body_source())
            .collect()
    }

    fn render_input(source: &str) -> DocCommentRenderInput {
        let loaded = sources::load(vec![sources::SourceFile {
            module_path: sources::Path::default(),
            source: source.to_string(),
        }]);
        let lower = infer::lowering::lower_loaded_files(&loaded).expect("lower doc fixture");
        let root = lower.modules.root_id();
        let def = lower.modules.value_decls(root, &Name("x".into()))[0].def;
        let doc = lower
            .modules
            .def_doc_comment(def)
            .expect("doc comment should attach to x");
        assert!(infer::doc_comment_render::doc_comment_is_safe_for_yumark_literal_reparse(doc));
        DocCommentRenderInput::from_safe_doc_comment(doc)
    }
}

use super::*;

pub(super) struct Runtime<'a> {
    pub(super) program: &'a Program,
    pub(super) instances: HashMap<InstanceId, Value>,
    pub(super) evaluating_instances: HashSet<InstanceId>,
    pub(super) blocks: HashMap<ExprId, RuntimeBlock>,
    pub(super) case_arms: HashMap<ExprId, RuntimeCaseArms>,
    pub(super) catch_arms: HashMap<ExprId, RuntimeCatchArms>,
    pub(super) continuations: HashMap<ContinuationId, Continuation>,
    pub(super) next_continuation_id: u32,
    pub(super) guard_ids: Vec<GuardId>,
    pub(super) active_frames: Vec<ActiveFrame>,
    pub(super) active_handler_frames: Vec<ActiveHandlerFrame>,
    // Only depth-zero add-id markers can attach a guard to a request in the
    // current scope. Deeper markers stay in active_marker_plans for call/resume
    // transitions and are pushed here after their depth is decremented.
    pub(super) active_add_ids: Vec<ActiveAddIdMarker>,
    pub(super) active_marker_plans: Vec<SharedMarkers>,
    pub(super) scope_state_shadow: Option<ScopeState>,
    pub(super) next_guard_id: u32,
    pub(super) stats: RuntimeStats,
    pub(super) ref_update_update_key: InternedPath,
    pub(super) path_interner: PathInterner,
}

impl<'a> Runtime<'a> {
    pub(super) fn new(program: &'a Program) -> Self {
        let mut path_interner = PathInterner::default();
        let ref_update_update_key = path_interner.intern(&ref_update_update_path());
        Self {
            program,
            instances: HashMap::new(),
            evaluating_instances: HashSet::new(),
            blocks: HashMap::new(),
            case_arms: HashMap::new(),
            catch_arms: HashMap::new(),
            continuations: HashMap::new(),
            next_continuation_id: 0,
            guard_ids: Vec::new(),
            active_frames: Vec::new(),
            active_handler_frames: Vec::new(),
            active_add_ids: Vec::new(),
            active_marker_plans: Vec::new(),
            scope_state_shadow: std::env::var_os("YULANG_VM_SCOPE_STATE_SHADOW")
                .is_some()
                .then(ScopeState::new),
            next_guard_id: 0,
            stats: RuntimeStats::default(),
            ref_update_update_key,
            path_interner,
        }
    }

    pub(super) fn run(&mut self) -> Result<Vec<Value>, RuntimeError> {
        self.run_with_host(&mut |_, _| None)
    }

    pub(super) fn run_with_host<F>(&mut self, host: &mut F) -> Result<Vec<Value>, RuntimeError>
    where
        F: FnMut(&[String], &Value) -> Option<Value>,
    {
        let mut results = Vec::new();
        let mut env = CapturedEnv::default();
        for root in &self.program.roots {
            match root {
                Root::Instance(instance) => {
                    let result = EvalResult::Value(self.eval_instance(*instance)?);
                    results.push(self.resolve_host_requests(result, host)?);
                }
                Root::EvalInstance(instance) => {
                    let result = EvalResult::Value(self.eval_instance(*instance)?);
                    let _ = self.resolve_host_requests(result, host)?;
                }
                Root::Expr(expr) => {
                    let result = self.eval_expr(*expr, &mut env)?;
                    results.push(self.resolve_host_requests(result, host)?);
                }
            };
        }
        Ok(results)
    }

    pub(super) fn record_env_lookup(&mut self, hit: bool, steps: usize) {
        self.stats.env_lookups += 1;
        self.stats.env_lookup_steps += steps as u64;
        if hit {
            self.stats.env_lookup_hits += 1;
        } else {
            self.stats.env_lookup_misses += 1;
        }
    }

    pub(super) fn record_env_insert(&mut self, stats: EnvInsertStats) {
        self.stats.env_inserts += 1;
        if stats.cow_cloned {
            self.stats.env_cow_clones += 1;
            self.stats.env_cow_entries_copied += stats.entries_copied as u64;
        }
        self.stats.env_max_size = self.stats.env_max_size.max(stats.new_size as u64);
    }

    pub(super) fn resolve_host_requests<F>(
        &mut self,
        mut result: EvalResult,
        host: &mut F,
    ) -> Result<Value, RuntimeError>
    where
        F: FnMut(&[String], &Value) -> Option<Value>,
    {
        loop {
            match result {
                EvalResult::Value(value) => return Ok(value),
                EvalResult::Request(request) => {
                    self.stats.host_requests += 1;
                    let Some(value) = host(&request.path, &request.payload) else {
                        return Err(RuntimeError::UnhandledEffect { path: request.path });
                    };
                    result = self.resume(request.continuation, value)?;
                }
            }
        }
    }

    pub(super) fn eval_instance(&mut self, instance: InstanceId) -> Result<Value, RuntimeError> {
        self.stats.instance_eval_calls += 1;
        if let Some(value) = self.instances.get(&instance) {
            self.stats.instance_cache_hits += 1;
            return Ok(value.clone());
        }
        self.stats.instance_cache_misses += 1;
        if !self.evaluating_instances.insert(instance) {
            return Err(RuntimeError::RecursiveInstance { instance });
        }
        let control_instance = self
            .program
            .instances
            .get(instance.0 as usize)
            .ok_or(RuntimeError::MissingInstance { instance })?;
        if control_instance.id != instance {
            self.evaluating_instances.remove(&instance);
            return Err(RuntimeError::MismatchedInstanceSlot {
                requested: instance,
                actual: control_instance.id,
            });
        }

        let mut env = CapturedEnv::default();
        let value = self.eval_expr(control_instance.entry, &mut env);
        self.evaluating_instances.remove(&instance);
        let value = strip_value_markers(expect_eval_value(value?)?);
        self.instances.insert(instance, value.clone());
        Ok(value)
    }

    pub(super) fn intern_path(&mut self, path: &[String]) -> InternedPath {
        self.path_interner.intern(path)
    }

    pub(super) fn request_is_ref_update(&self, request: &Request) -> bool {
        request.path_key.id == self.ref_update_update_key.id
    }
}

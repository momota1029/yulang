use crate::lower::LowerState;
use crate::symbols::Name;

pub(crate) fn with_companion_module(
    state: &mut LowerState,
    name: Name,
    f: impl FnOnce(&mut LowerState),
) {
    let saved = state.ctx.enter_module(name);
    state.mark_companion_module(state.ctx.current_module);
    f(state);
    state.ctx.leave_module(saved);
}
